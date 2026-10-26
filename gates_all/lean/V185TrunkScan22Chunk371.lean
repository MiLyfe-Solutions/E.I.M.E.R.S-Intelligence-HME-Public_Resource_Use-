import V185TrunkScan22Chunk370

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3309058 : List Nat := [3, 4, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3309058 : Nat := 118140960795 + 3309058 * 2 ^ 59
def prefixEnd_3309058 : Nat := 4983230072969 + 3 ^ 40 * 3309058 * 2
def baseEnd_3309058 : Nat := 377586059467915450901539

theorem tailTrace_3309058 : CollatzResearch.WordTrace tailWord_3309058 prefixEnd_3309058 377586059467915450901539 := by
  unfold tailWord_3309058
  simp only [CollatzResearch.WordTrace]
  refine ⟨30172815111463870739561957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80460840297236988638831885 30172815111463870739561957)
  ·
    refine ⟨5657402833399475763667867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30172815111463870739561957 5657402833399475763667867)
    ·
      refine ⟨8486104250099213645501801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5657402833399475763667867 8486104250099213645501801)
      ·
        refine ⟨6364578187574410234126351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8486104250099213645501801 6364578187574410234126351)
        ·
          refine ⟨9546867281361615351189527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6364578187574410234126351 9546867281361615351189527)
          ·
            refine ⟨14320300922042423026784291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9546867281361615351189527 14320300922042423026784291)
            ·
              refine ⟨21480451383063634540176437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14320300922042423026784291 21480451383063634540176437)
              ·
                refine ⟨2013792317162215738141541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21480451383063634540176437 2013792317162215738141541)
                ·
                  refine ⟨377586059467915450901539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2013792317162215738141541 377586059467915450901539)
                  ·
                    rfl

theorem cell22_3309058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3309058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309058 prefixEnd_3309058 := by exact prefixLift 3309058
  have htrace : WordTrace (prefixWord ++ tailWord_3309058) baseStart_3309058 baseEnd_3309058 := by
    simpa [prefixWord, tailWord_3309058, baseEnd_3309058] using wordTrace_append hprefix tailTrace_3309058
  have hstable : (prefixWord ++ tailWord_3309058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309058).length < 2 ^ (prefixWord ++ tailWord_3309058).sum := by decide
  have hdescent : baseEnd_3309058 < baseStart_3309058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309060 : List Nat := [2, 3, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_3309060 : Nat := 118140960795 + 3309060 * 2 ^ 59
def prefixEnd_3309060 : Nat := 4983230072969 + 3 ^ 40 * 3309060 * 2
def baseEnd_3309060 : Nat := 1132758863044619014154611

theorem tailTrace_3309060 : CollatzResearch.WordTrace tailWord_3309060 prefixEnd_3309060 1132758863044619014154611 := by
  unfold tailWord_3309060
  simp only [CollatzResearch.WordTrace]
  refine ⟨60345666695924118649910317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80460888927898824866547089 60345666695924118649910317)
  ·
    refine ⟨22629625010971544493716369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60345666695924118649910317 22629625010971544493716369)
    ·
      refine ⟨16972218758228658370287277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22629625010971544493716369 16972218758228658370287277)
      ·
        refine ⟨6364582034335746888857729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16972218758228658370287277 6364582034335746888857729)
        ·
          refine ⟨4773436525751810166643297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6364582034335746888857729 4773436525751810166643297)
          ·
            refine ⟨3580077394313857624982473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4773436525751810166643297 3580077394313857624982473)
            ·
              refine ⟨2685058045735393218736855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3580077394313857624982473 2685058045735393218736855)
              ·
                refine ⟨4027587068603089828105283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2685058045735393218736855 4027587068603089828105283)
                ·
                  refine ⟨6041380602904634742157925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027587068603089828105283 6041380602904634742157925)
                  ·
                    refine ⟨1132758863044619014154611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6041380602904634742157925 1132758863044619014154611)
                    ·
                      rfl

theorem cell22_3309060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_3309060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309060 prefixEnd_3309060 := by exact prefixLift 3309060
  have htrace : WordTrace (prefixWord ++ tailWord_3309060) baseStart_3309060 baseEnd_3309060 := by
    simpa [prefixWord, tailWord_3309060, baseEnd_3309060] using wordTrace_append hprefix tailTrace_3309060
  have hstable : (prefixWord ++ tailWord_3309060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309060).length < 2 ^ (prefixWord ++ tailWord_3309060).sum := by decide
  have hdescent : baseEnd_3309060 < baseStart_3309060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309144 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_3309144 : Nat := 118140960795 + 3309144 * 2 ^ 59
def prefixEnd_3309144 : Nat := 4983230072969 + 3 ^ 40 * 3309144 * 2
def baseEnd_3309144 : Nat := 1132787617961270795054353

theorem tailTrace_3309144 : CollatzResearch.WordTrace tailWord_3309144 prefixEnd_3309144 1132787617961270795054353 := by
  unfold tailWord_3309144
  simp only [CollatzResearch.WordTrace]
  refine ⟨60347198561771959822939243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80462931415695946430585657 60347198561771959822939243)
  ·
    refine ⟨90520797842657939734408865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60347198561771959822939243 90520797842657939734408865)
    ·
      refine ⟨67890598381993454800806649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90520797842657939734408865 67890598381993454800806649)
      ·
        refine ⟨50917948786495091100604987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67890598381993454800806649 50917948786495091100604987)
        ·
          refine ⟨76376923179742636650907481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50917948786495091100604987 76376923179742636650907481)
          ·
            refine ⟨57282692384806977488180611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76376923179742636650907481 57282692384806977488180611)
            ·
              refine ⟨85924038577210466232270917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57282692384806977488180611 85924038577210466232270917)
              ·
                refine ⟨16110757233226962418550797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85924038577210466232270917 16110757233226962418550797)
                ·
                  refine ⟨6041533962460110906956549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16110757233226962418550797 6041533962460110906956549)
                  ·
                    refine ⟨1132787617961270795054353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6041533962460110906956549 1132787617961270795054353)
                    ·
                      rfl

theorem cell22_3309144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_3309144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309144 prefixEnd_3309144 := by exact prefixLift 3309144
  have htrace : WordTrace (prefixWord ++ tailWord_3309144) baseStart_3309144 baseEnd_3309144 := by
    simpa [prefixWord, tailWord_3309144, baseEnd_3309144] using wordTrace_append hprefix tailTrace_3309144
  have hstable : (prefixWord ++ tailWord_3309144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309144).length < 2 ^ (prefixWord ++ tailWord_3309144).sum := by decide
  have hdescent : baseEnd_3309144 < baseStart_3309144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309148 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 5]
def baseStart_3309148 : Nat := 118140960795 + 3309148 * 2 ^ 59
def prefixEnd_3309148 : Nat := 4983230072969 + 3 ^ 40 * 3309148 * 2
def baseEnd_3309148 : Nat := 377596329081005372651447

theorem tailTrace_3309148 : CollatzResearch.WordTrace tailWord_3309148 prefixEnd_3309148 377596329081005372651447 := by
  unfold tailWord_3309148
  simp only [CollatzResearch.WordTrace]
  refine ⟨60347271507764714164512049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80463028677019618886016065 60347271507764714164512049)
  ·
    refine ⟨45260453630823535623384037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60347271507764714164512049 45260453630823535623384037)
    ·
      refine ⟨8486335055779412929384507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45260453630823535623384037 8486335055779412929384507)
      ·
        refine ⟨12729502583669119394076761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8486335055779412929384507 12729502583669119394076761)
        ·
          refine ⟨9547126937751839545557571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12729502583669119394076761 9547126937751839545557571)
          ·
            refine ⟨14320690406627759318336357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9547126937751839545557571 14320690406627759318336357)
            ·
              refine ⟨2685129451242704872188067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14320690406627759318336357 2685129451242704872188067)
              ·
                refine ⟨4027694176864057308282101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2685129451242704872188067 4027694176864057308282101)
                ·
                  refine ⟨377596329081005372651447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4027694176864057308282101 377596329081005372651447)
                  ·
                    rfl

theorem cell22_3309148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_3309148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309148 prefixEnd_3309148 := by exact prefixLift 3309148
  have htrace : WordTrace (prefixWord ++ tailWord_3309148) baseStart_3309148 baseEnd_3309148 := by
    simpa [prefixWord, tailWord_3309148, baseEnd_3309148] using wordTrace_append hprefix tailTrace_3309148
  have hstable : (prefixWord ++ tailWord_3309148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309148).length < 2 ^ (prefixWord ++ tailWord_3309148).sum := by decide
  have hdescent : baseEnd_3309148 < baseStart_3309148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309159 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 6]
def baseStart_3309159 : Nat := 118140960795 + 3309159 * 2 ^ 59
def prefixEnd_3309159 : Nat := 4983230072969 + 3 ^ 40 * 3309159 * 2
def baseEnd_3309159 : Nat := 377597584255938585309769

theorem tailTrace_3309159 : CollatzResearch.WordTrace tailWord_3309159 prefixEnd_3309159 377597584255938585309769 := by
  unfold tailWord_3309159
  simp only [CollatzResearch.WordTrace]
  refine ⟨120694944218489577207674531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80463296145659718138449687 120694944218489577207674531)
  ·
    refine ⟨181042416327734365811511797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120694944218489577207674531 181042416327734365811511797)
    ·
      refine ⟨16972726530725096794829231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181042416327734365811511797 16972726530725096794829231)
      ·
        refine ⟨25459089796087645192243847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16972726530725096794829231 25459089796087645192243847)
        ·
          refine ⟨38188634694131467788365771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25459089796087645192243847 38188634694131467788365771)
          ·
            refine ⟨57282952041197201682548657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38188634694131467788365771 57282952041197201682548657)
            ·
              refine ⟨42962214030897901261911493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57282952041197201682548657 42962214030897901261911493)
              ·
                refine ⟨8055415130793356486608405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42962214030897901261911493 8055415130793356486608405)
                ·
                  refine ⟨377597584255938585309769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8055415130793356486608405 377597584255938585309769)
                  ·
                    rfl

theorem cell22_3309159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 6].length) (baseStart_3309159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309159 prefixEnd_3309159 := by exact prefixLift 3309159
  have htrace : WordTrace (prefixWord ++ tailWord_3309159) baseStart_3309159 baseEnd_3309159 := by
    simpa [prefixWord, tailWord_3309159, baseEnd_3309159] using wordTrace_append hprefix tailTrace_3309159
  have hstable : (prefixWord ++ tailWord_3309159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309159).length < 2 ^ (prefixWord ++ tailWord_3309159).sum := by decide
  have hdescent : baseEnd_3309159 < baseStart_3309159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309161 : List Nat := [1, 2, 1, 1, 1, 4, 5, 2, 1, 4]
def baseStart_3309161 : Nat := 118140960795 + 3309161 * 2 ^ 59
def prefixEnd_3309161 : Nat := 4983230072969 + 3 ^ 40 * 3309161 * 2
def baseEnd_3309161 : Nat := 1132793437408688417379301

theorem tailTrace_3309161 : CollatzResearch.WordTrace tailWord_3309161 prefixEnd_3309161 1132793437408688417379301 := by
  unfold tailWord_3309161
  simp only [CollatzResearch.WordTrace]
  refine ⟨120695017164482331549247337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80463344776321554366164891 120695017164482331549247337)
  ·
    refine ⟨90521262873361748661935503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120695017164482331549247337 90521262873361748661935503)
    ·
      refine ⟨135781894310042622992903255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90521262873361748661935503 135781894310042622992903255)
      ·
        refine ⟨203672841465063934489354883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135781894310042622992903255 203672841465063934489354883)
        ·
          refine ⟨305509262197595901734032325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203672841465063934489354883 305509262197595901734032325)
          ·
            refine ⟨57282986662049231575131061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305509262197595901734032325 57282986662049231575131061)
            ·
              refine ⟨5370279999567115460168537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57282986662049231575131061 5370279999567115460168537)
              ·
                refine ⟨4027709999675336595126403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5370279999567115460168537 4027709999675336595126403)
                ·
                  refine ⟨6041564999513004892689605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4027709999675336595126403 6041564999513004892689605)
                  ·
                    refine ⟨1132793437408688417379301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6041564999513004892689605 1132793437408688417379301)
                    ·
                      rfl

theorem cell22_3309161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_3309161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309161 prefixEnd_3309161 := by exact prefixLift 3309161
  have htrace : WordTrace (prefixWord ++ tailWord_3309161) baseStart_3309161 baseEnd_3309161 := by
    simpa [prefixWord, tailWord_3309161, baseEnd_3309161] using wordTrace_append hprefix tailTrace_3309161
  have hstable : (prefixWord ++ tailWord_3309161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309161).length < 2 ^ (prefixWord ++ tailWord_3309161).sum := by decide
  have hdescent : baseEnd_3309161 < baseStart_3309161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309193 : List Nat := [1, 2, 1, 1, 4, 1, 6, 2, 4]
def baseStart_3309193 : Nat := 118140960795 + 3309193 * 2 ^ 59
def prefixEnd_3309193 : Nat := 4983230072969 + 3 ^ 40 * 3309193 * 2
def baseEnd_3309193 : Nat := 377601463887550333526401

theorem tailTrace_3309193 : CollatzResearch.WordTrace tailWord_3309193 prefixEnd_3309193 377601463887550333526401 := by
  unfold tailWord_3309193
  simp only [CollatzResearch.WordTrace]
  refine ⟨120696184300366401014412233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80464122866910934009608155 120696184300366401014412233)
  ·
    refine ⟨90522138225274800760809175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120696184300366401014412233 90522138225274800760809175)
    ·
      refine ⟨135783207337912201141213763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90522138225274800760809175 135783207337912201141213763)
      ·
        refine ⟨203674811006868301711820645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135783207337912201141213763 203674811006868301711820645)
        ·
          refine ⟨38189027063787806570966371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203674811006868301711820645 38189027063787806570966371)
          ·
            refine ⟨57283540595681709856449557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38189027063787806570966371 57283540595681709856449557)
            ·
              refine ⟨2685165965422580149521073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57283540595681709856449557 2685165965422580149521073)
              ·
                refine ⟨2013874474066935112140805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2685165965422580149521073 2013874474066935112140805)
                ·
                  refine ⟨377601463887550333526401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2013874474066935112140805 377601463887550333526401)
                  ·
                    rfl

theorem cell22_3309193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 4].length) (baseStart_3309193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309193 prefixEnd_3309193 := by exact prefixLift 3309193
  have htrace : WordTrace (prefixWord ++ tailWord_3309193) baseStart_3309193 baseEnd_3309193 := by
    simpa [prefixWord, tailWord_3309193, baseEnd_3309193] using wordTrace_append hprefix tailTrace_3309193
  have hstable : (prefixWord ++ tailWord_3309193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309193).length < 2 ^ (prefixWord ++ tailWord_3309193).sum := by decide
  have hdescent : baseEnd_3309193 < baseStart_3309193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309208 : List Nat := [2, 1, 2, 4, 1, 2, 2, 3, 2, 3]
def baseStart_3309208 : Nat := 118140960795 + 3309208 * 2 ^ 59
def prefixEnd_3309208 : Nat := 4983230072969 + 3 ^ 40 * 3309208 * 2
def baseEnd_3309208 : Nat := 1132809526469195961454157

theorem tailTrace_3309208 : CollatzResearch.WordTrace tailWord_3309208 prefixEnd_3309208 1132809526469195961454157 := by
  unfold tailWord_3309208
  simp only [CollatzResearch.WordTrace]
  refine ⟨60348365697656029288104139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80464487596874705717472185 60348365697656029288104139)
  ·
    refine ⟨90522548546484043932156209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60348365697656029288104139 90522548546484043932156209)
    ·
      refine ⟨67891911409863032949117157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90522548546484043932156209 67891911409863032949117157)
      ·
        refine ⟨12729733389349318677959467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67891911409863032949117157 12729733389349318677959467)
        ·
          refine ⟨19094600084023978016939201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12729733389349318677959467 19094600084023978016939201)
          ·
            refine ⟨14320950063017983512704401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19094600084023978016939201 14320950063017983512704401)
            ·
              refine ⟨10740712547263487634528301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14320950063017983512704401 10740712547263487634528301)
              ·
                refine ⟨4027767205223807862948113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10740712547263487634528301 4027767205223807862948113)
                ·
                  refine ⟨3020825403917855897211085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4027767205223807862948113 3020825403917855897211085)
                  ·
                    refine ⟨1132809526469195961454157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3020825403917855897211085 1132809526469195961454157)
                    ·
                      rfl

theorem cell22_3309208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_3309208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309208 prefixEnd_3309208 := by exact prefixLift 3309208
  have htrace : WordTrace (prefixWord ++ tailWord_3309208) baseStart_3309208 baseEnd_3309208 := by
    simpa [prefixWord, tailWord_3309208, baseEnd_3309208] using wordTrace_append hprefix tailTrace_3309208
  have hstable : (prefixWord ++ tailWord_3309208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309208).length < 2 ^ (prefixWord ++ tailWord_3309208).sum := by decide
  have hdescent : baseEnd_3309208 < baseStart_3309208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309238 : List Nat := [5, 1, 3, 1, 1, 2, 9]
def baseStart_3309238 : Nat := 118140960795 + 3309238 * 2 ^ 59
def prefixEnd_3309238 : Nat := 4983230072969 + 3 ^ 40 * 3309238 * 2
def baseEnd_3309238 : Nat := 41956288743788366044595

theorem tailTrace_3309238 : CollatzResearch.WordTrace tailWord_3309238 prefixEnd_3309238 41956288743788366044595 := by
  unfold tailWord_3309238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543614099075210856237523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80465217056802249133200245 7543614099075210856237523)
  ·
    refine ⟨11315421148612816284356285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7543614099075210856237523 11315421148612816284356285)
    ·
      refine ⟨4243282930729806106633607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11315421148612816284356285 4243282930729806106633607)
      ·
        refine ⟨6364924396094709159950411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243282930729806106633607 6364924396094709159950411)
        ·
          refine ⟨9547386594142063739925617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6364924396094709159950411 9547386594142063739925617)
          ·
            refine ⟨7160539945606547804944213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9547386594142063739925617 7160539945606547804944213)
            ·
              refine ⟨41956288743788366044595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7160539945606547804944213 41956288743788366044595)
              ·
                rfl

theorem cell22_3309238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 9].length) (baseStart_3309238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309238 prefixEnd_3309238 := by exact prefixLift 3309238
  have htrace : WordTrace (prefixWord ++ tailWord_3309238) baseStart_3309238 baseEnd_3309238 := by
    simpa [prefixWord, tailWord_3309238, baseEnd_3309238] using wordTrace_append hprefix tailTrace_3309238
  have hstable : (prefixWord ++ tailWord_3309238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309238).length < 2 ^ (prefixWord ++ tailWord_3309238).sum := by decide
  have hdescent : baseEnd_3309238 < baseStart_3309238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309264 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_3309264 : Nat := 118140960795 + 3309264 * 2 ^ 59
def prefixEnd_3309264 : Nat := 4983230072969 + 3 ^ 40 * 3309264 * 2
def baseEnd_3309264 : Nat := 1132828696413630482053985

theorem tailTrace_3309264 : CollatzResearch.WordTrace tailWord_3309264 prefixEnd_3309264 1132828696413630482053985 := by
  unfold tailWord_3309264
  simp only [CollatzResearch.WordTrace]
  refine ⟨60349386941554590070123423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80465849255406120093497897 60349386941554590070123423)
  ·
    refine ⟨90524080412331885105185135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60349386941554590070123423 90524080412331885105185135)
    ·
      refine ⟨135786120618497827657777703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90524080412331885105185135 135786120618497827657777703)
      ·
        refine ⟨203679180927746741486666555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135786120618497827657777703 203679180927746741486666555)
        ·
          refine ⟨305518771391620112229999833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203679180927746741486666555 305518771391620112229999833)
          ·
            refine ⟨229139078543715084172499875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305518771391620112229999833 229139078543715084172499875)
            ·
              refine ⟨343708617815572626258749813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229139078543715084172499875 343708617815572626258749813)
              ·
                refine ⟨32222682920209933711757795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 343708617815572626258749813 32222682920209933711757795)
                ·
                  refine ⟨48334024380314900567636693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32222682920209933711757795 48334024380314900567636693)
                  ·
                    refine ⟨1132828696413630482053985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48334024380314900567636693 1132828696413630482053985)
                    ·
                      rfl

theorem cell22_3309264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_3309264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309264 prefixEnd_3309264 := by exact prefixLift 3309264
  have htrace : WordTrace (prefixWord ++ tailWord_3309264) baseStart_3309264 baseEnd_3309264 := by
    simpa [prefixWord, tailWord_3309264, baseEnd_3309264] using wordTrace_append hprefix tailTrace_3309264
  have hstable : (prefixWord ++ tailWord_3309264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309264).length < 2 ^ (prefixWord ++ tailWord_3309264).sum := by decide
  have hdescent : baseEnd_3309264 < baseStart_3309264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309300 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 7]
def baseStart_3309300 : Nat := 118140960795 + 3309300 * 2 ^ 59
def prefixEnd_3309300 : Nat := 4983230072969 + 3 ^ 40 * 3309300 * 2
def baseEnd_3309300 : Nat := 377613673316446129384625

theorem tailTrace_3309300 : CollatzResearch.WordTrace tailWord_3309300 prefixEnd_3309300 377613673316446129384625 := by
  unfold tailWord_3309300
  simp only [CollatzResearch.WordTrace]
  refine ⟨60350043455489379144278677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80466724607319172192371569 60350043455489379144278677)
  ·
    refine ⟨2828908286976064647388063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60350043455489379144278677 2828908286976064647388063)
    ·
      refine ⟨4243362430464096971082095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828908286976064647388063 4243362430464096971082095)
      ·
        refine ⟨6365043645696145456623143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243362430464096971082095 6365043645696145456623143)
        ·
          refine ⟨9547565468544218184934715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365043645696145456623143 9547565468544218184934715)
          ·
            refine ⟨14321348202816327277402073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9547565468544218184934715 14321348202816327277402073)
            ·
              refine ⟨10741011152112245458051555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14321348202816327277402073 10741011152112245458051555)
              ·
                refine ⟨16111516728168368187077333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10741011152112245458051555 16111516728168368187077333)
                ·
                  refine ⟨377613673316446129384625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16111516728168368187077333 377613673316446129384625)
                  ·
                    rfl

theorem cell22_3309300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_3309300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309300 prefixEnd_3309300 := by exact prefixLift 3309300
  have htrace : WordTrace (prefixWord ++ tailWord_3309300) baseStart_3309300 baseEnd_3309300 := by
    simpa [prefixWord, tailWord_3309300, baseEnd_3309300] using wordTrace_append hprefix tailTrace_3309300
  have hstable : (prefixWord ++ tailWord_3309300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309300).length < 2 ^ (prefixWord ++ tailWord_3309300).sum := by decide
  have hdescent : baseEnd_3309300 < baseStart_3309300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309311 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 6]
def baseStart_3309311 : Nat := 118140960795 + 3309311 * 2 ^ 59
def prefixEnd_3309311 : Nat := 4983230072969 + 3 ^ 40 * 3309311 * 2
def baseEnd_3309311 : Nat := 377614928491379342042947

theorem tailTrace_3309311 : CollatzResearch.WordTrace tailWord_3309311 prefixEnd_3309311 377614928491379342042947 := by
  unfold tailWord_3309311
  simp only [CollatzResearch.WordTrace]
  refine ⟨120700488113938907167207787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80466992075959271444805191 120700488113938907167207787)
  ·
    refine ⟨181050732170908360750811681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120700488113938907167207787 181050732170908360750811681)
    ·
      refine ⟨135788049128181270563108761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181050732170908360750811681 135788049128181270563108761)
      ·
        refine ⟨101841036846135952922331571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135788049128181270563108761 101841036846135952922331571)
        ·
          refine ⟨152761555269203929383497357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101841036846135952922331571 152761555269203929383497357)
          ·
            refine ⟨57285583225951473518811509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152761555269203929383497357 57285583225951473518811509)
            ·
              refine ⟨5370523427432950642388579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57285583225951473518811509 5370523427432950642388579)
              ·
                refine ⟨8055785141149425963582869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5370523427432950642388579 8055785141149425963582869)
                ·
                  refine ⟨377614928491379342042947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8055785141149425963582869 377614928491379342042947)
                  ·
                    rfl

theorem cell22_3309311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 6].length) (baseStart_3309311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309311 prefixEnd_3309311 := by exact prefixLift 3309311
  have htrace : WordTrace (prefixWord ++ tailWord_3309311) baseStart_3309311 baseEnd_3309311 := by
    simpa [prefixWord, tailWord_3309311, baseEnd_3309311] using wordTrace_append hprefix tailTrace_3309311
  have hstable : (prefixWord ++ tailWord_3309311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309311).length < 2 ^ (prefixWord ++ tailWord_3309311).sum := by decide
  have hdescent : baseEnd_3309311 < baseStart_3309311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309330 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3309330 : Nat := 118140960795 + 3309330 * 2 ^ 59
def prefixEnd_3309330 : Nat := 4983230072969 + 3 ^ 40 * 3309330 * 2
def baseEnd_3309330 : Nat := 1132851289562428309903783

theorem tailTrace_3309330 : CollatzResearch.WordTrace tailWord_3309330 prefixEnd_3309330 1132851289562428309903783 := by
  unfold tailWord_3309330
  simp only [CollatzResearch.WordTrace]
  refine ⟨30175295275217518353037361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80467454067246715608099629 30175295275217518353037361)
  ·
    refine ⟨22631471456413138764778021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30175295275217518353037361 22631471456413138764778021)
    ·
      refine ⟨4243400898077463518395879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22631471456413138764778021 4243400898077463518395879)
      ·
        refine ⟨6365101347116195277593819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243400898077463518395879 6365101347116195277593819)
        ·
          refine ⟨9547652020674292916390729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365101347116195277593819 9547652020674292916390729)
          ·
            refine ⟨7160739015505719687293047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9547652020674292916390729 7160739015505719687293047)
            ·
              refine ⟨10741108523258579530939571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160739015505719687293047 10741108523258579530939571)
              ·
                refine ⟨16111662784887869296409357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10741108523258579530939571 16111662784887869296409357)
                ·
                  refine ⟨6041873544332950986153509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16111662784887869296409357 6041873544332950986153509)
                  ·
                    refine ⟨1132851289562428309903783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6041873544332950986153509 1132851289562428309903783)
                    ·
                      rfl

theorem cell22_3309330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3309330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309330 prefixEnd_3309330 := by exact prefixLift 3309330
  have htrace : WordTrace (prefixWord ++ tailWord_3309330) baseStart_3309330 baseEnd_3309330 := by
    simpa [prefixWord, tailWord_3309330, baseEnd_3309330] using wordTrace_append hprefix tailTrace_3309330
  have hstable : (prefixWord ++ tailWord_3309330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309330).length < 2 ^ (prefixWord ++ tailWord_3309330).sum := by decide
  have hdescent : baseEnd_3309330 < baseStart_3309330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309362 : List Nat := [3, 2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_3309362 : Nat := 118140960795 + 3309362 * 2 ^ 59
def prefixEnd_3309362 : Nat := 4983230072969 + 3 ^ 40 * 3309362 * 2
def baseEnd_3309362 : Nat := 377620747938796964367895

theorem tailTrace_3309362 : CollatzResearch.WordTrace tailWord_3309362 prefixEnd_3309362 377620747938796964367895 := by
  unfold tailWord_3309362
  simp only [CollatzResearch.WordTrace]
  refine ⟨30175587059188535719328585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80468232157836095251542893 30175587059188535719328585)
  ·
    refine ⟨22631690294391401789496439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30175587059188535719328585 22631690294391401789496439)
    ·
      refine ⟨33947535441587102684244659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22631690294391401789496439 33947535441587102684244659)
      ·
        refine ⟨50921303162380654026366989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33947535441587102684244659 50921303162380654026366989)
        ·
          refine ⟨19095488685892745259887621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50921303162380654026366989 19095488685892745259887621)
          ·
            refine ⟨3580404128604889736228929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19095488685892745259887621 3580404128604889736228929)
            ·
              refine ⟨2685303096453667302171697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3580404128604889736228929 2685303096453667302171697)
              ·
                refine ⟨2013977322340250476628773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2685303096453667302171697 2013977322340250476628773)
                ·
                  refine ⟨377620747938796964367895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2013977322340250476628773 377620747938796964367895)
                  ·
                    rfl

theorem cell22_3309362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_3309362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309362 prefixEnd_3309362 := by exact prefixLift 3309362
  have htrace : WordTrace (prefixWord ++ tailWord_3309362) baseStart_3309362 baseEnd_3309362 := by
    simpa [prefixWord, tailWord_3309362, baseEnd_3309362] using wordTrace_append hprefix tailTrace_3309362
  have hstable : (prefixWord ++ tailWord_3309362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309362).length < 2 ^ (prefixWord ++ tailWord_3309362).sum := by decide
  have hdescent : baseEnd_3309362 < baseStart_3309362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309373 : List Nat := [1, 4, 1, 4, 1, 1, 3, 7]
def baseStart_3309373 : Nat := 118140960795 + 3309373 * 2 ^ 59
def prefixEnd_3309373 : Nat := 4983230072969 + 3 ^ 40 * 3309373 * 2
def baseEnd_3309373 : Nat := 125874001037910059008739

theorem tailTrace_3309373 : CollatzResearch.WordTrace tailWord_3309373 prefixEnd_3309373 125874001037910059008739 := by
  unfold tailWord_3309373
  simp only [CollatzResearch.WordTrace]
  refine ⟨120702749439714291755964773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80468499626476194503976515 120702749439714291755964773)
  ·
    refine ⟨22631765519946429704243395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120702749439714291755964773 22631765519946429704243395)
    ·
      refine ⟨33947648279919644556365093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22631765519946429704243395 33947648279919644556365093)
      ·
        refine ⟨6365184052484933354318455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33947648279919644556365093 6365184052484933354318455)
        ·
          refine ⟨9547776078727400031477683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365184052484933354318455 9547776078727400031477683)
          ·
            refine ⟨14321664118091100047216525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9547776078727400031477683 14321664118091100047216525)
            ·
              refine ⟨5370624044284162517706197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14321664118091100047216525 5370624044284162517706197)
              ·
                refine ⟨125874001037910059008739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5370624044284162517706197 125874001037910059008739)
                ·
                  rfl

theorem cell22_3309373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 7].length) (baseStart_3309373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309373 prefixEnd_3309373 := by exact prefixLift 3309373
  have htrace : WordTrace (prefixWord ++ tailWord_3309373) baseStart_3309373 baseEnd_3309373 := by
    simpa [prefixWord, tailWord_3309373, baseEnd_3309373] using wordTrace_append hprefix tailTrace_3309373
  have hstable : (prefixWord ++ tailWord_3309373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309373).length < 2 ^ (prefixWord ++ tailWord_3309373).sum := by decide
  have hdescent : baseEnd_3309373 < baseStart_3309373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309386 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_3309386 : Nat := 118140960795 + 3309386 * 2 ^ 59
def prefixEnd_3309386 : Nat := 4983230072969 + 3 ^ 40 * 3309386 * 2
def baseEnd_3309386 : Nat := 1132870459506862830503611

theorem tailTrace_3309386 : CollatzResearch.WordTrace tailWord_3309386 prefixEnd_3309386 1132870459506862830503611 := by
  unfold tailWord_3309386
  simp only [CollatzResearch.WordTrace]
  refine ⟨30175805897166798744047003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80468815725778129984125341 30175805897166798744047003)
  ·
    refine ⟨45263708845750198116070505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30175805897166798744047003 45263708845750198116070505)
    ·
      refine ⟨33947781634312648587052879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45263708845750198116070505 33947781634312648587052879)
      ·
        refine ⟨50921672451468972880579319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33947781634312648587052879 50921672451468972880579319)
        ·
          refine ⟨76382508677203459320868979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50921672451468972880579319 76382508677203459320868979)
          ·
            refine ⟨114573763015805188981303469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76382508677203459320868979 114573763015805188981303469)
            ·
              refine ⟨42965161130926945867988801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114573763015805188981303469 42965161130926945867988801)
              ·
                refine ⟨32223870848195209400991601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42965161130926945867988801 32223870848195209400991601)
                ·
                  refine ⟨24167903136146407050743701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32223870848195209400991601 24167903136146407050743701)
                  ·
                    refine ⟨1132870459506862830503611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24167903136146407050743701 1132870459506862830503611)
                    ·
                      rfl

theorem cell22_3309386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_3309386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309386 prefixEnd_3309386 := by exact prefixLift 3309386
  have htrace : WordTrace (prefixWord ++ tailWord_3309386) baseStart_3309386 baseEnd_3309386 := by
    simpa [prefixWord, tailWord_3309386, baseEnd_3309386] using wordTrace_append hprefix tailTrace_3309386
  have hstable : (prefixWord ++ tailWord_3309386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309386).length < 2 ^ (prefixWord ++ tailWord_3309386).sum := by decide
  have hdescent : baseEnd_3309386 < baseStart_3309386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309401 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 7]
def baseStart_3309401 : Nat := 118140960795 + 3309401 * 2 ^ 59
def prefixEnd_3309401 : Nat := 4983230072969 + 3 ^ 40 * 3309401 * 2
def baseEnd_3309401 : Nat := 377625198104469263792855

theorem tailTrace_3309401 : CollatzResearch.WordTrace tailWord_3309401 prefixEnd_3309401 377625198104469263792855 := by
  unfold tailWord_3309401
  simp only [CollatzResearch.WordTrace]
  refine ⟨120703770683612852537984057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80469180455741901691989371 120703770683612852537984057)
  ·
    refine ⟨90527828012709639403488043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120703770683612852537984057 90527828012709639403488043)
    ·
      refine ⟨135791742019064459105232065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90527828012709639403488043 135791742019064459105232065)
      ·
        refine ⟨101843806514298344328924049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135791742019064459105232065 101843806514298344328924049)
        ·
          refine ⟨76382854885723758246693037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101843806514298344328924049 76382854885723758246693037)
          ·
            refine ⟨28643570582146409342509889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76382854885723758246693037 28643570582146409342509889)
            ·
              refine ⟨21482677936609807006882417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28643570582146409342509889 21482677936609807006882417)
              ·
                refine ⟨16112008452457355255161813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21482677936609807006882417 16112008452457355255161813)
                ·
                  refine ⟨377625198104469263792855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16112008452457355255161813 377625198104469263792855)
                  ·
                    rfl

theorem cell22_3309401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_3309401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309401 prefixEnd_3309401 := by exact prefixLift 3309401
  have htrace : WordTrace (prefixWord ++ tailWord_3309401) baseStart_3309401 baseEnd_3309401 := by
    simpa [prefixWord, tailWord_3309401, baseEnd_3309401] using wordTrace_append hprefix tailTrace_3309401
  have hstable : (prefixWord ++ tailWord_3309401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309401).length < 2 ^ (prefixWord ++ tailWord_3309401).sum := by decide
  have hdescent : baseEnd_3309401 < baseStart_3309401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309422 : List Nat := [4, 1, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_3309422 : Nat := 118140960795 + 3309422 * 2 ^ 59
def prefixEnd_3309422 : Nat := 4983230072969 + 3 ^ 40 * 3309422 * 2
def baseEnd_3309422 : Nat := 1132882783042570736603501

theorem tailTrace_3309422 : CollatzResearch.WordTrace tailWord_3309422 prefixEnd_3309422 1132882783042570736603501 := by
  unfold tailWord_3309422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15088067077067096640562315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80469691077691182082999013 15088067077067096640562315)
  ·
    refine ⟨22632100615600644960843473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15088067077067096640562315 22632100615600644960843473)
    ·
      refine ⟨16974075461700483720632605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22632100615600644960843473 16974075461700483720632605)
      ·
        refine ⟨6365278298137681395237227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16974075461700483720632605 6365278298137681395237227)
        ·
          refine ⟨9547917447206522092855841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365278298137681395237227 9547917447206522092855841)
          ·
            refine ⟨7160938085404891569641881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9547917447206522092855841 7160938085404891569641881)
            ·
              refine ⟨5370703564053668677231411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7160938085404891569641881 5370703564053668677231411)
              ·
                refine ⟨8056055346080503015847117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5370703564053668677231411 8056055346080503015847117)
                ·
                  refine ⟨3021020754780188630942669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8056055346080503015847117 3021020754780188630942669)
                  ·
                    refine ⟨1132882783042570736603501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3021020754780188630942669 1132882783042570736603501)
                    ·
                      rfl

theorem cell22_3309422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_3309422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309422 prefixEnd_3309422 := by exact prefixLift 3309422
  have htrace : WordTrace (prefixWord ++ tailWord_3309422) baseStart_3309422 baseEnd_3309422 := by
    simpa [prefixWord, tailWord_3309422, baseEnd_3309422] using wordTrace_append hprefix tailTrace_3309422
  have hstable : (prefixWord ++ tailWord_3309422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309422).length < 2 ^ (prefixWord ++ tailWord_3309422).sum := by decide
  have hdescent : baseEnd_3309422 < baseStart_3309422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309540 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_3309540 : Nat := 118140960795 + 3309540 * 2 ^ 59
def prefixEnd_3309540 : Nat := 4983230072969 + 3 ^ 40 * 3309540 * 2
def baseEnd_3309540 : Nat := 1132923176854057762153139

theorem tailTrace_3309540 : CollatzResearch.WordTrace tailWord_3309540 prefixEnd_3309540 1132923176854057762153139 := by
  unfold tailWord_3309540
  simp only [CollatzResearch.WordTrace]
  refine ⟨60354420215054639638647037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80472560286739519518196049 60354420215054639638647037)
  ·
    refine ⟨22632907580645489864492639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60354420215054639638647037 22632907580645489864492639)
    ·
      refine ⟨33949361370968234796738959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22632907580645489864492639 33949361370968234796738959)
      ·
        refine ⟨50924042056452352195108439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33949361370968234796738959 50924042056452352195108439)
        ·
          refine ⟨76386063084678528292662659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50924042056452352195108439 76386063084678528292662659)
          ·
            refine ⟨114579094627017792438993989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76386063084678528292662659 114579094627017792438993989)
            ·
              refine ⟨21483580242565836082311373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114579094627017792438993989 21483580242565836082311373)
              ·
                refine ⟨8056342590962188530866765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21483580242565836082311373 8056342590962188530866765)
                ·
                  refine ⟨3021128471610820699075037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8056342590962188530866765 3021128471610820699075037)
                  ·
                    refine ⟨1132923176854057762153139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3021128471610820699075037 1132923176854057762153139)
                    ·
                      rfl

theorem cell22_3309540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_3309540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309540 prefixEnd_3309540 := by exact prefixLift 3309540
  have htrace : WordTrace (prefixWord ++ tailWord_3309540) baseStart_3309540 baseEnd_3309540 := by
    simpa [prefixWord, tailWord_3309540, baseEnd_3309540] using wordTrace_append hprefix tailTrace_3309540
  have hstable : (prefixWord ++ tailWord_3309540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309540).length < 2 ^ (prefixWord ++ tailWord_3309540).sum := by decide
  have hdescent : baseEnd_3309540 < baseStart_3309540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309604 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 5]
def baseStart_3309604 : Nat := 118140960795 + 3309604 * 2 ^ 59
def prefixEnd_3309604 : Nat := 4983230072969 + 3 ^ 40 * 3309604 * 2
def baseEnd_3309604 : Nat := 377648361787327642850981

theorem tailTrace_3309604 : CollatzResearch.WordTrace tailWord_3309604 prefixEnd_3309604 377648361787327642850981 := by
  unfold tailWord_3309604
  simp only [CollatzResearch.WordTrace]
  refine ⟨60355587350938709103811933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80474116467918278805082577 60355587350938709103811933)
  ·
    refine ⟨22633345256602015913929475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60355587350938709103811933 22633345256602015913929475)
    ·
      refine ⟨33950017884903023870894213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22633345256602015913929475 33950017884903023870894213)
      ·
        refine ⟨6365628353419316975792665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33950017884903023870894213 6365628353419316975792665)
        ·
          refine ⟨4774221265064487731844499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6365628353419316975792665 4774221265064487731844499)
          ·
            refine ⟨7161331897596731597766749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4774221265064487731844499 7161331897596731597766749)
            ·
              refine ⟨2685499461598774349162531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7161331897596731597766749 2685499461598774349162531)
              ·
                refine ⟨4028249192398161523743797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2685499461598774349162531 4028249192398161523743797)
                ·
                  refine ⟨377648361787327642850981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4028249192398161523743797 377648361787327642850981)
                  ·
                    rfl

theorem cell22_3309604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_3309604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309604 prefixEnd_3309604 := by exact prefixLift 3309604
  have htrace : WordTrace (prefixWord ++ tailWord_3309604) baseStart_3309604 baseEnd_3309604 := by
    simpa [prefixWord, tailWord_3309604, baseEnd_3309604] using wordTrace_append hprefix tailTrace_3309604
  have hstable : (prefixWord ++ tailWord_3309604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309604).length < 2 ^ (prefixWord ++ tailWord_3309604).sum := by decide
  have hdescent : baseEnd_3309604 < baseStart_3309604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309617 : List Nat := [1, 2, 2, 3, 1, 4, 2, 2, 1, 4]
def baseStart_3309617 : Nat := 118140960795 + 3309617 * 2 ^ 59
def prefixEnd_3309617 : Nat := 4983230072969 + 3 ^ 40 * 3309617 * 2
def baseEnd_3309617 : Nat := 1132949535527655227977903

theorem tailTrace_3309617 : CollatzResearch.WordTrace tailWord_3309617 prefixEnd_3309617 1132949535527655227977903 := by
  unfold tailWord_3309617
  simp only [CollatzResearch.WordTrace]
  refine ⟨120711648850830321427847105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80474432567220214285231403 120711648850830321427847105)
  ·
    refine ⟨90533736638122741070885329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120711648850830321427847105 90533736638122741070885329)
    ·
      refine ⟨67900302478592055803163997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90533736638122741070885329 67900302478592055803163997)
      ·
        refine ⟨25462613429472020926186499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67900302478592055803163997 25462613429472020926186499)
        ·
          refine ⟨38193920144208031389279749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25462613429472020926186499 38193920144208031389279749)
          ·
            refine ⟨7161360027039005885489953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38193920144208031389279749 7161360027039005885489953)
            ·
              refine ⟨5371020020279254414117465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7161360027039005885489953 5371020020279254414117465)
              ·
                refine ⟨4028265015209440810588099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5371020020279254414117465 4028265015209440810588099)
                ·
                  refine ⟨6042397522814161215882149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4028265015209440810588099 6042397522814161215882149)
                  ·
                    refine ⟨1132949535527655227977903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6042397522814161215882149 1132949535527655227977903)
                    ·
                      rfl

theorem cell22_3309617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_3309617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309617 prefixEnd_3309617 := by exact prefixLift 3309617
  have htrace : WordTrace (prefixWord ++ tailWord_3309617) baseStart_3309617 baseEnd_3309617 := by
    simpa [prefixWord, tailWord_3309617, baseEnd_3309617] using wordTrace_append hprefix tailTrace_3309617
  have hstable : (prefixWord ++ tailWord_3309617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309617).length < 2 ^ (prefixWord ++ tailWord_3309617).sum := by decide
  have hdescent : baseEnd_3309617 < baseStart_3309617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309632 : List Nat := [2, 1, 1, 2, 2, 4, 3, 3, 4]
def baseStart_3309632 : Nat := 118140960795 + 3309632 * 2 ^ 59
def prefixEnd_3309632 : Nat := 4983230072969 + 3 ^ 40 * 3309632 * 2
def baseEnd_3309632 : Nat := 377651556778066729617619

theorem tailTrace_3309632 : CollatzResearch.WordTrace tailWord_3309632 prefixEnd_3309632 377651556778066729617619 := by
  unfold tailWord_3309632
  simp only [CollatzResearch.WordTrace]
  refine ⟨60356097972887989494821575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80474797297183985993095433 60356097972887989494821575)
  ·
    refine ⟨90534146959331984242232363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60356097972887989494821575 90534146959331984242232363)
    ·
      refine ⟨135801220438997976363348545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90534146959331984242232363 135801220438997976363348545)
      ·
        refine ⟨101850915329248482272511409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135801220438997976363348545 101850915329248482272511409)
        ·
          refine ⟨76388186496936361704383557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101850915329248482272511409 76388186496936361704383557)
          ·
            refine ⟨14322784968175567819571917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76388186496936361704383557 14322784968175567819571917)
            ·
              refine ⟨5371044363065837932339469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14322784968175567819571917 5371044363065837932339469)
              ·
                refine ⟨2014141636149689224627301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5371044363065837932339469 2014141636149689224627301)
                ·
                  refine ⟨377651556778066729617619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2014141636149689224627301 377651556778066729617619)
                  ·
                    rfl

theorem cell22_3309632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 4].length) (baseStart_3309632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309632 prefixEnd_3309632 := by exact prefixLift 3309632
  have htrace : WordTrace (prefixWord ++ tailWord_3309632) baseStart_3309632 baseEnd_3309632 := by
    simpa [prefixWord, tailWord_3309632, baseEnd_3309632] using wordTrace_append hprefix tailTrace_3309632
  have hstable : (prefixWord ++ tailWord_3309632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309632).length < 2 ^ (prefixWord ++ tailWord_3309632).sum := by decide
  have hdescent : baseEnd_3309632 < baseStart_3309632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309660 : List Nat := [2, 2, 4, 1, 1, 2, 1, 9]
def baseStart_3309660 : Nat := 118140960795 + 3309660 * 2 ^ 59
def prefixEnd_3309660 : Nat := 4983230072969 + 3 ^ 40 * 3309660 * 2
def baseEnd_3309660 : Nat := 125884917256268605461419

theorem tailTrace_3309660 : CollatzResearch.WordTrace tailWord_3309660 prefixEnd_3309660 125884917256268605461419 := by
  unfold tailWord_3309660
  simp only [CollatzResearch.WordTrace]
  refine ⟨60356608594837269885831217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80475478126449693181108289 60356608594837269885831217)
  ·
    refine ⟨45267456446127952414373413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60356608594837269885831217 45267456446127952414373413)
    ·
      refine ⟨8487648083648991077695015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45267456446127952414373413 8487648083648991077695015)
      ·
        refine ⟨12731472125473486616542523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8487648083648991077695015 12731472125473486616542523)
        ·
          refine ⟨19097208188210229924813785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12731472125473486616542523 19097208188210229924813785)
          ·
            refine ⟨14322906141157672443610339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19097208188210229924813785 14322906141157672443610339)
            ·
              refine ⟨21484359211736508665415509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14322906141157672443610339 21484359211736508665415509)
              ·
                refine ⟨125884917256268605461419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21484359211736508665415509 125884917256268605461419)
                ·
                  rfl

theorem cell22_3309660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 9].length) (baseStart_3309660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309660 prefixEnd_3309660 := by exact prefixLift 3309660
  have htrace : WordTrace (prefixWord ++ tailWord_3309660) baseStart_3309660 baseEnd_3309660 := by
    simpa [prefixWord, tailWord_3309660, baseEnd_3309660] using wordTrace_append hprefix tailTrace_3309660
  have hstable : (prefixWord ++ tailWord_3309660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309660).length < 2 ^ (prefixWord ++ tailWord_3309660).sum := by decide
  have hdescent : baseEnd_3309660 < baseStart_3309660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309664 : List Nat := [2, 1, 1, 3, 2, 3, 4, 1, 2, 3]
def baseStart_3309664 : Nat := 118140960795 + 3309664 * 2 ^ 59
def prefixEnd_3309664 : Nat := 4983230072969 + 3 ^ 40 * 3309664 * 2
def baseEnd_3309664 : Nat := 1132965624588162772052759

theorem tailTrace_3309664 : CollatzResearch.WordTrace tailWord_3309664 prefixEnd_3309664 1132965624588162772052759 := by
  unfold tailWord_3309664
  simp only [CollatzResearch.WordTrace]
  refine ⟨60356681540830024227404023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80475575387773365636538697 60356681540830024227404023)
  ·
    refine ⟨90535022311245036341106035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60356681540830024227404023 90535022311245036341106035)
    ·
      refine ⟨135802533466867554511659053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90535022311245036341106035 135802533466867554511659053)
      ·
        refine ⟨50925950050075332941872145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135802533466867554511659053 50925950050075332941872145)
        ·
          refine ⟨38194462537556499706404109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50925950050075332941872145 38194462537556499706404109)
          ·
            refine ⟨14322923451583687389901541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38194462537556499706404109 14322923451583687389901541)
            ·
              refine ⟨2685548147171941385606539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14322923451583687389901541 2685548147171941385606539)
              ·
                refine ⟨4028322220757912078409809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2685548147171941385606539 4028322220757912078409809)
                ·
                  refine ⟨3021241665568434058807357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4028322220757912078409809 3021241665568434058807357)
                  ·
                    refine ⟨1132965624588162772052759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3021241665568434058807357 1132965624588162772052759)
                    ·
                      rfl

theorem cell22_3309664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 4, 1, 2, 3].length) (baseStart_3309664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309664 prefixEnd_3309664 := by exact prefixLift 3309664
  have htrace : WordTrace (prefixWord ++ tailWord_3309664) baseStart_3309664 baseEnd_3309664 := by
    simpa [prefixWord, tailWord_3309664, baseEnd_3309664] using wordTrace_append hprefix tailTrace_3309664
  have hstable : (prefixWord ++ tailWord_3309664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309664).length < 2 ^ (prefixWord ++ tailWord_3309664).sum := by decide
  have hdescent : baseEnd_3309664 < baseStart_3309664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309726 : List Nat := [4, 3, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_3309726 : Nat := 118140960795 + 3309726 * 2 ^ 59
def prefixEnd_3309726 : Nat := 4983230072969 + 3 ^ 40 * 3309726 * 2
def baseEnd_3309726 : Nat := 1132986848455215277002569

theorem tailTrace_3309726 : CollatzResearch.WordTrace tailWord_3309726 prefixEnd_3309726 1132986848455215277002569 := by
  unfold tailWord_3309726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15089453050929429130445629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80477082938290288695710021 15089453050929429130445629)
  ·
    refine ⟨5658544894098535923917111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15089453050929429130445629 5658544894098535923917111)
    ·
      refine ⟨8487817341147803885875667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5658544894098535923917111 8487817341147803885875667)
      ·
        refine ⟨12731726011721705828813501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8487817341147803885875667 12731726011721705828813501)
        ·
          refine ⟨4774397254395639685805063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12731726011721705828813501 4774397254395639685805063)
          ·
            refine ⟨7161595881593459528707595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4774397254395639685805063 7161595881593459528707595)
            ·
              refine ⟨10742393822390189293061393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7161595881593459528707595 10742393822390189293061393)
              ·
                refine ⟨8056795366792641969796045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10742393822390189293061393 8056795366792641969796045)
                ·
                  refine ⟨3021298262547240738673517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8056795366792641969796045 3021298262547240738673517)
                  ·
                    refine ⟨1132986848455215277002569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3021298262547240738673517 1132986848455215277002569)
                    ·
                      rfl

theorem cell22_3309726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_3309726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309726 prefixEnd_3309726 := by exact prefixLift 3309726
  have htrace : WordTrace (prefixWord ++ tailWord_3309726) baseStart_3309726 baseEnd_3309726 := by
    simpa [prefixWord, tailWord_3309726, baseEnd_3309726] using wordTrace_append hprefix tailTrace_3309726
  have hstable : (prefixWord ++ tailWord_3309726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309726).length < 2 ^ (prefixWord ++ tailWord_3309726).sum := by decide
  have hdescent : baseEnd_3309726 < baseStart_3309726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309752 : List Nat := [2, 1, 2, 1, 2, 1, 5, 3, 1, 4]
def baseStart_3309752 : Nat := 118140960795 + 3309752 * 2 ^ 59
def prefixEnd_3309752 : Nat := 4983230072969 + 3 ^ 40 * 3309752 * 2
def baseEnd_3309752 : Nat := 1132995748786559875852489

theorem tailTrace_3309752 : CollatzResearch.WordTrace tailWord_3309752 prefixEnd_3309752 1132995748786559875852489 := by
  unfold tailWord_3309752
  simp only [CollatzResearch.WordTrace]
  refine ⟨60358286352670619742005755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80477715136894159656007673 60358286352670619742005755)
  ·
    refine ⟨90537429529005929613008633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60358286352670619742005755 90537429529005929613008633)
    ·
      refine ⟨67903072146754447209756475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90537429529005929613008633 67903072146754447209756475)
      ·
        refine ⟨101854608220131670814634713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67903072146754447209756475 101854608220131670814634713)
        ·
          refine ⟨76390956165098753110976035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101854608220131670814634713 76390956165098753110976035)
          ·
            refine ⟨114586434247648129666464053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76390956165098753110976035 114586434247648129666464053)
            ·
              refine ⟨10742478210717012156231005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114586434247648129666464053 10742478210717012156231005)
              ·
                refine ⟨4028429329018879558586627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10742478210717012156231005 4028429329018879558586627)
                ·
                  refine ⟨6042643993528319337879941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4028429329018879558586627 6042643993528319337879941)
                  ·
                    refine ⟨1132995748786559875852489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6042643993528319337879941 1132995748786559875852489)
                    ·
                      rfl

theorem cell22_3309752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_3309752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309752 prefixEnd_3309752 := by exact prefixLift 3309752
  have htrace : WordTrace (prefixWord ++ tailWord_3309752) baseStart_3309752 baseEnd_3309752 := by
    simpa [prefixWord, tailWord_3309752, baseEnd_3309752] using wordTrace_append hprefix tailTrace_3309752
  have hstable : (prefixWord ++ tailWord_3309752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309752).length < 2 ^ (prefixWord ++ tailWord_3309752).sum := by decide
  have hdescent : baseEnd_3309752 < baseStart_3309752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309756 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 5]
def baseStart_3309756 : Nat := 118140960795 + 3309756 * 2 ^ 59
def prefixEnd_3309756 : Nat := 4983230072969 + 3 ^ 40 * 3309756 * 2
def baseEnd_3309756 : Nat := 377665706022768399584159

theorem tailTrace_3309756 : CollatzResearch.WordTrace tailWord_3309756 prefixEnd_3309756 377665706022768399584159 := by
  unfold tailWord_3309756
  simp only [CollatzResearch.WordTrace]
  refine ⟨60358359298663374083578561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80477812398217832111438081 60358359298663374083578561)
  ·
    refine ⟨45268769473997530562683921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60358359298663374083578561 45268769473997530562683921)
    ·
      refine ⟨33951577105498147922012941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45268769473997530562683921 33951577105498147922012941)
      ·
        refine ⟨12731841414561805470754853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33951577105498147922012941 12731841414561805470754853)
        ·
          refine ⟨2387220265230338525766535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12731841414561805470754853 2387220265230338525766535)
          ·
            refine ⟨3580830397845507788649803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387220265230338525766535 3580830397845507788649803)
            ·
              refine ⟨5371245596768261682974705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580830397845507788649803 5371245596768261682974705)
              ·
                refine ⟨4028434197576196262231029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5371245596768261682974705 4028434197576196262231029)
                ·
                  refine ⟨377665706022768399584159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4028434197576196262231029 377665706022768399584159)
                  ·
                    rfl

theorem cell22_3309756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_3309756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309756 prefixEnd_3309756 := by exact prefixLift 3309756
  have htrace : WordTrace (prefixWord ++ tailWord_3309756) baseStart_3309756 baseEnd_3309756 := by
    simpa [prefixWord, tailWord_3309756, baseEnd_3309756] using wordTrace_append hprefix tailTrace_3309756
  have hstable : (prefixWord ++ tailWord_3309756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309756).length < 2 ^ (prefixWord ++ tailWord_3309756).sum := by decide
  have hdescent : baseEnd_3309756 < baseStart_3309756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309765 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_3309765 : Nat := 118140960795 + 3309765 * 2 ^ 59
def prefixEnd_3309765 : Nat := 4983230072969 + 3 ^ 40 * 3309765 * 2
def baseEnd_3309765 : Nat := 1133000198952232175277449

theorem tailTrace_3309765 : CollatzResearch.WordTrace tailWord_3309765 prefixEnd_3309765 1133000198952232175277449 := by
  unfold tailWord_3309765
  simp only [CollatzResearch.WordTrace]
  refine ⟨120717046854294142704234749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80478031236196095136156499 120717046854294142704234749)
  ·
    refine ⟨45268892570360303514088031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120717046854294142704234749 45268892570360303514088031)
    ·
      refine ⟨67903338855540455271132047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45268892570360303514088031 67903338855540455271132047)
      ·
        refine ⟨101855008283310682906698071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67903338855540455271132047 101855008283310682906698071)
        ·
          refine ⟨152782512424966024360047107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101855008283310682906698071 152782512424966024360047107)
          ·
            refine ⟨229173768637449036540070661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152782512424966024360047107 229173768637449036540070661)
            ·
              refine ⟨42970081619521694351263249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229173768637449036540070661 42970081619521694351263249)
              ·
                refine ⟨32227561214641270763447437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42970081619521694351263249 32227561214641270763447437)
                ·
                  refine ⟨12085335455490476536292789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32227561214641270763447437 12085335455490476536292789)
                  ·
                    refine ⟨1133000198952232175277449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12085335455490476536292789 1133000198952232175277449)
                    ·
                      rfl

theorem cell22_3309765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_3309765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309765 prefixEnd_3309765 := by exact prefixLift 3309765
  have htrace : WordTrace (prefixWord ++ tailWord_3309765) baseStart_3309765 baseEnd_3309765 := by
    simpa [prefixWord, tailWord_3309765, baseEnd_3309765] using wordTrace_append hprefix tailTrace_3309765
  have hstable : (prefixWord ++ tailWord_3309765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309765).length < 2 ^ (prefixWord ++ tailWord_3309765).sum := by decide
  have hdescent : baseEnd_3309765 < baseStart_3309765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309794 : List Nat := [3, 3, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3309794 : Nat := 118140960795 + 3309794 * 2 ^ 59
def prefixEnd_3309794 : Nat := 4983230072969 + 3 ^ 40 * 3309794 * 2
def baseEnd_3309794 : Nat := 1133010126244885766302361

theorem tailTrace_3309794 : CollatzResearch.WordTrace tailWord_3309794 prefixEnd_3309794 1133010126244885766302361 := by
  unfold tailWord_3309794
  simp only [CollatzResearch.WordTrace]
  refine ⟨30179526142797270164260109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80478736380792720438026957 30179526142797270164260109)
  ·
    refine ⟨11317322303548976311597541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30179526142797270164260109 11317322303548976311597541)
    ·
      refine ⟨2121997931915433058424539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11317322303548976311597541 2121997931915433058424539)
      ·
        refine ⟨3182996897873149587636809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121997931915433058424539 3182996897873149587636809)
        ·
          refine ⟨2387247673404862190727607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3182996897873149587636809 2387247673404862190727607)
          ·
            refine ⟨3580871510107293286091411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387247673404862190727607 3580871510107293286091411)
            ·
              refine ⟨5371307265160939929137117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580871510107293286091411 5371307265160939929137117)
              ·
                refine ⟨2014240224435352473426419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5371307265160939929137117 2014240224435352473426419)
                ·
                  refine ⟨3021360336653028710139629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014240224435352473426419 3021360336653028710139629)
                  ·
                    refine ⟨1133010126244885766302361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3021360336653028710139629 1133010126244885766302361)
                    ·
                      rfl

theorem cell22_3309794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3309794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309794 prefixEnd_3309794 := by exact prefixLift 3309794
  have htrace : WordTrace (prefixWord ++ tailWord_3309794) baseStart_3309794 baseEnd_3309794 := by
    simpa [prefixWord, tailWord_3309794, baseEnd_3309794] using wordTrace_append hprefix tailTrace_3309794
  have hstable : (prefixWord ++ tailWord_3309794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309794).length < 2 ^ (prefixWord ++ tailWord_3309794).sum := by decide
  have hdescent : baseEnd_3309794 < baseStart_3309794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309797 : List Nat := [1, 3, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_3309797 : Nat := 118140960795 + 3309797 * 2 ^ 59
def prefixEnd_3309797 : Nat := 4983230072969 + 3 ^ 40 * 3309797 * 2
def baseEnd_3309797 : Nat := 1133011153206194758477351

theorem tailTrace_3309797 : CollatzResearch.WordTrace tailWord_3309797 prefixEnd_3309797 1133011153206194758477351 := by
  unfold tailWord_3309797
  simp only [CollatzResearch.WordTrace]
  refine ⟨120718213990178212169399645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80478809326785474779599763 120718213990178212169399645)
  ·
    refine ⟨45269330246316829563524867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120718213990178212169399645 45269330246316829563524867)
    ·
      refine ⟨67903995369475244345287301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45269330246316829563524867 67903995369475244345287301)
      ·
        refine ⟨12731999131776608314741369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67903995369475244345287301 12731999131776608314741369)
        ·
          refine ⟨9548999348832456236056027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12731999131776608314741369 9548999348832456236056027)
          ·
            refine ⟨14323499023248684354084041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9548999348832456236056027 14323499023248684354084041)
            ·
              refine ⟨10742624267436513265563031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14323499023248684354084041 10742624267436513265563031)
              ·
                refine ⟨16113936401154769898344547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10742624267436513265563031 16113936401154769898344547)
                ·
                  refine ⟨24170904601732154847516821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16113936401154769898344547 24170904601732154847516821)
                  ·
                    refine ⟨1133011153206194758477351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24170904601732154847516821 1133011153206194758477351)
                    ·
                      rfl

theorem cell22_3309797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_3309797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309797 prefixEnd_3309797 := by exact prefixLift 3309797
  have htrace : WordTrace (prefixWord ++ tailWord_3309797) baseStart_3309797 baseEnd_3309797 := by
    simpa [prefixWord, tailWord_3309797, baseEnd_3309797] using wordTrace_append hprefix tailTrace_3309797
  have hstable : (prefixWord ++ tailWord_3309797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309797).length < 2 ^ (prefixWord ++ tailWord_3309797).sum := by decide
  have hdescent : baseEnd_3309797 < baseStart_3309797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309799 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 4, 3]
def baseStart_3309799 : Nat := 118140960795 + 3309799 * 2 ^ 59
def prefixEnd_3309799 : Nat := 4983230072969 + 3 ^ 40 * 3309799 * 2
def baseEnd_3309799 : Nat := 1133011837847067419927345

theorem tailTrace_3309799 : CollatzResearch.WordTrace tailWord_3309799 prefixEnd_3309799 1133011837847067419927345 := by
  unfold tailWord_3309799
  simp only [CollatzResearch.WordTrace]
  refine ⟨120718286936170966510972451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80478857957447311007314967 120718286936170966510972451)
  ·
    refine ⟨181077430404256449766458677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120718286936170966510972451 181077430404256449766458677)
    ·
      refine ⟨16976009100399042165605501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181077430404256449766458677 16976009100399042165605501)
      ·
        refine ⟨6366003412649640812102063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16976009100399042165605501 6366003412649640812102063)
        ·
          refine ⟨9549005118974461218153095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6366003412649640812102063 9549005118974461218153095)
          ·
            refine ⟨14323507678461691827229643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9549005118974461218153095 14323507678461691827229643)
            ·
              refine ⟨21485261517692537740844465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14323507678461691827229643 21485261517692537740844465)
              ·
                refine ⟨16113946138269403305633349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21485261517692537740844465 16113946138269403305633349)
                ·
                  refine ⟨3021364900925513119806253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16113946138269403305633349 3021364900925513119806253)
                  ·
                    refine ⟨1133011837847067419927345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3021364900925513119806253 1133011837847067419927345)
                    ·
                      rfl

theorem cell22_3309799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_3309799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309799 prefixEnd_3309799 := by exact prefixLift 3309799
  have htrace : WordTrace (prefixWord ++ tailWord_3309799) baseStart_3309799 baseEnd_3309799 := by
    simpa [prefixWord, tailWord_3309799, baseEnd_3309799] using wordTrace_append hprefix tailTrace_3309799
  have hstable : (prefixWord ++ tailWord_3309799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309799).length < 2 ^ (prefixWord ++ tailWord_3309799).sum := by decide
  have hdescent : baseEnd_3309799 < baseStart_3309799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309887 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 5, 4]
def baseStart_3309887 : Nat := 118140960795 + 3309887 * 2 ^ 59
def prefixEnd_3309887 : Nat := 4983230072969 + 3 ^ 40 * 3309887 * 2
def baseEnd_3309887 : Nat := 1133041962045464523727075

theorem tailTrace_3309887 : CollatzResearch.WordTrace tailWord_3309887 prefixEnd_3309887 1133041962045464523727075 := by
  unfold tailWord_3309887
  simp only [CollatzResearch.WordTrace]
  refine ⟨120721496559852157540175915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80480997706568105026783943 120721496559852157540175915)
  ·
    refine ⟨181082244839778236310263873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120721496559852157540175915 181082244839778236310263873)
    ·
      refine ⟨135811683629833677232697905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181082244839778236310263873 135811683629833677232697905)
      ·
        refine ⟨101858762722375257924523429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135811683629833677232697905 101858762722375257924523429)
        ·
          refine ⟨19098518010445360860848143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101858762722375257924523429 19098518010445360860848143)
          ·
            refine ⟨28647777015668041291272215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19098518010445360860848143 28647777015668041291272215)
            ·
              refine ⟨42971665523502061936908323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28647777015668041291272215 42971665523502061936908323)
              ·
                refine ⟨64457498285253092905362485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42971665523502061936908323 64457498285253092905362485)
                ·
                  refine ⟨6042890464242477459877733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64457498285253092905362485 6042890464242477459877733)
                  ·
                    refine ⟨1133041962045464523727075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6042890464242477459877733 1133041962045464523727075)
                    ·
                      rfl

theorem cell22_3309887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 4].length) (baseStart_3309887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309887 prefixEnd_3309887 := by exact prefixLift 3309887
  have htrace : WordTrace (prefixWord ++ tailWord_3309887) baseStart_3309887 baseEnd_3309887 := by
    simpa [prefixWord, tailWord_3309887, baseEnd_3309887] using wordTrace_append hprefix tailTrace_3309887
  have hstable : (prefixWord ++ tailWord_3309887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309887).length < 2 ^ (prefixWord ++ tailWord_3309887).sum := by decide
  have hdescent : baseEnd_3309887 < baseStart_3309887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309919 : List Nat := [1, 1, 2, 3, 1, 2, 3, 5, 4]
def baseStart_3309919 : Nat := 118140960795 + 3309919 * 2 ^ 59
def prefixEnd_3309919 : Nat := 4983230072969 + 3 ^ 40 * 3309919 * 2
def baseEnd_3309919 : Nat := 377684305433142368975659

theorem tailTrace_3309919 : CollatzResearch.WordTrace tailWord_3309919 prefixEnd_3309919 377684305433142368975659 := by
  unfold tailWord_3309919
  simp only [CollatzResearch.WordTrace]
  refine ⟨120722663695736227005340811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80481775797157484670227207 120722663695736227005340811)
  ·
    refine ⟨181083995543604340508011217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120722663695736227005340811 181083995543604340508011217)
    ·
      refine ⟨135812996657703255381008413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181083995543604340508011217 135812996657703255381008413)
      ·
        refine ⟨50929873746638720767878155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135812996657703255381008413 50929873746638720767878155)
        ·
          refine ⟨76394810619958081151817233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50929873746638720767878155 76394810619958081151817233)
          ·
            refine ⟨57296107964968560863862925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76394810619958081151817233 57296107964968560863862925)
            ·
              refine ⟨21486040486863210323948597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57296107964968560863862925 21486040486863210323948597)
              ·
                refine ⟨2014316295643425967870181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21486040486863210323948597 2014316295643425967870181)
                ·
                  refine ⟨377684305433142368975659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2014316295643425967870181 377684305433142368975659)
                  ·
                    rfl

theorem cell22_3309919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 4].length) (baseStart_3309919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309919 prefixEnd_3309919 := by exact prefixLift 3309919
  have htrace : WordTrace (prefixWord ++ tailWord_3309919) baseStart_3309919 baseEnd_3309919 := by
    simpa [prefixWord, tailWord_3309919, baseEnd_3309919] using wordTrace_append hprefix tailTrace_3309919
  have hstable : (prefixWord ++ tailWord_3309919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309919).length < 2 ^ (prefixWord ++ tailWord_3309919).sum := by decide
  have hdescent : baseEnd_3309919 < baseStart_3309919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309964 : List Nat := [2, 2, 1, 2, 1, 4, 4, 6]
def baseStart_3309964 : Nat := 118140960795 + 3309964 * 2 ^ 59
def prefixEnd_3309964 : Nat := 4983230072969 + 3 ^ 40 * 3309964 * 2
def baseEnd_3309964 : Nat := 125896480079895776616871

theorem tailTrace_3309964 : CollatzResearch.WordTrace tailWord_3309964 prefixEnd_3309964 125896480079895776616871 := by
  unfold tailWord_3309964
  simp only [CollatzResearch.WordTrace]
  refine ⟨60362152490286599845364473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80482869987048799793819297 60362152490286599845364473)
  ·
    refine ⟨45271614367714949884023355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60362152490286599845364473 45271614367714949884023355)
    ·
      refine ⟨67907421551572424826035033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45271614367714949884023355 67907421551572424826035033)
      ·
        refine ⟨50930566163679318619526275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67907421551572424826035033 50930566163679318619526275)
        ·
          refine ⟨76395849245518977929289413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50930566163679318619526275 76395849245518977929289413)
          ·
            refine ⟨14324221733534808361741765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76395849245518977929289413 14324221733534808361741765)
            ·
              refine ⟨2685791575037776567826581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14324221733534808361741765 2685791575037776567826581)
              ·
                refine ⟨125896480079895776616871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2685791575037776567826581 125896480079895776616871)
                ·
                  rfl

theorem cell22_3309964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 4, 6].length) (baseStart_3309964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309964 prefixEnd_3309964 := by exact prefixLift 3309964
  have htrace : WordTrace (prefixWord ++ tailWord_3309964) baseStart_3309964 baseEnd_3309964 := by
    simpa [prefixWord, tailWord_3309964, baseEnd_3309964] using wordTrace_append hprefix tailTrace_3309964
  have hstable : (prefixWord ++ tailWord_3309964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309964).length < 2 ^ (prefixWord ++ tailWord_3309964).sum := by decide
  have hdescent : baseEnd_3309964 < baseStart_3309964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3309981 : List Nat := [1, 4, 2, 1, 5, 1, 8]
def baseStart_3309981 : Nat := 118140960795 + 3309981 * 2 ^ 59
def prefixEnd_3309981 : Nat := 4983230072969 + 3 ^ 40 * 3309981 * 2
def baseEnd_3309981 : Nat := 41965708895054800439881

theorem tailTrace_3309981 : CollatzResearch.WordTrace tailWord_3309981 prefixEnd_3309981 41965708895054800439881 := by
  unfold tailWord_3309981
  simp only [CollatzResearch.WordTrace]
  refine ⟨120724925021511611594097797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80483283347674407729398531 120724925021511611594097797)
  ·
    refine ⟨22635923441533427173893337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120724925021511611594097797 22635923441533427173893337)
    ·
      refine ⟨16976942581150070380420003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22635923441533427173893337 16976942581150070380420003)
      ·
        refine ⟨25465413871725105570630005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16976942581150070380420003 25465413871725105570630005)
        ·
          refine ⟨2387382550474228647246563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25465413871725105570630005 2387382550474228647246563)
          ·
            refine ⟨3581073825711342970869845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387382550474228647246563 3581073825711342970869845)
            ·
              refine ⟨41965708895054800439881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3581073825711342970869845 41965708895054800439881)
              ·
                rfl

theorem cell22_3309981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 8].length) (baseStart_3309981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3309981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3309981 prefixEnd_3309981 := by exact prefixLift 3309981
  have htrace : WordTrace (prefixWord ++ tailWord_3309981) baseStart_3309981 baseEnd_3309981 := by
    simpa [prefixWord, tailWord_3309981, baseEnd_3309981] using wordTrace_append hprefix tailTrace_3309981
  have hstable : (prefixWord ++ tailWord_3309981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3309981).length < 2 ^ (prefixWord ++ tailWord_3309981).sum := by decide
  have hdescent : baseEnd_3309981 < baseStart_3309981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3309981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310129 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_3310129 : Nat := 118140960795 + 3310129 * 2 ^ 59
def prefixEnd_3310129 : Nat := 4983230072969 + 3 ^ 40 * 3310129 * 2
def baseEnd_3310129 : Nat := 1133124803591056559176333

theorem tailTrace_3310129 : CollatzResearch.WordTrace tailWord_3310129 prefixEnd_3310129 1133124803591056559176333 := by
  unfold tailWord_3310129
  simp only [CollatzResearch.WordTrace]
  refine ⟨120730323024975432870485441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80486882016650288580323627 120730323024975432870485441)
  ·
    refine ⟨90547742268731574652864081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120730323024975432870485441 90547742268731574652864081)
    ·
      refine ⟨67910806701548680989648061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90547742268731574652864081 67910806701548680989648061)
      ·
        refine ⟨25466552513080755371118023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67910806701548680989648061 25466552513080755371118023)
        ·
          refine ⟨38199828769621133056677035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25466552513080755371118023 38199828769621133056677035)
          ·
            refine ⟨57299743154431699585015553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38199828769621133056677035 57299743154431699585015553)
            ·
              refine ⟨42974807365823774688761665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57299743154431699585015553 42974807365823774688761665)
              ·
                refine ⟨32231105524367831016571249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42974807365823774688761665 32231105524367831016571249)
                ·
                  refine ⟨24173329143275873262428437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32231105524367831016571249 24173329143275873262428437)
                  ·
                    refine ⟨1133124803591056559176333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24173329143275873262428437 1133124803591056559176333)
                    ·
                      rfl

theorem cell22_3310129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_3310129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310129 prefixEnd_3310129 := by exact prefixLift 3310129
  have htrace : WordTrace (prefixWord ++ tailWord_3310129) baseStart_3310129 baseEnd_3310129 := by
    simpa [prefixWord, tailWord_3310129, baseEnd_3310129] using wordTrace_append hprefix tailTrace_3310129
  have hstable : (prefixWord ++ tailWord_3310129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310129).length < 2 ^ (prefixWord ++ tailWord_3310129).sum := by decide
  have hdescent : baseEnd_3310129 < baseStart_3310129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310131 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 3, 3]
def baseStart_3310131 : Nat := 118140960795 + 3310131 * 2 ^ 59
def prefixEnd_3310131 : Nat := 4983230072969 + 3 ^ 40 * 3310131 * 2
def baseEnd_3310131 : Nat := 1133125488231929220626327

theorem tailTrace_3310131 : CollatzResearch.WordTrace tailWord_3310131 prefixEnd_3310131 1133125488231929220626327 := by
  unfold tailWord_3310131
  simp only [CollatzResearch.WordTrace]
  refine ⟨120730395970968187212058247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80486930647312124808038831 120730395970968187212058247)
  ·
    refine ⟨181095593956452280818087371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120730395970968187212058247 181095593956452280818087371)
    ·
      refine ⟨271643390934678421227131057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181095593956452280818087371 271643390934678421227131057)
      ·
        refine ⟨203732543201008815920348293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271643390934678421227131057 203732543201008815920348293)
        ·
          refine ⟨38199851850189152985065305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203732543201008815920348293 38199851850189152985065305)
          ·
            refine ⟨28649888887641864738798979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38199851850189152985065305 28649888887641864738798979)
            ·
              refine ⟨42974833331462797108198469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28649888887641864738798979 42974833331462797108198469)
              ·
                refine ⟨8057781249649274457787213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42974833331462797108198469 8057781249649274457787213)
                ·
                  refine ⟨3021667968618477921670205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8057781249649274457787213 3021667968618477921670205)
                  ·
                    refine ⟨1133125488231929220626327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3021667968618477921670205 1133125488231929220626327)
                    ·
                      rfl

theorem cell22_3310131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 3, 3].length) (baseStart_3310131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310131 prefixEnd_3310131 := by exact prefixLift 3310131
  have htrace : WordTrace (prefixWord ++ tailWord_3310131) baseStart_3310131 baseEnd_3310131 := by
    simpa [prefixWord, tailWord_3310131, baseEnd_3310131] using wordTrace_append hprefix tailTrace_3310131
  have hstable : (prefixWord ++ tailWord_3310131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310131).length < 2 ^ (prefixWord ++ tailWord_3310131).sum := by decide
  have hdescent : baseEnd_3310131 < baseStart_3310131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310144 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 7]
def baseStart_3310144 : Nat := 118140960795 + 3310144 * 2 ^ 59
def prefixEnd_3310144 : Nat := 4983230072969 + 3 ^ 40 * 3310144 * 2
def baseEnd_3310144 : Nat := 377709979465867173350429

theorem tailTrace_3310144 : CollatzResearch.WordTrace tailWord_3310144 prefixEnd_3310144 377709979465867173350429 := by
  unfold tailWord_3310144
  simp only [CollatzResearch.WordTrace]
  refine ⟨60365435059960545216140743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80487246746614060288187657 60365435059960545216140743)
  ·
    refine ⟨90548152589940817824211115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60365435059960545216140743 90548152589940817824211115)
    ·
      refine ⟨135822228884911226736316673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90548152589940817824211115 135822228884911226736316673)
      ·
        refine ⟨101866671663683420052237505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135822228884911226736316673 101866671663683420052237505)
        ·
          refine ⟨76400003747762565039178129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101866671663683420052237505 76400003747762565039178129)
          ·
            refine ⟨57300002810821923779383597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76400003747762565039178129 57300002810821923779383597)
            ·
              refine ⟨21487501054058221417268849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57300002810821923779383597 21487501054058221417268849)
              ·
                refine ⟨16115625790543666062951637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21487501054058221417268849 16115625790543666062951637)
                ·
                  refine ⟨377709979465867173350429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16115625790543666062951637 377709979465867173350429)
                  ·
                    rfl

theorem cell22_3310144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_3310144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310144 prefixEnd_3310144 := by exact prefixLift 3310144
  have htrace : WordTrace (prefixWord ++ tailWord_3310144) baseStart_3310144 baseEnd_3310144 := by
    simpa [prefixWord, tailWord_3310144, baseEnd_3310144] using wordTrace_append hprefix tailTrace_3310144
  have hstable : (prefixWord ++ tailWord_3310144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310144).length < 2 ^ (prefixWord ++ tailWord_3310144).sum := by decide
  have hdescent : baseEnd_3310144 < baseStart_3310144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310159 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 4, 5]
def baseStart_3310159 : Nat := 118140960795 + 3310159 * 2 ^ 59
def prefixEnd_3310159 : Nat := 4983230072969 + 3 ^ 40 * 3310159 * 2
def baseEnd_3310159 : Nat := 1133135073204146480926241

theorem tailTrace_3310159 : CollatzResearch.WordTrace tailWord_3310159 prefixEnd_3310159 1133135073204146480926241 := by
  unfold tailWord_3310159
  simp only [CollatzResearch.WordTrace]
  refine ⟨120731417214866747994077531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80487611476577831996051687 120731417214866747994077531)
  ·
    refine ⟨181097125822300121991116297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120731417214866747994077531 181097125822300121991116297)
    ·
      refine ⟨135822844366725091493337223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181097125822300121991116297 135822844366725091493337223)
      ·
        refine ⟨203734266550087637240005835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135822844366725091493337223 203734266550087637240005835)
        ·
          refine ⟨305601399825131455860008753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203734266550087637240005835 305601399825131455860008753)
          ·
            refine ⟨229201049868848591895006565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305601399825131455860008753 229201049868848591895006565)
            ·
              refine ⟨42975196850409110980313731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229201049868848591895006565 42975196850409110980313731)
              ·
                refine ⟨64462795275613666470470597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42975196850409110980313731 64462795275613666470470597)
                ·
                  refine ⟨12086774114177562463213237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64462795275613666470470597 12086774114177562463213237)
                  ·
                    refine ⟨1133135073204146480926241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12086774114177562463213237 1133135073204146480926241)
                    ·
                      rfl

theorem cell22_3310159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_3310159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310159 prefixEnd_3310159 := by exact prefixLift 3310159
  have htrace : WordTrace (prefixWord ++ tailWord_3310159) baseStart_3310159 baseEnd_3310159 := by
    simpa [prefixWord, tailWord_3310159, baseEnd_3310159] using wordTrace_append hprefix tailTrace_3310159
  have hstable : (prefixWord ++ tailWord_3310159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310159).length < 2 ^ (prefixWord ++ tailWord_3310159).sum := by decide
  have hdescent : baseEnd_3310159 < baseStart_3310159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310253 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3310253 : Nat := 118140960795 + 3310253 * 2 ^ 59
def prefixEnd_3310253 : Nat := 4983230072969 + 3 ^ 40 * 3310253 * 2
def baseEnd_3310253 : Nat := 1133167251325161569075953

theorem tailTrace_3310253 : CollatzResearch.WordTrace tailWord_3310253 prefixEnd_3310253 1133167251325161569075953 := by
  unfold tailWord_3310253
  simp only [CollatzResearch.WordTrace]
  refine ⟨120734845676526202047999413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80489897117684134698666275 120734845676526202047999413)
  ·
    refine ⟨11318891782174331441999945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120734845676526202047999413 11318891782174331441999945)
    ·
      refine ⟨8489168836630748581499959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11318891782174331441999945 8489168836630748581499959)
      ·
        refine ⟨12733753254946122872249939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8489168836630748581499959 12733753254946122872249939)
        ·
          refine ⟨19100629882419184308374909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12733753254946122872249939 19100629882419184308374909)
          ·
            refine ⟨7162736205907194115640591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19100629882419184308374909 7162736205907194115640591)
            ·
              refine ⟨10744104308860791173460887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7162736205907194115640591 10744104308860791173460887)
              ·
                refine ⟨16116156463291186760191331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10744104308860791173460887 16116156463291186760191331)
                ·
                  refine ⟨24174234694936780140286997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16116156463291186760191331 24174234694936780140286997)
                  ·
                    refine ⟨1133167251325161569075953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24174234694936780140286997 1133167251325161569075953)
                    ·
                      rfl

theorem cell22_3310253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3310253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310253 prefixEnd_3310253 := by exact prefixLift 3310253
  have htrace : WordTrace (prefixWord ++ tailWord_3310253) baseStart_3310253 baseEnd_3310253 := by
    simpa [prefixWord, tailWord_3310253, baseEnd_3310253] using wordTrace_append hprefix tailTrace_3310253
  have hstable : (prefixWord ++ tailWord_3310253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310253).length < 2 ^ (prefixWord ++ tailWord_3310253).sum := by decide
  have hdescent : baseEnd_3310253 < baseStart_3310253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310257 : List Nat := [1, 2, 2, 6, 1, 1, 2, 3, 4]
def baseStart_3310257 : Nat := 118140960795 + 3310257 * 2 ^ 59
def prefixEnd_3310257 : Nat := 4983230072969 + 3 ^ 40 * 3310257 * 2
def baseEnd_3310257 : Nat := 377722873535635630658647

theorem tailTrace_3310257 : CollatzResearch.WordTrace tailWord_3310257 prefixEnd_3310257 377722873535635630658647 := by
  unfold tailWord_3310257
  simp only [CollatzResearch.WordTrace]
  refine ⟨120734991568511710731145025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80489994379007807154096683 120734991568511710731145025)
  ·
    refine ⟨90551243676383783048358769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120734991568511710731145025 90551243676383783048358769)
    ·
      refine ⟨67913432757287837286269077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90551243676383783048358769 67913432757287837286269077)
      ·
        refine ⟨3183442160497867372793863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67913432757287837286269077 3183442160497867372793863)
        ·
          refine ⟨4775163240746801059190795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3183442160497867372793863 4775163240746801059190795)
          ·
            refine ⟨7162744861120201588786193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4775163240746801059190795 7162744861120201588786193)
            ·
              refine ⟨5372058645840151191589645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7162744861120201588786193 5372058645840151191589645)
              ·
                refine ⟨2014521992190056696846117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5372058645840151191589645 2014521992190056696846117)
                ·
                  refine ⟨377722873535635630658647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2014521992190056696846117 377722873535635630658647)
                  ·
                    rfl

theorem cell22_3310257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 4].length) (baseStart_3310257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310257 prefixEnd_3310257 := by exact prefixLift 3310257
  have htrace : WordTrace (prefixWord ++ tailWord_3310257) baseStart_3310257 baseEnd_3310257 := by
    simpa [prefixWord, tailWord_3310257, baseEnd_3310257] using wordTrace_append hprefix tailTrace_3310257
  have hstable : (prefixWord ++ tailWord_3310257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310257).length < 2 ^ (prefixWord ++ tailWord_3310257).sum := by decide
  have hdescent : baseEnd_3310257 < baseStart_3310257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310373 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_3310373 : Nat := 118140960795 + 3310373 * 2 ^ 59
def prefixEnd_3310373 : Nat := 4983230072969 + 3 ^ 40 * 3310373 * 2
def baseEnd_3310373 : Nat := 1133208329777521256075585

theorem tailTrace_3310373 : CollatzResearch.WordTrace tailWord_3310373 prefixEnd_3310373 1133208329777521256075585 := by
  unfold tailWord_3310373
  simp only [CollatzResearch.WordTrace]
  refine ⟨120739222436091462542367773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80492814957394308361578515 120739222436091462542367773)
  ·
    refine ⟨45277208413534298453387915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120739222436091462542367773 45277208413534298453387915)
    ·
      refine ⟨67915812620301447680081873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45277208413534298453387915 67915812620301447680081873)
      ·
        refine ⟨50936859465226085760061405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67915812620301447680081873 50936859465226085760061405)
        ·
          refine ⟨19101322299459782160023027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50936859465226085760061405 19101322299459782160023027)
          ·
            refine ⟨28651983449189673240034541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19101322299459782160023027 28651983449189673240034541)
            ·
              refine ⟨10744493793446127465012953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28651983449189673240034541 10744493793446127465012953)
              ·
                refine ⟨8058370345084595598759715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10744493793446127465012953 8058370345084595598759715)
                ·
                  refine ⟨12087555517626893398139573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8058370345084595598759715 12087555517626893398139573)
                  ·
                    refine ⟨1133208329777521256075585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12087555517626893398139573 1133208329777521256075585)
                    ·
                      rfl

theorem cell22_3310373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_3310373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310373 prefixEnd_3310373 := by exact prefixLift 3310373
  have htrace : WordTrace (prefixWord ++ tailWord_3310373) baseStart_3310373 baseEnd_3310373 := by
    simpa [prefixWord, tailWord_3310373, baseEnd_3310373] using wordTrace_append hprefix tailTrace_3310373
  have hstable : (prefixWord ++ tailWord_3310373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310373).length < 2 ^ (prefixWord ++ tailWord_3310373).sum := by decide
  have hdescent : baseEnd_3310373 < baseStart_3310373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310463 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 2, 5]
def baseStart_3310463 : Nat := 118140960795 + 3310463 * 2 ^ 59
def prefixEnd_3310463 : Nat := 4983230072969 + 3 ^ 40 * 3310463 * 2
def baseEnd_3310463 : Nat := 1133239138616791021325309

theorem tailTrace_3310463 : CollatzResearch.WordTrace tailWord_3310463 prefixEnd_3310463 1133239138616791021325309 := by
  unfold tailWord_3310463
  simp only [CollatzResearch.WordTrace]
  refine ⟨120742505005765407913144043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80495003337176938608762695 120742505005765407913144043)
  ·
    refine ⟨181113757508648111869716065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120742505005765407913144043 181113757508648111869716065)
    ·
      refine ⟨135835318131486083902287049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181113757508648111869716065 135835318131486083902287049)
      ·
        refine ⟨101876488598614562926715287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135835318131486083902287049 101876488598614562926715287)
        ·
          refine ⟨152814732897921844390072931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101876488598614562926715287 152814732897921844390072931)
          ·
            refine ⟨229222099346882766585109397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152814732897921844390072931 229222099346882766585109397)
            ·
              refine ⟨10744785906885129683677003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229222099346882766585109397 10744785906885129683677003)
              ·
                refine ⟨16117178860327694525515505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10744785906885129683677003 16117178860327694525515505)
                ·
                  refine ⟨12087884145245770894136629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16117178860327694525515505 12087884145245770894136629)
                  ·
                    refine ⟨1133239138616791021325309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12087884145245770894136629 1133239138616791021325309)
                    ·
                      rfl

theorem cell22_3310463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 2, 5].length) (baseStart_3310463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310463 prefixEnd_3310463 := by exact prefixLift 3310463
  have htrace : WordTrace (prefixWord ++ tailWord_3310463) baseStart_3310463 baseEnd_3310463 := by
    simpa [prefixWord, tailWord_3310463, baseEnd_3310463] using wordTrace_append hprefix tailTrace_3310463
  have hstable : (prefixWord ++ tailWord_3310463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310463).length < 2 ^ (prefixWord ++ tailWord_3310463).sum := by decide
  have hdescent : baseEnd_3310463 < baseStart_3310463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310508 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_3310508 : Nat := 118140960795 + 3310508 * 2 ^ 59
def prefixEnd_3310508 : Nat := 4983230072969 + 3 ^ 40 * 3310508 * 2
def baseEnd_3310508 : Nat := 1133254543036425903950171

theorem tailTrace_3310508 : CollatzResearch.WordTrace tailWord_3310508 prefixEnd_3310508 1133254543036425903950171 := by
  unfold tailWord_3310508
  simp only [CollatzResearch.WordTrace]
  refine ⟨60372073145301190299266089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80496097527068253732354785 60372073145301190299266089)
  ·
    refine ⟨45279054858975892724449567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60372073145301190299266089 45279054858975892724449567)
    ·
      refine ⟨67918582288463839086674351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45279054858975892724449567 67918582288463839086674351)
      ·
        refine ⟨101877873432695758630011527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67918582288463839086674351 101877873432695758630011527)
        ·
          refine ⟨152816810149043637945017291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101877873432695758630011527 152816810149043637945017291)
          ·
            refine ⟨229225215223565456917525937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152816810149043637945017291 229225215223565456917525937)
            ·
              refine ⟨171918911417674092688144453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229225215223565456917525937 171918911417674092688144453)
              ·
                refine ⟨32234795890813892379027085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171918911417674092688144453 32234795890813892379027085)
                ·
                  refine ⟨12088048459055209642135157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32234795890813892379027085 12088048459055209642135157)
                  ·
                    refine ⟨1133254543036425903950171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12088048459055209642135157 1133254543036425903950171)
                    ·
                      rfl

theorem cell22_3310508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_3310508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310508 prefixEnd_3310508 := by exact prefixLift 3310508
  have htrace : WordTrace (prefixWord ++ tailWord_3310508) baseStart_3310508 baseEnd_3310508 := by
    simpa [prefixWord, tailWord_3310508, baseEnd_3310508] using wordTrace_append hprefix tailTrace_3310508
  have hstable : (prefixWord ++ tailWord_3310508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310508).length < 2 ^ (prefixWord ++ tailWord_3310508).sum := by decide
  have hdescent : baseEnd_3310508 < baseStart_3310508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310516 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3310516 : Nat := 118140960795 + 3310516 * 2 ^ 59
def prefixEnd_3310516 : Nat := 4983230072969 + 3 ^ 40 * 3310516 * 2
def baseEnd_3310516 : Nat := 377752427199972183250049

theorem tailTrace_3310516 : CollatzResearch.WordTrace tailWord_3310516 prefixEnd_3310516 377752427199972183250049 := by
  unfold tailWord_3310516
  simp only [CollatzResearch.WordTrace]
  refine ⟨60372219037286698982411701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80496292049715598643215601 60372219037286698982411701)
  ·
    refine ⟨5659895534745628029601097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60372219037286698982411701 5659895534745628029601097)
    ·
      refine ⟨4244921651059221022200823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5659895534745628029601097 4244921651059221022200823)
      ·
        refine ⟨6367382476588831533301235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4244921651059221022200823 6367382476588831533301235)
        ·
          refine ⟨9551073714883247299951853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6367382476588831533301235 9551073714883247299951853)
          ·
            refine ⟨3581652643081217737481945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9551073714883247299951853 3581652643081217737481945)
            ·
              refine ⟨2686239482310913303111459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3581652643081217737481945 2686239482310913303111459)
              ·
                refine ⟨4029359223466369954667189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2686239482310913303111459 4029359223466369954667189)
                ·
                  refine ⟨377752427199972183250049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4029359223466369954667189 377752427199972183250049)
                  ·
                    rfl

theorem cell22_3310516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3310516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310516 prefixEnd_3310516 := by exact prefixLift 3310516
  have htrace : WordTrace (prefixWord ++ tailWord_3310516) baseStart_3310516 baseEnd_3310516 := by
    simpa [prefixWord, tailWord_3310516, baseEnd_3310516] using wordTrace_append hprefix tailTrace_3310516
  have hstable : (prefixWord ++ tailWord_3310516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310516).length < 2 ^ (prefixWord ++ tailWord_3310516).sum := by decide
  have hdescent : baseEnd_3310516 < baseStart_3310516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310557 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3310557 : Nat := 118140960795 + 3310557 * 2 ^ 59
def prefixEnd_3310557 : Nat := 4983230072969 + 3 ^ 40 * 3310557 * 2
def baseEnd_3310557 : Nat := 1133271316737806109475021

theorem tailTrace_3310557 : CollatzResearch.WordTrace tailWord_3310557 prefixEnd_3310557 1133271316737806109475021 := by
  unfold tailWord_3310557
  simp only [CollatzResearch.WordTrace]
  refine ⟨120745933467424861967065925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80497288978283241311377283 120745933467424861967065925)
  ·
    refine ⟨22639862525142161618824861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120745933467424861967065925 22639862525142161618824861)
    ·
      refine ⟨8489948446928310607059323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22639862525142161618824861 8489948446928310607059323)
      ·
        refine ⟨12734922670392465910588985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8489948446928310607059323 12734922670392465910588985)
        ·
          refine ⟨9551192002794349432941739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12734922670392465910588985 9551192002794349432941739)
          ·
            refine ⟨14326788004191524149412609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9551192002794349432941739 14326788004191524149412609)
            ·
              refine ⟨10745091003143643112059457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14326788004191524149412609 10745091003143643112059457)
              ·
                refine ⟨8058818252357732334044593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10745091003143643112059457 8058818252357732334044593)
                ·
                  refine ⟨6044113689268299250533445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8058818252357732334044593 6044113689268299250533445)
                  ·
                    refine ⟨1133271316737806109475021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6044113689268299250533445 1133271316737806109475021)
                    ·
                      rfl

theorem cell22_3310557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3310557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310557 prefixEnd_3310557 := by exact prefixLift 3310557
  have htrace : WordTrace (prefixWord ++ tailWord_3310557) baseStart_3310557 baseEnd_3310557 := by
    simpa [prefixWord, tailWord_3310557, baseEnd_3310557] using wordTrace_append hprefix tailTrace_3310557
  have hstable : (prefixWord ++ tailWord_3310557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310557).length < 2 ^ (prefixWord ++ tailWord_3310557).sum := by decide
  have hdescent : baseEnd_3310557 < baseStart_3310557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310559 : List Nat := [1, 1, 2, 3, 5, 1, 2, 2, 2, 3]
def baseStart_3310559 : Nat := 118140960795 + 3310559 * 2 ^ 59
def prefixEnd_3310559 : Nat := 4983230072969 + 3 ^ 40 * 3310559 * 2
def baseEnd_3310559 : Nat := 1133272001378678770925015

theorem tailTrace_3310559 : CollatzResearch.WordTrace tailWord_3310559 prefixEnd_3310559 1133272001378678770925015 := by
  unfold tailWord_3310559
  simp only [CollatzResearch.WordTrace]
  refine ⟨120746006413417616308638731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80497337608945077539092487 120746006413417616308638731)
  ·
    refine ⟨181119009620126424462958097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120746006413417616308638731 181119009620126424462958097)
    ·
      refine ⟨135839257215094818347218573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181119009620126424462958097 135839257215094818347218573)
      ·
        refine ⟨50939721455660556880206965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135839257215094818347218573 50939721455660556880206965)
        ·
          refine ⟨4775598886468177207519403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50939721455660556880206965 4775598886468177207519403)
          ·
            refine ⟨7163398329702265811279105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4775598886468177207519403 7163398329702265811279105)
            ·
              refine ⟨5372548747276699358459329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7163398329702265811279105 5372548747276699358459329)
              ·
                refine ⟨4029411560457524518844497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5372548747276699358459329 4029411560457524518844497)
                ·
                  refine ⟨3022058670343143389133373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4029411560457524518844497 3022058670343143389133373)
                  ·
                    refine ⟨1133272001378678770925015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022058670343143389133373 1133272001378678770925015)
                    ·
                      rfl

theorem cell22_3310559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 2, 3].length) (baseStart_3310559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310559 prefixEnd_3310559 := by exact prefixLift 3310559
  have htrace : WordTrace (prefixWord ++ tailWord_3310559) baseStart_3310559 baseEnd_3310559 := by
    simpa [prefixWord, tailWord_3310559, baseEnd_3310559] using wordTrace_append hprefix tailTrace_3310559
  have hstable : (prefixWord ++ tailWord_3310559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310559).length < 2 ^ (prefixWord ++ tailWord_3310559).sum := by decide
  have hdescent : baseEnd_3310559 < baseStart_3310559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310604 : List Nat := [2, 2, 1, 2, 3, 2, 1, 5, 1, 3]
def baseStart_3310604 : Nat := 118140960795 + 3310604 * 2 ^ 59
def prefixEnd_3310604 : Nat := 4983230072969 + 3 ^ 40 * 3310604 * 2
def baseEnd_3310604 : Nat := 1133287405798313653549877

theorem tailTrace_3310604 : CollatzResearch.WordTrace tailWord_3310604 prefixEnd_3310604 1133287405798313653549877 := by
  unfold tailWord_3310604
  simp only [CollatzResearch.WordTrace]
  refine ⟨60373823849127294497013433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80498431798836392662684577 60373823849127294497013433)
  ·
    refine ⟨45280367886845470872760075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60373823849127294497013433 45280367886845470872760075)
    ·
      refine ⟨67920551830268206309140113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45280367886845470872760075 67920551830268206309140113)
      ·
        refine ⟨50940413872701154731855085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67920551830268206309140113 50940413872701154731855085)
        ·
          refine ⟨19102655202262933024445657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50940413872701154731855085 19102655202262933024445657)
          ·
            refine ⟨14326991401697199768334243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19102655202262933024445657 14326991401697199768334243)
            ·
              refine ⟨21490487102545799652501365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14326991401697199768334243 21490487102545799652501365)
              ·
                refine ⟨2014733165863668717422003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21490487102545799652501365 2014733165863668717422003)
                ·
                  refine ⟨3022099748795503076133005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014733165863668717422003 3022099748795503076133005)
                  ·
                    refine ⟨1133287405798313653549877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022099748795503076133005 1133287405798313653549877)
                    ·
                      rfl

theorem cell22_3310604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_3310604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310604 prefixEnd_3310604 := by exact prefixLift 3310604
  have htrace : WordTrace (prefixWord ++ tailWord_3310604) baseStart_3310604 baseEnd_3310604 := by
    simpa [prefixWord, tailWord_3310604, baseEnd_3310604] using wordTrace_append hprefix tailTrace_3310604
  have hstable : (prefixWord ++ tailWord_3310604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310604).length < 2 ^ (prefixWord ++ tailWord_3310604).sum := by decide
  have hdescent : baseEnd_3310604 < baseStart_3310604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310610 : List Nat := [3, 2, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_3310610 : Nat := 118140960795 + 3310610 * 2 ^ 59
def prefixEnd_3310610 : Nat := 4983230072969 + 3 ^ 40 * 3310610 * 2
def baseEnd_3310610 : Nat := 1133289459720931637899859

theorem tailTrace_3310610 : CollatzResearch.WordTrace tailWord_3310610 prefixEnd_3310610 1133289459720931637899859 := by
  unfold tailWord_3310610
  simp only [CollatzResearch.WordTrace]
  refine ⟨30186966634058213004686321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80498577690821901345830189 30186966634058213004686321)
  ·
    refine ⟨22640224975543659753514741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30186966634058213004686321 22640224975543659753514741)
    ·
      refine ⟨2122521091457218101892007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22640224975543659753514741 2122521091457218101892007)
      ·
        refine ⟨3183781637185827152838011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2122521091457218101892007 3183781637185827152838011)
        ·
          refine ⟨4775672455778740729257017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3183781637185827152838011 4775672455778740729257017)
          ·
            refine ⟨3581754341834055546942763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4775672455778740729257017 3581754341834055546942763)
            ·
              refine ⟨5372631512751083320414145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3581754341834055546942763 5372631512751083320414145)
              ·
                refine ⟨4029473634563312490310609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5372631512751083320414145 4029473634563312490310609)
                ·
                  refine ⟨3022105225922484367732957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4029473634563312490310609 3022105225922484367732957)
                  ·
                    refine ⟨1133289459720931637899859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022105225922484367732957 1133289459720931637899859)
                    ·
                      rfl

theorem cell22_3310610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_3310610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310610 prefixEnd_3310610 := by exact prefixLift 3310610
  have htrace : WordTrace (prefixWord ++ tailWord_3310610) baseStart_3310610 baseEnd_3310610 := by
    simpa [prefixWord, tailWord_3310610, baseEnd_3310610] using wordTrace_append hprefix tailTrace_3310610
  have hstable : (prefixWord ++ tailWord_3310610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310610).length < 2 ^ (prefixWord ++ tailWord_3310610).sum := by decide
  have hdescent : baseEnd_3310610 < baseStart_3310610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310675 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 4, 4]
def baseStart_3310675 : Nat := 118140960795 + 3310675 * 2 ^ 59
def prefixEnd_3310675 : Nat := 4983230072969 + 3 ^ 40 * 3310675 * 2
def baseEnd_3310675 : Nat := 1133311710549293135024659

theorem tailTrace_3310675 : CollatzResearch.WordTrace tailWord_3310675 prefixEnd_3310675 1133311710549293135024659 := by
  unfold tailWord_3310675
  simp only [CollatzResearch.WordTrace]
  refine ⟨120750237280997368119861479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80500158187331578746574319 120750237280997368119861479)
  ·
    refine ⟨181125355921496052179792219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120750237280997368119861479 181125355921496052179792219)
    ·
      refine ⟨271688033882244078269688329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181125355921496052179792219 271688033882244078269688329)
      ·
        refine ⟨203766025411683058702266247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271688033882244078269688329 203766025411683058702266247)
        ·
          refine ⟨305649038117524588053399371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203766025411683058702266247 305649038117524588053399371)
          ·
            refine ⟨458473557176286882080099057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305649038117524588053399371 458473557176286882080099057)
            ·
              refine ⟨343855167882215161560074293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458473557176286882080099057 343855167882215161560074293)
              ·
                refine ⟨32236421988957671396256965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 343855167882215161560074293 32236421988957671396256965)
                ·
                  refine ⟨6044329122929563386798181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32236421988957671396256965 6044329122929563386798181)
                  ·
                    refine ⟨1133311710549293135024659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6044329122929563386798181 1133311710549293135024659)
                    ·
                      rfl

theorem cell22_3310675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 4].length) (baseStart_3310675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310675 prefixEnd_3310675 := by exact prefixLift 3310675
  have htrace : WordTrace (prefixWord ++ tailWord_3310675) baseStart_3310675 baseEnd_3310675 := by
    simpa [prefixWord, tailWord_3310675, baseEnd_3310675] using wordTrace_append hprefix tailTrace_3310675
  have hstable : (prefixWord ++ tailWord_3310675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310675).length < 2 ^ (prefixWord ++ tailWord_3310675).sum := by decide
  have hdescent : baseEnd_3310675 < baseStart_3310675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310677 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 4, 3]
def baseStart_3310677 : Nat := 118140960795 + 3310677 * 2 ^ 59
def prefixEnd_3310677 : Nat := 4983230072969 + 3 ^ 40 * 3310677 * 2
def baseEnd_3310677 : Nat := 1133312395190165796474653

theorem tailTrace_3310677 : CollatzResearch.WordTrace tailWord_3310677 prefixEnd_3310677 1133312395190165796474653 := by
  unfold tailWord_3310677
  simp only [CollatzResearch.WordTrace]
  refine ⟨120750310226990122461434285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80500206817993414974289523 120750310226990122461434285)
  ·
    refine ⟨45281366335121295923037857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120750310226990122461434285 45281366335121295923037857)
    ·
      refine ⟨33961024751340971942278393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45281366335121295923037857 33961024751340971942278393)
      ·
        refine ⟨25470768563505728956708795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33961024751340971942278393 25470768563505728956708795)
        ·
          refine ⟨38206152845258593435063193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25470768563505728956708795 38206152845258593435063193)
          ·
            refine ⟨28654614633943945076297395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38206152845258593435063193 28654614633943945076297395)
            ·
              refine ⟨42981921950915917614446093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28654614633943945076297395 42981921950915917614446093)
              ·
                refine ⟨16118220731593469105417285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42981921950915917614446093 16118220731593469105417285)
                ·
                  refine ⟨3022166387173775457265741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16118220731593469105417285 3022166387173775457265741)
                  ·
                    refine ⟨1133312395190165796474653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022166387173775457265741 1133312395190165796474653)
                    ·
                      rfl

theorem cell22_3310677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_3310677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310677 prefixEnd_3310677 := by exact prefixLift 3310677
  have htrace : WordTrace (prefixWord ++ tailWord_3310677) baseStart_3310677 baseEnd_3310677 := by
    simpa [prefixWord, tailWord_3310677, baseEnd_3310677] using wordTrace_append hprefix tailTrace_3310677
  have hstable : (prefixWord ++ tailWord_3310677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310677).length < 2 ^ (prefixWord ++ tailWord_3310677).sum := by decide
  have hdescent : baseEnd_3310677 < baseStart_3310677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310752 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 5]
def baseStart_3310752 : Nat := 118140960795 + 3310752 * 2 ^ 59
def prefixEnd_3310752 : Nat := 4983230072969 + 3 ^ 40 * 3310752 * 2
def baseEnd_3310752 : Nat := 377779356407630200283141

theorem tailTrace_3310752 : CollatzResearch.WordTrace tailWord_3310752 prefixEnd_3310752 377779356407630200283141 := by
  unfold tailWord_3310752
  simp only [CollatzResearch.WordTrace]
  refine ⟨60376522850859205135207255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80502030467812273513609673 60376522850859205135207255)
  ·
    refine ⟨90564784276288807702810883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60376522850859205135207255 90564784276288807702810883)
    ·
      refine ⟨135847176414433211554216325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90564784276288807702810883 135847176414433211554216325)
      ·
        refine ⟨25471345577706227166415561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135847176414433211554216325 25471345577706227166415561)
        ·
          refine ⟨19103509183279670374811671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25471345577706227166415561 19103509183279670374811671)
          ·
            refine ⟨28655263774919505562217507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19103509183279670374811671 28655263774919505562217507)
            ·
              refine ⟨42982895662379258343326261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28655263774919505562217507 42982895662379258343326261)
              ·
                refine ⟨4029646468348055469686837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42982895662379258343326261 4029646468348055469686837)
                ·
                  refine ⟨377779356407630200283141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4029646468348055469686837 377779356407630200283141)
                  ·
                    rfl

theorem cell22_3310752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_3310752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310752 prefixEnd_3310752 := by exact prefixLift 3310752
  have htrace : WordTrace (prefixWord ++ tailWord_3310752) baseStart_3310752 baseEnd_3310752 := by
    simpa [prefixWord, tailWord_3310752, baseEnd_3310752] using wordTrace_append hprefix tailTrace_3310752
  have hstable : (prefixWord ++ tailWord_3310752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310752).length < 2 ^ (prefixWord ++ tailWord_3310752).sum := by decide
  have hdescent : baseEnd_3310752 < baseStart_3310752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310827 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 1, 6]
def baseStart_3310827 : Nat := 118140960795 + 3310827 * 2 ^ 59
def prefixEnd_3310827 : Nat := 4983230072969 + 3 ^ 40 * 3310827 * 2
def baseEnd_3310827 : Nat := 1133363743255615405224193

theorem tailTrace_3310827 : CollatzResearch.WordTrace tailWord_3310827 prefixEnd_3310827 1133363743255615405224193 := by
  unfold tailWord_3310827
  simp only [CollatzResearch.WordTrace]
  refine ⟨120755781176446698079394735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80503854117631132052929823 120755781176446698079394735)
  ·
    refine ⟨181133671764670047119092103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120755781176446698079394735 181133671764670047119092103)
    ·
      refine ⟨271700507647005070678638155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181133671764670047119092103 271700507647005070678638155)
      ·
        refine ⟨407550761470507606017957233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271700507647005070678638155 407550761470507606017957233)
        ·
          refine ⟨305663071102880704513467925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407550761470507606017957233 305663071102880704513467925)
          ·
            refine ⟨14327956457947533024068809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 305663071102880704513467925 14327956457947533024068809)
            ·
              refine ⟨10745967343460649768051607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14327956457947533024068809 10745967343460649768051607)
              ·
                refine ⟨16118951015190974652077411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10745967343460649768051607 16118951015190974652077411)
                ·
                  refine ⟨24178426522786461978116117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16118951015190974652077411 24178426522786461978116117)
                  ·
                    refine ⟨1133363743255615405224193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24178426522786461978116117 1133363743255615405224193)
                    ·
                      rfl

theorem cell22_3310827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 6].length) (baseStart_3310827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310827 prefixEnd_3310827 := by exact prefixLift 3310827
  have htrace : WordTrace (prefixWord ++ tailWord_3310827) baseStart_3310827 baseEnd_3310827 := by
    simpa [prefixWord, tailWord_3310827, baseEnd_3310827] using wordTrace_append hprefix tailTrace_3310827
  have hstable : (prefixWord ++ tailWord_3310827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310827).length < 2 ^ (prefixWord ++ tailWord_3310827).sum := by decide
  have hdescent : baseEnd_3310827 < baseStart_3310827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310846 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_3310846 : Nat := 118140960795 + 3310846 * 2 ^ 59
def prefixEnd_3310846 : Nat := 4983230072969 + 3 ^ 40 * 3310846 * 2
def baseEnd_3310846 : Nat := 1133370247343905688999135

theorem tailTrace_3310846 : CollatzResearch.WordTrace tailWord_3310846 prefixEnd_3310846 1133370247343905688999135 := by
  unfold tailWord_3310846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15094559270422233040542049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80504316108918576216224261 15094559270422233040542049)
  ·
    refine ⟨11320919452816674780406537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15094559270422233040542049 11320919452816674780406537)
    ·
      refine ⟨8490689589612506085304903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11320919452816674780406537 8490689589612506085304903)
      ·
        refine ⟨12736034384418759127957355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8490689589612506085304903 12736034384418759127957355)
        ·
          refine ⟨19104051576628138691936033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12736034384418759127957355 19104051576628138691936033)
          ·
            refine ⟨14328038682471104018952025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19104051576628138691936033 14328038682471104018952025)
            ·
              refine ⟨10746029011853328014214019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14328038682471104018952025 10746029011853328014214019)
              ·
                refine ⟨16119043517779992021321029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746029011853328014214019 16119043517779992021321029)
                ·
                  refine ⟨3022320659583748503997693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16119043517779992021321029 3022320659583748503997693)
                  ·
                    refine ⟨1133370247343905688999135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022320659583748503997693 1133370247343905688999135)
                    ·
                      rfl

theorem cell22_3310846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_3310846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310846 prefixEnd_3310846 := by exact prefixLift 3310846
  have htrace : WordTrace (prefixWord ++ tailWord_3310846) baseStart_3310846 baseEnd_3310846 := by
    simpa [prefixWord, tailWord_3310846, baseEnd_3310846] using wordTrace_append hprefix tailTrace_3310846
  have hstable : (prefixWord ++ tailWord_3310846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310846).length < 2 ^ (prefixWord ++ tailWord_3310846).sum := by decide
  have hdescent : baseEnd_3310846 < baseStart_3310846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310908 : List Nat := [2, 2, 2, 2, 1, 4, 1, 4, 1, 3]
def baseStart_3310908 : Nat := 118140960795 + 3310908 * 2 ^ 59
def prefixEnd_3310908 : Nat := 4983230072969 + 3 ^ 40 * 3310908 * 2
def baseEnd_3310908 : Nat := 1133391471210958193948945

theorem tailTrace_3310908 : CollatzResearch.WordTrace tailWord_3310908 prefixEnd_3310908 1133391471210958193948945 := by
  unfold tailWord_3310908
  simp only [CollatzResearch.WordTrace]
  refine ⟨60379367744576624456546689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80505823659435499275395585 60379367744576624456546689)
  ·
    refine ⟨45284525808432468342410017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60379367744576624456546689 45284525808432468342410017)
    ·
      refine ⟨33963394356324351256807513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45284525808432468342410017 33963394356324351256807513)
      ·
        refine ⟨25472545767243263442605635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33963394356324351256807513 25472545767243263442605635)
        ·
          refine ⟨38208818650864895163908453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25472545767243263442605635 38208818650864895163908453)
          ·
            refine ⟨7164153497037167843232835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38208818650864895163908453 7164153497037167843232835)
            ·
              refine ⟨10746230245555751764849253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164153497037167843232835 10746230245555751764849253)
              ·
                refine ⟨2014918171041703455909235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10746230245555751764849253 2014918171041703455909235)
                ·
                  refine ⟨3022377256562555183863853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014918171041703455909235 3022377256562555183863853)
                  ·
                    refine ⟨1133391471210958193948945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022377256562555183863853 1133391471210958193948945)
                    ·
                      rfl

theorem cell22_3310908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_3310908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310908 prefixEnd_3310908 := by exact prefixLift 3310908
  have htrace : WordTrace (prefixWord ++ tailWord_3310908) baseStart_3310908 baseEnd_3310908 := by
    simpa [prefixWord, tailWord_3310908, baseEnd_3310908] using wordTrace_append hprefix tailTrace_3310908
  have hstable : (prefixWord ++ tailWord_3310908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310908).length < 2 ^ (prefixWord ++ tailWord_3310908).sum := by decide
  have hdescent : baseEnd_3310908 < baseStart_3310908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310919 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 2, 5]
def baseStart_3310919 : Nat := 118140960795 + 3310919 * 2 ^ 59
def prefixEnd_3310919 : Nat := 4983230072969 + 3 ^ 40 * 3310919 * 2
def baseEnd_3310919 : Nat := 1133395236735757831923911

theorem tailTrace_3310919 : CollatzResearch.WordTrace tailWord_3310919 prefixEnd_3310919 1133395236735757831923911 := by
  unfold tailWord_3310919
  simp only [CollatzResearch.WordTrace]
  refine ⟨120759136692113397791743811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80506091128075598527829207 120759136692113397791743811)
  ·
    refine ⟨181138705038170096687615717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120759136692113397791743811 181138705038170096687615717)
    ·
      refine ⟨33963507194656893128927947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181138705038170096687615717 33963507194656893128927947)
      ·
        refine ⟨50945260791985339693391921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33963507194656893128927947 50945260791985339693391921)
        ·
          refine ⟨38208945593989004770043941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50945260791985339693391921 38208945593989004770043941)
          ·
            refine ⟨7164177298872938394383239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38208945593989004770043941 7164177298872938394383239)
            ·
              refine ⟨10746265948309407591574859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164177298872938394383239 10746265948309407591574859)
              ·
                refine ⟨16119398922464111387362289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746265948309407591574859 16119398922464111387362289)
                ·
                  refine ⟨12089549191848083540521717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16119398922464111387362289 12089549191848083540521717)
                  ·
                    refine ⟨1133395236735757831923911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12089549191848083540521717 1133395236735757831923911)
                    ·
                      rfl

theorem cell22_3310919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_3310919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310919 prefixEnd_3310919 := by exact prefixLift 3310919
  have htrace : WordTrace (prefixWord ++ tailWord_3310919) baseStart_3310919 baseEnd_3310919 := by
    simpa [prefixWord, tailWord_3310919, baseEnd_3310919] using wordTrace_append hprefix tailTrace_3310919
  have hstable : (prefixWord ++ tailWord_3310919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310919).length < 2 ^ (prefixWord ++ tailWord_3310919).sum := by decide
  have hdescent : baseEnd_3310919 < baseStart_3310919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310925 : List Nat := [1, 6, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3310925 : Nat := 118140960795 + 3310925 * 2 ^ 59
def prefixEnd_3310925 : Nat := 4983230072969 + 3 ^ 40 * 3310925 * 2
def baseEnd_3310925 : Nat := 1133397290658375816273893

theorem tailTrace_3310925 : CollatzResearch.WordTrace tailWord_3310925 prefixEnd_3310925 1133397290658375816273893 := by
  unfold tailWord_3310925
  simp only [CollatzResearch.WordTrace]
  refine ⟨120759355530091660816462229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80506237020061107210974819 120759355530091660816462229)
  ·
    refine ⟨5660594790473046600771667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120759355530091660816462229 5660594790473046600771667)
    ·
      refine ⟨8490892185709569901157501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5660594790473046600771667 8490892185709569901157501)
      ·
        refine ⟨3184084569641088712934063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8490892185709569901157501 3184084569641088712934063)
        ·
          refine ⟨4776126854461633069401095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184084569641088712934063 4776126854461633069401095)
          ·
            refine ⟨7164190281692449604101643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776126854461633069401095 7164190281692449604101643)
            ·
              refine ⟨10746285422538674406152465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164190281692449604101643 10746285422538674406152465)
              ·
                refine ⟨8059714066904005804614349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10746285422538674406152465 8059714066904005804614349)
                ·
                  refine ⟨3022392775089002176730381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8059714066904005804614349 3022392775089002176730381)
                  ·
                    refine ⟨1133397290658375816273893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022392775089002176730381 1133397290658375816273893)
                    ·
                      rfl

theorem cell22_3310925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3310925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310925 prefixEnd_3310925 := by exact prefixLift 3310925
  have htrace : WordTrace (prefixWord ++ tailWord_3310925) baseStart_3310925 baseEnd_3310925 := by
    simpa [prefixWord, tailWord_3310925, baseEnd_3310925] using wordTrace_append hprefix tailTrace_3310925
  have hstable : (prefixWord ++ tailWord_3310925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310925).length < 2 ^ (prefixWord ++ tailWord_3310925).sum := by decide
  have hdescent : baseEnd_3310925 < baseStart_3310925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310979 : List Nat := [1, 1, 1, 3, 5, 1, 1, 2, 1, 6]
def baseStart_3310979 : Nat := 118140960795 + 3310979 * 2 ^ 59
def prefixEnd_3310979 : Nat := 4983230072969 + 3 ^ 40 * 3310979 * 2
def baseEnd_3310979 : Nat := 1133415775961937675423727

theorem tailTrace_3310979 : CollatzResearch.WordTrace tailWord_3310979 prefixEnd_3310979 1133415775961937675423727 := by
  unfold tailWord_3310979
  simp only [CollatzResearch.WordTrace]
  refine ⟨120761325071896028038927991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80507550047930685359285327 120761325071896028038927991)
  ·
    refine ⟨181141987607844042058391987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120761325071896028038927991 181141987607844042058391987)
    ·
      refine ⟨271712981411766063087587981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181141987607844042058391987 271712981411766063087587981)
      ·
        refine ⟨101892368029412273657845493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271712981411766063087587981 101892368029412273657845493)
        ·
          refine ⟨9552409502757400655423015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101892368029412273657845493 9552409502757400655423015)
          ·
            refine ⟨14328614254136100983134523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9552409502757400655423015 14328614254136100983134523)
            ·
              refine ⟨21492921381204151474701785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14328614254136100983134523 21492921381204151474701785)
              ·
                refine ⟨16119691035903113606026339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21492921381204151474701785 16119691035903113606026339)
                ·
                  refine ⟨24179536553854670409039509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16119691035903113606026339 24179536553854670409039509)
                  ·
                    refine ⟨1133415775961937675423727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24179536553854670409039509 1133415775961937675423727)
                    ·
                      rfl

theorem cell22_3310979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 6].length) (baseStart_3310979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310979 prefixEnd_3310979 := by exact prefixLift 3310979
  have htrace : WordTrace (prefixWord ++ tailWord_3310979) baseStart_3310979 baseEnd_3310979 := by
    simpa [prefixWord, tailWord_3310979, baseEnd_3310979] using wordTrace_append hprefix tailTrace_3310979
  have hstable : (prefixWord ++ tailWord_3310979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310979).length < 2 ^ (prefixWord ++ tailWord_3310979).sum := by decide
  have hdescent : baseEnd_3310979 < baseStart_3310979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310981 : List Nat := [1, 3, 1, 1, 3, 1, 2, 5, 2, 3]
def baseStart_3310981 : Nat := 118140960795 + 3310981 * 2 ^ 59
def prefixEnd_3310981 : Nat := 4983230072969 + 3 ^ 40 * 3310981 * 2
def baseEnd_3310981 : Nat := 1133416460602810336873721

theorem tailTrace_3310981 : CollatzResearch.WordTrace tailWord_3310981 prefixEnd_3310981 1133416460602810336873721 := by
  unfold tailWord_3310981
  simp only [CollatzResearch.WordTrace]
  refine ⟨120761398017888782380500797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80507598678592521587000531 120761398017888782380500797)
  ·
    refine ⟨45285524256708293392687799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120761398017888782380500797 45285524256708293392687799)
    ·
      refine ⟨67928286385062440089031699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45285524256708293392687799 67928286385062440089031699)
      ·
        refine ⟨101892429577593660133547549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67928286385062440089031699 101892429577593660133547549)
        ·
          refine ⟨38209661091597622550080331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101892429577593660133547549 38209661091597622550080331)
          ·
            refine ⟨57314491637396433825120497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38209661091597622550080331 57314491637396433825120497)
            ·
              refine ⟨42985868728047325368840373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57314491637396433825120497 42985868728047325368840373)
              ·
                refine ⟨4029925193254436753328785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42985868728047325368840373 4029925193254436753328785)
                ·
                  refine ⟨3022443894940827564996589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4029925193254436753328785 3022443894940827564996589)
                  ·
                    refine ⟨1133416460602810336873721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022443894940827564996589 1133416460602810336873721)
                    ·
                      rfl

theorem cell22_3310981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_3310981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310981 prefixEnd_3310981 := by exact prefixLift 3310981
  have htrace : WordTrace (prefixWord ++ tailWord_3310981) baseStart_3310981 baseEnd_3310981 := by
    simpa [prefixWord, tailWord_3310981, baseEnd_3310981] using wordTrace_append hprefix tailTrace_3310981
  have hstable : (prefixWord ++ tailWord_3310981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310981).length < 2 ^ (prefixWord ++ tailWord_3310981).sum := by decide
  have hdescent : baseEnd_3310981 < baseStart_3310981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3310996 : List Nat := [2, 4, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_3310996 : Nat := 118140960795 + 3310996 * 2 ^ 59
def prefixEnd_3310996 : Nat := 4983230072969 + 3 ^ 40 * 3310996 * 2
def baseEnd_3310996 : Nat := 1133421595409355297748675

theorem tailTrace_3310996 : CollatzResearch.WordTrace tailWord_3310996 prefixEnd_3310996 1133421595409355297748675 := by
  unfold tailWord_3310996
  simp only [CollatzResearch.WordTrace]
  refine ⟨60380972556417219971148421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80507963408556293294864561 60380972556417219971148421)
  ·
    refine ⟨11321432354328228744590329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60380972556417219971148421 11321432354328228744590329)
    ·
      refine ⟨8491074265746171558442747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11321432354328228744590329 8491074265746171558442747)
      ·
        refine ⟨12736611398619257337664121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491074265746171558442747 12736611398619257337664121)
        ·
          refine ⟨9552458548964443003248091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12736611398619257337664121 9552458548964443003248091)
          ·
            refine ⟨14328687823446664504872137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9552458548964443003248091 14328687823446664504872137)
            ·
              refine ⟨10746515867584998378654103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14328687823446664504872137 10746515867584998378654103)
              ·
                refine ⟨16119773801377497567981155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746515867584998378654103 16119773801377497567981155)
                ·
                  refine ⟨24179660702066246351971733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16119773801377497567981155 24179660702066246351971733)
                  ·
                    refine ⟨1133421595409355297748675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24179660702066246351971733 1133421595409355297748675)
                    ·
                      rfl

theorem cell22_3310996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_3310996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3310996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3310996 prefixEnd_3310996 := by exact prefixLift 3310996
  have htrace : WordTrace (prefixWord ++ tailWord_3310996) baseStart_3310996 baseEnd_3310996 := by
    simpa [prefixWord, tailWord_3310996, baseEnd_3310996] using wordTrace_append hprefix tailTrace_3310996
  have hstable : (prefixWord ++ tailWord_3310996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3310996).length < 2 ^ (prefixWord ++ tailWord_3310996).sum := by decide
  have hdescent : baseEnd_3310996 < baseStart_3310996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3310996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311000 : List Nat := [2, 1, 2, 5, 2, 2, 1, 3, 4]
def baseStart_3311000 : Nat := 118140960795 + 3311000 * 2 ^ 59
def prefixEnd_3311000 : Nat := 4983230072969 + 3 ^ 40 * 3311000 * 2
def baseEnd_3311000 : Nat := 377807654897033540216221

theorem tailTrace_3311000 : CollatzResearch.WordTrace tailWord_3311000 prefixEnd_3311000 377807654897033540216221 := by
  unfold tailWord_3311000
  simp only [CollatzResearch.WordTrace]
  refine ⟨60381045502409974312721227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80508060669879965750294969 60381045502409974312721227)
  ·
    refine ⟨90571568253614961469081841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60381045502409974312721227 90571568253614961469081841)
    ·
      refine ⟨67928676190211221101811381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90571568253614961469081841 67928676190211221101811381)
      ·
        refine ⟨6368313392832301978294817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67928676190211221101811381 6368313392832301978294817)
        ·
          refine ⟨4776235044624226483721113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6368313392832301978294817 4776235044624226483721113)
          ·
            refine ⟨3582176283468169862790835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4776235044624226483721113 3582176283468169862790835)
            ·
              refine ⟨5373264425202254794186253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582176283468169862790835 5373264425202254794186253)
              ·
                refine ⟨2014974159450845547819845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5373264425202254794186253 2014974159450845547819845)
                ·
                  refine ⟨377807654897033540216221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2014974159450845547819845 377807654897033540216221)
                  ·
                    rfl

theorem cell22_3311000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 4].length) (baseStart_3311000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311000 prefixEnd_3311000 := by exact prefixLift 3311000
  have htrace : WordTrace (prefixWord ++ tailWord_3311000) baseStart_3311000 baseEnd_3311000 := by
    simpa [prefixWord, tailWord_3311000, baseEnd_3311000] using wordTrace_append hprefix tailTrace_3311000
  have hstable : (prefixWord ++ tailWord_3311000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311000).length < 2 ^ (prefixWord ++ tailWord_3311000).sum := by decide
  have hdescent : baseEnd_3311000 < baseStart_3311000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311026 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 3, 3]
def baseStart_3311026 : Nat := 118140960795 + 3311026 * 2 ^ 59
def prefixEnd_3311026 : Nat := 4983230072969 + 3 ^ 40 * 3311026 * 2
def baseEnd_3311026 : Nat := 1133431865022445219498583

theorem tailTrace_3311026 : CollatzResearch.WordTrace tailWord_3311026 prefixEnd_3311026 1133431865022445219498583 := by
  unfold tailWord_3311026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30190759825681438766472233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80508692868483836710592621 30190759825681438766472233)
  ·
    refine ⟨22643069869261079074854175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30190759825681438766472233 22643069869261079074854175)
    ·
      refine ⟨33964604803891618612281263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22643069869261079074854175 33964604803891618612281263)
      ·
        refine ⟨50946907205837427918421895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33964604803891618612281263 50946907205837427918421895)
        ·
          refine ⟨76420360808756141877632843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50946907205837427918421895 76420360808756141877632843)
          ·
            refine ⟨114630541213134212816449265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76420360808756141877632843 114630541213134212816449265)
            ·
              refine ⟨85972905909850659612336949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114630541213134212816449265 85972905909850659612336949)
              ·
                refine ⟨8059959929048499338656589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85972905909850659612336949 8059959929048499338656589)
                ·
                  refine ⟨3022484973393187251996221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8059959929048499338656589 3022484973393187251996221)
                  ·
                    refine ⟨1133431865022445219498583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022484973393187251996221 1133431865022445219498583)
                    ·
                      rfl

theorem cell22_3311026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_3311026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311026 prefixEnd_3311026 := by exact prefixLift 3311026
  have htrace : WordTrace (prefixWord ++ tailWord_3311026) baseStart_3311026 baseEnd_3311026 := by
    simpa [prefixWord, tailWord_3311026, baseEnd_3311026] using wordTrace_append hprefix tailTrace_3311026
  have hstable : (prefixWord ++ tailWord_3311026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311026).length < 2 ^ (prefixWord ++ tailWord_3311026).sum := by decide
  have hdescent : baseEnd_3311026 < baseStart_3311026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311077 : List Nat := [1, 3, 1, 5, 1, 1, 4, 2, 1, 3]
def baseStart_3311077 : Nat := 118140960795 + 3311077 * 2 ^ 59
def prefixEnd_3311077 : Nat := 4983230072969 + 3 ^ 40 * 3311077 * 2
def baseEnd_3311077 : Nat := 1133449323364698086473427

theorem tailTrace_3311077 : CollatzResearch.WordTrace tailWord_3311077 prefixEnd_3311077 1133449323364698086473427 := by
  unfold tailWord_3311077
  simp only [CollatzResearch.WordTrace]
  refine ⟨120764899425540990775995485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80509932950360660517330323 120764899425540990775995485)
  ·
    refine ⟨45286837284577871540998307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120764899425540990775995485 45286837284577871540998307)
    ·
      refine ⟨67930255926866807311497461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45286837284577871540998307 67930255926866807311497461)
      ·
        refine ⟨6368461493143763185452887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67930255926866807311497461 6368461493143763185452887)
        ·
          refine ⟨9552692239715644778179331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6368461493143763185452887 9552692239715644778179331)
          ·
            refine ⟨14329038359573467167268997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9552692239715644778179331 14329038359573467167268997)
            ·
              refine ⟨2686694692420025093862937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14329038359573467167268997 2686694692420025093862937)
              ·
                refine ⟨2015021019315018820397203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2686694692420025093862937 2015021019315018820397203)
                ·
                  refine ⟨3022531528972528230595805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015021019315018820397203 3022531528972528230595805)
                  ·
                    refine ⟨1133449323364698086473427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022531528972528230595805 1133449323364698086473427)
                    ·
                      rfl

theorem cell22_3311077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_3311077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311077 prefixEnd_3311077 := by exact prefixLift 3311077
  have htrace : WordTrace (prefixWord ++ tailWord_3311077) baseStart_3311077 baseEnd_3311077 := by
    simpa [prefixWord, tailWord_3311077, baseEnd_3311077] using wordTrace_append hprefix tailTrace_3311077
  have hstable : (prefixWord ++ tailWord_3311077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311077).length < 2 ^ (prefixWord ++ tailWord_3311077).sum := by decide
  have hdescent : baseEnd_3311077 < baseStart_3311077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311086 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3311086 : Nat := 118140960795 + 3311086 * 2 ^ 59
def prefixEnd_3311086 : Nat := 4983230072969 + 3 ^ 40 * 3311086 * 2
def baseEnd_3311086 : Nat := 1133452404248625062998399

theorem tailTrace_3311086 : CollatzResearch.WordTrace tailWord_3311086 prefixEnd_3311086 1133452404248625062998399 := by
  unfold tailWord_3311086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15095653460313548164134139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80510151788338923542048741 15095653460313548164134139)
  ·
    refine ⟨22643480190470322246201209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15095653460313548164134139 22643480190470322246201209)
    ·
      refine ⟨16982610142852741684650907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22643480190470322246201209 16982610142852741684650907)
      ·
        refine ⟨25473915214279112526976361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16982610142852741684650907 25473915214279112526976361)
        ·
          refine ⟨19105436410709334395232271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25473915214279112526976361 19105436410709334395232271)
          ·
            refine ⟨28658154616064001592848407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19105436410709334395232271 28658154616064001592848407)
            ·
              refine ⟨42987231924096002389272611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28658154616064001592848407 42987231924096002389272611)
              ·
                refine ⟨64480847886144003583908917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42987231924096002389272611 64480847886144003583908917)
                ·
                  refine ⟨6045079489326000335991461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64480847886144003583908917 6045079489326000335991461)
                  ·
                    refine ⟨1133452404248625062998399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6045079489326000335991461 1133452404248625062998399)
                    ·
                      rfl

theorem cell22_3311086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3311086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311086 prefixEnd_3311086 := by exact prefixLift 3311086
  have htrace : WordTrace (prefixWord ++ tailWord_3311086) baseStart_3311086 baseEnd_3311086 := by
    simpa [prefixWord, tailWord_3311086, baseEnd_3311086] using wordTrace_append hprefix tailTrace_3311086
  have hstable : (prefixWord ++ tailWord_3311086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311086).length < 2 ^ (prefixWord ++ tailWord_3311086).sum := by decide
  have hdescent : baseEnd_3311086 < baseStart_3311086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311099 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 5, 5]
def baseStart_3311099 : Nat := 118140960795 + 3311099 * 2 ^ 59
def prefixEnd_3311099 : Nat := 4983230072969 + 3 ^ 40 * 3311099 * 2
def baseEnd_3311099 : Nat := 1133456854414297362423359

theorem tailTrace_3311099 : CollatzResearch.WordTrace tailWord_3311099 prefixEnd_3311099 1133456854414297362423359 := by
  unfold tailWord_3311099
  simp only [CollatzResearch.WordTrace]
  refine ⟨120765701831461288533296351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80510467887640859022197567 120765701831461288533296351)
  ·
    refine ⟨181148552747191932799944527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120765701831461288533296351 181148552747191932799944527)
    ·
      refine ⟨271722829120787899199916791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181148552747191932799944527 271722829120787899199916791)
      ·
        refine ⟨407584243681181848799875187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271722829120787899199916791 407584243681181848799875187)
        ·
          refine ⟨611376365521772773199812781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407584243681181848799875187 611376365521772773199812781)
          ·
            refine ⟨229266137070664789949929793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611376365521772773199812781 229266137070664789949929793)
            ·
              refine ⟨171949602802998592462447345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229266137070664789949929793 171949602802998592462447345)
              ·
                refine ⟨128962202102248944346835509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171949602802998592462447345 128962202102248944346835509)
                ·
                  refine ⟨12090206447085838532515829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128962202102248944346835509 12090206447085838532515829)
                  ·
                    refine ⟨1133456854414297362423359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12090206447085838532515829 1133456854414297362423359)
                    ·
                      rfl

theorem cell22_3311099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_3311099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311099 prefixEnd_3311099 := by exact prefixLift 3311099
  have htrace : WordTrace (prefixWord ++ tailWord_3311099) baseStart_3311099 baseEnd_3311099 := by
    simpa [prefixWord, tailWord_3311099, baseEnd_3311099] using wordTrace_append hprefix tailTrace_3311099
  have hstable : (prefixWord ++ tailWord_3311099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311099).length < 2 ^ (prefixWord ++ tailWord_3311099).sum := by decide
  have hdescent : baseEnd_3311099 < baseStart_3311099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311101 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 6]
def baseStart_3311101 : Nat := 118140960795 + 3311101 * 2 ^ 59
def prefixEnd_3311101 : Nat := 4983230072969 + 3 ^ 40 * 3311101 * 2
def baseEnd_3311101 : Nat := 377819179685056674624451

theorem tailTrace_3311101 : CollatzResearch.WordTrace tailWord_3311101 prefixEnd_3311101 377819179685056674624451 := by
  unfold tailWord_3311101
  simp only [CollatzResearch.WordTrace]
  refine ⟨120765774777454042874869157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80510516518302695249912771 120765774777454042874869157)
  ·
    refine ⟨22643582770772633039037967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120765774777454042874869157 22643582770772633039037967)
    ·
      refine ⟨33965374156158949558556951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22643582770772633039037967 33965374156158949558556951)
      ·
        refine ⟨50948061234238424337835427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33965374156158949558556951 50948061234238424337835427)
        ·
          refine ⟨76422091851357636506753141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50948061234238424337835427 76422091851357636506753141)
          ·
            refine ⟨7164571111064778422508107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76422091851357636506753141 7164571111064778422508107)
            ·
              refine ⟨10746856666597167633762161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164571111064778422508107 10746856666597167633762161)
              ·
                refine ⟨8060142499947875725321621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10746856666597167633762161 8060142499947875725321621)
                ·
                  refine ⟨377819179685056674624451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8060142499947875725321621 377819179685056674624451)
                  ·
                    rfl

theorem cell22_3311101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_3311101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311101 prefixEnd_3311101 := by exact prefixLift 3311101
  have htrace : WordTrace (prefixWord ++ tailWord_3311101) baseStart_3311101 baseEnd_3311101 := by
    simpa [prefixWord, tailWord_3311101, baseEnd_3311101] using wordTrace_append hprefix tailTrace_3311101
  have hstable : (prefixWord ++ tailWord_3311101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311101).length < 2 ^ (prefixWord ++ tailWord_3311101).sum := by decide
  have hdescent : baseEnd_3311101 < baseStart_3311101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311133 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_3311133 : Nat := 118140960795 + 3311133 * 2 ^ 59
def prefixEnd_3311133 : Nat := 4983230072969 + 3 ^ 40 * 3311133 * 2
def baseEnd_3311133 : Nat := 1133468493309132607073255

theorem tailTrace_3311133 : CollatzResearch.WordTrace tailWord_3311133 prefixEnd_3311133 1133468493309132607073255 := by
  unfold tailWord_3311133
  simp only [CollatzResearch.WordTrace]
  refine ⟨120766941913338112340034053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80511294608892074893356035 120766941913338112340034053)
  ·
    refine ⟨22643801608750896063756385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120766941913338112340034053 22643801608750896063756385)
    ·
      refine ⟨16982851206563172047817289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22643801608750896063756385 16982851206563172047817289)
      ·
        refine ⟨12737138404922379035862967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16982851206563172047817289 12737138404922379035862967)
        ·
          refine ⟨19105707607383568553794451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12737138404922379035862967 19105707607383568553794451)
          ·
            refine ⟨28658561411075352830691677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19105707607383568553794451 28658561411075352830691677)
            ·
              refine ⟨10746960529153257311509379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28658561411075352830691677 10746960529153257311509379)
              ·
                refine ⟨16120440793729885967264069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746960529153257311509379 16120440793729885967264069)
                ·
                  refine ⟨3022582648824353618862013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16120440793729885967264069 3022582648824353618862013)
                  ·
                    refine ⟨1133468493309132607073255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022582648824353618862013 1133468493309132607073255)
                    ·
                      rfl

theorem cell22_3311133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_3311133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311133 prefixEnd_3311133 := by exact prefixLift 3311133
  have htrace : WordTrace (prefixWord ++ tailWord_3311133) baseStart_3311133 baseEnd_3311133 := by
    simpa [prefixWord, tailWord_3311133, baseEnd_3311133] using wordTrace_append hprefix tailTrace_3311133
  have hstable : (prefixWord ++ tailWord_3311133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311133).length < 2 ^ (prefixWord ++ tailWord_3311133).sum := by decide
  have hdescent : baseEnd_3311133 < baseStart_3311133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311146 : List Nat := [3, 1, 4, 1, 1, 1, 2, 9]
def baseStart_3311146 : Nat := 118140960795 + 3311146 * 2 ^ 59
def prefixEnd_3311146 : Nat := 4983230072969 + 3 ^ 40 * 3311146 * 2
def baseEnd_3311146 : Nat := 125941438163867211833135

theorem tailTrace_3311146 : CollatzResearch.WordTrace tailWord_3311146 prefixEnd_3311146 125941438163867211833135 := by
  unfold tailWord_3311146
  simp only [CollatzResearch.WordTrace]
  refine ⟨30191854015572753890064323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80511610708194010373504861 30191854015572753890064323)
  ·
    refine ⟨45287781023359130835096485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30191854015572753890064323 45287781023359130835096485)
    ·
      refine ⟨8491458941879837031580591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45287781023359130835096485 8491458941879837031580591)
      ·
        refine ⟨12737188412819755547370887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491458941879837031580591 12737188412819755547370887)
        ·
          refine ⟨19105782619229633321056331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12737188412819755547370887 19105782619229633321056331)
          ·
            refine ⟨28658673928844449981584497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19105782619229633321056331 28658673928844449981584497)
            ·
              refine ⟨21494005446633337486188373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28658673928844449981584497 21494005446633337486188373)
              ·
                refine ⟨125941438163867211833135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21494005446633337486188373 125941438163867211833135)
                ·
                  rfl

theorem cell22_3311146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 9].length) (baseStart_3311146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311146 prefixEnd_3311146 := by exact prefixLift 3311146
  have htrace : WordTrace (prefixWord ++ tailWord_3311146) baseStart_3311146 baseEnd_3311146 := by
    simpa [prefixWord, tailWord_3311146, baseEnd_3311146] using wordTrace_append hprefix tailTrace_3311146
  have hstable : (prefixWord ++ tailWord_3311146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311146).length < 2 ^ (prefixWord ++ tailWord_3311146).sum := by decide
  have hdescent : baseEnd_3311146 < baseStart_3311146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311150 : List Nat := [4, 1, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_3311150 : Nat := 118140960795 + 3311150 * 2 ^ 59
def prefixEnd_3311150 : Nat := 4983230072969 + 3 ^ 40 * 3311150 * 2
def baseEnd_3311150 : Nat := 1133474312756550229398203

theorem tailTrace_3311150 : CollatzResearch.WordTrace tailWord_3311150 prefixEnd_3311150 1133474312756550229398203 := by
  unfold tailWord_3311150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15095945244284565530425363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80511707969517682828935269 15095945244284565530425363)
  ·
    refine ⟨22643917866426848295638045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15095945244284565530425363 22643917866426848295638045)
    ·
      refine ⟨8491469199910068110864267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22643917866426848295638045 8491469199910068110864267)
      ·
        refine ⟨12737203799865102166296401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8491469199910068110864267 12737203799865102166296401)
        ·
          refine ⟨9552902849898826624722301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12737203799865102166296401 9552902849898826624722301)
          ·
            refine ⟨3582338568712059984270863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9552902849898826624722301 3582338568712059984270863)
            ·
              refine ⟨5373507853068089976406295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582338568712059984270863 5373507853068089976406295)
              ·
                refine ⟨8060261779602134964609443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5373507853068089976406295 8060261779602134964609443)
                ·
                  refine ⟨12090392669403202446914165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060261779602134964609443 12090392669403202446914165)
                  ·
                    refine ⟨1133474312756550229398203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12090392669403202446914165 1133474312756550229398203)
                    ·
                      rfl

theorem cell22_3311150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_3311150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311150 prefixEnd_3311150 := by exact prefixLift 3311150
  have htrace : WordTrace (prefixWord ++ tailWord_3311150) baseStart_3311150 baseEnd_3311150 := by
    simpa [prefixWord, tailWord_3311150, baseEnd_3311150] using wordTrace_append hprefix tailTrace_3311150
  have hstable : (prefixWord ++ tailWord_3311150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311150).length < 2 ^ (prefixWord ++ tailWord_3311150).sum := by decide
  have hdescent : baseEnd_3311150 < baseStart_3311150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311191 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 7]
def baseStart_3311191 : Nat := 118140960795 + 3311191 * 2 ^ 59
def prefixEnd_3311191 : Nat := 4983230072969 + 3 ^ 40 * 3311191 * 2
def baseEnd_3311191 : Nat := 377829449298146596374359

theorem tailTrace_3311191 : CollatzResearch.WordTrace tailWord_3311191 prefixEnd_3311191 377829449298146596374359 := by
  unfold tailWord_3311191
  simp only [CollatzResearch.WordTrace]
  refine ⟨120769057347127988245645427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80512704898085325497096951 120769057347127988245645427)
  ·
    refine ⟨181153586020691982368468141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120769057347127988245645427 181153586020691982368468141)
    ·
      refine ⟨67932594757759493388175553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181153586020691982368468141 67932594757759493388175553)
      ·
        refine ⟨50949446068319620041131665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67932594757759493388175553 50949446068319620041131665)
        ·
          refine ⟨38212084551239715030848749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50949446068319620041131665 38212084551239715030848749)
          ·
            refine ⟨14329531706714893136568281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38212084551239715030848749 14329531706714893136568281)
            ·
              refine ⟨10747148780036169852426211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14329531706714893136568281 10747148780036169852426211)
              ·
                refine ⟨16120723170054254778639317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10747148780036169852426211 16120723170054254778639317)
                ·
                  refine ⟨377829449298146596374359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16120723170054254778639317 377829449298146596374359)
                  ·
                    rfl

theorem cell22_3311191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 7].length) (baseStart_3311191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311191 prefixEnd_3311191 := by exact prefixLift 3311191
  have htrace : WordTrace (prefixWord ++ tailWord_3311191) baseStart_3311191 baseEnd_3311191 := by
    simpa [prefixWord, tailWord_3311191, baseEnd_3311191] using wordTrace_append hprefix tailTrace_3311191
  have hstable : (prefixWord ++ tailWord_3311191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311191).length < 2 ^ (prefixWord ++ tailWord_3311191).sum := by decide
  have hdescent : baseEnd_3311191 < baseStart_3311191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311268 : List Nat := [2, 3, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_3311268 : Nat := 118140960795 + 3311268 * 2 ^ 59
def prefixEnd_3311268 : Nat := 4983230072969 + 3 ^ 40 * 3311268 * 2
def baseEnd_3311268 : Nat := 1133514706568037254947841

theorem tailTrace_3311268 : CollatzResearch.WordTrace tailWord_3311268 prefixEnd_3311268 1133514706568037254947841 := by
  unfold tailWord_3311268
  simp only [CollatzResearch.WordTrace]
  refine ⟨60385932883924515198099229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80514577178566020264132305 60385932883924515198099229)
  ·
    refine ⟨22644724831471693199287211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60385932883924515198099229 22644724831471693199287211)
    ·
      refine ⟨33967087247207539798930817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22644724831471693199287211 33967087247207539798930817)
      ·
        refine ⟨25475315435405654849198113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33967087247207539798930817 25475315435405654849198113)
        ·
          refine ⟨19106486576554241136898585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25475315435405654849198113 19106486576554241136898585)
          ·
            refine ⟨14329864932415680852673939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19106486576554241136898585 14329864932415680852673939)
            ·
              refine ⟨21494797398623521279010909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14329864932415680852673939 21494797398623521279010909)
              ·
                refine ⟨8060549024483820479629091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21494797398623521279010909 8060549024483820479629091)
                ·
                  refine ⟨12090823536725730719443637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060549024483820479629091 12090823536725730719443637)
                  ·
                    refine ⟨1133514706568037254947841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12090823536725730719443637 1133514706568037254947841)
                    ·
                      rfl

theorem cell22_3311268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_3311268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311268 prefixEnd_3311268 := by exact prefixLift 3311268
  have htrace : WordTrace (prefixWord ++ tailWord_3311268) baseStart_3311268 baseEnd_3311268 := by
    simpa [prefixWord, tailWord_3311268, baseEnd_3311268] using wordTrace_append hprefix tailTrace_3311268
  have hstable : (prefixWord ++ tailWord_3311268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311268).length < 2 ^ (prefixWord ++ tailWord_3311268).sum := by decide
  have hdescent : baseEnd_3311268 < baseStart_3311268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311311 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 1, 8]
def baseStart_3311311 : Nat := 118140960795 + 3311311 * 2 ^ 59
def prefixEnd_3311311 : Nat := 4983230072969 + 3 ^ 40 * 3311311 * 2
def baseEnd_3311311 : Nat := 1133529426346799476122709

theorem tailTrace_3311311 : CollatzResearch.WordTrace tailWord_3311311 prefixEnd_3311311 1133529426346799476122709 := by
  unfold tailWord_3311311
  simp only [CollatzResearch.WordTrace]
  refine ⟨120773434106693248740013787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80515622737795499160009191 120773434106693248740013787)
  ·
    refine ⟨181160151160039873110020681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120773434106693248740013787 181160151160039873110020681)
    ·
      refine ⟨135870113370029904832515511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181160151160039873110020681 135870113370029904832515511)
      ·
        refine ⟨203805170055044857248773267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135870113370029904832515511 203805170055044857248773267)
        ·
          refine ⟨305707755082567285873159901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203805170055044857248773267 305707755082567285873159901)
          ·
            refine ⟨114640408155962732202434963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305707755082567285873159901 114640408155962732202434963)
            ·
              refine ⟨171960612233944098303652445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114640408155962732202434963 171960612233944098303652445)
              ·
                refine ⟨64485229587729036863869667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171960612233944098303652445 64485229587729036863869667)
                ·
                  refine ⟨96727844381593555295804501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64485229587729036863869667 96727844381593555295804501)
                  ·
                    refine ⟨1133529426346799476122709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96727844381593555295804501 1133529426346799476122709)
                    ·
                      rfl

theorem cell22_3311311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_3311311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311311 prefixEnd_3311311 := by exact prefixLift 3311311
  have htrace : WordTrace (prefixWord ++ tailWord_3311311) baseStart_3311311 baseEnd_3311311 := by
    simpa [prefixWord, tailWord_3311311, baseEnd_3311311] using wordTrace_append hprefix tailTrace_3311311
  have hstable : (prefixWord ++ tailWord_3311311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311311).length < 2 ^ (prefixWord ++ tailWord_3311311).sum := by decide
  have hdescent : baseEnd_3311311 < baseStart_3311311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311347 : List Nat := [1, 1, 1, 2, 2, 3, 5, 3, 1, 3]
def baseStart_3311347 : Nat := 118140960795 + 3311347 * 2 ^ 59
def prefixEnd_3311347 : Nat := 4983230072969 + 3 ^ 40 * 3311347 * 2
def baseEnd_3311347 : Nat := 1133541749882507382222599

theorem tailTrace_3311347 : CollatzResearch.WordTrace tailWord_3311347 prefixEnd_3311347 1133541749882507382222599 := by
  unfold tailWord_3311347
  simp only [CollatzResearch.WordTrace]
  refine ⟨120774747134562826888324295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80516498089708551258882863 120774747134562826888324295)
  ·
    refine ⟨181162120701844240332486443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120774747134562826888324295 181162120701844240332486443)
    ·
      refine ⟨271743181052766360498729665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181162120701844240332486443 271743181052766360498729665)
      ·
        refine ⟨203807385789574770374047249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271743181052766360498729665 203807385789574770374047249)
        ·
          refine ⟨152855539342181077780535437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203807385789574770374047249 152855539342181077780535437)
          ·
            refine ⟨57320827253317904167700789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152855539342181077780535437 57320827253317904167700789)
            ·
              refine ⟨5373827554998553515721949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57320827253317904167700789 5373827554998553515721949)
              ·
                refine ⟨2015185333124457568395731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5373827554998553515721949 2015185333124457568395731)
                ·
                  refine ⟨3022777999686686352593597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015185333124457568395731 3022777999686686352593597)
                  ·
                    refine ⟨1133541749882507382222599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022777999686686352593597 1133541749882507382222599)
                    ·
                      rfl

theorem cell22_3311347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 3, 1, 3].length) (baseStart_3311347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311347 prefixEnd_3311347 := by exact prefixLift 3311347
  have htrace : WordTrace (prefixWord ++ tailWord_3311347) baseStart_3311347 baseEnd_3311347 := by
    simpa [prefixWord, tailWord_3311347, baseEnd_3311347] using wordTrace_append hprefix tailTrace_3311347
  have hstable : (prefixWord ++ tailWord_3311347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311347).length < 2 ^ (prefixWord ++ tailWord_3311347).sum := by decide
  have hdescent : baseEnd_3311347 < baseStart_3311347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311388 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 8]
def baseStart_3311388 : Nat := 118140960795 + 3311388 * 2 ^ 59
def prefixEnd_3311388 : Nat := 4983230072969 + 3 ^ 40 * 3311388 * 2
def baseEnd_3311388 : Nat := 377851928340132313982491

theorem tailTrace_3311388 : CollatzResearch.WordTrace tailWord_3311388 prefixEnd_3311388 377851928340132313982491 := by
  unfold tailWord_3311388
  simp only [CollatzResearch.WordTrace]
  refine ⟨60388121263707145445283409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80517495018276193927044545 60388121263707145445283409)
  ·
    refine ⟨45291090947780359083962557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60388121263707145445283409 45291090947780359083962557)
    ·
      refine ⟨16984159105417634656485959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45291090947780359083962557 16984159105417634656485959)
      ·
        refine ⟨25476238658126451984728939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16984159105417634656485959 25476238658126451984728939)
        ·
          refine ⟨38214357987189677977093409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25476238658126451984728939 38214357987189677977093409)
          ·
            refine ⟨28660768490392258482820057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38214357987189677977093409 28660768490392258482820057)
            ·
              refine ⟨21495576367794193862115043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28660768490392258482820057 21495576367794193862115043)
              ·
                refine ⟨32243364551691290793172565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21495576367794193862115043 32243364551691290793172565)
                ·
                  refine ⟨377851928340132313982491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32243364551691290793172565 377851928340132313982491)
                  ·
                    rfl

theorem cell22_3311388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_3311388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311388 prefixEnd_3311388 := by exact prefixLift 3311388
  have htrace : WordTrace (prefixWord ++ tailWord_3311388) baseStart_3311388 baseEnd_3311388 := by
    simpa [prefixWord, tailWord_3311388, baseEnd_3311388] using wordTrace_append hprefix tailTrace_3311388
  have hstable : (prefixWord ++ tailWord_3311388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311388).length < 2 ^ (prefixWord ++ tailWord_3311388).sum := by decide
  have hdescent : baseEnd_3311388 < baseStart_3311388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311420 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 4, 3]
def baseStart_3311420 : Nat := 118140960795 + 3311420 * 2 ^ 59
def prefixEnd_3311420 : Nat := 4983230072969 + 3 ^ 40 * 3311420 * 2
def baseEnd_3311420 : Nat := 1133566739274359525147375

theorem tailTrace_3311420 : CollatzResearch.WordTrace tailWord_3311420 prefixEnd_3311420 1133566739274359525147375 := by
  unfold tailWord_3311420
  simp only [CollatzResearch.WordTrace]
  refine ⟨60388704831649180177865857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80518273108865573570487809 60388704831649180177865857)
  ·
    refine ⟨45291528623736885133399393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60388704831649180177865857 45291528623736885133399393)
    ·
      refine ⟨33968646467802663850049545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45291528623736885133399393 33968646467802663850049545)
      ·
        refine ⟨25476484850851997887537159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33968646467802663850049545 25476484850851997887537159)
        ·
          refine ⟨38214727276277996831305739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25476484850851997887537159 38214727276277996831305739)
          ·
            refine ⟨57322090914416995246958609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38214727276277996831305739 57322090914416995246958609)
            ·
              refine ⟨42991568185812746435218957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57322090914416995246958609 42991568185812746435218957)
              ·
                refine ⟨16121838069679779913207109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42991568185812746435218957 16121838069679779913207109)
                ·
                  refine ⟨3022844638064958733726333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16121838069679779913207109 3022844638064958733726333)
                  ·
                    refine ⟨1133566739274359525147375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022844638064958733726333 1133566739274359525147375)
                    ·
                      rfl

theorem cell22_3311420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_3311420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311420 prefixEnd_3311420 := by exact prefixLift 3311420
  have htrace : WordTrace (prefixWord ++ tailWord_3311420) baseStart_3311420 baseEnd_3311420 := by
    simpa [prefixWord, tailWord_3311420, baseEnd_3311420] using wordTrace_append hprefix tailTrace_3311420
  have hstable : (prefixWord ++ tailWord_3311420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311420).length < 2 ^ (prefixWord ++ tailWord_3311420).sum := by decide
  have hdescent : baseEnd_3311420 < baseStart_3311420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311437 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3311437 : Nat := 118140960795 + 3311437 * 2 ^ 59
def prefixEnd_3311437 : Nat := 4983230072969 + 3 ^ 40 * 3311437 * 2
def baseEnd_3311437 : Nat := 1133572558721777147472323

theorem tailTrace_3311437 : CollatzResearch.WordTrace tailWord_3311437 prefixEnd_3311437 1133572558721777147472323 := by
  unfold tailWord_3311437
  simp only [CollatzResearch.WordTrace]
  refine ⟨120778029704236772259100565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80518686469491181506067043 120778029704236772259100565)
  ·
    refine ⟨5661470142386098699645339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120778029704236772259100565 5661470142386098699645339)
    ·
      refine ⟨8492205213579148049468009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5661470142386098699645339 8492205213579148049468009)
      ·
        refine ⟨6369153910184361037101007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8492205213579148049468009 6369153910184361037101007)
        ·
          refine ⟨9553730865276541555651511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369153910184361037101007 9553730865276541555651511)
          ·
            refine ⟨14330596297914812333477267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9553730865276541555651511 14330596297914812333477267)
            ·
              refine ⟨21495894446872218500215901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14330596297914812333477267 21495894446872218500215901)
              ·
                refine ⟨8060960417577081937580963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21495894446872218500215901 8060960417577081937580963)
                ·
                  refine ⟨12091440626365622906371445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060960417577081937580963 12091440626365622906371445)
                  ·
                    refine ⟨1133572558721777147472323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12091440626365622906371445 1133572558721777147472323)
                    ·
                      rfl

theorem cell22_3311437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3311437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311437 prefixEnd_3311437 := by exact prefixLift 3311437
  have htrace : WordTrace (prefixWord ++ tailWord_3311437) baseStart_3311437 baseEnd_3311437 := by
    simpa [prefixWord, tailWord_3311437, baseEnd_3311437] using wordTrace_append hprefix tailTrace_3311437
  have hstable : (prefixWord ++ tailWord_3311437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311437).length < 2 ^ (prefixWord ++ tailWord_3311437).sum := by decide
  have hdescent : baseEnd_3311437 < baseStart_3311437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311450 : List Nat := [3, 1, 1, 2, 1, 3, 5, 6]
def baseStart_3311450 : Nat := 118140960795 + 3311450 * 2 ^ 59
def prefixEnd_3311450 : Nat := 4983230072969 + 3 ^ 40 * 3311450 * 2
def baseEnd_3311450 : Nat := 125953000987494382988587

theorem tailTrace_3311450 : CollatzResearch.WordTrace tailWord_3311450 prefixEnd_3311450 125953000987494382988587 := by
  unfold tailWord_3311450
  simp only [CollatzResearch.WordTrace]
  refine ⟨30194625963297418869830951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80519002568793116986215869 30194625963297418869830951)
  ·
    refine ⟨45291938944946128304746427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30194625963297418869830951 45291938944946128304746427)
    ·
      refine ⟨67937908417419192457119641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45291938944946128304746427 67937908417419192457119641)
      ·
        refine ⟨50953431313064394342839731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67937908417419192457119641 50953431313064394342839731)
        ·
          refine ⟨76430146969596591514259597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50953431313064394342839731 76430146969596591514259597)
          ·
            refine ⟨28661305113598721817847349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76430146969596591514259597 28661305113598721817847349)
            ·
              refine ⟨2686997354399880170423189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28661305113598721817847349 2686997354399880170423189)
              ·
                refine ⟨125953000987494382988587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2686997354399880170423189 125953000987494382988587)
                ·
                  rfl

theorem cell22_3311450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_3311450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311450 prefixEnd_3311450 := by exact prefixLift 3311450
  have htrace : WordTrace (prefixWord ++ tailWord_3311450) baseStart_3311450 baseEnd_3311450 := by
    simpa [prefixWord, tailWord_3311450, baseEnd_3311450] using wordTrace_append hprefix tailTrace_3311450
  have hstable : (prefixWord ++ tailWord_3311450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311450).length < 2 ^ (prefixWord ++ tailWord_3311450).sum := by decide
  have hdescent : baseEnd_3311450 < baseStart_3311450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311452 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3311452 : Nat := 118140960795 + 3311452 * 2 ^ 59
def prefixEnd_3311452 : Nat := 4983230072969 + 3 ^ 40 * 3311452 * 2
def baseEnd_3311452 : Nat := 1133577693528322108347277

theorem tailTrace_3311452 : CollatzResearch.WordTrace tailWord_3311452 prefixEnd_3311452 1133577693528322108347277 := by
  unfold tailWord_3311452
  simp only [CollatzResearch.WordTrace]
  refine ⟨60389288399591214910448305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80519051199454953213931073 60389288399591214910448305)
  ·
    refine ⟨45291966299693411182836229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60389288399591214910448305 45291966299693411182836229)
    ·
      refine ⟨8492243681192514596781793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45291966299693411182836229 8492243681192514596781793)
      ·
        refine ⟨6369182760894385947586345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8492243681192514596781793 6369182760894385947586345)
        ·
          refine ⟨4776887070670789460689759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6369182760894385947586345 4776887070670789460689759)
          ·
            refine ⟨7165330606006184191034639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776887070670789460689759 7165330606006184191034639)
            ·
              refine ⟨10747995909009276286551959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7165330606006184191034639 10747995909009276286551959)
              ·
                refine ⟨16121993863513914429827939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10747995909009276286551959 16121993863513914429827939)
                ·
                  refine ⟨24182990795270871644741909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16121993863513914429827939 24182990795270871644741909)
                  ·
                    refine ⟨1133577693528322108347277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24182990795270871644741909 1133577693528322108347277)
                    ·
                      rfl

theorem cell22_3311452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3311452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311452 prefixEnd_3311452 := by exact prefixLift 3311452
  have htrace : WordTrace (prefixWord ++ tailWord_3311452) baseStart_3311452 baseEnd_3311452 := by
    simpa [prefixWord, tailWord_3311452, baseEnd_3311452] using wordTrace_append hprefix tailTrace_3311452
  have hstable : (prefixWord ++ tailWord_3311452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311452).length < 2 ^ (prefixWord ++ tailWord_3311452).sum := by decide
  have hdescent : baseEnd_3311452 < baseStart_3311452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311516 : List Nat := [2, 2, 3, 3, 1, 1, 3, 3, 1, 3]
def baseStart_3311516 : Nat := 118140960795 + 3311516 * 2 ^ 59
def prefixEnd_3311516 : Nat := 4983230072969 + 3 ^ 40 * 3311516 * 2
def baseEnd_3311516 : Nat := 1133599602036247274747081

theorem tailTrace_3311516 : CollatzResearch.WordTrace tailWord_3311516 prefixEnd_3311516 1133599602036247274747081 := by
  unfold tailWord_3311516
  simp only [CollatzResearch.WordTrace]
  refine ⟨60390455535475284375613201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80520607380633712500817601 60390455535475284375613201)
  ·
    refine ⟨45292841651606463281709901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60390455535475284375613201 45292841651606463281709901)
    ·
      refine ⟨16984815619352423730641213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45292841651606463281709901 16984815619352423730641213)
      ·
        refine ⟨6369305857257158898990455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16984815619352423730641213 6369305857257158898990455)
        ·
          refine ⟨9553958785885738348485683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369305857257158898990455 9553958785885738348485683)
          ·
            refine ⟨14330938178828607522728525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9553958785885738348485683 14330938178828607522728525)
            ·
              refine ⟨5374101817060727821023197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14330938178828607522728525 5374101817060727821023197)
              ·
                refine ⟨2015288181397772932883699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5374101817060727821023197 2015288181397772932883699)
                ·
                  refine ⟨3022932272096659399325549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015288181397772932883699 3022932272096659399325549)
                  ·
                    refine ⟨1133599602036247274747081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3022932272096659399325549 1133599602036247274747081)
                    ·
                      rfl

theorem cell22_3311516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_3311516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311516 prefixEnd_3311516 := by exact prefixLift 3311516
  have htrace : WordTrace (prefixWord ++ tailWord_3311516) baseStart_3311516 baseEnd_3311516 := by
    simpa [prefixWord, tailWord_3311516, baseEnd_3311516] using wordTrace_append hprefix tailTrace_3311516
  have hstable : (prefixWord ++ tailWord_3311516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311516).length < 2 ^ (prefixWord ++ tailWord_3311516).sum := by decide
  have hdescent : baseEnd_3311516 < baseStart_3311516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311572 : List Nat := [2, 4, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_3311572 : Nat := 118140960795 + 3311572 * 2 ^ 59
def prefixEnd_3311572 : Nat := 4983230072969 + 3 ^ 40 * 3311572 * 2
def baseEnd_3311572 : Nat := 1133618771980681795346909

theorem tailTrace_3311572 : CollatzResearch.WordTrace tailWord_3311572 prefixEnd_3311572 1133618771980681795346909 := by
  unfold tailWord_3311572
  simp only [CollatzResearch.WordTrace]
  refine ⟨60391476779373845157632485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80521969039165126876843313 60391476779373845157632485)
  ·
    refine ⟨11323401896132595967056091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60391476779373845157632485 11323401896132595967056091)
    ·
      refine ⟨16985102844198893950584137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11323401896132595967056091 16985102844198893950584137)
      ·
        refine ⟨12738827133149170462938103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16985102844198893950584137 12738827133149170462938103)
        ·
          refine ⟨19108240699723755694407155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12738827133149170462938103 19108240699723755694407155)
          ·
            refine ⟨28662361049585633541610733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19108240699723755694407155 28662361049585633541610733)
            ·
              refine ⟨10748385393594612578104025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28662361049585633541610733 10748385393594612578104025)
              ·
                refine ⟨8061289045195959433578019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10748385393594612578104025 8061289045195959433578019)
                ·
                  refine ⟨12091933567793939150367029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8061289045195959433578019 12091933567793939150367029)
                  ·
                    refine ⟨1133618771980681795346909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12091933567793939150367029 1133618771980681795346909)
                    ·
                      rfl

theorem cell22_3311572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_3311572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311572 prefixEnd_3311572 := by exact prefixLift 3311572
  have htrace : WordTrace (prefixWord ++ tailWord_3311572) baseStart_3311572 baseEnd_3311572 := by
    simpa [prefixWord, tailWord_3311572, baseEnd_3311572] using wordTrace_append hprefix tailTrace_3311572
  have hstable : (prefixWord ++ tailWord_3311572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311572).length < 2 ^ (prefixWord ++ tailWord_3311572).sum := by decide
  have hdescent : baseEnd_3311572 < baseStart_3311572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311587 : List Nat := [1, 1, 1, 6, 1, 2, 2, 2, 2, 4]
def baseStart_3311587 : Nat := 118140960795 + 3311587 * 2 ^ 59
def prefixEnd_3311587 : Nat := 4983230072969 + 3 ^ 40 * 3311587 * 2
def baseEnd_3311587 : Nat := 1133623906787226756221863

theorem tailTrace_3311587 : CollatzResearch.WordTrace tailWord_3311587 prefixEnd_3311587 1133623906787226756221863 := by
  unfold tailWord_3311587
  simp only [CollatzResearch.WordTrace]
  refine ⟨120783500653693347877061015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80522333769128898584707343 120783500653693347877061015)
  ·
    refine ⟨181175250980540021815591523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120783500653693347877061015 181175250980540021815591523)
    ·
      refine ⟨271762876470810032723387285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181175250980540021815591523 271762876470810032723387285)
      ·
        refine ⟨12738884834569220283908779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 271762876470810032723387285 12738884834569220283908779)
        ·
          refine ⟨19108327251853830425863169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12738884834569220283908779 19108327251853830425863169)
          ·
            refine ⟨14331245438890372819397377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19108327251853830425863169 14331245438890372819397377)
            ·
              refine ⟨10748434079167779614548033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14331245438890372819397377 10748434079167779614548033)
              ·
                refine ⟨8061325559375834710911025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10748434079167779614548033 8061325559375834710911025)
                ·
                  refine ⟨6045994169531876033183269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8061325559375834710911025 6045994169531876033183269)
                  ·
                    refine ⟨1133623906787226756221863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6045994169531876033183269 1133623906787226756221863)
                    ·
                      rfl

theorem cell22_3311587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 4].length) (baseStart_3311587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311587 prefixEnd_3311587 := by exact prefixLift 3311587
  have htrace : WordTrace (prefixWord ++ tailWord_3311587) baseStart_3311587 baseEnd_3311587 := by
    simpa [prefixWord, tailWord_3311587, baseEnd_3311587] using wordTrace_append hprefix tailTrace_3311587
  have hstable : (prefixWord ++ tailWord_3311587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311587).length < 2 ^ (prefixWord ++ tailWord_3311587).sum := by decide
  have hdescent : baseEnd_3311587 < baseStart_3311587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311660 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_3311660 : Nat := 118140960795 + 3311660 * 2 ^ 59
def prefixEnd_3311660 : Nat := 4983230072969 + 3 ^ 40 * 3311660 * 2
def baseEnd_3311660 : Nat := 1133648896179078899146639

theorem tailTrace_3311660 : CollatzResearch.WordTrace tailWord_3311660 prefixEnd_3311660 1133648896179078899146639 := by
  unfold tailWord_3311660
  simp only [CollatzResearch.WordTrace]
  refine ⟨60393081591214440672234217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80524108788285920896312289 60393081591214440672234217)
  ·
    refine ⟨45294811193410830504175663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60393081591214440672234217 45294811193410830504175663)
    ·
      refine ⟨67942216790116245756263495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45294811193410830504175663 67942216790116245756263495)
      ·
        refine ⟨101913325185174368634395243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67942216790116245756263495 101913325185174368634395243)
        ·
          refine ⟨152869987777761552951592865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101913325185174368634395243 152869987777761552951592865)
          ·
            refine ⟨114652490833321164713694649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152869987777761552951592865 114652490833321164713694649)
            ·
              refine ⟨85989368124990873535270987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114652490833321164713694649 85989368124990873535270987)
              ·
                refine ⟨128984052187486310302906481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85989368124990873535270987 128984052187486310302906481)
                ·
                  refine ⟨96738039140614732727179861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128984052187486310302906481 96738039140614732727179861)
                  ·
                    refine ⟨1133648896179078899146639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96738039140614732727179861 1133648896179078899146639)
                    ·
                      rfl

theorem cell22_3311660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_3311660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311660 prefixEnd_3311660 := by exact prefixLift 3311660
  have htrace : WordTrace (prefixWord ++ tailWord_3311660) baseStart_3311660 baseEnd_3311660 := by
    simpa [prefixWord, tailWord_3311660, baseEnd_3311660] using wordTrace_append hprefix tailTrace_3311660
  have hstable : (prefixWord ++ tailWord_3311660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311660).length < 2 ^ (prefixWord ++ tailWord_3311660).sum := by decide
  have hdescent : baseEnd_3311660 < baseStart_3311660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311664 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 5]
def baseStart_3311664 : Nat := 118140960795 + 3311664 * 2 ^ 59
def prefixEnd_3311664 : Nat := 4983230072969 + 3 ^ 40 * 3311664 * 2
def baseEnd_3311664 : Nat := 377883421820274740682209

theorem tailTrace_3311664 : CollatzResearch.WordTrace tailWord_3311664 prefixEnd_3311664 377883421820274740682209 := by
  unfold tailWord_3311664
  simp only [CollatzResearch.WordTrace]
  refine ⟨60393154537207195013807023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80524206049609593351742697 60393154537207195013807023)
  ·
    refine ⟨90589731805810792520710535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60393154537207195013807023 90589731805810792520710535)
    ·
      refine ⟨135884597708716188781065803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90589731805810792520710535 135884597708716188781065803)
      ·
        refine ⟨203826896563074283171598705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135884597708716188781065803 203826896563074283171598705)
        ·
          refine ⟨152870172422305712378699029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203826896563074283171598705 152870172422305712378699029)
          ·
            refine ⟨7165789332295580267751517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152870172422305712378699029 7165789332295580267751517)
            ·
              refine ⟨2687170999610842600406819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7165789332295580267751517 2687170999610842600406819)
              ·
                refine ⟨4030756499416263900610229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687170999610842600406819 4030756499416263900610229)
                ·
                  refine ⟨377883421820274740682209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4030756499416263900610229 377883421820274740682209)
                  ·
                    rfl

theorem cell22_3311664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 5].length) (baseStart_3311664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311664 prefixEnd_3311664 := by exact prefixLift 3311664
  have htrace : WordTrace (prefixWord ++ tailWord_3311664) baseStart_3311664 baseEnd_3311664 := by
    simpa [prefixWord, tailWord_3311664, baseEnd_3311664] using wordTrace_append hprefix tailTrace_3311664
  have hstable : (prefixWord ++ tailWord_3311664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311664).length < 2 ^ (prefixWord ++ tailWord_3311664).sum := by decide
  have hdescent : baseEnd_3311664 < baseStart_3311664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311694 : List Nat := [4, 1, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_3311694 : Nat := 118140960795 + 3311694 * 2 ^ 59
def prefixEnd_3311694 : Nat := 4983230072969 + 3 ^ 40 * 3311694 * 2
def baseEnd_3311694 : Nat := 1133660535073914143796535

theorem tailTrace_3311694 : CollatzResearch.WordTrace tailWord_3311694 prefixEnd_3311694 1133660535073914143796535 := by
  unfold tailWord_3311694
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098425408038213143900767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80524935509537136767470757 15098425408038213143900767)
  ·
    refine ⟨22647638112057319715851151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15098425408038213143900767 22647638112057319715851151)
    ·
      refine ⟨33971457168085979573776727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22647638112057319715851151 33971457168085979573776727)
      ·
        refine ⟨50957185752128969360665091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33971457168085979573776727 50957185752128969360665091)
        ·
          refine ⟨76435778628193454040997637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50957185752128969360665091 76435778628193454040997637)
          ·
            refine ⟨14331708492786272632687057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76435778628193454040997637 14331708492786272632687057)
            ·
              refine ⟨10748781369589704474515293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14331708492786272632687057 10748781369589704474515293)
              ·
                refine ⟨4030793013596139177943235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10748781369589704474515293 4030793013596139177943235)
                ·
                  refine ⟨6046189520394208766914853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4030793013596139177943235 6046189520394208766914853)
                  ·
                    refine ⟨1133660535073914143796535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6046189520394208766914853 1133660535073914143796535)
                    ·
                      rfl

theorem cell22_3311694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_3311694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311694 prefixEnd_3311694 := by exact prefixLift 3311694
  have htrace : WordTrace (prefixWord ++ tailWord_3311694) baseStart_3311694 baseEnd_3311694 := by
    simpa [prefixWord, tailWord_3311694, baseEnd_3311694] using wordTrace_append hprefix tailTrace_3311694
  have hstable : (prefixWord ++ tailWord_3311694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311694).length < 2 ^ (prefixWord ++ tailWord_3311694).sum := by decide
  have hdescent : baseEnd_3311694 < baseStart_3311694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311702 : List Nat := [5, 2, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3311702 : Nat := 118140960795 + 3311702 * 2 ^ 59
def prefixEnd_3311702 : Nat := 4983230072969 + 3 ^ 40 * 3311702 * 2
def baseEnd_3311702 : Nat := 1133663273637404789596511

theorem tailTrace_3311702 : CollatzResearch.WordTrace tailWord_3311702 prefixEnd_3311702 1133663273637404789596511 := by
  unfold tailWord_3311702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7549230940517295157343585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80525130032184481678331573 7549230940517295157343585)
  ·
    refine ⟨5661923205387971368007689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7549230940517295157343585 5661923205387971368007689)
    ·
      refine ⟨4246442404040978526005767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5661923205387971368007689 4246442404040978526005767)
      ·
        refine ⟨6369663606061467789008651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4246442404040978526005767 6369663606061467789008651)
        ·
          refine ⟨9554495409092201683512977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6369663606061467789008651 9554495409092201683512977)
          ·
            refine ⟨7165871556819151262634733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9554495409092201683512977 7165871556819151262634733)
            ·
              refine ⟨2687201833807181723488025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7165871556819151262634733 2687201833807181723488025)
              ·
                refine ⟨2015401375355386292616019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2687201833807181723488025 2015401375355386292616019)
                ·
                  refine ⟨3023102063033079438924029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015401375355386292616019 3023102063033079438924029)
                  ·
                    refine ⟨1133663273637404789596511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023102063033079438924029 1133663273637404789596511)
                    ·
                      rfl

theorem cell22_3311702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3311702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311702 prefixEnd_3311702 := by exact prefixLift 3311702
  have htrace : WordTrace (prefixWord ++ tailWord_3311702) baseStart_3311702 baseEnd_3311702 := by
    simpa [prefixWord, tailWord_3311702, baseEnd_3311702] using wordTrace_append hprefix tailTrace_3311702
  have hstable : (prefixWord ++ tailWord_3311702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311702).length < 2 ^ (prefixWord ++ tailWord_3311702).sum := by decide
  have hdescent : baseEnd_3311702 < baseStart_3311702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311737 : List Nat := [1, 2, 1, 3, 4, 1, 2, 8]
def baseStart_3311737 : Nat := 118140960795 + 3311737 * 2 ^ 59
def prefixEnd_3311737 : Nat := 4983230072969 + 3 ^ 40 * 3311737 * 2
def baseEnd_3311737 : Nat := 125963917205852929441267

theorem tailTrace_3311737 : CollatzResearch.WordTrace tailWord_3311737 prefixEnd_3311737 125963917205852929441267 := by
  unfold tailWord_3311737
  simp only [CollatzResearch.WordTrace]
  refine ⟨120788971603149923495021465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80525981068766615663347643 120788971603149923495021465)
  ·
    refine ⟨90591728702362442621266099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120788971603149923495021465 90591728702362442621266099)
    ·
      refine ⟨135887593053543663931899149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90591728702362442621266099 135887593053543663931899149)
      ·
        refine ⟨50957847395078873974462181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135887593053543663931899149 50957847395078873974462181)
        ·
          refine ⟨9554596386577288870211659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50957847395078873974462181 9554596386577288870211659)
          ·
            refine ⟨14331894579865933305317489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9554596386577288870211659 14331894579865933305317489)
            ·
              refine ⟨10748920934899449978988117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14331894579865933305317489 10748920934899449978988117)
              ·
                refine ⟨125963917205852929441267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10748920934899449978988117 125963917205852929441267)
                ·
                  rfl

theorem cell22_3311737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 8].length) (baseStart_3311737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311737 prefixEnd_3311737 := by exact prefixLift 3311737
  have htrace : WordTrace (prefixWord ++ tailWord_3311737) baseStart_3311737 baseEnd_3311737 := by
    simpa [prefixWord, tailWord_3311737, baseEnd_3311737] using wordTrace_append hprefix tailTrace_3311737
  have hstable : (prefixWord ++ tailWord_3311737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311737).length < 2 ^ (prefixWord ++ tailWord_3311737).sum := by decide
  have hdescent : baseEnd_3311737 < baseStart_3311737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311758 : List Nat := [4, 1, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_3311758 : Nat := 118140960795 + 3311758 * 2 ^ 59
def prefixEnd_3311758 : Nat := 4983230072969 + 3 ^ 40 * 3311758 * 2
def baseEnd_3311758 : Nat := 1133682443581839310196339

theorem tailTrace_3311758 : CollatzResearch.WordTrace tailWord_3311758 prefixEnd_3311758 1133682443581839310196339 := by
  unfold tailWord_3311758
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098717192009230510191991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80526491690715896054357285 15098717192009230510191991)
  ·
    refine ⟨22648075788013845765287987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15098717192009230510191991 22648075788013845765287987)
    ·
      refine ⟨33972113682020768647931981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22648075788013845765287987 33972113682020768647931981)
      ·
        refine ⟨12739542630757788242974493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33972113682020768647931981 12739542630757788242974493)
        ·
          refine ⟨4777328486534170591115435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12739542630757788242974493 4777328486534170591115435)
          ·
            refine ⟨7165992729801255886673153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4777328486534170591115435 7165992729801255886673153)
            ·
              refine ⟨5374494547350941915004865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7165992729801255886673153 5374494547350941915004865)
              ·
                refine ⟨4030870910513206436253649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5374494547350941915004865 4030870910513206436253649)
                ·
                  refine ⟨3023153182884904827190237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4030870910513206436253649 3023153182884904827190237)
                  ·
                    refine ⟨1133682443581839310196339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023153182884904827190237 1133682443581839310196339)
                    ·
                      rfl

theorem cell22_3311758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_3311758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311758 prefixEnd_3311758 := by exact prefixLift 3311758
  have htrace : WordTrace (prefixWord ++ tailWord_3311758) baseStart_3311758 baseEnd_3311758 := by
    simpa [prefixWord, tailWord_3311758, baseEnd_3311758] using wordTrace_append hprefix tailTrace_3311758
  have hstable : (prefixWord ++ tailWord_3311758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311758).length < 2 ^ (prefixWord ++ tailWord_3311758).sum := by decide
  have hdescent : baseEnd_3311758 < baseStart_3311758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311790 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3311790 : Nat := 118140960795 + 3311790 * 2 ^ 59
def prefixEnd_3311790 : Nat := 4983230072969 + 3 ^ 40 * 3311790 * 2
def baseEnd_3311790 : Nat := 1133693397835801893396241

theorem tailTrace_3311790 : CollatzResearch.WordTrace tailWord_3311790 prefixEnd_3311790 1133693397835801893396241 := by
  unfold tailWord_3311790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098863083994739193337603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80527269781305275697800549 15098863083994739193337603)
  ·
    refine ⟨22648294625992108790006405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15098863083994739193337603 22648294625992108790006405)
    ·
      refine ⟨4246555242373520398126201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22648294625992108790006405 4246555242373520398126201)
      ·
        refine ⟨3184916431780140298594651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4246555242373520398126201 3184916431780140298594651)
        ·
          refine ⟨4777374647670210447891977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184916431780140298594651 4777374647670210447891977)
          ·
            refine ⟨3583030985752657835918983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777374647670210447891977 3583030985752657835918983)
            ·
              refine ⟨5374546478628986753878475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583030985752657835918983 5374546478628986753878475)
              ·
                refine ⟨8061819717943480130817713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5374546478628986753878475 8061819717943480130817713)
                ·
                  refine ⟨6046364788457610098113285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8061819717943480130817713 6046364788457610098113285)
                  ·
                    refine ⟨1133693397835801893396241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6046364788457610098113285 1133693397835801893396241)
                    ·
                      rfl

theorem cell22_3311790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3311790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311790 prefixEnd_3311790 := by exact prefixLift 3311790
  have htrace : WordTrace (prefixWord ++ tailWord_3311790) baseStart_3311790 baseEnd_3311790 := by
    simpa [prefixWord, tailWord_3311790, baseEnd_3311790] using wordTrace_append hprefix tailTrace_3311790
  have hstable : (prefixWord ++ tailWord_3311790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311790).length < 2 ^ (prefixWord ++ tailWord_3311790).sum := by decide
  have hdescent : baseEnd_3311790 < baseStart_3311790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311859 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 6, 3]
def baseStart_3311859 : Nat := 118140960795 + 3311859 * 2 ^ 59
def prefixEnd_3311859 : Nat := 4983230072969 + 3 ^ 40 * 3311859 * 2
def baseEnd_3311859 : Nat := 1133717017945908713421029

theorem tailTrace_3311859 : CollatzResearch.WordTrace tailWord_3311859 prefixEnd_3311859 1133717017945908713421029 := by
  unfold tailWord_3311859
  simp only [CollatzResearch.WordTrace]
  refine ⟨120793421308707938330962631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80528947539138625553975087 120793421308707938330962631)
  ·
    refine ⟨181190131963061907496443947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120793421308707938330962631 181190131963061907496443947)
    ·
      refine ⟨271785197944592861244665921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181190131963061907496443947 271785197944592861244665921)
      ·
        refine ⟨203838898458444645933499441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271785197944592861244665921 203838898458444645933499441)
        ·
          refine ⟨152879173843833484450124581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203838898458444645933499441 152879173843833484450124581)
          ·
            refine ⟨28664845095718778334398359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152879173843833484450124581 28664845095718778334398359)
            ·
              refine ⟨42997267643578167501597539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28664845095718778334398359 42997267643578167501597539)
              ·
                refine ⟨64495901465367251252396309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42997267643578167501597539 64495901465367251252396309)
                ·
                  refine ⟨3023245381189089902456077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 64495901465367251252396309 3023245381189089902456077)
                  ·
                    refine ⟨1133717017945908713421029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023245381189089902456077 1133717017945908713421029)
                    ·
                      rfl

theorem cell22_3311859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 3].length) (baseStart_3311859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311859 prefixEnd_3311859 := by exact prefixLift 3311859
  have htrace : WordTrace (prefixWord ++ tailWord_3311859) baseStart_3311859 baseEnd_3311859 := by
    simpa [prefixWord, tailWord_3311859, baseEnd_3311859] using wordTrace_append hprefix tailTrace_3311859
  have hstable : (prefixWord ++ tailWord_3311859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311859).length < 2 ^ (prefixWord ++ tailWord_3311859).sum := by decide
  have hdescent : baseEnd_3311859 < baseStart_3311859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311872 : List Nat := [2, 1, 1, 2, 1, 1, 14]
def baseStart_3311872 : Nat := 118140960795 + 3311872 * 2 ^ 59
def prefixEnd_3311872 : Nat := 4983230072969 + 3 ^ 40 * 3311872 * 2
def baseEnd_3311872 : Nat := 41989684004132630105407

theorem tailTrace_3311872 : CollatzResearch.WordTrace tailWord_3311872 prefixEnd_3311872 41989684004132630105407 := by
  unfold tailWord_3311872
  simp only [CollatzResearch.WordTrace]
  refine ⟨60396947728830420775592935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80529263638440561034123913 60396947728830420775592935)
  ·
    refine ⟨90595421593245631163389403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60396947728830420775592935 90595421593245631163389403)
    ·
      refine ⟨135893132389868446745084105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90595421593245631163389403 135893132389868446745084105)
      ·
        refine ⟨101919849292401335058813079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135893132389868446745084105 101919849292401335058813079)
        ·
          refine ⟨152879773938602002588219619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101919849292401335058813079 152879773938602002588219619)
          ·
            refine ⟨229319660907903003882329429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152879773938602002588219619 229319660907903003882329429)
            ·
              refine ⟨41989684004132630105407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 229319660907903003882329429 41989684004132630105407)
              ·
                rfl

theorem cell22_3311872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 14].length) (baseStart_3311872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311872 prefixEnd_3311872 := by exact prefixLift 3311872
  have htrace : WordTrace (prefixWord ++ tailWord_3311872) baseStart_3311872 baseEnd_3311872 := by
    simpa [prefixWord, tailWord_3311872, baseEnd_3311872] using wordTrace_append hprefix tailTrace_3311872
  have hstable : (prefixWord ++ tailWord_3311872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311872).length < 2 ^ (prefixWord ++ tailWord_3311872).sum := by decide
  have hdescent : baseEnd_3311872 < baseStart_3311872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311889 : List Nat := [1, 2, 2, 1, 1, 6, 2, 7]
def baseStart_3311889 : Nat := 118140960795 + 3311889 * 2 ^ 59
def prefixEnd_3311889 : Nat := 4983230072969 + 3 ^ 40 * 3311889 * 2
def baseEnd_3311889 : Nat := 125969698617666515018993

theorem tailTrace_3311889 : CollatzResearch.WordTrace tailWord_3311889 prefixEnd_3311889 125969698617666515018993 := by
  unfold tailWord_3311889
  simp only [CollatzResearch.WordTrace]
  refine ⟨120794515498599253454554721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80529676999066168969703147 120794515498599253454554721)
  ·
    refine ⟨90595886623949440090916041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120794515498599253454554721 90595886623949440090916041)
    ·
      refine ⟨67946914967962080068187031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90595886623949440090916041 67946914967962080068187031)
      ·
        refine ⟨101920372451943120102280547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67946914967962080068187031 101920372451943120102280547)
        ·
          refine ⟨152880558677914680153420821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101920372451943120102280547 152880558677914680153420821)
          ·
            refine ⟨7166276188027250632191601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152880558677914680153420821 7166276188027250632191601)
            ·
              refine ⟨5374707141020437974143701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7166276188027250632191601 5374707141020437974143701)
              ·
                refine ⟨125969698617666515018993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5374707141020437974143701 125969698617666515018993)
                ·
                  rfl

theorem cell22_3311889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 7].length) (baseStart_3311889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311889 prefixEnd_3311889 := by exact prefixLift 3311889
  have htrace : WordTrace (prefixWord ++ tailWord_3311889) baseStart_3311889 baseEnd_3311889 := by
    simpa [prefixWord, tailWord_3311889, baseEnd_3311889] using wordTrace_append hprefix tailTrace_3311889
  have hstable : (prefixWord ++ tailWord_3311889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311889).length < 2 ^ (prefixWord ++ tailWord_3311889).sum := by decide
  have hdescent : baseEnd_3311889 < baseStart_3311889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311893 : List Nat := [1, 3, 2, 1, 2, 1, 6, 1, 2, 3]
def baseStart_3311893 : Nat := 118140960795 + 3311893 * 2 ^ 59
def prefixEnd_3311893 : Nat := 4983230072969 + 3 ^ 40 * 3311893 * 2
def baseEnd_3311893 : Nat := 1133728656840743958070925

theorem tailTrace_3311893 : CollatzResearch.WordTrace tailWord_3311893 prefixEnd_3311893 1133728656840743958070925 := by
  unfold tailWord_3311893
  simp only [CollatzResearch.WordTrace]
  refine ⟨120794661390584762137700333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80529774260389841425133555 120794661390584762137700333)
  ·
    refine ⟨45297998021469285801637625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120794661390584762137700333 45297998021469285801637625)
    ·
      refine ⟨33973498516101964351228219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45297998021469285801637625 33973498516101964351228219)
      ·
        refine ⟨50960247774152946526842329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33973498516101964351228219 50960247774152946526842329)
        ·
          refine ⟨38220185830614709895131747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50960247774152946526842329 38220185830614709895131747)
          ·
            refine ⟨57330278745922064842697621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38220185830614709895131747 57330278745922064842697621)
            ·
              refine ⟨2687356816215096789501451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57330278745922064842697621 2687356816215096789501451)
              ·
                refine ⟨4031035224322645184252177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687356816215096789501451 4031035224322645184252177)
                ·
                  refine ⟨3023276418241983888189133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4031035224322645184252177 3023276418241983888189133)
                  ·
                    refine ⟨1133728656840743958070925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023276418241983888189133 1133728656840743958070925)
                    ·
                      rfl

theorem cell22_3311893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_3311893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311893 prefixEnd_3311893 := by exact prefixLift 3311893
  have htrace : WordTrace (prefixWord ++ tailWord_3311893) baseStart_3311893 baseEnd_3311893 := by
    simpa [prefixWord, tailWord_3311893, baseEnd_3311893] using wordTrace_append hprefix tailTrace_3311893
  have hstable : (prefixWord ++ tailWord_3311893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311893).length < 2 ^ (prefixWord ++ tailWord_3311893).sum := by decide
  have hdescent : baseEnd_3311893 < baseStart_3311893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3311940 : List Nat := [2, 3, 4, 1, 3, 1, 1, 7]
def baseStart_3311940 : Nat := 118140960795 + 3311940 * 2 ^ 59
def prefixEnd_3311940 : Nat := 4983230072969 + 3 ^ 40 * 3311940 * 2
def baseEnd_3311940 : Nat := 125971638433472389127309

theorem tailTrace_3311940 : CollatzResearch.WordTrace tailWord_3311940 prefixEnd_3311940 125971638433472389127309 := by
  unfold tailWord_3311940
  simp only [CollatzResearch.WordTrace]
  refine ⟨60398187810707244582330637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80530917080942992776440849 60398187810707244582330637)
  ·
    refine ⟨22649320429015216718373989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60398187810707244582330637 22649320429015216718373989)
    ·
      refine ⟨4246747580440353134695123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22649320429015216718373989 4246747580440353134695123)
      ·
        refine ⟨6370121370660529702042685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4246747580440353134695123 6370121370660529702042685)
        ·
          refine ⟨2388795513997698638266007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6370121370660529702042685 2388795513997698638266007)
          ·
            refine ⟨3583193270996547957399011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388795513997698638266007 3583193270996547957399011)
            ·
              refine ⟨5374789906494821936098517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583193270996547957399011 5374789906494821936098517)
              ·
                refine ⟨125971638433472389127309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5374789906494821936098517 125971638433472389127309)
                ·
                  rfl

theorem cell22_3311940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 7].length) (baseStart_3311940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3311940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3311940 prefixEnd_3311940 := by exact prefixLift 3311940
  have htrace : WordTrace (prefixWord ++ tailWord_3311940) baseStart_3311940 baseEnd_3311940 := by
    simpa [prefixWord, tailWord_3311940, baseEnd_3311940] using wordTrace_append hprefix tailTrace_3311940
  have hstable : (prefixWord ++ tailWord_3311940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3311940).length < 2 ^ (prefixWord ++ tailWord_3311940).sum := by decide
  have hdescent : baseEnd_3311940 < baseStart_3311940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3311940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312002 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_3312002 : Nat := 118140960795 + 3312002 * 2 ^ 59
def prefixEnd_3312002 : Nat := 4983230072969 + 3 ^ 40 * 3312002 * 2
def baseEnd_3312002 : Nat := 377921989922768002365197

theorem tailTrace_3312002 : CollatzResearch.WordTrace tailWord_3312002 prefixEnd_3312002 377921989922768002365197 := by
  unfold tailWord_3312002
  simp only [CollatzResearch.WordTrace]
  refine ⟨30199659236797468438354565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80532424631459915835612173 30199659236797468438354565)
  ·
    refine ⟨5662436106899525332191481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30199659236797468438354565 5662436106899525332191481)
    ·
      refine ⟨4246827080174643999143611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5662436106899525332191481 4246827080174643999143611)
      ·
        refine ⟨6370240620261965998715417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4246827080174643999143611 6370240620261965998715417)
        ·
          refine ⟨4777680465196474499036563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6370240620261965998715417 4777680465196474499036563)
          ·
            refine ⟨7166520697794711748554845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4777680465196474499036563 7166520697794711748554845)
            ·
              refine ⟨2687445261673016905708067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7166520697794711748554845 2687445261673016905708067)
              ·
                refine ⟨4031167892509525358562101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687445261673016905708067 4031167892509525358562101)
                ·
                  refine ⟨377921989922768002365197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4031167892509525358562101 377921989922768002365197)
                  ·
                    rfl

theorem cell22_3312002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_3312002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312002 prefixEnd_3312002 := by exact prefixLift 3312002
  have htrace : WordTrace (prefixWord ++ tailWord_3312002) baseStart_3312002 baseEnd_3312002 := by
    simpa [prefixWord, tailWord_3312002, baseEnd_3312002] using wordTrace_append hprefix tailTrace_3312002
  have hstable : (prefixWord ++ tailWord_3312002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312002).length < 2 ^ (prefixWord ++ tailWord_3312002).sum := by decide
  have hdescent : baseEnd_3312002 < baseStart_3312002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312011 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 1, 5]
def baseStart_3312011 : Nat := 118140960795 + 3312011 * 2 ^ 59
def prefixEnd_3312011 : Nat := 4983230072969 + 3 ^ 40 * 3312011 * 2
def baseEnd_3312011 : Nat := 1133769050652230983620563

theorem tailTrace_3312011 : CollatzResearch.WordTrace tailWord_3312011 prefixEnd_3312011 1133769050652230983620563 := by
  unfold tailWord_3312011
  simp only [CollatzResearch.WordTrace]
  refine ⟨120798965204157268290495887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80532643469438178860330591 120798965204157268290495887)
  ·
    refine ⟨181198447806235902435743831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120798965204157268290495887 181198447806235902435743831)
    ·
      refine ⟨271797671709353853653615747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181198447806235902435743831 271797671709353853653615747)
      ·
        refine ⟨407696507564030780480423621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271797671709353853653615747 407696507564030780480423621)
        ·
          refine ⟨76443095168255771340079429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407696507564030780480423621 76443095168255771340079429)
          ·
            refine ⟨14333080344047957126264893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76443095168255771340079429 14333080344047957126264893)
            ·
              refine ⟨5374905129017983922349335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14333080344047957126264893 5374905129017983922349335)
              ·
                refine ⟨8062357693526975883524003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5374905129017983922349335 8062357693526975883524003)
                ·
                  refine ⟨12093536540290463825286005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8062357693526975883524003 12093536540290463825286005)
                  ·
                    refine ⟨1133769050652230983620563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12093536540290463825286005 1133769050652230983620563)
                    ·
                      rfl

theorem cell22_3312011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 5].length) (baseStart_3312011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312011 prefixEnd_3312011 := by exact prefixLift 3312011
  have htrace : WordTrace (prefixWord ++ tailWord_3312011) baseStart_3312011 baseEnd_3312011 := by
    simpa [prefixWord, tailWord_3312011, baseEnd_3312011] using wordTrace_append hprefix tailTrace_3312011
  have hstable : (prefixWord ++ tailWord_3312011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312011).length < 2 ^ (prefixWord ++ tailWord_3312011).sum := by decide
  have hdescent : baseEnd_3312011 < baseStart_3312011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312026 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_3312026 : Nat := 118140960795 + 3312026 * 2 ^ 59
def prefixEnd_3312026 : Nat := 4983230072969 + 3 ^ 40 * 3312026 * 2
def baseEnd_3312026 : Nat := 1133774185458775944495517

theorem tailTrace_3312026 : CollatzResearch.WordTrace tailWord_3312026 prefixEnd_3312026 1133774185458775944495517 := by
  unfold tailWord_3312026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30199878074775731463072983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80533008199401950568194621 30199878074775731463072983)
  ·
    refine ⟨45299817112163597194609475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30199878074775731463072983 45299817112163597194609475)
    ·
      refine ⟨67949725668245395791914213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45299817112163597194609475 67949725668245395791914213)
      ·
        refine ⟨12740573562796011710983915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67949725668245395791914213 12740573562796011710983915)
        ·
          refine ⟨19110860344194017566475873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12740573562796011710983915 19110860344194017566475873)
          ·
            refine ⟨14333145258145513174856905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19110860344194017566475873 14333145258145513174856905)
            ·
              refine ⟨10749858943609134881142679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14333145258145513174856905 10749858943609134881142679)
              ·
                refine ⟨16124788415413702321714019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10749858943609134881142679 16124788415413702321714019)
                ·
                  refine ⟨24187182623120553482571029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16124788415413702321714019 24187182623120553482571029)
                  ·
                    refine ⟨1133774185458775944495517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24187182623120553482571029 1133774185458775944495517)
                    ·
                      rfl

theorem cell22_3312026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_3312026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312026 prefixEnd_3312026 := by exact prefixLift 3312026
  have htrace : WordTrace (prefixWord ++ tailWord_3312026) baseStart_3312026 baseEnd_3312026 := by
    simpa [prefixWord, tailWord_3312026, baseEnd_3312026] using wordTrace_append hprefix tailTrace_3312026
  have hstable : (prefixWord ++ tailWord_3312026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312026).length < 2 ^ (prefixWord ++ tailWord_3312026).sum := by decide
  have hdescent : baseEnd_3312026 < baseStart_3312026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312090 : List Nat := [3, 1, 1, 2, 3, 1, 2, 5, 1, 3]
def baseStart_3312090 : Nat := 118140960795 + 3312090 * 2 ^ 59
def prefixEnd_3312090 : Nat := 4983230072969 + 3 ^ 40 * 3312090 * 2
def baseEnd_3312090 : Nat := 1133796093966701110895321

theorem tailTrace_3312090 : CollatzResearch.WordTrace tailWord_3312090 prefixEnd_3312090 1133796093966701110895321 := by
  unfold tailWord_3312090
  simp only [CollatzResearch.WordTrace]
  refine ⟨30200461642717766195655431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80534564380580709855081149 30200461642717766195655431)
  ·
    refine ⟨45300692464076649293483147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30200461642717766195655431 45300692464076649293483147)
    ·
      refine ⟨67951038696114973940224721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45300692464076649293483147 67951038696114973940224721)
      ·
        refine ⟨50963279022086230455168541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67951038696114973940224721 50963279022086230455168541)
        ·
          refine ⟨19111229633282336420688203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50963279022086230455168541 19111229633282336420688203)
          ·
            refine ⟨28666844449923504631032305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19111229633282336420688203 28666844449923504631032305)
            ·
              refine ⟨21500133337442628473274229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28666844449923504631032305 21500133337442628473274229)
              ·
                refine ⟨2015637500385246419369459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21500133337442628473274229 2015637500385246419369459)
                ·
                  refine ⟨3023456250577869629054189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015637500385246419369459 3023456250577869629054189)
                  ·
                    refine ⟨1133796093966701110895321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023456250577869629054189 1133796093966701110895321)
                    ·
                      rfl

theorem cell22_3312090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_3312090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312090 prefixEnd_3312090 := by exact prefixLift 3312090
  have htrace : WordTrace (prefixWord ++ tailWord_3312090) baseStart_3312090 baseEnd_3312090 := by
    simpa [prefixWord, tailWord_3312090, baseEnd_3312090] using wordTrace_append hprefix tailTrace_3312090
  have hstable : (prefixWord ++ tailWord_3312090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312090).length < 2 ^ (prefixWord ++ tailWord_3312090).sum := by decide
  have hdescent : baseEnd_3312090 < baseStart_3312090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312103 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 5]
def baseStart_3312103 : Nat := 118140960795 + 3312103 * 2 ^ 59
def prefixEnd_3312103 : Nat := 4983230072969 + 3 ^ 40 * 3312103 * 2
def baseEnd_3312103 : Nat := 377933514710791136773427

theorem tailTrace_3312103 : CollatzResearch.WordTrace tailWord_3312103 prefixEnd_3312103 377933514710791136773427 := by
  unfold tailWord_3312103
  simp only [CollatzResearch.WordTrace]
  refine ⟨120802320719823968002844963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80534880479882645335229975 120802320719823968002844963)
  ·
    refine ⟨181203481079735952004267445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120802320719823968002844963 181203481079735952004267445)
    ·
      refine ⟨16987826351225245500400073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181203481079735952004267445 16987826351225245500400073)
      ·
        refine ⟨12740869763418934125300055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16987826351225245500400073 12740869763418934125300055)
        ·
          refine ⟨19111304645128401187950083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12740869763418934125300055 19111304645128401187950083)
          ·
            refine ⟨28666956967692601781925125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19111304645128401187950083 28666956967692601781925125)
            ·
              refine ⟨5375054431442362834110961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28666956967692601781925125 5375054431442362834110961)
              ·
                refine ⟨4031290823581772125583221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5375054431442362834110961 4031290823581772125583221)
                ·
                  refine ⟨377933514710791136773427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4031290823581772125583221 377933514710791136773427)
                  ·
                    rfl

theorem cell22_3312103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 5].length) (baseStart_3312103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312103 prefixEnd_3312103 := by exact prefixLift 3312103
  have htrace : WordTrace (prefixWord ++ tailWord_3312103) baseStart_3312103 baseEnd_3312103 := by
    simpa [prefixWord, tailWord_3312103, baseEnd_3312103] using wordTrace_append hprefix tailTrace_3312103
  have hstable : (prefixWord ++ tailWord_3312103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312103).length < 2 ^ (prefixWord ++ tailWord_3312103).sum := by decide
  have hdescent : baseEnd_3312103 < baseStart_3312103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312118 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_3312118 : Nat := 118140960795 + 3312118 * 2 ^ 59
def prefixEnd_3312118 : Nat := 4983230072969 + 3 ^ 40 * 3312118 * 2
def baseEnd_3312118 : Nat := 1133805678938918371195235

theorem tailTrace_3312118 : CollatzResearch.WordTrace tailWord_3312118 prefixEnd_3312118 1133805678938918371195235 := by
  unfold tailWord_3312118
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550179238423101597790063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80535245209846417043094005 7550179238423101597790063)
  ·
    refine ⟨11325268857634652396685095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7550179238423101597790063 11325268857634652396685095)
    ·
      refine ⟨16987903286451978595027643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11325268857634652396685095 16987903286451978595027643)
      ·
        refine ⟨25481854929677967892541465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16987903286451978595027643 25481854929677967892541465)
        ·
          refine ⟨19111391197258475919406099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25481854929677967892541465 19111391197258475919406099)
          ·
            refine ⟨28667086795887713879109149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19111391197258475919406099 28667086795887713879109149)
            ·
              refine ⟨10750157548457892704665931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28667086795887713879109149 10750157548457892704665931)
              ·
                refine ⟨16125236322686839056998897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10750157548457892704665931 16125236322686839056998897)
                ·
                  refine ⟨12093927242015129292749173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16125236322686839056998897 12093927242015129292749173)
                  ·
                    refine ⟨1133805678938918371195235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12093927242015129292749173 1133805678938918371195235)
                    ·
                      rfl

theorem cell22_3312118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_3312118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312118 prefixEnd_3312118 := by exact prefixLift 3312118
  have htrace : WordTrace (prefixWord ++ tailWord_3312118) baseStart_3312118 baseEnd_3312118 := by
    simpa [prefixWord, tailWord_3312118, baseEnd_3312118] using wordTrace_append hprefix tailTrace_3312118
  have hstable : (prefixWord ++ tailWord_3312118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312118).length < 2 ^ (prefixWord ++ tailWord_3312118).sum := by decide
  have hdescent : baseEnd_3312118 < baseStart_3312118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312131 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 6]
def baseStart_3312131 : Nat := 118140960795 + 3312131 * 2 ^ 59
def prefixEnd_3312131 : Nat := 4983230072969 + 3 ^ 40 * 3312131 * 2
def baseEnd_3312131 : Nat := 377936709701530223540065

theorem tailTrace_3312131 : CollatzResearch.WordTrace tailWord_3312131 prefixEnd_3312131 377936709701530223540065 := by
  unfold tailWord_3312131
  simp only [CollatzResearch.WordTrace]
  refine ⟨120803341963722528784864247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80535561309148352523242831 120803341963722528784864247)
  ·
    refine ⟨181205012945583793177296371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120803341963722528784864247 181205012945583793177296371)
    ·
      refine ⟨271807519418375689765944557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181205012945583793177296371 271807519418375689765944557)
      ·
        refine ⟨101927819781890883662229209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271807519418375689765944557 101927819781890883662229209)
        ·
          refine ⟨76445864836418162746671907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101927819781890883662229209 76445864836418162746671907)
          ·
            refine ⟨114668797254627244120007861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76445864836418162746671907 114668797254627244120007861)
            ·
              refine ⟨10750199742621304136250737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114668797254627244120007861 10750199742621304136250737)
              ·
                refine ⟨8062649806965978102188053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10750199742621304136250737 8062649806965978102188053)
                ·
                  refine ⟨377936709701530223540065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8062649806965978102188053 377936709701530223540065)
                  ·
                    rfl

theorem cell22_3312131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 6].length) (baseStart_3312131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312131 prefixEnd_3312131 := by exact prefixLift 3312131
  have htrace : WordTrace (prefixWord ++ tailWord_3312131) baseStart_3312131 baseEnd_3312131 := by
    simpa [prefixWord, tailWord_3312131, baseEnd_3312131] using wordTrace_append hprefix tailTrace_3312131
  have hstable : (prefixWord ++ tailWord_3312131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312131).length < 2 ^ (prefixWord ++ tailWord_3312131).sum := by decide
  have hdescent : baseEnd_3312131 < baseStart_3312131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312141 : List Nat := [1, 7, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3312141 : Nat := 118140960795 + 3312141 * 2 ^ 59
def prefixEnd_3312141 : Nat := 4983230072969 + 3 ^ 40 * 3312141 * 2
def baseEnd_3312141 : Nat := 1133813552308953977870165

theorem tailTrace_3312141 : CollatzResearch.WordTrace tailWord_3312141 prefixEnd_3312141 1133813552308953977870165 := by
  unfold tailWord_3312141
  simp only [CollatzResearch.WordTrace]
  refine ⟨120803706693686300492728277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80535804462457533661818851 120803706693686300492728277)
  ·
    refine ⟨2831336875633272667798319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 120803706693686300492728277 2831336875633272667798319)
    ·
      refine ⟨4247005313449909001697479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2831336875633272667798319 4247005313449909001697479)
      ·
        refine ⟨6370507970174863502546219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4247005313449909001697479 6370507970174863502546219)
        ·
          refine ⟨9555761955262295253819329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6370507970174863502546219 9555761955262295253819329)
          ·
            refine ⟨7166821466446721440364497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9555761955262295253819329 7166821466446721440364497)
            ·
              refine ⟨5375116099835041080273373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7166821466446721440364497 5375116099835041080273373)
              ·
                refine ⟨2015668537438140405102515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5375116099835041080273373 2015668537438140405102515)
                ·
                  refine ⟨3023502806157210607653773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015668537438140405102515 3023502806157210607653773)
                  ·
                    refine ⟨1133813552308953977870165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023502806157210607653773 1133813552308953977870165)
                    ·
                      rfl

theorem cell22_3312141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3312141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312141 prefixEnd_3312141 := by exact prefixLift 3312141
  have htrace : WordTrace (prefixWord ++ tailWord_3312141) baseStart_3312141 baseEnd_3312141 := by
    simpa [prefixWord, tailWord_3312141, baseEnd_3312141] using wordTrace_append hprefix tailTrace_3312141
  have hstable : (prefixWord ++ tailWord_3312141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312141).length < 2 ^ (prefixWord ++ tailWord_3312141).sum := by decide
  have hdescent : baseEnd_3312141 < baseStart_3312141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312191 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 2, 7]
def baseStart_3312191 : Nat := 118140960795 + 3312191 * 2 ^ 59
def prefixEnd_3312191 : Nat := 4983230072969 + 3 ^ 40 * 3312191 * 2
def baseEnd_3312191 : Nat := 1133830668330770514120011

theorem tailTrace_3312191 : CollatzResearch.WordTrace tailWord_3312191 prefixEnd_3312191 1133830668330770514120011 := by
  unfold tailWord_3312191
  simp only [CollatzResearch.WordTrace]
  refine ⟨120805530343505159032048427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80537020229003439354698951 120805530343505159032048427)
  ·
    refine ⟨181208295515257738548072641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120805530343505159032048427 181208295515257738548072641)
    ·
      refine ⟨135906221636443303911054481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181208295515257738548072641 135906221636443303911054481)
      ·
        refine ⟨101929666227332477933290861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135906221636443303911054481 101929666227332477933290861)
        ·
          refine ⟨38223624835249679224984073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101929666227332477933290861 38223624835249679224984073)
          ·
            refine ⟨28667718626437259418738055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38223624835249679224984073 28667718626437259418738055)
            ·
              refine ⟨43001577939655889128107083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28667718626437259418738055 43001577939655889128107083)
              ·
                refine ⟨64502366909483833692160625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43001577939655889128107083 64502366909483833692160625)
                ·
                  refine ⟨48376775182112875269120469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64502366909483833692160625 48376775182112875269120469)
                  ·
                    refine ⟨1133830668330770514120011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48376775182112875269120469 1133830668330770514120011)
                    ·
                      rfl

theorem cell22_3312191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_3312191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312191 prefixEnd_3312191 := by exact prefixLift 3312191
  have htrace : WordTrace (prefixWord ++ tailWord_3312191) baseStart_3312191 baseEnd_3312191 := by
    simpa [prefixWord, tailWord_3312191, baseEnd_3312191] using wordTrace_append hprefix tailTrace_3312191
  have hstable : (prefixWord ++ tailWord_3312191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312191).length < 2 ^ (prefixWord ++ tailWord_3312191).sum := by decide
  have hdescent : baseEnd_3312191 < baseStart_3312191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312193 : List Nat := [1, 2, 5, 1, 1, 3, 1, 8]
def baseStart_3312193 : Nat := 118140960795 + 3312193 * 2 ^ 59
def prefixEnd_3312193 : Nat := 4983230072969 + 3 ^ 40 * 3312193 * 2
def baseEnd_3312193 : Nat := 125981261441293686174445

theorem tailTrace_3312193 : CollatzResearch.WordTrace tailWord_3312193 prefixEnd_3312193 125981261441293686174445 := by
  unfold tailWord_3312193
  simp only [CollatzResearch.WordTrace]
  refine ⟨120805603289497913373621233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80537068859665275582414155 120805603289497913373621233)
  ·
    refine ⟨90604202467123435030215925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120805603289497913373621233 90604202467123435030215925)
    ·
      refine ⟨8494143981292822034082743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90604202467123435030215925 8494143981292822034082743)
      ·
        refine ⟨12741215971939233051124115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8494143981292822034082743 12741215971939233051124115)
        ·
          refine ⟨19111823957908849576686173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12741215971939233051124115 19111823957908849576686173)
          ·
            refine ⟨7166933984215818591257315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19111823957908849576686173 7166933984215818591257315)
            ·
              refine ⟨10750400976323727886885973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7166933984215818591257315 10750400976323727886885973)
              ·
                refine ⟨125981261441293686174445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10750400976323727886885973 125981261441293686174445)
                ·
                  rfl

theorem cell22_3312193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 8].length) (baseStart_3312193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312193 prefixEnd_3312193 := by exact prefixLift 3312193
  have htrace : WordTrace (prefixWord ++ tailWord_3312193) baseStart_3312193 baseEnd_3312193 := by
    simpa [prefixWord, tailWord_3312193, baseEnd_3312193] using wordTrace_append hprefix tailTrace_3312193
  have hstable : (prefixWord ++ tailWord_3312193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312193).length < 2 ^ (prefixWord ++ tailWord_3312193).sum := by decide
  have hdescent : baseEnd_3312193 < baseStart_3312193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312225 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 3, 3]
def baseStart_3312225 : Nat := 118140960795 + 3312225 * 2 ^ 59
def prefixEnd_3312225 : Nat := 4983230072969 + 3 ^ 40 * 3312225 * 2
def baseEnd_3312225 : Nat := 1133842307225605758769907

theorem tailTrace_3312225 : CollatzResearch.WordTrace tailWord_3312225 prefixEnd_3312225 1133842307225605758769907 := by
  unfold tailWord_3312225
  simp only [CollatzResearch.WordTrace]
  refine ⟨120806770425381982838786129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80537846950254655225857419 120806770425381982838786129)
  ·
    refine ⟨90605077819036487129089597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120806770425381982838786129 90605077819036487129089597)
    ·
      refine ⟨33976904182138682673408599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90605077819036487129089597 33976904182138682673408599)
      ·
        refine ⟨50965356273208024010112899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33976904182138682673408599 50965356273208024010112899)
        ·
          refine ⟨76448034409812036015169349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50965356273208024010112899 76448034409812036015169349)
          ·
            refine ⟨14334006451839756752844253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76448034409812036015169349 14334006451839756752844253)
            ·
              refine ⟨5375252419439908782316595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14334006451839756752844253 5375252419439908782316595)
              ·
                refine ⟨8062878629159863173474893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5375252419439908782316595 8062878629159863173474893)
                ·
                  refine ⟨3023579485934948690053085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8062878629159863173474893 3023579485934948690053085)
                  ·
                    refine ⟨1133842307225605758769907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023579485934948690053085 1133842307225605758769907)
                    ·
                      rfl

theorem cell22_3312225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_3312225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312225 prefixEnd_3312225 := by exact prefixLift 3312225
  have htrace : WordTrace (prefixWord ++ tailWord_3312225) baseStart_3312225 baseEnd_3312225 := by
    simpa [prefixWord, tailWord_3312225, baseEnd_3312225] using wordTrace_append hprefix tailTrace_3312225
  have hstable : (prefixWord ++ tailWord_3312225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312225).length < 2 ^ (prefixWord ++ tailWord_3312225).sum := by decide
  have hdescent : baseEnd_3312225 < baseStart_3312225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312276 : List Nat := [2, 4, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_3312276 : Nat := 118140960795 + 3312276 * 2 ^ 59
def prefixEnd_3312276 : Nat := 4983230072969 + 3 ^ 40 * 3312276 * 2
def baseEnd_3312276 : Nat := 1133859765567858625744751

theorem tailTrace_3312276 : CollatzResearch.WordTrace tailWord_3312276 prefixEnd_3312276 1133859765567858625744751 := by
  unfold tailWord_3312276
  simp only [CollatzResearch.WordTrace]
  refine ⟨60404315274098609274446341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80539087032131479032595121 60404315274098609274446341)
  ·
    refine ⟨11325809113893489238958689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60404315274098609274446341 11325809113893489238958689)
    ·
      refine ⟨8494356835420116929219017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11325809113893489238958689 8494356835420116929219017)
      ·
        refine ⟨6370767626565087696914263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8494356835420116929219017 6370767626565087696914263)
        ·
          refine ⟨9556151439847631545371395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6370767626565087696914263 9556151439847631545371395)
          ·
            refine ⟨14334227159771447318057093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9556151439847631545371395 14334227159771447318057093)
            ·
              refine ⟨2687667592457146372135705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14334227159771447318057093 2687667592457146372135705)
              ·
                refine ⟨2015750694342859779101779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2687667592457146372135705 2015750694342859779101779)
                ·
                  refine ⟨3023626041514289668652669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015750694342859779101779 3023626041514289668652669)
                  ·
                    refine ⟨1133859765567858625744751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023626041514289668652669 1133859765567858625744751)
                    ·
                      rfl

theorem cell22_3312276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_3312276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312276 prefixEnd_3312276 := by exact prefixLift 3312276
  have htrace : WordTrace (prefixWord ++ tailWord_3312276) baseStart_3312276 baseEnd_3312276 := by
    simpa [prefixWord, tailWord_3312276, baseEnd_3312276] using wordTrace_append hprefix tailTrace_3312276
  have hstable : (prefixWord ++ tailWord_3312276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312276).length < 2 ^ (prefixWord ++ tailWord_3312276).sum := by decide
  have hdescent : baseEnd_3312276 < baseStart_3312276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312302 : List Nat := [4, 1, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_3312302 : Nat := 118140960795 + 3312302 * 2 ^ 59
def prefixEnd_3312302 : Nat := 4983230072969 + 3 ^ 40 * 3312302 * 2
def baseEnd_3312302 : Nat := 1133868665899203224594671

theorem tailTrace_3312302 : CollatzResearch.WordTrace tailWord_3312302 prefixEnd_3312302 1133868665899203224594671 := by
  unfold tailWord_3312302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15101197355762878123667395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80539719230735349992892773 15101197355762878123667395)
  ·
    refine ⟨22651796033644317185501093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15101197355762878123667395 22651796033644317185501093)
    ·
      refine ⟨4247211756308309472281455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22651796033644317185501093 4247211756308309472281455)
      ·
        refine ⟨6370817634462464208422183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4247211756308309472281455 6370817634462464208422183)
        ·
          refine ⟨9556226451693696312633275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6370817634462464208422183 9556226451693696312633275)
          ·
            refine ⟨14334339677540544468949913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9556226451693696312633275 14334339677540544468949913)
            ·
              refine ⟨10750754758155408351712435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14334339677540544468949913 10750754758155408351712435)
              ·
                refine ⟨16126132137233112527568653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10750754758155408351712435 16126132137233112527568653)
                ·
                  refine ⟨6047299551462417197838245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16126132137233112527568653 6047299551462417197838245)
                  ·
                    refine ⟨1133868665899203224594671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6047299551462417197838245 1133868665899203224594671)
                    ·
                      rfl

theorem cell22_3312302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_3312302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312302 prefixEnd_3312302 := by exact prefixLift 3312302
  have htrace : WordTrace (prefixWord ++ tailWord_3312302) baseStart_3312302 baseEnd_3312302 := by
    simpa [prefixWord, tailWord_3312302, baseEnd_3312302] using wordTrace_append hprefix tailTrace_3312302
  have hstable : (prefixWord ++ tailWord_3312302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312302).length < 2 ^ (prefixWord ++ tailWord_3312302).sum := by decide
  have hdescent : baseEnd_3312302 < baseStart_3312302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312317 : List Nat := [1, 4, 1, 2, 1, 4, 2, 3, 4]
def baseStart_3312317 : Nat := 118140960795 + 3312317 * 2 ^ 59
def prefixEnd_3312317 : Nat := 4983230072969 + 3 ^ 40 * 3312317 * 2
def baseEnd_3312317 : Nat := 377957933568582728489875

theorem tailTrace_3312317 : CollatzResearch.WordTrace tailWord_3312317 prefixEnd_3312317 377957933568582728489875 := by
  unfold tailWord_3312317
  simp only [CollatzResearch.WordTrace]
  refine ⟨120810125941048682551135205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80540083960699121700756803 120810125941048682551135205)
  ·
    refine ⟨22651898613946627978337851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120810125941048682551135205 22651898613946627978337851)
    ·
      refine ⟨33977847920919941967506777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22651898613946627978337851 33977847920919941967506777)
      ·
        refine ⟨25483385940689956475630083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33977847920919941967506777 25483385940689956475630083)
        ·
          refine ⟨38225078911034934713445125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25483385940689956475630083 38225078911034934713445125)
          ·
            refine ⟨7167202295819050258770961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38225078911034934713445125 7167202295819050258770961)
            ·
              refine ⟨5375401721864287694078221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7167202295819050258770961 5375401721864287694078221)
              ·
                refine ⟨2015775645699107885279333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5375401721864287694078221 2015775645699107885279333)
                ·
                  refine ⟨377957933568582728489875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2015775645699107885279333 377957933568582728489875)
                  ·
                    rfl

theorem cell22_3312317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_3312317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312317 prefixEnd_3312317 := by exact prefixLift 3312317
  have htrace : WordTrace (prefixWord ++ tailWord_3312317) baseStart_3312317 baseEnd_3312317 := by
    simpa [prefixWord, tailWord_3312317, baseEnd_3312317] using wordTrace_append hprefix tailTrace_3312317
  have hstable : (prefixWord ++ tailWord_3312317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312317).length < 2 ^ (prefixWord ++ tailWord_3312317).sum := by decide
  have hdescent : baseEnd_3312317 < baseStart_3312317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312328 : List Nat := [2, 1, 3, 1, 2, 4, 9]
def baseStart_3312328 : Nat := 118140960795 + 3312328 * 2 ^ 59
def prefixEnd_3312328 : Nat := 4983230072969 + 3 ^ 40 * 3312328 * 2
def baseEnd_3312328 : Nat := 41995465415946215683133

theorem tailTrace_3312328 : CollatzResearch.WordTrace tailWord_3312328 prefixEnd_3312328 41995465415946215683133 := by
  unfold tailWord_3312328
  simp only [CollatzResearch.WordTrace]
  refine ⟨60405263572004415714892819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80540351429339220953190425 60405263572004415714892819)
  ·
    refine ⟨90607895358006623572339229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60405263572004415714892819 90607895358006623572339229)
    ·
      refine ⟨33977960759252483839627211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90607895358006623572339229 33977960759252483839627211)
      ·
        refine ⟨50966941138878725759440817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33977960759252483839627211 50966941138878725759440817)
        ·
          refine ⟨38225205854159044319580613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50966941138878725759440817 38225205854159044319580613)
          ·
            refine ⟨7167226097654820809921365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38225205854159044319580613 7167226097654820809921365)
            ·
              refine ⟨41995465415946215683133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7167226097654820809921365 41995465415946215683133)
              ·
                rfl

theorem cell22_3312328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 9].length) (baseStart_3312328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312328 prefixEnd_3312328 := by exact prefixLift 3312328
  have htrace : WordTrace (prefixWord ++ tailWord_3312328) baseStart_3312328 baseEnd_3312328 := by
    simpa [prefixWord, tailWord_3312328, baseEnd_3312328] using wordTrace_append hprefix tailTrace_3312328
  have hstable : (prefixWord ++ tailWord_3312328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312328).length < 2 ^ (prefixWord ++ tailWord_3312328).sum := by decide
  have hdescent : baseEnd_3312328 < baseStart_3312328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312332 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 4, 3]
def baseStart_3312332 : Nat := 118140960795 + 3312332 * 2 ^ 59
def prefixEnd_3312332 : Nat := 4983230072969 + 3 ^ 40 * 3312332 * 2
def baseEnd_3312332 : Nat := 1133878935512293146344579

theorem tailTrace_3312332 : CollatzResearch.WordTrace tailWord_3312332 prefixEnd_3312332 1133878935512293146344579 := by
  unfold tailWord_3312332
  simp only [CollatzResearch.WordTrace]
  refine ⟨60405336517997170056465625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80540448690662893408620833 60405336517997170056465625)
  ·
    refine ⟨45304002388497877542349219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60405336517997170056465625 45304002388497877542349219)
    ·
      refine ⟨67956003582746816313523829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45304002388497877542349219 67956003582746816313523829)
      ·
        refine ⟨6370875335882514029392859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67956003582746816313523829 6370875335882514029392859)
        ·
          refine ⟨9556313003823771044089289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6370875335882514029392859 9556313003823771044089289)
          ·
            refine ⟨7167234752867828283066967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9556313003823771044089289 7167234752867828283066967)
            ·
              refine ⟨10750852129301742424600451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167234752867828283066967 10750852129301742424600451)
              ·
                refine ⟨16126278193952613636900677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10750852129301742424600451 16126278193952613636900677)
                ·
                  refine ⟨3023677161366115056918877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16126278193952613636900677 3023677161366115056918877)
                  ·
                    refine ⟨1133878935512293146344579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023677161366115056918877 1133878935512293146344579)
                    ·
                      rfl

theorem cell22_3312332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_3312332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312332 prefixEnd_3312332 := by exact prefixLift 3312332
  have htrace : WordTrace (prefixWord ++ tailWord_3312332) baseStart_3312332 baseEnd_3312332 := by
    simpa [prefixWord, tailWord_3312332, baseEnd_3312332] using wordTrace_append hprefix tailTrace_3312332
  have hstable : (prefixWord ++ tailWord_3312332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312332).length < 2 ^ (prefixWord ++ tailWord_3312332).sum := by decide
  have hdescent : baseEnd_3312332 < baseStart_3312332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312407 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 5]
def baseStart_3312407 : Nat := 118140960795 + 3312407 * 2 ^ 59
def prefixEnd_3312407 : Nat := 4983230072969 + 3 ^ 40 * 3312407 * 2
def baseEnd_3312407 : Nat := 377968203181672650239783

theorem tailTrace_3312407 : CollatzResearch.WordTrace tailWord_3312407 prefixEnd_3312407 377968203181672650239783 := by
  unfold tailWord_3312407
  simp only [CollatzResearch.WordTrace]
  refine ⟨120813408510722627921911475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80542272340481751947940983 120813408510722627921911475)
  ·
    refine ⟨181220112766083941882867213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120813408510722627921911475 181220112766083941882867213)
    ·
      refine ⟨67957542287281478206075205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181220112766083941882867213 67957542287281478206075205)
      ·
        refine ⟨12742039178865277163639101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67957542287281478206075205 12742039178865277163639101)
        ·
          refine ⟨4778264692074478936364663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12742039178865277163639101 4778264692074478936364663)
          ·
            refine ⟨7167397038111718404546995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778264692074478936364663 7167397038111718404546995)
            ·
              refine ⟨10751095557167577606820493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167397038111718404546995 10751095557167577606820493)
              ·
                refine ⟨4031660833937841602557685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10751095557167577606820493 4031660833937841602557685)
                ·
                  refine ⟨377968203181672650239783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4031660833937841602557685 377968203181672650239783)
                  ·
                    rfl

theorem cell22_3312407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 5].length) (baseStart_3312407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312407 prefixEnd_3312407 := by exact prefixLift 3312407
  have htrace : WordTrace (prefixWord ++ tailWord_3312407) baseStart_3312407 baseEnd_3312407 := by
    simpa [prefixWord, tailWord_3312407, baseEnd_3312407] using wordTrace_append hprefix tailTrace_3312407
  have hstable : (prefixWord ++ tailWord_3312407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312407).length < 2 ^ (prefixWord ++ tailWord_3312407).sum := by decide
  have hdescent : baseEnd_3312407 < baseStart_3312407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312445 : List Nat := [1, 4, 1, 4, 3, 1, 2, 2, 1, 3]
def baseStart_3312445 : Nat := 118140960795 + 3312445 * 2 ^ 59
def prefixEnd_3312445 : Nat := 4983230072969 + 3 ^ 40 * 3312445 * 2
def baseEnd_3312445 : Nat := 1133917617721598518269233

theorem tailTrace_3312445 : CollatzResearch.WordTrace tailWord_3312445 prefixEnd_3312445 1133917617721598518269233 := by
  unfold tailWord_3312445
  simp only [CollatzResearch.WordTrace]
  refine ⟨120814794484584960411794789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80543196323056640274529859 120814794484584960411794789)
  ·
    refine ⟨22652773965859680077211523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120814794484584960411794789 22652773965859680077211523)
    ·
      refine ⟨33979160948789520115817285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22652773965859680077211523 33979160948789520115817285)
      ·
        refine ⟨6371092677898035021715741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33979160948789520115817285 6371092677898035021715741)
        ·
          refine ⟨2389159754211763133143403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6371092677898035021715741 2389159754211763133143403)
          ·
            refine ⟨3583739631317644699715105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389159754211763133143403 3583739631317644699715105)
            ·
              refine ⟨2687804723488233524786329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3583739631317644699715105 2687804723488233524786329)
              ·
                refine ⟨2015853542616175143589747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2687804723488233524786329 2015853542616175143589747)
                ·
                  refine ⟨3023780313924262715384621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015853542616175143589747 3023780313924262715384621)
                  ·
                    refine ⟨1133917617721598518269233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023780313924262715384621 1133917617721598518269233)
                    ·
                      rfl

theorem cell22_3312445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_3312445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312445 prefixEnd_3312445 := by exact prefixLift 3312445
  have htrace : WordTrace (prefixWord ++ tailWord_3312445) baseStart_3312445 baseEnd_3312445 := by
    simpa [prefixWord, tailWord_3312445, baseEnd_3312445] using wordTrace_append hprefix tailTrace_3312445
  have hstable : (prefixWord ++ tailWord_3312445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312445).length < 2 ^ (prefixWord ++ tailWord_3312445).sum := by decide
  have hdescent : baseEnd_3312445 < baseStart_3312445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312501 : List Nat := [1, 3, 4, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3312501 : Nat := 118140960795 + 3312501 * 2 ^ 59
def prefixEnd_3312501 : Nat := 4983230072969 + 3 ^ 40 * 3312501 * 2
def baseEnd_3312501 : Nat := 1133936787666033038869061

theorem tailTrace_3312501 : CollatzResearch.WordTrace tailWord_3312501 prefixEnd_3312501 1133936787666033038869061 := by
  unfold tailWord_3312501
  simp only [CollatzResearch.WordTrace]
  refine ⟨120816836972382081975833357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80544557981588054650555571 120816836972382081975833357)
  ·
    refine ⟨45306313864643280740937509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120816836972382081975833357 45306313864643280740937509)
    ·
      refine ⟨8494933849620615138925783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45306313864643280740937509 8494933849620615138925783)
      ·
        refine ⟨12742400774430922708388675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8494933849620615138925783 12742400774430922708388675)
        ·
          refine ⟨19113601161646384062583013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12742400774430922708388675 19113601161646384062583013)
          ·
            refine ⟨3583800217808697011734315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19113601161646384062583013 3583800217808697011734315)
            ·
              refine ⟨5375700326713045517601473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3583800217808697011734315 5375700326713045517601473)
              ·
                refine ⟨4031775245034784138201105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5375700326713045517601473 4031775245034784138201105)
                ·
                  refine ⟨3023831433776088103650829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4031775245034784138201105 3023831433776088103650829)
                  ·
                    refine ⟨1133936787666033038869061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3023831433776088103650829 1133936787666033038869061)
                    ·
                      rfl

theorem cell22_3312501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3312501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312501 prefixEnd_3312501 := by exact prefixLift 3312501
  have htrace : WordTrace (prefixWord ++ tailWord_3312501) baseStart_3312501 baseEnd_3312501 := by
    simpa [prefixWord, tailWord_3312501, baseEnd_3312501] using wordTrace_append hprefix tailTrace_3312501
  have hstable : (prefixWord ++ tailWord_3312501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312501).length < 2 ^ (prefixWord ++ tailWord_3312501).sum := by decide
  have hdescent : baseEnd_3312501 < baseStart_3312501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312602 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_3312602 : Nat := 118140960795 + 3312602 * 2 ^ 59
def prefixEnd_3312602 : Nat := 4983230072969 + 3 ^ 40 * 3312602 * 2
def baseEnd_3312602 : Nat := 1133971362030102442093751

theorem tailTrace_3312602 : CollatzResearch.WordTrace tailWord_3312602 prefixEnd_3312602 1133971362030102442093751 := by
  unfold tailWord_3312602
  simp only [CollatzResearch.WordTrace]
  refine ⟨30205130186254044056315015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80547013830010784150173373 30205130186254044056315015)
  ·
    refine ⟨45307695279381066084472523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30205130186254044056315015 45307695279381066084472523)
    ·
      refine ⟨67961542919071599126708785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45307695279381066084472523 67961542919071599126708785)
      ·
        refine ⟨50971157189303699345031589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67961542919071599126708785 50971157189303699345031589)
        ·
          refine ⟨9557091972994443627193423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50971157189303699345031589 9557091972994443627193423)
          ·
            refine ⟨14335637959491665440790135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9557091972994443627193423 14335637959491665440790135)
            ·
              refine ⟨21503456939237498161185203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14335637959491665440790135 21503456939237498161185203)
              ·
                refine ⟨32255185408856247241777805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21503456939237498161185203 32255185408856247241777805)
                ·
                  refine ⟨12095694528321092715666677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32255185408856247241777805 12095694528321092715666677)
                  ·
                    refine ⟨1133971362030102442093751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12095694528321092715666677 1133971362030102442093751)
                    ·
                      rfl

theorem cell22_3312602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_3312602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312602 prefixEnd_3312602 := by exact prefixLift 3312602
  have htrace : WordTrace (prefixWord ++ tailWord_3312602) baseStart_3312602 baseEnd_3312602 := by
    simpa [prefixWord, tailWord_3312602, baseEnd_3312602] using wordTrace_append hprefix tailTrace_3312602
  have hstable : (prefixWord ++ tailWord_3312602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312602).length < 2 ^ (prefixWord ++ tailWord_3312602).sum := by decide
  have hdescent : baseEnd_3312602 < baseStart_3312602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312677 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 7]
def baseStart_3312677 : Nat := 118140960795 + 3312677 * 2 ^ 59
def prefixEnd_3312677 : Nat := 4983230072969 + 3 ^ 40 * 3312677 * 2
def baseEnd_3312677 : Nat := 377999012020942415489507

theorem tailTrace_3312677 : CollatzResearch.WordTrace tailWord_3312677 prefixEnd_3312677 377999012020942415489507 := by
  unfold tailWord_3312677
  simp only [CollatzResearch.WordTrace]
  refine ⟨120823256219744464034240285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80548837479829642689493523 120823256219744464034240285)
  ·
    refine ⟨45308721082404174012840107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120823256219744464034240285 45308721082404174012840107)
    ·
      refine ⟨67963081623606261019260161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45308721082404174012840107 67963081623606261019260161)
      ·
        refine ⟨50972311217704695764445121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67963081623606261019260161 50972311217704695764445121)
        ·
          refine ⟨38229233413278521823333841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50972311217704695764445121 38229233413278521823333841)
          ·
            refine ⟨28671925059958891367500381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38229233413278521823333841 28671925059958891367500381)
            ·
              refine ⟨10751971897484584262812643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28671925059958891367500381 10751971897484584262812643)
              ·
                refine ⟨16127957846226876394218965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10751971897484584262812643 16127957846226876394218965)
                ·
                  refine ⟨377999012020942415489507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16127957846226876394218965 377999012020942415489507)
                  ·
                    rfl

theorem cell22_3312677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_3312677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312677 prefixEnd_3312677 := by exact prefixLift 3312677
  have htrace : WordTrace (prefixWord ++ tailWord_3312677) baseStart_3312677 baseEnd_3312677 := by
    simpa [prefixWord, tailWord_3312677, baseEnd_3312677] using wordTrace_append hprefix tailTrace_3312677
  have hstable : (prefixWord ++ tailWord_3312677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312677).length < 2 ^ (prefixWord ++ tailWord_3312677).sum := by decide
  have hdescent : baseEnd_3312677 < baseStart_3312677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312754 : List Nat := [3, 2, 1, 2, 2, 1, 2, 3, 1, 5]
def baseStart_3312754 : Nat := 118140960795 + 3312754 * 2 ^ 59
def prefixEnd_3312754 : Nat := 4983230072969 + 3 ^ 40 * 3312754 * 2
def baseEnd_3312754 : Nat := 1134023394736424712293285

theorem tailTrace_3312754 : CollatzResearch.WordTrace tailWord_3312754 prefixEnd_3312754 1134023394736424712293285 := by
  unfold tailWord_3312754
  simp only [CollatzResearch.WordTrace]
  refine ⟨30206516160116376546198329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80550709760310337456528877 30206516160116376546198329)
  ·
    refine ⟨22654887120087282409648747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30206516160116376546198329 22654887120087282409648747)
    ·
      refine ⟨33982330680130923614473121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22654887120087282409648747 33982330680130923614473121)
      ·
        refine ⟨25486748010098192710854841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33982330680130923614473121 25486748010098192710854841)
        ·
          refine ⟨19115061007573644533141131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25486748010098192710854841 19115061007573644533141131)
          ·
            refine ⟨28672591511360466799711697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19115061007573644533141131 28672591511360466799711697)
            ·
              refine ⟨21504443633520350099783773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28672591511360466799711697 21504443633520350099783773)
              ·
                refine ⟨8064166362570131287418915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21504443633520350099783773 8064166362570131287418915)
                ·
                  refine ⟨12096249543855196931128373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8064166362570131287418915 12096249543855196931128373)
                  ·
                    refine ⟨1134023394736424712293285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12096249543855196931128373 1134023394736424712293285)
                    ·
                      rfl

theorem cell22_3312754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_3312754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312754 prefixEnd_3312754 := by exact prefixLift 3312754
  have htrace : WordTrace (prefixWord ++ tailWord_3312754) baseStart_3312754 baseEnd_3312754 := by
    simpa [prefixWord, tailWord_3312754, baseEnd_3312754] using wordTrace_append hprefix tailTrace_3312754
  have hstable : (prefixWord ++ tailWord_3312754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312754).length < 2 ^ (prefixWord ++ tailWord_3312754).sum := by decide
  have hdescent : baseEnd_3312754 < baseStart_3312754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312786 : List Nat := [3, 2, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3312786 : Nat := 118140960795 + 3312786 * 2 ^ 59
def prefixEnd_3312786 : Nat := 4983230072969 + 3 ^ 40 * 3312786 * 2
def baseEnd_3312786 : Nat := 1134034348990387295493187

theorem tailTrace_3312786 : CollatzResearch.WordTrace tailWord_3312786 prefixEnd_3312786 1134034348990387295493187 := by
  unfold tailWord_3312786
  simp only [CollatzResearch.WordTrace]
  refine ⟨30206807944087393912489553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80551487850899717099972141 30206807944087393912489553)
  ·
    refine ⟨22655105958065545434367165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30206807944087393912489553 22655105958065545434367165)
    ·
      refine ⟨8495664734274579537887687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22655105958065545434367165 8495664734274579537887687)
      ·
        refine ⟨12743497101411869306831531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8495664734274579537887687 12743497101411869306831531)
        ·
          refine ⟨19115245652117803960247297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12743497101411869306831531 19115245652117803960247297)
          ·
            refine ⟨14336434239088352970185473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19115245652117803960247297 14336434239088352970185473)
            ·
              refine ⟨10752325679316264727639105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14336434239088352970185473 10752325679316264727639105)
              ·
                refine ⟨8064244259487198545729329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10752325679316264727639105 8064244259487198545729329)
                ·
                  refine ⟨6048183194615398909296997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8064244259487198545729329 6048183194615398909296997)
                  ·
                    refine ⟨1134034348990387295493187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048183194615398909296997 1134034348990387295493187)
                    ·
                      rfl

theorem cell22_3312786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3312786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312786 prefixEnd_3312786 := by exact prefixLift 3312786
  have htrace : WordTrace (prefixWord ++ tailWord_3312786) baseStart_3312786 baseEnd_3312786 := by
    simpa [prefixWord, tailWord_3312786, baseEnd_3312786] using wordTrace_append hprefix tailTrace_3312786
  have hstable : (prefixWord ++ tailWord_3312786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312786).length < 2 ^ (prefixWord ++ tailWord_3312786).sum := by decide
  have hdescent : baseEnd_3312786 < baseStart_3312786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312846 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_3312846 : Nat := 118140960795 + 3312846 * 2 ^ 59
def prefixEnd_3312846 : Nat := 4983230072969 + 3 ^ 40 * 3312846 * 2
def baseEnd_3312846 : Nat := 378018296072189046331001

theorem tailTrace_3312846 : CollatzResearch.WordTrace tailWord_3312846 prefixEnd_3312846 378018296072189046331001 := by
  unfold tailWord_3312846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15103677519516525737142799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80552946770754803931428261 15103677519516525737142799)
  ·
    refine ⟨22655516279274788605714199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15103677519516525737142799 22655516279274788605714199)
    ·
      refine ⟨33983274418912182908571299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22655516279274788605714199 33983274418912182908571299)
      ·
        refine ⟨50974911628368274362856949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33983274418912182908571299 50974911628368274362856949)
        ·
          refine ⟨4778897965159525721517839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50974911628368274362856949 4778897965159525721517839)
          ·
            refine ⟨7168346947739288582276759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778897965159525721517839 7168346947739288582276759)
            ·
              refine ⟨10752520421608932873415139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7168346947739288582276759 10752520421608932873415139)
              ·
                refine ⟨16128780632413399310122709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10752520421608932873415139 16128780632413399310122709)
                ·
                  refine ⟨378018296072189046331001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16128780632413399310122709 378018296072189046331001)
                  ·
                    rfl

theorem cell22_3312846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_3312846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312846 prefixEnd_3312846 := by exact prefixLift 3312846
  have htrace : WordTrace (prefixWord ++ tailWord_3312846) baseStart_3312846 baseEnd_3312846 := by
    simpa [prefixWord, tailWord_3312846, baseEnd_3312846] using wordTrace_append hprefix tailTrace_3312846
  have hstable : (prefixWord ++ tailWord_3312846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312846).length < 2 ^ (prefixWord ++ tailWord_3312846).sum := by decide
  have hdescent : baseEnd_3312846 < baseStart_3312846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312876 : List Nat := [2, 2, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_3312876 : Nat := 118140960795 + 3312876 * 2 ^ 59
def prefixEnd_3312876 : Nat := 4983230072969 + 3 ^ 40 * 3312876 * 2
def baseEnd_3312876 : Nat := 1134065157829657060742911

theorem tailTrace_3312876 : CollatzResearch.WordTrace tailWord_3312876 prefixEnd_3312876 1134065157829657060742911 := by
  unfold tailWord_3312876
  simp only [CollatzResearch.WordTrace]
  refine ⟨60415257173011760510367241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80553676230682347347156321 60415257173011760510367241)
  ·
    refine ⟨45311442879758820382775431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60415257173011760510367241 45311442879758820382775431)
    ·
      refine ⟨67967164319638230574163147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45311442879758820382775431 67967164319638230574163147)
      ·
        refine ⟨101950746479457345861244721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67967164319638230574163147 101950746479457345861244721)
        ·
          refine ⟨76463059859593009395933541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101950746479457345861244721 76463059859593009395933541)
          ·
            refine ⟨14336823723673689261737539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76463059859593009395933541 14336823723673689261737539)
            ·
              refine ⟨21505235585510533892606309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14336823723673689261737539 21505235585510533892606309)
              ·
                refine ⟨4032231672283225104863683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21505235585510533892606309 4032231672283225104863683)
                ·
                  refine ⟨6048347508424837657295525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032231672283225104863683 6048347508424837657295525)
                  ·
                    refine ⟨1134065157829657060742911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048347508424837657295525 1134065157829657060742911)
                    ·
                      rfl

theorem cell22_3312876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_3312876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312876 prefixEnd_3312876 := by exact prefixLift 3312876
  have htrace : WordTrace (prefixWord ++ tailWord_3312876) baseStart_3312876 baseEnd_3312876 := by
    simpa [prefixWord, tailWord_3312876, baseEnd_3312876] using wordTrace_append hprefix tailTrace_3312876
  have hstable : (prefixWord ++ tailWord_3312876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312876).length < 2 ^ (prefixWord ++ tailWord_3312876).sum := by decide
  have hdescent : baseEnd_3312876 < baseStart_3312876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312889 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 3, 5]
def baseStart_3312889 : Nat := 118140960795 + 3312889 * 2 ^ 59
def prefixEnd_3312889 : Nat := 4983230072969 + 3 ^ 40 * 3312889 * 2
def baseEnd_3312889 : Nat := 1134069607995329360167871

theorem tailTrace_3312889 : CollatzResearch.WordTrace tailWord_3312889 prefixEnd_3312889 1134069607995329360167871 := by
  unfold tailWord_3312889
  simp only [CollatzResearch.WordTrace]
  refine ⟨120830988494976424240957721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80553992329984282827305147 120830988494976424240957721)
  ·
    refine ⟨90623241371232318180718291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120830988494976424240957721 90623241371232318180718291)
    ·
      refine ⟨135934862056848477271077437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90623241371232318180718291 135934862056848477271077437)
      ·
        refine ⟨50975573271318178976654039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135934862056848477271077437 50975573271318178976654039)
        ·
          refine ⟨76463359906977268464981059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50975573271318178976654039 76463359906977268464981059)
          ·
            refine ⟨114695039860465902697471589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76463359906977268464981059 114695039860465902697471589)
            ·
              refine ⟨21505319973837356755775923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114695039860465902697471589 21505319973837356755775923)
              ·
                refine ⟨32257979960756035133663885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21505319973837356755775923 32257979960756035133663885)
                ·
                  refine ⟨12096742485283513175123957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32257979960756035133663885 12096742485283513175123957)
                  ·
                    refine ⟨1134069607995329360167871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12096742485283513175123957 1134069607995329360167871)
                    ·
                      rfl

theorem cell22_3312889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_3312889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312889 prefixEnd_3312889 := by exact prefixLift 3312889
  have htrace : WordTrace (prefixWord ++ tailWord_3312889) baseStart_3312889 baseEnd_3312889 := by
    simpa [prefixWord, tailWord_3312889, baseEnd_3312889] using wordTrace_append hprefix tailTrace_3312889
  have hstable : (prefixWord ++ tailWord_3312889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312889).length < 2 ^ (prefixWord ++ tailWord_3312889).sum := by decide
  have hdescent : baseEnd_3312889 < baseStart_3312889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312914 : List Nat := [3, 2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_3312914 : Nat := 118140960795 + 3312914 * 2 ^ 59
def prefixEnd_3312914 : Nat := 4983230072969 + 3 ^ 40 * 3312914 * 2
def baseEnd_3312914 : Nat := 378026055335412542764265

theorem tailTrace_3312914 : CollatzResearch.WordTrace tailWord_3312914 prefixEnd_3312914 378026055335412542764265 := by
  unfold tailWord_3312914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30207975079971463377654449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80554600213257235673745197 30207975079971463377654449)
  ·
    refine ⟨22655981309978597533240837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30207975079971463377654449 22655981309978597533240837)
    ·
      refine ⟨4247996495620987037482657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22655981309978597533240837 4247996495620987037482657)
      ·
        refine ⟨3185997371715740278111993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4247996495620987037482657 3185997371715740278111993)
        ·
          refine ⟨2389498028786805208583995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3185997371715740278111993 2389498028786805208583995)
          ·
            refine ⟨3584247043180207812875993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389498028786805208583995 3584247043180207812875993)
            ·
              refine ⟨2688185282385155859656995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3584247043180207812875993 2688185282385155859656995)
              ·
                refine ⟨4032277923577733789485493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688185282385155859656995 4032277923577733789485493)
                ·
                  refine ⟨378026055335412542764265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4032277923577733789485493 378026055335412542764265)
                  ·
                    rfl

theorem cell22_3312914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_3312914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312914 prefixEnd_3312914 := by exact prefixLift 3312914
  have htrace : WordTrace (prefixWord ++ tailWord_3312914) baseStart_3312914 baseEnd_3312914 := by
    simpa [prefixWord, tailWord_3312914, baseEnd_3312914] using wordTrace_append hprefix tailTrace_3312914
  have hstable : (prefixWord ++ tailWord_3312914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312914).length < 2 ^ (prefixWord ++ tailWord_3312914).sum := by decide
  have hdescent : baseEnd_3312914 < baseStart_3312914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312936 : List Nat := [2, 1, 5, 1, 2, 1, 2, 8]
def baseStart_3312936 : Nat := 118140960795 + 3312936 * 2 ^ 59
def prefixEnd_3312936 : Nat := 4983230072969 + 3 ^ 40 * 3312936 * 2
def baseEnd_3312936 : Nat := 126009521895092989360303

theorem tailTrace_3312936 : CollatzResearch.WordTrace tailWord_3312936 prefixEnd_3312936 126009521895092989360303 := by
  unfold tailWord_3312936
  simp only [CollatzResearch.WordTrace]
  refine ⟨60416351362903075633959331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80555135150537434178612441 60416351362903075633959331)
  ·
    refine ⟨90624527044354613450938997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60416351362903075633959331 90624527044354613450938997)
    ·
      refine ⟨8496049410408245011025531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90624527044354613450938997 8496049410408245011025531)
      ·
        refine ⟨12744074115612367516538297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8496049410408245011025531 12744074115612367516538297)
        ·
          refine ⟨9558055586709275637403723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12744074115612367516538297 9558055586709275637403723)
          ·
            refine ⟨14337083380063913456105585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9558055586709275637403723 14337083380063913456105585)
            ·
              refine ⟨10752812535047935092079189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14337083380063913456105585 10752812535047935092079189)
              ·
                refine ⟨126009521895092989360303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10752812535047935092079189 126009521895092989360303)
                ·
                  rfl

theorem cell22_3312936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 8].length) (baseStart_3312936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312936 prefixEnd_3312936 := by exact prefixLift 3312936
  have htrace : WordTrace (prefixWord ++ tailWord_3312936) baseStart_3312936 baseEnd_3312936 := by
    simpa [prefixWord, tailWord_3312936, baseEnd_3312936] using wordTrace_append hprefix tailTrace_3312936
  have hstable : (prefixWord ++ tailWord_3312936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312936).length < 2 ^ (prefixWord ++ tailWord_3312936).sum := by decide
  have hdescent : baseEnd_3312936 < baseStart_3312936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312938 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_3312938 : Nat := 118140960795 + 3312938 * 2 ^ 59
def prefixEnd_3312938 : Nat := 4983230072969 + 3 ^ 40 * 3312938 * 2
def baseEnd_3312938 : Nat := 1134086381696709565692721

theorem tailTrace_3312938 : CollatzResearch.WordTrace tailWord_3312938 prefixEnd_3312938 1134086381696709565692721 := by
  unfold tailWord_3312938
  simp only [CollatzResearch.WordTrace]
  refine ⟨30208193917949726402372867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80555183781199270406327645 30208193917949726402372867)
  ·
    refine ⟨45312290876924589603559301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30208193917949726402372867 45312290876924589603559301)
    ·
      refine ⟨8496054539423360550667369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45312290876924589603559301 8496054539423360550667369)
      ·
        refine ⟨6372040904567520413000527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8496054539423360550667369 6372040904567520413000527)
        ·
          refine ⟨9558061356851280619500791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372040904567520413000527 9558061356851280619500791)
          ·
            refine ⟨14337092035276920929251187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9558061356851280619500791 14337092035276920929251187)
            ·
              refine ⟨21505638052915381393876781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14337092035276920929251187 21505638052915381393876781)
              ·
                refine ⟨8064614269843268022703793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21505638052915381393876781 8064614269843268022703793)
                ·
                  refine ⟨6048460702382451017027845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8064614269843268022703793 6048460702382451017027845)
                  ·
                    refine ⟨1134086381696709565692721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048460702382451017027845 1134086381696709565692721)
                    ·
                      rfl

theorem cell22_3312938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_3312938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312938 prefixEnd_3312938 := by exact prefixLift 3312938
  have htrace : WordTrace (prefixWord ++ tailWord_3312938) baseStart_3312938 baseEnd_3312938 := by
    simpa [prefixWord, tailWord_3312938, baseEnd_3312938] using wordTrace_append hprefix tailTrace_3312938
  have hstable : (prefixWord ++ tailWord_3312938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312938).length < 2 ^ (prefixWord ++ tailWord_3312938).sum := by decide
  have hdescent : baseEnd_3312938 < baseStart_3312938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312957 : List Nat := [1, 4, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_3312957 : Nat := 118140960795 + 3312957 * 2 ^ 59
def prefixEnd_3312957 : Nat := 4983230072969 + 3 ^ 40 * 3312957 * 2
def baseEnd_3312957 : Nat := 1134092885784999849467663

theorem tailTrace_3312957 : CollatzResearch.WordTrace tailWord_3312957 prefixEnd_3312957 1134092885784999849467663 := by
  unfold tailWord_3312957
  simp only [CollatzResearch.WordTrace]
  refine ⟨120833468658730071854433125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80555645772486714569622083 120833468658730071854433125)
  ·
    refine ⟨22656275373511888472706211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120833468658730071854433125 22656275373511888472706211)
    ·
      refine ⟨33984413060267832709059317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22656275373511888472706211 33984413060267832709059317)
      ·
        refine ⟨3186038724400109316474311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33984413060267832709059317 3186038724400109316474311)
        ·
          refine ⟨4779058086600163974711467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186038724400109316474311 4779058086600163974711467)
          ·
            refine ⟨7168587129900245962067201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4779058086600163974711467 7168587129900245962067201)
            ·
              refine ⟨5376440347425184471550401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7168587129900245962067201 5376440347425184471550401)
              ·
                refine ⟨4032330260568888353662801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5376440347425184471550401 4032330260568888353662801)
                ·
                  refine ⟨3024247695426666265247101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4032330260568888353662801 3024247695426666265247101)
                  ·
                    refine ⟨1134092885784999849467663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3024247695426666265247101 1134092885784999849467663)
                    ·
                      rfl

theorem cell22_3312957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_3312957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312957 prefixEnd_3312957 := by exact prefixLift 3312957
  have htrace : WordTrace (prefixWord ++ tailWord_3312957) baseStart_3312957 baseEnd_3312957 := by
    simpa [prefixWord, tailWord_3312957, baseEnd_3312957] using wordTrace_append hprefix tailTrace_3312957
  have hstable : (prefixWord ++ tailWord_3312957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312957).length < 2 ^ (prefixWord ++ tailWord_3312957).sum := by decide
  have hdescent : baseEnd_3312957 < baseStart_3312957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3312989 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3312989 : Nat := 118140960795 + 3312989 * 2 ^ 59
def prefixEnd_3312989 : Nat := 4983230072969 + 3 ^ 40 * 3312989 * 2
def baseEnd_3312989 : Nat := 1134103840038962432667565

theorem tailTrace_3312989 : CollatzResearch.WordTrace tailWord_3312989 prefixEnd_3312989 1134103840038962432667565 := by
  unfold tailWord_3312989
  simp only [CollatzResearch.WordTrace]
  refine ⟨120834635794614141319598021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80556423863076094213065347 120834635794614141319598021)
  ·
    refine ⟨22656494211490151497424629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120834635794614141319598021 22656494211490151497424629)
    ·
      refine ⟨2124046332327201702883559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22656494211490151497424629 2124046332327201702883559)
      ·
        refine ⟨3186069498490802554325339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2124046332327201702883559 3186069498490802554325339)
        ·
          refine ⟨4779104247736203831488009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186069498490802554325339 4779104247736203831488009)
          ·
            refine ⟨3584328185802152873616007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4779104247736203831488009 3584328185802152873616007)
            ·
              refine ⟨5376492278703229310424011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584328185802152873616007 5376492278703229310424011)
              ·
                refine ⟨8064738418054843965636017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376492278703229310424011 8064738418054843965636017)
                ·
                  refine ⟨6048553813541132974227013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8064738418054843965636017 6048553813541132974227013)
                  ·
                    refine ⟨1134103840038962432667565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048553813541132974227013 1134103840038962432667565)
                    ·
                      rfl

theorem cell22_3312989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3312989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3312989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3312989 prefixEnd_3312989 := by exact prefixLift 3312989
  have htrace : WordTrace (prefixWord ++ tailWord_3312989) baseStart_3312989 baseEnd_3312989 := by
    simpa [prefixWord, tailWord_3312989, baseEnd_3312989] using wordTrace_append hprefix tailTrace_3312989
  have hstable : (prefixWord ++ tailWord_3312989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3312989).length < 2 ^ (prefixWord ++ tailWord_3312989).sum := by decide
  have hdescent : baseEnd_3312989 < baseStart_3312989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3312989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313056 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_3313056 : Nat := 118140960795 + 3313056 * 2 ^ 59
def prefixEnd_3313056 : Nat := 4983230072969 + 3 ^ 40 * 3313056 * 2
def baseEnd_3313056 : Nat := 1134126775508196591242359

theorem tailTrace_3313056 : CollatzResearch.WordTrace tailWord_3313056 prefixEnd_3313056 1134126775508196591242359 := by
  unfold tailWord_3313056
  simp only [CollatzResearch.WordTrace]
  refine ⟨60418539742685705881143511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80558052990247607841524681 60418539742685705881143511)
  ·
    refine ⟨90627809614028558821715267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60418539742685705881143511 90627809614028558821715267)
    ·
      refine ⟨135941714421042838232572901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90627809614028558821715267 135941714421042838232572901)
      ·
        refine ⟨25489071453945532168607419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135941714421042838232572901 25489071453945532168607419)
        ·
          refine ⟨38233607180918298252911129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25489071453945532168607419 38233607180918298252911129)
          ·
            refine ⟨28675205385688723689683347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38233607180918298252911129 28675205385688723689683347)
            ·
              refine ⟨43012808078533085534525021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28675205385688723689683347 43012808078533085534525021)
              ·
                refine ⟨16129803029449907075446883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43012808078533085534525021 16129803029449907075446883)
                ·
                  refine ⟨24194704544174860613170325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16129803029449907075446883 24194704544174860613170325)
                  ·
                    refine ⟨1134126775508196591242359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24194704544174860613170325 1134126775508196591242359)
                    ·
                      rfl

theorem cell22_3313056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_3313056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313056 prefixEnd_3313056 := by exact prefixLift 3313056
  have htrace : WordTrace (prefixWord ++ tailWord_3313056) baseStart_3313056 baseEnd_3313056 := by
    simpa [prefixWord, tailWord_3313056, baseEnd_3313056] using wordTrace_append hprefix tailTrace_3313056
  have hstable : (prefixWord ++ tailWord_3313056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313056).length < 2 ^ (prefixWord ++ tailWord_3313056).sum := by decide
  have hdescent : baseEnd_3313056 < baseStart_3313056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313073 : List Nat := [1, 2, 2, 4, 1, 1, 3, 2, 2, 4]
def baseStart_3313073 : Nat := 118140960795 + 3313073 * 2 ^ 59
def prefixEnd_3313073 : Nat := 4983230072969 + 3 ^ 40 * 3313073 * 2
def baseEnd_3313073 : Nat := 1134132594955614213567307

theorem tailTrace_3313073 : CollatzResearch.WordTrace tailWord_3313073 prefixEnd_3313073 1134132594955614213567307 := by
  unfold tailWord_3313073
  simp only [CollatzResearch.WordTrace]
  refine ⟨120837699526309823665655873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80558466350873215777103915 120837699526309823665655873)
  ·
    refine ⟨90628274644732367749241905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120837699526309823665655873 90628274644732367749241905)
    ·
      refine ⟨67971205983549275811931429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90628274644732367749241905 67971205983549275811931429)
      ·
        refine ⟨12744601121915489214737143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67971205983549275811931429 12744601121915489214737143)
        ·
          refine ⟨19116901682873233822105715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12744601121915489214737143 19116901682873233822105715)
          ·
            refine ⟨28675352524309850733158573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19116901682873233822105715 28675352524309850733158573)
            ·
              refine ⟨10753257196616194024934465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28675352524309850733158573 10753257196616194024934465)
              ·
                refine ⟨8064942897462145518700849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10753257196616194024934465 8064942897462145518700849)
                ·
                  refine ⟨6048707173096609139025637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8064942897462145518700849 6048707173096609139025637)
                  ·
                    refine ⟨1134132594955614213567307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048707173096609139025637 1134132594955614213567307)
                    ·
                      rfl

theorem cell22_3313073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 4].length) (baseStart_3313073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313073 prefixEnd_3313073 := by exact prefixLift 3313073
  have htrace : WordTrace (prefixWord ++ tailWord_3313073) baseStart_3313073 baseEnd_3313073 := by
    simpa [prefixWord, tailWord_3313073, baseEnd_3313073] using wordTrace_append hprefix tailTrace_3313073
  have hstable : (prefixWord ++ tailWord_3313073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313073).length < 2 ^ (prefixWord ++ tailWord_3313073).sum := by decide
  have hdescent : baseEnd_3313073 < baseStart_3313073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313077 : List Nat := [1, 3, 3, 2, 2, 2, 3, 2, 4]
def baseStart_3313077 : Nat := 118140960795 + 3313077 * 2 ^ 59
def prefixEnd_3313077 : Nat := 4983230072969 + 3 ^ 40 * 3313077 * 2
def baseEnd_3313077 : Nat := 378044654745786512155765

theorem tailTrace_3313077 : CollatzResearch.WordTrace tailWord_3313077 prefixEnd_3313077 378044654745786512155765 := by
  unfold tailWord_3313077
  simp only [CollatzResearch.WordTrace]
  refine ⟨120837845418295332348801485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80558563612196888232534323 120837845418295332348801485)
  ·
    refine ⟨45314192031860749630800557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120837845418295332348801485 45314192031860749630800557)
    ·
      refine ⟨16992822011947781111550209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45314192031860749630800557 16992822011947781111550209)
      ·
        refine ⟨12744616508960835833662657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16992822011947781111550209 12744616508960835833662657)
        ·
          refine ⟨9558462381720626875246993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12744616508960835833662657 9558462381720626875246993)
          ·
            refine ⟨7168846786290470156435245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9558462381720626875246993 7168846786290470156435245)
            ·
              refine ⟨2688317544858926308663217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7168846786290470156435245 2688317544858926308663217)
              ·
                refine ⟨2016238158644194731497413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2688317544858926308663217 2016238158644194731497413)
                ·
                  refine ⟨378044654745786512155765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2016238158644194731497413 378044654745786512155765)
                  ·
                    rfl

theorem cell22_3313077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_3313077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313077 prefixEnd_3313077 := by exact prefixLift 3313077
  have htrace : WordTrace (prefixWord ++ tailWord_3313077) baseStart_3313077 baseEnd_3313077 := by
    simpa [prefixWord, tailWord_3313077, baseEnd_3313077] using wordTrace_append hprefix tailTrace_3313077
  have hstable : (prefixWord ++ tailWord_3313077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313077).length < 2 ^ (prefixWord ++ tailWord_3313077).sum := by decide
  have hdescent : baseEnd_3313077 < baseStart_3313077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313092 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_3313092 : Nat := 118140960795 + 3313092 * 2 ^ 59
def prefixEnd_3313092 : Nat := 4983230072969 + 3 ^ 40 * 3313092 * 2
def baseEnd_3313092 : Nat := 1134139099043904497342249

theorem tailTrace_3313092 : CollatzResearch.WordTrace tailWord_3313092 prefixEnd_3313092 1134139099043904497342249 := by
  unfold tailWord_3313092
  simp only [CollatzResearch.WordTrace]
  refine ⟨60419196256620494955298765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80558928342160659940398353 60419196256620494955298765)
  ·
    refine ⟨22657198596232685608237037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60419196256620494955298765 22657198596232685608237037)
    ·
      refine ⟨8496449473587257103088889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22657198596232685608237037 8496449473587257103088889)
      ·
        refine ⟨6372337105190442827316667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8496449473587257103088889 6372337105190442827316667)
        ·
          refine ⟨9558505657785664240975001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372337105190442827316667 9558505657785664240975001)
          ·
            refine ⟨7168879243339248180731251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9558505657785664240975001 7168879243339248180731251)
            ·
              refine ⟨10753318865008872271096877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7168879243339248180731251 10753318865008872271096877)
              ·
                refine ⟨4032494574378327101661329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10753318865008872271096877 4032494574378327101661329)
                ·
                  refine ⟨3024370930783745326245997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4032494574378327101661329 3024370930783745326245997)
                  ·
                    refine ⟨1134139099043904497342249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3024370930783745326245997 1134139099043904497342249)
                    ·
                      rfl

theorem cell22_3313092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_3313092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313092 prefixEnd_3313092 := by exact prefixLift 3313092
  have htrace : WordTrace (prefixWord ++ tailWord_3313092) baseStart_3313092 baseEnd_3313092 := by
    simpa [prefixWord, tailWord_3313092, baseEnd_3313092] using wordTrace_append hprefix tailTrace_3313092
  have hstable : (prefixWord ++ tailWord_3313092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313092).length < 2 ^ (prefixWord ++ tailWord_3313092).sum := by decide
  have hdescent : baseEnd_3313092 < baseStart_3313092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313103 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 3, 3]
def baseStart_3313103 : Nat := 118140960795 + 3313103 * 2 ^ 59
def prefixEnd_3313103 : Nat := 4983230072969 + 3 ^ 40 * 3313103 * 2
def baseEnd_3313103 : Nat := 1134142864568704135317215

theorem tailTrace_3313103 : CollatzResearch.WordTrace tailWord_3313103 prefixEnd_3313103 1134142864568704135317215 := by
  unfold tailWord_3313103
  simp only [CollatzResearch.WordTrace]
  refine ⟨120838793716201138789247963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80559195810800759192831975 120838793716201138789247963)
  ·
    refine ⟨181258190574301708183871945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120838793716201138789247963 181258190574301708183871945)
    ·
      refine ⟨135943642930726281137903959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181258190574301708183871945 135943642930726281137903959)
      ·
        refine ⟨203915464396089421706855939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135943642930726281137903959 203915464396089421706855939)
        ·
          refine ⟨305873196594134132560283909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203915464396089421706855939 305873196594134132560283909)
          ·
            refine ⟨57351224361400149855053233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305873196594134132560283909 57351224361400149855053233)
            ·
              refine ⟨43013418271050112391289925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57351224361400149855053233 43013418271050112391289925)
              ·
                refine ⟨8065015925821896073366861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43013418271050112391289925 8065015925821896073366861)
                ·
                  refine ⟨3024380972183211027512573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8065015925821896073366861 3024380972183211027512573)
                  ·
                    refine ⟨1134142864568704135317215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3024380972183211027512573 1134142864568704135317215)
                    ·
                      rfl

theorem cell22_3313103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 3].length) (baseStart_3313103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313103 prefixEnd_3313103 := by exact prefixLift 3313103
  have htrace : WordTrace (prefixWord ++ tailWord_3313103) baseStart_3313103 baseEnd_3313103 := by
    simpa [prefixWord, tailWord_3313103, baseEnd_3313103] using wordTrace_append hprefix tailTrace_3313103
  have hstable : (prefixWord ++ tailWord_3313103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313103).length < 2 ^ (prefixWord ++ tailWord_3313103).sum := by decide
  have hdescent : baseEnd_3313103 < baseStart_3313103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313137 : List Nat := [1, 2, 2, 2, 3, 3, 1, 4, 1, 3]
def baseStart_3313137 : Nat := 118140960795 + 3313137 * 2 ^ 59
def prefixEnd_3313137 : Nat := 4983230072969 + 3 ^ 40 * 3313137 * 2
def baseEnd_3313137 : Nat := 1134154503463539379967111

theorem tailTrace_3313137 : CollatzResearch.WordTrace tailWord_3313137 prefixEnd_3313137 1134154503463539379967111 := by
  unfold tailWord_3313137
  simp only [CollatzResearch.WordTrace]
  refine ⟨120840033798077962595985665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80560022532051975063990443 120840033798077962595985665)
  ·
    refine ⟨90630025348558471946989249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120840033798077962595985665 90630025348558471946989249)
    ·
      refine ⟨67972519011418853960241937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90630025348558471946989249 67972519011418853960241937)
      ·
        refine ⟨50979389258564140470181453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67972519011418853960241937 50979389258564140470181453)
        ·
          refine ⟨19117270971961552676318045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50979389258564140470181453 19117270971961552676318045)
          ·
            refine ⟨7168976614485582253619267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19117270971961552676318045 7168976614485582253619267)
            ·
              refine ⟨10753464921728373380428901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7168976614485582253619267 10753464921728373380428901)
              ·
                refine ⟨2016274672824070008830419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10753464921728373380428901 2016274672824070008830419)
                ·
                  refine ⟨3024412009236105013245629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016274672824070008830419 3024412009236105013245629)
                  ·
                    refine ⟨1134154503463539379967111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3024412009236105013245629 1134154503463539379967111)
                    ·
                      rfl

theorem cell22_3313137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 4, 1, 3].length) (baseStart_3313137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313137 prefixEnd_3313137 := by exact prefixLift 3313137
  have htrace : WordTrace (prefixWord ++ tailWord_3313137) baseStart_3313137 baseEnd_3313137 := by
    simpa [prefixWord, tailWord_3313137, baseEnd_3313137] using wordTrace_append hprefix tailTrace_3313137
  have hstable : (prefixWord ++ tailWord_3313137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313137).length < 2 ^ (prefixWord ++ tailWord_3313137).sum := by decide
  have hdescent : baseEnd_3313137 < baseStart_3313137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313158 : List Nat := [6, 2, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3313158 : Nat := 118140960795 + 3313158 * 2 ^ 59
def prefixEnd_3313158 : Nat := 4983230072969 + 3 ^ 40 * 3313158 * 2
def baseEnd_3313158 : Nat := 1134161692192702325192047

theorem tailTrace_3313158 : CollatzResearch.WordTrace tailWord_3313158 prefixEnd_3313158 1134161692192702325192047 := by
  unfold tailWord_3313158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3776274991593808849453129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 80560533154001255455000085 3776274991593808849453129)
  ·
    refine ⟨2832206243695356637089847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3776274991593808849453129 2832206243695356637089847)
    ·
      refine ⟨4248309365543034955634771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2832206243695356637089847 4248309365543034955634771)
      ·
        refine ⟨6372464048314552433452157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248309365543034955634771 6372464048314552433452157)
        ·
          refine ⟨2389674018117957162544559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6372464048314552433452157 2389674018117957162544559)
          ·
            refine ⟨3584511027176935743816839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389674018117957162544559 3584511027176935743816839)
            ·
              refine ⟨5376766540765403615725259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584511027176935743816839 5376766540765403615725259)
              ·
                refine ⟨8065149811148105423587889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5376766540765403615725259 8065149811148105423587889)
                ·
                  refine ⟨6048862358361079067690917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8065149811148105423587889 6048862358361079067690917)
                  ·
                    refine ⟨1134161692192702325192047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048862358361079067690917 1134161692192702325192047)
                    ·
                      rfl

theorem cell22_3313158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3313158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313158 prefixEnd_3313158 := by exact prefixLift 3313158
  have htrace : WordTrace (prefixWord ++ tailWord_3313158) baseStart_3313158 baseEnd_3313158 := by
    simpa [prefixWord, tailWord_3313158, baseEnd_3313158] using wordTrace_append hprefix tailTrace_3313158
  have hstable : (prefixWord ++ tailWord_3313158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313158).length < 2 ^ (prefixWord ++ tailWord_3313158).sum := by decide
  have hdescent : baseEnd_3313158 < baseStart_3313158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313180 : List Nat := [2, 2, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_3313180 : Nat := 118140960795 + 3313180 * 2 ^ 59
def prefixEnd_3313180 : Nat := 4983230072969 + 3 ^ 40 * 3313180 * 2
def baseEnd_3313180 : Nat := 1134169223242301601141979

theorem tailTrace_3313180 : CollatzResearch.WordTrace tailWord_3313180 prefixEnd_3313180 1134169223242301601141979 := by
  unfold tailWord_3313180
  simp only [CollatzResearch.WordTrace]
  refine ⟨60420801068461090469900497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80561068091281453959867329 60420801068461090469900497)
  ·
    refine ⟨45315600801345817852425373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60420801068461090469900497 45315600801345817852425373)
    ·
      refine ⟨16993350300504681694659515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45315600801345817852425373 16993350300504681694659515)
      ·
        refine ⟨25490025450757022541989273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16993350300504681694659515 25490025450757022541989273)
        ·
          refine ⟨19117519088067766906491955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25490025450757022541989273 19117519088067766906491955)
          ·
            refine ⟨28676278632101650359737933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19117519088067766906491955 28676278632101650359737933)
            ·
              refine ⟨10753604487038118884901725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28676278632101650359737933 10753604487038118884901725)
              ·
                refine ⟨4032601682639294581838147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10753604487038118884901725 4032601682639294581838147)
                ·
                  refine ⟨6048902523958941872757221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032601682639294581838147 6048902523958941872757221)
                  ·
                    refine ⟨1134169223242301601141979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6048902523958941872757221 1134169223242301601141979)
                    ·
                      rfl

theorem cell22_3313180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_3313180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313180 prefixEnd_3313180 := by exact prefixLift 3313180
  have htrace : WordTrace (prefixWord ++ tailWord_3313180) baseStart_3313180 baseEnd_3313180 := by
    simpa [prefixWord, tailWord_3313180, baseEnd_3313180] using wordTrace_append hprefix tailTrace_3313180
  have hstable : (prefixWord ++ tailWord_3313180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313180).length < 2 ^ (prefixWord ++ tailWord_3313180).sum := by decide
  have hdescent : baseEnd_3313180 < baseStart_3313180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313208 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_3313208 : Nat := 118140960795 + 3313208 * 2 ^ 59
def prefixEnd_3313208 : Nat := 4983230072969 + 3 ^ 40 * 3313208 * 2
def baseEnd_3313208 : Nat := 1134178808214518861441893

theorem tailTrace_3313208 : CollatzResearch.WordTrace tailWord_3313208 prefixEnd_3313208 1134178808214518861441893 := by
  unfold tailWord_3313208
  simp only [CollatzResearch.WordTrace]
  refine ⟨60421311690410370860910139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80561748920547161147880185 60421311690410370860910139)
  ·
    refine ⟨90631967535615556291365209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60421311690410370860910139 90631967535615556291365209)
    ·
      refine ⟨67973975651711667218523907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90631967535615556291365209 67973975651711667218523907)
      ·
        refine ⟨101960963477567500827785861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67973975651711667218523907 101960963477567500827785861)
        ·
          refine ⟨19117680652043906405209849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101960963477567500827785861 19117680652043906405209849)
          ·
            refine ⟨14338260489032929803907387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19117680652043906405209849 14338260489032929803907387)
            ·
              refine ⟨21507390733549394705861081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14338260489032929803907387 21507390733549394705861081)
              ·
                refine ⟨16130543050162046029395811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21507390733549394705861081 16130543050162046029395811)
                ·
                  refine ⟨24195814575243069044093717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16130543050162046029395811 24195814575243069044093717)
                  ·
                    refine ⟨1134178808214518861441893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24195814575243069044093717 1134178808214518861441893)
                    ·
                      rfl

theorem cell22_3313208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_3313208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313208 prefixEnd_3313208 := by exact prefixLift 3313208
  have htrace : WordTrace (prefixWord ++ tailWord_3313208) baseStart_3313208 baseEnd_3313208 := by
    simpa [prefixWord, tailWord_3313208, baseEnd_3313208] using wordTrace_append hprefix tailTrace_3313208
  have hstable : (prefixWord ++ tailWord_3313208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313208).length < 2 ^ (prefixWord ++ tailWord_3313208).sum := by decide
  have hdescent : baseEnd_3313208 < baseStart_3313208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313261 : List Nat := [1, 5, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_3313261 : Nat := 118140960795 + 3313261 * 2 ^ 59
def prefixEnd_3313261 : Nat := 4983230072969 + 3 ^ 40 * 3313261 * 2
def baseEnd_3313261 : Nat := 1134196951197644389866731

theorem tailTrace_3313261 : CollatzResearch.WordTrace tailWord_3313261 prefixEnd_3313261 1134196951197644389866731 := by
  unfold tailWord_3313261
  simp only [CollatzResearch.WordTrace]
  refine ⟨120844556449628731773499637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80563037633085821182333091 120844556449628731773499637)
  ·
    refine ⟨11329177167152693603765591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120844556449628731773499637 11329177167152693603765591)
    ·
      refine ⟨16993765750729040405648387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11329177167152693603765591 16993765750729040405648387)
      ·
        refine ⟨25490648626093560608472581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16993765750729040405648387 25490648626093560608472581)
        ·
          refine ⟨4779496617392542614088609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25490648626093560608472581 4779496617392542614088609)
          ·
            refine ⟨3584622463044406960566457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4779496617392542614088609 3584622463044406960566457)
            ·
              refine ⟨2688466847283305220424843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3584622463044406960566457 2688466847283305220424843)
              ·
                refine ⟨4032700270924957830637265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688466847283305220424843 4032700270924957830637265)
                ·
                  refine ⟨3024525203193718372977949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4032700270924957830637265 3024525203193718372977949)
                  ·
                    refine ⟨1134196951197644389866731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3024525203193718372977949 1134196951197644389866731)
                    ·
                      rfl

theorem cell22_3313261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_3313261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313261 prefixEnd_3313261 := by exact prefixLift 3313261
  have htrace : WordTrace (prefixWord ++ tailWord_3313261) baseStart_3313261 baseEnd_3313261 := by
    simpa [prefixWord, tailWord_3313261, baseEnd_3313261] using wordTrace_append hprefix tailTrace_3313261
  have hstable : (prefixWord ++ tailWord_3313261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313261).length < 2 ^ (prefixWord ++ tailWord_3313261).sum := by decide
  have hdescent : baseEnd_3313261 < baseStart_3313261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313283 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 4, 5]
def baseStart_3313283 : Nat := 118140960795 + 3313283 * 2 ^ 59
def prefixEnd_3313283 : Nat := 4983230072969 + 3 ^ 40 * 3313283 * 2
def baseEnd_3313283 : Nat := 1134204482247243665816663

theorem tailTrace_3313283 : CollatzResearch.WordTrace tailWord_3313283 prefixEnd_3313283 1134204482247243665816663 := by
  unfold tailWord_3313283
  simp only [CollatzResearch.WordTrace]
  refine ⟨120845358855549029530800503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80563572570366019687200335 120845358855549029530800503)
  ·
    refine ⟨181268038283323544296200755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120845358855549029530800503 181268038283323544296200755)
    ·
      refine ⟨271902057424985316444301133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181268038283323544296200755 271902057424985316444301133)
      ·
        refine ⟨101963271534369493666612925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271902057424985316444301133 101963271534369493666612925)
        ·
          refine ⟨38236226825388560124979847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101963271534369493666612925 38236226825388560124979847)
          ·
            refine ⟨57354340238082840187469771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38236226825388560124979847 57354340238082840187469771)
            ·
              refine ⟨86031510357124260281204657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57354340238082840187469771 86031510357124260281204657)
              ·
                refine ⟨64523632767843195210903493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86031510357124260281204657 64523632767843195210903493)
                ·
                  refine ⟨12098181143970599102044405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64523632767843195210903493 12098181143970599102044405)
                  ·
                    refine ⟨1134204482247243665816663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12098181143970599102044405 1134204482247243665816663)
                    ·
                      rfl

theorem cell22_3313283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_3313283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313283 prefixEnd_3313283 := by exact prefixLift 3313283
  have htrace : WordTrace (prefixWord ++ tailWord_3313283) baseStart_3313283 baseEnd_3313283 := by
    simpa [prefixWord, tailWord_3313283, baseEnd_3313283] using wordTrace_append hprefix tailTrace_3313283
  have hstable : (prefixWord ++ tailWord_3313283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313283).length < 2 ^ (prefixWord ++ tailWord_3313283).sum := by decide
  have hdescent : baseEnd_3313283 < baseStart_3313283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313364 : List Nat := [2, 4, 1, 3, 1, 1, 2, 4, 4]
def baseStart_3313364 : Nat := 118140960795 + 3313364 * 2 ^ 59
def prefixEnd_3313364 : Nat := 4983230072969 + 3 ^ 40 * 3313364 * 2
def baseEnd_3313364 : Nat := 378077403400862151513805

theorem tailTrace_3313364 : CollatzResearch.WordTrace tailWord_3313364 prefixEnd_3313364 378077403400862151513805 := by
  unfold tailWord_3313364
  simp only [CollatzResearch.WordTrace]
  refine ⟨60424156584127790182249573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80565542112170386909666097 60424156584127790182249573)
  ·
    refine ⟨11329529359523960659171795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60424156584127790182249573 11329529359523960659171795)
    ·
      refine ⟨16994294039285940988757693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11329529359523960659171795 16994294039285940988757693)
      ·
        refine ⟨6372860264732227870784135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16994294039285940988757693 6372860264732227870784135)
        ·
          refine ⟨9559290397098341806176203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372860264732227870784135 9559290397098341806176203)
          ·
            refine ⟨14338935595647512709264305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9559290397098341806176203 14338935595647512709264305)
            ·
              refine ⟨10754201696735634531948229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14338935595647512709264305 10754201696735634531948229)
              ·
                refine ⟨2016412818137931474740293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10754201696735634531948229 2016412818137931474740293)
                ·
                  refine ⟨378077403400862151513805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2016412818137931474740293 378077403400862151513805)
                  ·
                    rfl

theorem cell22_3313364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_3313364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313364 prefixEnd_3313364 := by exact prefixLift 3313364
  have htrace : WordTrace (prefixWord ++ tailWord_3313364) baseStart_3313364 baseEnd_3313364 := by
    simpa [prefixWord, tailWord_3313364, baseEnd_3313364] using wordTrace_append hprefix tailTrace_3313364
  have hstable : (prefixWord ++ tailWord_3313364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313364).length < 2 ^ (prefixWord ++ tailWord_3313364).sum := by decide
  have hdescent : baseEnd_3313364 < baseStart_3313364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313379 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 1, 5]
def baseStart_3313379 : Nat := 118140960795 + 3313379 * 2 ^ 59
def prefixEnd_3313379 : Nat := 4983230072969 + 3 ^ 40 * 3313379 * 2
def baseEnd_3313379 : Nat := 1134237345009131415416369

theorem tailTrace_3313379 : CollatzResearch.WordTrace tailWord_3313379 prefixEnd_3313379 1134237345009131415416369 := by
  unfold tailWord_3313379
  simp only [CollatzResearch.WordTrace]
  refine ⟨120848860263201237926295191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80565906842134158617530127 120848860263201237926295191)
  ·
    refine ⟨181273290394801856889442787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120848860263201237926295191 181273290394801856889442787)
    ·
      refine ⟨271909935592202785334164181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181273290394801856889442787 271909935592202785334164181)
      ·
        refine ⟨6372889115442252781269473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 271909935592202785334164181 6372889115442252781269473)
        ·
          refine ⟨4779666836581689585952105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6372889115442252781269473 4779666836581689585952105)
          ·
            refine ⟨3584750127436267189464079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4779666836581689585952105 3584750127436267189464079)
            ·
              refine ⟨5377125191154400784196119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3584750127436267189464079 5377125191154400784196119)
              ·
                refine ⟨8065687786731601176294179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377125191154400784196119 8065687786731601176294179)
                ·
                  refine ⟨12098531680097401764441269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8065687786731601176294179 12098531680097401764441269)
                  ·
                    refine ⟨1134237345009131415416369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12098531680097401764441269 1134237345009131415416369)
                    ·
                      rfl

theorem cell22_3313379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 5].length) (baseStart_3313379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313379 prefixEnd_3313379 := by exact prefixLift 3313379
  have htrace : WordTrace (prefixWord ++ tailWord_3313379) baseStart_3313379 baseEnd_3313379 := by
    simpa [prefixWord, tailWord_3313379, baseEnd_3313379] using wordTrace_append hprefix tailTrace_3313379
  have hstable : (prefixWord ++ tailWord_3313379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313379).length < 2 ^ (prefixWord ++ tailWord_3313379).sum := by decide
  have hdescent : baseEnd_3313379 < baseStart_3313379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313390 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3313390 : Nat := 118140960795 + 3313390 * 2 ^ 59
def prefixEnd_3313390 : Nat := 4983230072969 + 3 ^ 40 * 3313390 * 2
def baseEnd_3313390 : Nat := 1134241110533931053391335

theorem tailTrace_3313390 : CollatzResearch.WordTrace tailWord_3313390 prefixEnd_3313390 1134241110533931053391335 := by
  unfold tailWord_3313390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15106157683270173350618203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80566174310774257869963749 15106157683270173350618203)
  ·
    refine ⟨22659236524905260025927305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15106157683270173350618203 22659236524905260025927305)
    ·
      refine ⟨16994427393678945019445479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22659236524905260025927305 16994427393678945019445479)
      ·
        refine ⟨25491641090518417529168219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16994427393678945019445479 25491641090518417529168219)
        ·
          refine ⟨38237461635777626293752329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25491641090518417529168219 38237461635777626293752329)
          ·
            refine ⟨28678096226833219720314247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38237461635777626293752329 28678096226833219720314247)
            ·
              refine ⟨43017144340249829580471371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28678096226833219720314247 43017144340249829580471371)
              ·
                refine ⟨64525716510374744370707057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43017144340249829580471371 64525716510374744370707057)
                ·
                  refine ⟨48394287382781058278030293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64525716510374744370707057 48394287382781058278030293)
                  ·
                    refine ⟨1134241110533931053391335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48394287382781058278030293 1134241110533931053391335)
                    ·
                      rfl

theorem cell22_3313390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3313390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313390 prefixEnd_3313390 := by exact prefixLift 3313390
  have htrace : WordTrace (prefixWord ++ tailWord_3313390) baseStart_3313390 baseEnd_3313390 := by
    simpa [prefixWord, tailWord_3313390, baseEnd_3313390] using wordTrace_append hprefix tailTrace_3313390
  have hstable : (prefixWord ++ tailWord_3313390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313390).length < 2 ^ (prefixWord ++ tailWord_3313390).sum := by decide
  have hdescent : baseEnd_3313390 < baseStart_3313390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313396 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3313396 : Nat := 118140960795 + 3313396 * 2 ^ 59
def prefixEnd_3313396 : Nat := 4983230072969 + 3 ^ 40 * 3313396 * 2
def baseEnd_3313396 : Nat := 1134243164456549037741317

theorem tailTrace_3313396 : CollatzResearch.WordTrace tailWord_3313396 prefixEnd_3313396 1134243164456549037741317 := by
  unfold tailWord_3313396
  simp only [CollatzResearch.WordTrace]
  refine ⟨60424740152069824914832021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80566320202759766553109361 60424740152069824914832021)
  ·
    refine ⟨2832409694628273042882751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60424740152069824914832021 2832409694628273042882751)
    ·
      refine ⟨4248614541942409564324127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2832409694628273042882751 4248614541942409564324127)
      ·
        refine ⟨6372921812913614346486191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248614541942409564324127 6372921812913614346486191)
        ·
          refine ⟨9559382719370421519729287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372921812913614346486191 9559382719370421519729287)
          ·
            refine ⟨14339074079055632279593931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9559382719370421519729287 14339074079055632279593931)
            ·
              refine ⟨21508611118583448419390897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14339074079055632279593931 21508611118583448419390897)
              ·
                refine ⟨16131458338937586314543173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21508611118583448419390897 16131458338937586314543173)
                ·
                  refine ⟨3024648438550797433976845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16131458338937586314543173 3024648438550797433976845)
                  ·
                    refine ⟨1134243164456549037741317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3024648438550797433976845 1134243164456549037741317)
                    ·
                      rfl

theorem cell22_3313396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3313396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313396 prefixEnd_3313396 := by exact prefixLift 3313396
  have htrace : WordTrace (prefixWord ++ tailWord_3313396) baseStart_3313396 baseEnd_3313396 := by
    simpa [prefixWord, tailWord_3313396, baseEnd_3313396] using wordTrace_append hprefix tailTrace_3313396
  have hstable : (prefixWord ++ tailWord_3313396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313396).length < 2 ^ (prefixWord ++ tailWord_3313396).sum := by decide
  have hdescent : baseEnd_3313396 < baseStart_3313396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313420 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 7]
def baseStart_3313420 : Nat := 118140960795 + 3313420 * 2 ^ 59
def prefixEnd_3313420 : Nat := 4983230072969 + 3 ^ 40 * 3313420 * 2
def baseEnd_3313420 : Nat := 378083793382340325047081

theorem tailTrace_3313420 : CollatzResearch.WordTrace tailWord_3313420 prefixEnd_3313420 378083793382340325047081 := by
  unfold tailWord_3313420
  simp only [CollatzResearch.WordTrace]
  refine ⟨60425177828026350964268857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80566903770701801285691809 60425177828026350964268857)
  ·
    refine ⟨45318883371019763223201643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60425177828026350964268857 45318883371019763223201643)
    ·
      refine ⟨67978325056529644834802465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45318883371019763223201643 67978325056529644834802465)
      ·
        refine ⟨50983743792397233626101849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67978325056529644834802465 50983743792397233626101849)
        ·
          refine ⟨38237807844297925219576387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50983743792397233626101849 38237807844297925219576387)
          ·
            refine ⟨57356711766446887829364581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38237807844297925219576387 57356711766446887829364581)
            ·
              refine ⟨10754383456208791468005859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57356711766446887829364581 10754383456208791468005859)
              ·
                refine ⟨16131575184313187202008789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10754383456208791468005859 16131575184313187202008789)
                ·
                  refine ⟨378083793382340325047081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16131575184313187202008789 378083793382340325047081)
                  ·
                    rfl

theorem cell22_3313420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_3313420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313420 prefixEnd_3313420 := by exact prefixLift 3313420
  have htrace : WordTrace (prefixWord ++ tailWord_3313420) baseStart_3313420 baseEnd_3313420 := by
    simpa [prefixWord, tailWord_3313420, baseEnd_3313420] using wordTrace_append hprefix tailTrace_3313420
  have hstable : (prefixWord ++ tailWord_3313420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313420).length < 2 ^ (prefixWord ++ tailWord_3313420).sum := by decide
  have hdescent : baseEnd_3313420 < baseStart_3313420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313497 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 1, 5]
def baseStart_3313497 : Nat := 118140960795 + 3313497 * 2 ^ 59
def prefixEnd_3313497 : Nat := 4983230072969 + 3 ^ 40 * 3313497 * 2
def baseEnd_3313497 : Nat := 1134277738820618440966007

theorem tailTrace_3313497 : CollatzResearch.WordTrace tailWord_3313497 prefixEnd_3313497 1134277738820618440966007 := by
  unfold tailWord_3313497
  simp only [CollatzResearch.WordTrace]
  refine ⟨120853164076773744079090745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80568776051182496052727163 120853164076773744079090745)
  ·
    refine ⟨90639873057580308059318059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120853164076773744079090745 90639873057580308059318059)
    ·
      refine ⟨135959809586370462088977089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90639873057580308059318059 135959809586370462088977089)
      ·
        refine ⟨101969857189777846566732817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135959809586370462088977089 101969857189777846566732817)
        ·
          refine ⟨76477392892333384925049613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101969857189777846566732817 76477392892333384925049613)
          ·
            refine ⟨28679022334625019346893605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76477392892333384925049613 28679022334625019346893605)
            ·
              refine ⟨5377316687742191127542551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28679022334625019346893605 5377316687742191127542551)
              ·
                refine ⟨8065975031613286691313827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377316687742191127542551 8065975031613286691313827)
                ·
                  refine ⟨12098962547419930036970741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8065975031613286691313827 12098962547419930036970741)
                  ·
                    refine ⟨1134277738820618440966007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12098962547419930036970741 1134277738820618440966007)
                    ·
                      rfl

theorem cell22_3313497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 5].length) (baseStart_3313497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313497 prefixEnd_3313497 := by exact prefixLift 3313497
  have htrace : WordTrace (prefixWord ++ tailWord_3313497) baseStart_3313497 baseEnd_3313497 := by
    simpa [prefixWord, tailWord_3313497, baseEnd_3313497] using wordTrace_append hprefix tailTrace_3313497
  have hstable : (prefixWord ++ tailWord_3313497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313497).length < 2 ^ (prefixWord ++ tailWord_3313497).sum := by decide
  have hdescent : baseEnd_3313497 < baseStart_3313497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313512 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_3313512 : Nat := 118140960795 + 3313512 * 2 ^ 59
def prefixEnd_3313512 : Nat := 4983230072969 + 3 ^ 40 * 3313512 * 2
def baseEnd_3313512 : Nat := 1134282873627163401840961

theorem tailTrace_3313512 : CollatzResearch.WordTrace tailWord_3313512 prefixEnd_3313512 1134282873627163401840961 := by
  unfold tailWord_3313512
  simp only [CollatzResearch.WordTrace]
  refine ⟨60426855585859700820443395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80569140781146267760591193 60426855585859700820443395)
  ·
    refine ⟨90640283378789551230665093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60426855585859700820443395 90640283378789551230665093)
    ·
      refine ⟨16995053133523040855749705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90640283378789551230665093 16995053133523040855749705)
      ·
        refine ⟨12746289850142280641812279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16995053133523040855749705 12746289850142280641812279)
        ·
          refine ⟨19119434775213420962718419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12746289850142280641812279 19119434775213420962718419)
          ·
            refine ⟨28679152162820131444077629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19119434775213420962718419 28679152162820131444077629)
            ·
              refine ⟨10754682061057549291529111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28679152162820131444077629 10754682061057549291529111)
              ·
                refine ⟨16132023091586323937293667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10754682061057549291529111 16132023091586323937293667)
                ·
                  refine ⟨24198034637379485905940501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16132023091586323937293667 24198034637379485905940501)
                  ·
                    refine ⟨1134282873627163401840961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24198034637379485905940501 1134282873627163401840961)
                    ·
                      rfl

theorem cell22_3313512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_3313512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313512 prefixEnd_3313512 := by exact prefixLift 3313512
  have htrace : WordTrace (prefixWord ++ tailWord_3313512) baseStart_3313512 baseEnd_3313512 := by
    simpa [prefixWord, tailWord_3313512, baseEnd_3313512] using wordTrace_append hprefix tailTrace_3313512
  have hstable : (prefixWord ++ tailWord_3313512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313512).length < 2 ^ (prefixWord ++ tailWord_3313512).sum := by decide
  have hdescent : baseEnd_3313512 < baseStart_3313512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313518 : List Nat := [4, 1, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_3313518 : Nat := 118140960795 + 3313518 * 2 ^ 59
def prefixEnd_3313518 : Nat := 4983230072969 + 3 ^ 40 * 3313518 * 2
def baseEnd_3313518 : Nat := 1134284927549781386190943

theorem tailTrace_3313518 : CollatzResearch.WordTrace tailWord_3313518 prefixEnd_3313518 1134284927549781386190943 := by
  unfold tailWord_3313518
  simp only [CollatzResearch.WordTrace]
  refine ⟨15106741251212208083200651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80569286673131776443736805 15106741251212208083200651)
  ·
    refine ⟨22660111876818312124800977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15106741251212208083200651 22660111876818312124800977)
    ·
      refine ⟨16995083907613734093600733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22660111876818312124800977 16995083907613734093600733)
      ·
        refine ⟨6373156465355150285100275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16995083907613734093600733 6373156465355150285100275)
        ·
          refine ⟨9559734698032725427650413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373156465355150285100275 9559734698032725427650413)
          ·
            refine ⟨3584900511762272035368905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9559734698032725427650413 3584900511762272035368905)
            ·
              refine ⟨2688675383821704026526679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3584900511762272035368905 2688675383821704026526679)
              ·
                refine ⟨4033013075732556039790019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688675383821704026526679 4033013075732556039790019)
                ·
                  refine ⟨6049519613598834059685029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033013075732556039790019 6049519613598834059685029)
                  ·
                    refine ⟨1134284927549781386190943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6049519613598834059685029 1134284927549781386190943)
                    ·
                      rfl

theorem cell22_3313518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_3313518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313518 prefixEnd_3313518 := by exact prefixLift 3313518
  have htrace : WordTrace (prefixWord ++ tailWord_3313518) baseStart_3313518 baseEnd_3313518 := by
    simpa [prefixWord, tailWord_3313518, baseEnd_3313518] using wordTrace_append hprefix tailTrace_3313518
  have hstable : (prefixWord ++ tailWord_3313518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313518).length < 2 ^ (prefixWord ++ tailWord_3313518).sum := by decide
  have hdescent : baseEnd_3313518 < baseStart_3313518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313559 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 3, 3]
def baseStart_3313559 : Nat := 118140960795 + 3313559 * 2 ^ 59
def prefixEnd_3313559 : Nat := 4983230072969 + 3 ^ 40 * 3313559 * 2
def baseEnd_3313559 : Nat := 1134298962687670945915817

theorem tailTrace_3313559 : CollatzResearch.WordTrace tailWord_3313559 prefixEnd_3313559 1134298962687670945915817 := by
  unfold tailWord_3313559
  simp only [CollatzResearch.WordTrace]
  refine ⟨120855425402549128667847731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80570283601699419111898487 120855425402549128667847731)
  ·
    refine ⟨181283138103823693001771597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120855425402549128667847731 181283138103823693001771597)
    ·
      refine ⟨67981176788933884875664349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181283138103823693001771597 67981176788933884875664349)
      ·
        refine ⟨25492941295850206828374131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67981176788933884875664349 25492941295850206828374131)
        ·
          refine ⟨38239411943775310242561197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25492941295850206828374131 38239411943775310242561197)
          ·
            refine ⟨14339779478915741340960449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38239411943775310242561197 14339779478915741340960449)
            ·
              refine ⟨10754834609186806005720337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14339779478915741340960449 10754834609186806005720337)
              ·
                refine ⟨8066125956890104504290253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10754834609186806005720337 8066125956890104504290253)
                ·
                  refine ⟨3024797233833789189108845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8066125956890104504290253 3024797233833789189108845)
                  ·
                    refine ⟨1134298962687670945915817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3024797233833789189108845 1134298962687670945915817)
                    ·
                      rfl

theorem cell22_3313559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_3313559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313559 prefixEnd_3313559 := by exact prefixLift 3313559
  have htrace : WordTrace (prefixWord ++ tailWord_3313559) baseStart_3313559 baseEnd_3313559 := by
    simpa [prefixWord, tailWord_3313559, baseEnd_3313559] using wordTrace_append hprefix tailTrace_3313559
  have hstable : (prefixWord ++ tailWord_3313559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313559).length < 2 ^ (prefixWord ++ tailWord_3313559).sum := by decide
  have hdescent : baseEnd_3313559 < baseStart_3313559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313572 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 7]
def baseStart_3313572 : Nat := 118140960795 + 3313572 * 2 ^ 59
def prefixEnd_3313572 : Nat := 4983230072969 + 3 ^ 40 * 3313572 * 2
def baseEnd_3313572 : Nat := 378101137617781081780259

theorem tailTrace_3313572 : CollatzResearch.WordTrace tailWord_3313572 prefixEnd_3313572 378101137617781081780259 := by
  unfold tailWord_3313572
  simp only [CollatzResearch.WordTrace]
  refine ⟨60427949775751015944035485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80570599701001354592047313 60427949775751015944035485)
  ·
    refine ⟨22660481165906630979013307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60427949775751015944035485 22660481165906630979013307)
    ·
      refine ⟨33990721748859946468519961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22660481165906630979013307 33990721748859946468519961)
      ·
        refine ⟨25493041311644959851389971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33990721748859946468519961 25493041311644959851389971)
        ·
          refine ⟨38239561967467439777084957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25493041311644959851389971 38239561967467439777084957)
          ·
            refine ⟨14339835737800289916406859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38239561967467439777084957 14339835737800289916406859)
            ·
              refine ⟨21509753606700434874610289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14339835737800289916406859 21509753606700434874610289)
              ·
                refine ⟨16132315205025326155957717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21509753606700434874610289 16132315205025326155957717)
                ·
                  refine ⟨378101137617781081780259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16132315205025326155957717 378101137617781081780259)
                  ·
                    rfl

theorem cell22_3313572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_3313572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313572 prefixEnd_3313572 := by exact prefixLift 3313572
  have htrace : WordTrace (prefixWord ++ tailWord_3313572) baseStart_3313572 baseEnd_3313572 := by
    simpa [prefixWord, tailWord_3313572, baseEnd_3313572] using wordTrace_append hprefix tailTrace_3313572
  have hstable : (prefixWord ++ tailWord_3313572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313572).length < 2 ^ (prefixWord ++ tailWord_3313572).sum := by decide
  have hdescent : baseEnd_3313572 < baseStart_3313572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313593 : List Nat := [1, 2, 1, 4, 2, 1, 5, 2, 1, 3]
def baseStart_3313593 : Nat := 118140960795 + 3313593 * 2 ^ 59
def prefixEnd_3313593 : Nat := 4983230072969 + 3 ^ 40 * 3313593 * 2
def baseEnd_3313593 : Nat := 1134310601582506190565713

theorem tailTrace_3313593 : CollatzResearch.WordTrace tailWord_3313593 prefixEnd_3313593 1134310601582506190565713 := by
  unfold tailWord_3313593
  simp only [CollatzResearch.WordTrace]
  refine ⟨120856665484425952474585433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80571110322950634983056955 120856665484425952474585433)
  ·
    refine ⟨90642499113319464355939075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120856665484425952474585433 90642499113319464355939075)
    ·
      refine ⟨135963748669979196533908613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90642499113319464355939075 135963748669979196533908613)
      ·
        refine ⟨25493202875621099350107865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135963748669979196533908613 25493202875621099350107865)
        ·
          refine ⟨19119902156715824512580899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25493202875621099350107865 19119902156715824512580899)
          ·
            refine ⟨28679853235073736768871349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19119902156715824512580899 28679853235073736768871349)
            ·
              refine ⟨2688736240788162822081689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28679853235073736768871349 2688736240788162822081689)
              ·
                refine ⟨2016552180591122116561267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2688736240788162822081689 2016552180591122116561267)
                ·
                  refine ⟨3024828270886683174841901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016552180591122116561267 3024828270886683174841901)
                  ·
                    refine ⟨1134310601582506190565713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3024828270886683174841901 1134310601582506190565713)
                    ·
                      rfl

theorem cell22_3313593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 1, 3].length) (baseStart_3313593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313593 prefixEnd_3313593 := by exact prefixLift 3313593
  have htrace : WordTrace (prefixWord ++ tailWord_3313593) baseStart_3313593 baseEnd_3313593 := by
    simpa [prefixWord, tailWord_3313593, baseEnd_3313593] using wordTrace_append hprefix tailTrace_3313593
  have hstable : (prefixWord ++ tailWord_3313593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313593).length < 2 ^ (prefixWord ++ tailWord_3313593).sum := by decide
  have hdescent : baseEnd_3313593 < baseStart_3313593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313636 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_3313636 : Nat := 118140960795 + 3313636 * 2 ^ 59
def prefixEnd_3313636 : Nat := 4983230072969 + 3 ^ 40 * 3313636 * 2
def baseEnd_3313636 : Nat := 1134325321361268411740581

theorem tailTrace_3313636 : CollatzResearch.WordTrace tailWord_3313636 prefixEnd_3313636 1134325321361268411740581 := by
  unfold tailWord_3313636
  simp only [CollatzResearch.WordTrace]
  refine ⟨60429116911635085409200381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80572155882180113878933841 60429116911635085409200381)
  ·
    refine ⟨22660918841863157028450143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60429116911635085409200381 22660918841863157028450143)
    ·
      refine ⟨33991378262794735542675215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22660918841863157028450143 33991378262794735542675215)
      ·
        refine ⟨50987067394192103314012823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33991378262794735542675215 50987067394192103314012823)
        ·
          refine ⟨76480601091288154971019235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50987067394192103314012823 76480601091288154971019235)
          ·
            refine ⟨114720901636932232456528853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76480601091288154971019235 114720901636932232456528853)
            ·
              refine ⟨2688771132115599198199895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 114720901636932232456528853 2688771132115599198199895)
              ·
                refine ⟨4033156698173398797299843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688771132115599198199895 4033156698173398797299843)
                ·
                  refine ⟨6049735047260098195949765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033156698173398797299843 6049735047260098195949765)
                  ·
                    refine ⟨1134325321361268411740581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6049735047260098195949765 1134325321361268411740581)
                    ·
                      rfl

theorem cell22_3313636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_3313636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313636 prefixEnd_3313636 := by exact prefixLift 3313636
  have htrace : WordTrace (prefixWord ++ tailWord_3313636) baseStart_3313636 baseEnd_3313636 := by
    simpa [prefixWord, tailWord_3313636, baseEnd_3313636] using wordTrace_append hprefix tailTrace_3313636
  have hstable : (prefixWord ++ tailWord_3313636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313636).length < 2 ^ (prefixWord ++ tailWord_3313636).sum := by decide
  have hdescent : baseEnd_3313636 < baseStart_3313636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313700 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_3313700 : Nat := 118140960795 + 3313700 * 2 ^ 59
def prefixEnd_3313700 : Nat := 4983230072969 + 3 ^ 40 * 3313700 * 2
def baseEnd_3313700 : Nat := 1134347229869193578140385

theorem tailTrace_3313700 : CollatzResearch.WordTrace tailWord_3313700 prefixEnd_3313700 1134347229869193578140385 := by
  unfold tailWord_3313700
  simp only [CollatzResearch.WordTrace]
  refine ⟨60430284047519154874365277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80573712063358873165820369 60430284047519154874365277)
  ·
    refine ⟨22661356517819683077886979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60430284047519154874365277 22661356517819683077886979)
    ·
      refine ⟨33992034776729524616830469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22661356517819683077886979 33992034776729524616830469)
      ·
        refine ⟨6373506520636785865655713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33992034776729524616830469 6373506520636785865655713)
        ·
          refine ⟨4780129890477589399241785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6373506520636785865655713 4780129890477589399241785)
          ·
            refine ⟨3585097417858192049431339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4780129890477589399241785 3585097417858192049431339)
            ·
              refine ⟨5377646126787288074147009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585097417858192049431339 5377646126787288074147009)
              ·
                refine ⟨4033234595090466055610257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5377646126787288074147009 4033234595090466055610257)
                ·
                  refine ⟨3024925946317849541707693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4033234595090466055610257 3024925946317849541707693)
                  ·
                    refine ⟨1134347229869193578140385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3024925946317849541707693 1134347229869193578140385)
                    ·
                      rfl

theorem cell22_3313700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_3313700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313700 prefixEnd_3313700 := by exact prefixLift 3313700
  have htrace : WordTrace (prefixWord ++ tailWord_3313700) baseStart_3313700 baseEnd_3313700 := by
    simpa [prefixWord, tailWord_3313700, baseEnd_3313700] using wordTrace_append hprefix tailTrace_3313700
  have hstable : (prefixWord ++ tailWord_3313700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313700).length < 2 ^ (prefixWord ++ tailWord_3313700).sum := by decide
  have hdescent : baseEnd_3313700 < baseStart_3313700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313762 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3313762 : Nat := 118140960795 + 3313762 * 2 ^ 59
def prefixEnd_3313762 : Nat := 4983230072969 + 3 ^ 40 * 3313762 * 2
def baseEnd_3313762 : Nat := 1134368453736246083090195

theorem tailTrace_3313762 : CollatzResearch.WordTrace tailWord_3313762 prefixEnd_3313762 1134368453736246083090195 := by
  unfold tailWord_3313762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30215707355203423584371885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80575219613875796224991693 30215707355203423584371885)
  ·
    refine ⟨11330890258201283844139457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30215707355203423584371885 11330890258201283844139457)
    ·
      refine ⟨8498167693650962883104593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11330890258201283844139457 8498167693650962883104593)
      ·
        refine ⟨6373625770238222162328445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8498167693650962883104593 6373625770238222162328445)
        ·
          refine ⟨2390109663839333310873167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6373625770238222162328445 2390109663839333310873167)
          ·
            refine ⟨3585164495758999966309751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390109663839333310873167 3585164495758999966309751)
            ·
              refine ⟨5377746743638499949464627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585164495758999966309751 5377746743638499949464627)
              ·
                refine ⟨8066620115457749924196941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377746743638499949464627 8066620115457749924196941)
                ·
                  refine ⟨3024982543296656221573853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8066620115457749924196941 3024982543296656221573853)
                  ·
                    refine ⟨1134368453736246083090195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3024982543296656221573853 1134368453736246083090195)
                    ·
                      rfl

theorem cell22_3313762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3313762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313762 prefixEnd_3313762 := by exact prefixLift 3313762
  have htrace : WordTrace (prefixWord ++ tailWord_3313762) baseStart_3313762 baseEnd_3313762 := by
    simpa [prefixWord, tailWord_3313762, baseEnd_3313762] using wordTrace_append hprefix tailTrace_3313762
  have hstable : (prefixWord ++ tailWord_3313762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313762).length < 2 ^ (prefixWord ++ tailWord_3313762).sum := by decide
  have hdescent : baseEnd_3313762 < baseStart_3313762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313784 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_3313784 : Nat := 118140960795 + 3313784 * 2 ^ 59
def prefixEnd_3313784 : Nat := 4983230072969 + 3 ^ 40 * 3313784 * 2
def baseEnd_3313784 : Nat := 1134375984785845359040127

theorem tailTrace_3313784 : CollatzResearch.WordTrace tailWord_3313784 prefixEnd_3313784 1134375984785845359040127 := by
  unfold tailWord_3313784
  simp only [CollatzResearch.WordTrace]
  refine ⟨60431815913366996047394203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80575754551155994729858937 60431815913366996047394203)
  ·
    refine ⟨90647723870050494071091305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60431815913366996047394203 90647723870050494071091305)
    ·
      refine ⟨67985792902537870553318479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90647723870050494071091305 67985792902537870553318479)
      ·
        refine ⟨101978689353806805829977719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67985792902537870553318479 101978689353806805829977719)
        ·
          refine ⟨152968034030710208744966579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101978689353806805829977719 152968034030710208744966579)
          ·
            refine ⟨229452051046065313117449869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152968034030710208744966579 229452051046065313117449869)
            ·
              refine ⟨86044519142274492419043701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229452051046065313117449869 86044519142274492419043701)
              ·
                refine ⟨8066673669588233664285347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86044519142274492419043701 8066673669588233664285347)
                ·
                  refine ⟨12100010504382350496428021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8066673669588233664285347 12100010504382350496428021)
                  ·
                    refine ⟨1134375984785845359040127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12100010504382350496428021 1134375984785845359040127)
                    ·
                      rfl

theorem cell22_3313784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_3313784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313784 prefixEnd_3313784 := by exact prefixLift 3313784
  have htrace : WordTrace (prefixWord ++ tailWord_3313784) baseStart_3313784 baseEnd_3313784 := by
    simpa [prefixWord, tailWord_3313784, baseEnd_3313784] using wordTrace_append hprefix tailTrace_3313784
  have hstable : (prefixWord ++ tailWord_3313784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313784).length < 2 ^ (prefixWord ++ tailWord_3313784).sum := by decide
  have hdescent : baseEnd_3313784 < baseStart_3313784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313788 : List Nat := [2, 2, 2, 1, 1, 6, 1, 2, 1, 4]
def baseStart_3313788 : Nat := 118140960795 + 3313788 * 2 ^ 59
def prefixEnd_3313788 : Nat := 4983230072969 + 3 ^ 40 * 3313788 * 2
def baseEnd_3313788 : Nat := 1134377354067590681940115

theorem tailTrace_3313788 : CollatzResearch.WordTrace tailWord_3313788 prefixEnd_3313788 1134377354067590681940115 := by
  unfold tailWord_3313788
  simp only [CollatzResearch.WordTrace]
  refine ⟨60431888859359750388967009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80575851812479667185289345 60431888859359750388967009)
  ·
    refine ⟨45323916644519812791725257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60431888859359750388967009 45323916644519812791725257)
    ·
      refine ⟨33992937483389859593793943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45323916644519812791725257 33992937483389859593793943)
      ·
        refine ⟨50989406225084789390690915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33992937483389859593793943 50989406225084789390690915)
        ·
          refine ⟨76484109337627184086036373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50989406225084789390690915 76484109337627184086036373)
          ·
            refine ⟨3585192625201274254032955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76484109337627184086036373 3585192625201274254032955)
            ·
              refine ⟨5377788937801911381049433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585192625201274254032955 5377788937801911381049433)
              ·
                refine ⟨4033341703351433535787075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5377788937801911381049433 4033341703351433535787075)
                ·
                  refine ⟨6050012555027150303680613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033341703351433535787075 6050012555027150303680613)
                  ·
                    refine ⟨1134377354067590681940115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6050012555027150303680613 1134377354067590681940115)
                    ·
                      rfl

theorem cell22_3313788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_3313788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313788 prefixEnd_3313788 := by exact prefixLift 3313788
  have htrace : WordTrace (prefixWord ++ tailWord_3313788) baseStart_3313788 baseEnd_3313788 := by
    simpa [prefixWord, tailWord_3313788, baseEnd_3313788] using wordTrace_append hprefix tailTrace_3313788
  have hstable : (prefixWord ++ tailWord_3313788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313788).length < 2 ^ (prefixWord ++ tailWord_3313788).sum := by decide
  have hdescent : baseEnd_3313788 < baseStart_3313788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313799 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3313799 : Nat := 118140960795 + 3313799 * 2 ^ 59
def prefixEnd_3313799 : Nat := 4983230072969 + 3 ^ 40 * 3313799 * 2
def baseEnd_3313799 : Nat := 1134381119592390319915081

theorem tailTrace_3313799 : CollatzResearch.WordTrace tailWord_3313799 prefixEnd_3313799 1134381119592390319915081 := by
  unfold tailWord_3313799
  simp only [CollatzResearch.WordTrace]
  refine ⟨120864178921679649656584451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80576119281119766437722967 120864178921679649656584451)
  ·
    refine ⟨181296268382519474484876677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120864178921679649656584451 181296268382519474484876677)
    ·
      refine ⟨33993050321722401465914377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181296268382519474484876677 33993050321722401465914377)
      ·
        refine ⟨25494787741291801099435783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33993050321722401465914377 25494787741291801099435783)
        ·
          refine ⟨38242181611937701649153675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25494787741291801099435783 38242181611937701649153675)
          ·
            refine ⟨57363272417906552473730513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38242181611937701649153675 57363272417906552473730513)
            ·
              refine ⟨43022454313429914355297885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57363272417906552473730513 43022454313429914355297885)
              ·
                refine ⟨16133420367536217883236707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43022454313429914355297885 16133420367536217883236707)
                ·
                  refine ⟨24200130551304326824855061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16133420367536217883236707 24200130551304326824855061)
                  ·
                    refine ⟨1134381119592390319915081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24200130551304326824855061 1134381119592390319915081)
                    ·
                      rfl

theorem cell22_3313799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3313799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313799 prefixEnd_3313799 := by exact prefixLift 3313799
  have htrace : WordTrace (prefixWord ++ tailWord_3313799) baseStart_3313799 baseEnd_3313799 := by
    simpa [prefixWord, tailWord_3313799, baseEnd_3313799] using wordTrace_append hprefix tailTrace_3313799
  have hstable : (prefixWord ++ tailWord_3313799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313799).length < 2 ^ (prefixWord ++ tailWord_3313799).sum := by decide
  have hdescent : baseEnd_3313799 < baseStart_3313799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313880 : List Nat := [2, 1, 2, 2, 4, 1, 2, 4, 1, 3]
def baseStart_3313880 : Nat := 118140960795 + 3313880 * 2 ^ 59
def prefixEnd_3313880 : Nat := 4983230072969 + 3 ^ 40 * 3313880 * 2
def baseEnd_3313880 : Nat := 1134408847547733108639833

theorem tailTrace_3313880 : CollatzResearch.WordTrace tailWord_3313880 prefixEnd_3313880 1134408847547733108639833 := by
  unfold tailWord_3313880
  simp only [CollatzResearch.WordTrace]
  refine ⟨60433566617193100245141547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80578088822924133660188729 60433566617193100245141547)
  ·
    refine ⟨90650349925789650367712321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60433566617193100245141547 90650349925789650367712321)
    ·
      refine ⟨67987762444342237775784241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90650349925789650367712321 67987762444342237775784241)
      ·
        refine ⟨50990821833256678331838181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67987762444342237775784241 50990821833256678331838181)
        ·
          refine ⟨9560779093735627187219659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50990821833256678331838181 9560779093735627187219659)
          ·
            refine ⟨14341168640603440780829489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9560779093735627187219659 14341168640603440780829489)
            ·
              refine ⟨10755876480452580585622117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14341168640603440780829489 10755876480452580585622117)
              ·
                refine ⟨2016726840084858859804147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10755876480452580585622117 2016726840084858859804147)
                ·
                  refine ⟨3025090260127288289706221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016726840084858859804147 3025090260127288289706221)
                  ·
                    refine ⟨1134408847547733108639833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3025090260127288289706221 1134408847547733108639833)
                    ·
                      rfl

theorem cell22_3313880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_3313880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313880 prefixEnd_3313880 := by exact prefixLift 3313880
  have htrace : WordTrace (prefixWord ++ tailWord_3313880) baseStart_3313880 baseEnd_3313880 := by
    simpa [prefixWord, tailWord_3313880, baseEnd_3313880] using wordTrace_append hprefix tailTrace_3313880
  have hstable : (prefixWord ++ tailWord_3313880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313880).length < 2 ^ (prefixWord ++ tailWord_3313880).sum := by decide
  have hdescent : baseEnd_3313880 < baseStart_3313880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313957 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 1, 4]
def baseStart_3313957 : Nat := 118140960795 + 3313957 * 2 ^ 59
def prefixEnd_3313957 : Nat := 4983230072969 + 3 ^ 40 * 3313957 * 2
def baseEnd_3313957 : Nat := 1134435206221330574464597

theorem tailTrace_3313957 : CollatzResearch.WordTrace tailWord_3313957 prefixEnd_3313957 1134435206221330574464597 := by
  unfold tailWord_3313957
  simp only [CollatzResearch.WordTrace]
  refine ⟨120869941655107242640836125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80579961103404828427224083 120869941655107242640836125)
  ·
    refine ⟨45326228120665215990313547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120869941655107242640836125 45326228120665215990313547)
    ·
      refine ⟨67989342180997823985470321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45326228120665215990313547 67989342180997823985470321)
      ·
        refine ⟨50992006635748367989102741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67989342180997823985470321 50992006635748367989102741)
        ·
          refine ⟨2390250311050704749489191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50992006635748367989102741 2390250311050704749489191)
          ·
            refine ⟨3585375466576057124233787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390250311050704749489191 3585375466576057124233787)
            ·
              refine ⟨5378063199864085686350681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585375466576057124233787 5378063199864085686350681)
              ·
                refine ⟨4033547399898064264763011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5378063199864085686350681 4033547399898064264763011)
                ·
                  refine ⟨6050321099847096397144517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4033547399898064264763011 6050321099847096397144517)
                  ·
                    refine ⟨1134435206221330574464597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6050321099847096397144517 1134435206221330574464597)
                    ·
                      rfl

theorem cell22_3313957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_3313957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313957 prefixEnd_3313957 := by exact prefixLift 3313957
  have htrace : WordTrace (prefixWord ++ tailWord_3313957) baseStart_3313957 baseEnd_3313957 := by
    simpa [prefixWord, tailWord_3313957, baseEnd_3313957] using wordTrace_append hprefix tailTrace_3313957
  have hstable : (prefixWord ++ tailWord_3313957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313957).length < 2 ^ (prefixWord ++ tailWord_3313957).sum := by decide
  have hdescent : baseEnd_3313957 < baseStart_3313957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3313996 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_3313996 : Nat := 118140960795 + 3313996 * 2 ^ 59
def prefixEnd_3313996 : Nat := 4983230072969 + 3 ^ 40 * 3313996 * 2
def baseEnd_3313996 : Nat := 1134448556718347472739477

theorem tailTrace_3313996 : CollatzResearch.WordTrace tailWord_3313996 prefixEnd_3313996 1134448556718347472739477 := by
  unfold tailWord_3313996
  simp only [CollatzResearch.WordTrace]
  refine ⟨60435682050982976150752921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80580909401310634867670561 60435682050982976150752921)
  ·
    refine ⟨45326761538237232113064691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60435682050982976150752921 45326761538237232113064691)
    ·
      refine ⟨67990142307355848169597037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45326761538237232113064691 67990142307355848169597037)
      ·
        refine ⟨25496303365258443063598889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67990142307355848169597037 25496303365258443063598889)
        ·
          refine ⟨19122227523943832297699167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25496303365258443063598889 19122227523943832297699167)
          ·
            refine ⟨28683341285915748446548751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19122227523943832297699167 28683341285915748446548751)
            ·
              refine ⟨43025011928873622669823127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28683341285915748446548751 43025011928873622669823127)
              ·
                refine ⟨64537517893310434004734691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43025011928873622669823127 64537517893310434004734691)
                ·
                  refine ⟨96806276839965651007102037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64537517893310434004734691 96806276839965651007102037)
                  ·
                    refine ⟨1134448556718347472739477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96806276839965651007102037 1134448556718347472739477)
                    ·
                      rfl

theorem cell22_3313996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_3313996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3313996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3313996 prefixEnd_3313996 := by exact prefixLift 3313996
  have htrace : WordTrace (prefixWord ++ tailWord_3313996) baseStart_3313996 baseEnd_3313996 := by
    simpa [prefixWord, tailWord_3313996, baseEnd_3313996] using wordTrace_append hprefix tailTrace_3313996
  have hstable : (prefixWord ++ tailWord_3313996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3313996).length < 2 ^ (prefixWord ++ tailWord_3313996).sum := by decide
  have hdescent : baseEnd_3313996 < baseStart_3313996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3313996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314032 : List Nat := [2, 1, 1, 1, 4, 4, 2, 3, 1, 3]
def baseStart_3314032 : Nat := 118140960795 + 3314032 * 2 ^ 59
def prefixEnd_3314032 : Nat := 4983230072969 + 3 ^ 40 * 3314032 * 2
def baseEnd_3314032 : Nat := 1134460880254055378839367

theorem tailTrace_3314032 : CollatzResearch.WordTrace tailWord_3314032 prefixEnd_3314032 1134460880254055378839367 := by
  unfold tailWord_3314032
  simp only [CollatzResearch.WordTrace]
  refine ⟨60436338564917765224908175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80581784753223686966544233 60436338564917765224908175)
  ·
    refine ⟨90654507847376647837362263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60436338564917765224908175 90654507847376647837362263)
    ·
      refine ⟨135981761771064971756043395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90654507847376647837362263 135981761771064971756043395)
      ·
        refine ⟨203972642656597457634065093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135981761771064971756043395 203972642656597457634065093)
        ·
          refine ⟨38244870498112023306387205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203972642656597457634065093 38244870498112023306387205)
          ·
            refine ⟨7170913218396004369947601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38244870498112023306387205 7170913218396004369947601)
            ·
              refine ⟨5378184913797003277460701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7170913218396004369947601 5378184913797003277460701)
              ·
                refine ⟨2016819342673876229047763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5378184913797003277460701 2016819342673876229047763)
                ·
                  refine ⟨3025229014010814343571645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2016819342673876229047763 3025229014010814343571645)
                  ·
                    refine ⟨1134460880254055378839367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3025229014010814343571645 1134460880254055378839367)
                    ·
                      rfl

theorem cell22_3314032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 3, 1, 3].length) (baseStart_3314032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314032 prefixEnd_3314032 := by exact prefixLift 3314032
  have htrace : WordTrace (prefixWord ++ tailWord_3314032) baseStart_3314032 baseEnd_3314032 := by
    simpa [prefixWord, tailWord_3314032, baseEnd_3314032] using wordTrace_append hprefix tailTrace_3314032
  have hstable : (prefixWord ++ tailWord_3314032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314032).length < 2 ^ (prefixWord ++ tailWord_3314032).sum := by decide
  have hdescent : baseEnd_3314032 < baseStart_3314032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314045 : List Nat := [1, 4, 1, 1, 2, 5, 1, 2, 5]
def baseStart_3314045 : Nat := 118140960795 + 3314045 * 2 ^ 59
def prefixEnd_3314045 : Nat := 4983230072969 + 3 ^ 40 * 3314045 * 2
def baseEnd_3314045 : Nat := 378155110139909226088109

theorem tailTrace_3314045 : CollatzResearch.WordTrace tailWord_3314045 prefixEnd_3314045 378155110139909226088109 := by
  unfold tailWord_3314045
  simp only [CollatzResearch.WordTrace]
  refine ⟨120873151278788433670039589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80582100852525622446693059 120873151278788433670039589)
  ·
    refine ⟨22663715864772831313132423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120873151278788433670039589 22663715864772831313132423)
    ·
      refine ⟨33995573797159246969698635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22663715864772831313132423 33995573797159246969698635)
      ·
        refine ⟨50993360695738870454547953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33995573797159246969698635 50993360695738870454547953)
        ·
          refine ⟨38245020521804152840910965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50993360695738870454547953 38245020521804152840910965)
          ·
            refine ⟨3585470673919139328835403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38245020521804152840910965 3585470673919139328835403)
            ·
              refine ⟨5378206010878708993253105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585470673919139328835403 5378206010878708993253105)
              ·
                refine ⟨4033654508159031744939829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5378206010878708993253105 4033654508159031744939829)
                ·
                  refine ⟨378155110139909226088109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4033654508159031744939829 378155110139909226088109)
                  ·
                    rfl

theorem cell22_3314045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_3314045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314045 prefixEnd_3314045 := by exact prefixLift 3314045
  have htrace : WordTrace (prefixWord ++ tailWord_3314045) baseStart_3314045 baseEnd_3314045 := by
    simpa [prefixWord, tailWord_3314045, baseEnd_3314045] using wordTrace_append hprefix tailTrace_3314045
  have hstable : (prefixWord ++ tailWord_3314045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314045).length < 2 ^ (prefixWord ++ tailWord_3314045).sum := by decide
  have hdescent : baseEnd_3314045 < baseStart_3314045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314062 : List Nat := [4, 1, 1, 4, 1, 2, 3, 1, 5]
def baseStart_3314062 : Nat := 118140960795 + 3314062 * 2 ^ 59
def prefixEnd_3314062 : Nat := 4983230072969 + 3 ^ 40 * 3314062 * 2
def baseEnd_3314062 : Nat := 378157049955715100196425

theorem tailTrace_3314062 : CollatzResearch.WordTrace tailWord_3314062 prefixEnd_3314062 378157049955715100196425 := by
  unfold tailWord_3314062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109221414965855696676055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80582514213151230382272293 15109221414965855696676055)
  ·
    refine ⟨22663832122448783545014083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15109221414965855696676055 22663832122448783545014083)
    ·
      refine ⟨33995748183673175317521125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22663832122448783545014083 33995748183673175317521125)
      ·
        refine ⟨6374202784438720372035211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33995748183673175317521125 6374202784438720372035211)
        ·
          refine ⟨9561304176658080558052817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6374202784438720372035211 9561304176658080558052817)
          ·
            refine ⟨7170978132493560418539613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9561304176658080558052817 7170978132493560418539613)
            ·
              refine ⟨2689116799685085156952355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7170978132493560418539613 2689116799685085156952355)
              ·
                refine ⟨4033675199527627735428533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689116799685085156952355 4033675199527627735428533)
                ·
                  refine ⟨378157049955715100196425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4033675199527627735428533 378157049955715100196425)
                  ·
                    rfl

theorem cell22_3314062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_3314062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314062 prefixEnd_3314062 := by exact prefixLift 3314062
  have htrace : WordTrace (prefixWord ++ tailWord_3314062) baseStart_3314062 baseEnd_3314062 := by
    simpa [prefixWord, tailWord_3314062, baseEnd_3314062] using wordTrace_append hprefix tailTrace_3314062
  have hstable : (prefixWord ++ tailWord_3314062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314062).length < 2 ^ (prefixWord ++ tailWord_3314062).sum := by decide
  have hdescent : baseEnd_3314062 < baseStart_3314062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314103 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 4, 4]
def baseStart_3314103 : Nat := 118140960795 + 3314103 * 2 ^ 59
def prefixEnd_3314103 : Nat := 4983230072969 + 3 ^ 40 * 3314103 * 2
def baseEnd_3314103 : Nat := 1134485185005034860314149

theorem tailTrace_3314103 : CollatzResearch.WordTrace tailWord_3314103 prefixEnd_3314103 1134485185005034860314149 := by
  unfold tailWord_3314103
  simp only [CollatzResearch.WordTrace]
  refine ⟨120875266712578309575650963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80583511141718873050433975 120875266712578309575650963)
  ·
    refine ⟨181312900068867464363476445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120875266712578309575650963 181312900068867464363476445)
    ·
      refine ⟨67992337525825299136303667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181312900068867464363476445 67992337525825299136303667)
      ·
        refine ⟨101988506288737948704455501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67992337525825299136303667 101988506288737948704455501)
        ·
          refine ⟨38245689858276730764170813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101988506288737948704455501 38245689858276730764170813)
          ·
            refine ⟨14342133696853774036564055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38245689858276730764170813 14342133696853774036564055)
            ·
              refine ⟨21513200545280661054846083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14342133696853774036564055 21513200545280661054846083)
              ·
                refine ⟨32269800817920991582269125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21513200545280661054846083 32269800817920991582269125)
                ·
                  refine ⟨6050587653360185921675461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32269800817920991582269125 6050587653360185921675461)
                  ·
                    refine ⟨1134485185005034860314149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6050587653360185921675461 1134485185005034860314149)
                    ·
                      rfl

theorem cell22_3314103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_3314103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314103 prefixEnd_3314103 := by exact prefixLift 3314103
  have htrace : WordTrace (prefixWord ++ tailWord_3314103) baseStart_3314103 baseEnd_3314103 := by
    simpa [prefixWord, tailWord_3314103, baseEnd_3314103] using wordTrace_append hprefix tailTrace_3314103
  have hstable : (prefixWord ++ tailWord_3314103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314103).length < 2 ^ (prefixWord ++ tailWord_3314103).sum := by decide
  have hdescent : baseEnd_3314103 < baseStart_3314103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314105 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 4, 3]
def baseStart_3314105 : Nat := 118140960795 + 3314105 * 2 ^ 59
def prefixEnd_3314105 : Nat := 4983230072969 + 3 ^ 40 * 3314105 * 2
def baseEnd_3314105 : Nat := 1134485869645907521764143

theorem tailTrace_3314105 : CollatzResearch.WordTrace tailWord_3314105 prefixEnd_3314105 1134485869645907521764143 := by
  unfold tailWord_3314105
  simp only [CollatzResearch.WordTrace]
  refine ⟨120875339658571063917223769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80583559772380709278149179 120875339658571063917223769)
  ·
    refine ⟨90656504743928297937917827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120875339658571063917223769 90656504743928297937917827)
    ·
      refine ⟨135984757115892446906876741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90656504743928297937917827 135984757115892446906876741)
      ·
        refine ⟨25497141959229833795039389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135984757115892446906876741 25497141959229833795039389)
        ·
          refine ⟨9561428234711187673139771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25497141959229833795039389 9561428234711187673139771)
          ·
            refine ⟨14342142352066781509709657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9561428234711187673139771 14342142352066781509709657)
            ·
              refine ⟨10756606764050086132282243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14342142352066781509709657 10756606764050086132282243)
              ·
                refine ⟨16134910146075129198423365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10756606764050086132282243 16134910146075129198423365)
                ·
                  refine ⟨3025295652389086724704381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16134910146075129198423365 3025295652389086724704381)
                  ·
                    refine ⟨1134485869645907521764143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3025295652389086724704381 1134485869645907521764143)
                    ·
                      rfl

theorem cell22_3314105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 3].length) (baseStart_3314105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314105 prefixEnd_3314105 := by exact prefixLift 3314105
  have htrace : WordTrace (prefixWord ++ tailWord_3314105) baseStart_3314105 baseEnd_3314105 := by
    simpa [prefixWord, tailWord_3314105, baseEnd_3314105] using wordTrace_append hprefix tailTrace_3314105
  have hstable : (prefixWord ++ tailWord_3314105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314105).length < 2 ^ (prefixWord ++ tailWord_3314105).sum := by decide
  have hdescent : baseEnd_3314105 < baseStart_3314105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314113 : List Nat := [1, 2, 7, 1, 2, 1, 2, 1, 5]
def baseStart_3314113 : Nat := 118140960795 + 3314113 * 2 ^ 59
def prefixEnd_3314113 : Nat := 4983230072969 + 3 ^ 40 * 3314113 * 2
def baseEnd_3314113 : Nat := 378162869403132722521373

theorem tailTrace_3314113 : CollatzResearch.WordTrace tailWord_3314113 prefixEnd_3314113 378162869403132722521373 := by
  unfold tailWord_3314113
  simp only [CollatzResearch.WordTrace]
  refine ⟨120875631442542081283514993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80583754295028054189009995 120875631442542081283514993)
  ·
    refine ⟨90656723581906560962636245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120875631442542081283514993 90656723581906560962636245)
    ·
      refine ⟨2124766958950935022561787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 90656723581906560962636245 2124766958950935022561787)
      ·
        refine ⟨3187150438426402533842681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2124766958950935022561787 3187150438426402533842681)
        ·
          refine ⟨2390362828819801900382011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3187150438426402533842681 2390362828819801900382011)
          ·
            refine ⟨3585544243229702850573017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390362828819801900382011 3585544243229702850573017)
            ·
              refine ⟨2689158182422277137929763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3585544243229702850573017 2689158182422277137929763)
              ·
                refine ⟨4033737273633415706894645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689158182422277137929763 4033737273633415706894645)
                ·
                  refine ⟨378162869403132722521373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4033737273633415706894645 378162869403132722521373)
                  ·
                    rfl

theorem cell22_3314113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 1, 5].length) (baseStart_3314113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314113 prefixEnd_3314113 := by exact prefixLift 3314113
  have htrace : WordTrace (prefixWord ++ tailWord_3314113) baseStart_3314113 baseEnd_3314113 := by
    simpa [prefixWord, tailWord_3314113, baseEnd_3314113] using wordTrace_append hprefix tailTrace_3314113
  have hstable : (prefixWord ++ tailWord_3314113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314113).length < 2 ^ (prefixWord ++ tailWord_3314113).sum := by decide
  have hdescent : baseEnd_3314113 < baseStart_3314113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314240 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 1, 5]
def baseStart_3314240 : Nat := 118140960795 + 3314240 * 2 ^ 59
def prefixEnd_3314240 : Nat := 4983230072969 + 3 ^ 40 * 3314240 * 2
def baseEnd_3314240 : Nat := 1134532082904812169638729

theorem tailTrace_3314240 : CollatzResearch.WordTrace tailWord_3314240 prefixEnd_3314240 1134532082904812169638729 := by
  unfold tailWord_3314240
  simp only [CollatzResearch.WordTrace]
  refine ⟨60440131756540990986694087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80586842342054654648925449 60440131756540990986694087)
  ·
    refine ⟨90660197634811486480041131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60440131756540990986694087 90660197634811486480041131)
    ·
      refine ⟨135990296452217229720061697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90660197634811486480041131 135990296452217229720061697)
      ·
        refine ⟨101992722339162922290046273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135990296452217229720061697 101992722339162922290046273)
        ·
          refine ⟨76494541754372191717534705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101992722339162922290046273 76494541754372191717534705)
          ·
            refine ⟨57370906315779143788151029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76494541754372191717534705 57370906315779143788151029)
            ·
              refine ⟨5378522467104294730139159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57370906315779143788151029 5378522467104294730139159)
              ·
                refine ⟨8067783700656442095208739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5378522467104294730139159 8067783700656442095208739)
                ·
                  refine ⟨12101675550984663142813109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8067783700656442095208739 12101675550984663142813109)
                  ·
                    refine ⟨1134532082904812169638729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12101675550984663142813109 1134532082904812169638729)
                    ·
                      rfl

theorem cell22_3314240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_3314240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314240 prefixEnd_3314240 := by exact prefixLift 3314240
  have htrace : WordTrace (prefixWord ++ tailWord_3314240) baseStart_3314240 baseEnd_3314240 := by
    simpa [prefixWord, tailWord_3314240, baseEnd_3314240] using wordTrace_append hprefix tailTrace_3314240
  have hstable : (prefixWord ++ tailWord_3314240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314240).length < 2 ^ (prefixWord ++ tailWord_3314240).sum := by decide
  have hdescent : baseEnd_3314240 < baseStart_3314240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314332 : List Nat := [2, 2, 3, 2, 2, 1, 1, 4, 5]
def baseStart_3314332 : Nat := 118140960795 + 3314332 * 2 ^ 59
def prefixEnd_3314332 : Nat := 4983230072969 + 3 ^ 40 * 3314332 * 2
def baseEnd_3314332 : Nat := 378187858794984865446149

theorem tailTrace_3314332 : CollatzResearch.WordTrace tailWord_3314332 prefixEnd_3314332 378187858794984865446149 := by
  unfold tailWord_3314332
  simp only [CollatzResearch.WordTrace]
  refine ⟨60441809514374340842868625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80589079352499121123824833 60441809514374340842868625)
  ·
    refine ⟨45331357135780755632151469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60441809514374340842868625 45331357135780755632151469)
    ·
      refine ⟨16999258925917783362056801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45331357135780755632151469 16999258925917783362056801)
      ·
        refine ⟨12749444194438337521542601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16999258925917783362056801 12749444194438337521542601)
        ·
          refine ⟨9562083145828753141156951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12749444194438337521542601 9562083145828753141156951)
          ·
            refine ⟨14343124718743129711735427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9562083145828753141156951 14343124718743129711735427)
            ·
              refine ⟨21514687078114694567603141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14343124718743129711735427 21514687078114694567603141)
              ·
                refine ⟨4034003827146505231425589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21514687078114694567603141 4034003827146505231425589)
                ·
                  refine ⟨378187858794984865446149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4034003827146505231425589 378187858794984865446149)
                  ·
                    rfl

theorem cell22_3314332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_3314332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314332 prefixEnd_3314332 := by exact prefixLift 3314332
  have htrace : WordTrace (prefixWord ++ tailWord_3314332) baseStart_3314332 baseEnd_3314332 := by
    simpa [prefixWord, tailWord_3314332, baseEnd_3314332] using wordTrace_append hprefix tailTrace_3314332
  have hstable : (prefixWord ++ tailWord_3314332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314332).length < 2 ^ (prefixWord ++ tailWord_3314332).sum := by decide
  have hdescent : baseEnd_3314332 < baseStart_3314332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314336 : List Nat := [2, 1, 1, 4, 4, 1, 1, 4, 1, 3]
def baseStart_3314336 : Nat := 118140960795 + 3314336 * 2 ^ 59
def prefixEnd_3314336 : Nat := 4983230072969 + 3 ^ 40 * 3314336 * 2
def baseEnd_3314336 : Nat := 1134564945666699919238435

theorem tailTrace_3314336 : CollatzResearch.WordTrace tailWord_3314336 prefixEnd_3314336 1134564945666699919238435 := by
  unfold tailWord_3314336
  simp only [CollatzResearch.WordTrace]
  refine ⟨60441882460367095184441431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80589176613822793579255241 60441882460367095184441431)
  ·
    refine ⟨90662823690550642776662147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60441882460367095184441431 90662823690550642776662147)
    ·
      refine ⟨135994235535825964164993221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90662823690550642776662147 135994235535825964164993221)
      ·
        refine ⟨25498919162967368280936229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135994235535825964164993221 25498919162967368280936229)
        ·
          refine ⟨4781047343056381552675543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25498919162967368280936229 4781047343056381552675543)
          ·
            refine ⟨7171571014584572329013315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781047343056381552675543 7171571014584572329013315)
            ·
              refine ⟨10757356521876858493519973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7171571014584572329013315 10757356521876858493519973)
              ·
                refine ⟨2017004347851910967534995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10757356521876858493519973 2017004347851910967534995)
                ·
                  refine ⟨3025506521777866451302493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017004347851910967534995 3025506521777866451302493)
                  ·
                    refine ⟨1134564945666699919238435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3025506521777866451302493 1134564945666699919238435)
                    ·
                      rfl

theorem cell22_3314336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 4, 1, 3].length) (baseStart_3314336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314336 prefixEnd_3314336 := by exact prefixLift 3314336
  have htrace : WordTrace (prefixWord ++ tailWord_3314336) baseStart_3314336 baseEnd_3314336 := by
    simpa [prefixWord, tailWord_3314336, baseEnd_3314336] using wordTrace_append hprefix tailTrace_3314336
  have hstable : (prefixWord ++ tailWord_3314336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314336).length < 2 ^ (prefixWord ++ tailWord_3314336).sum := by decide
  have hdescent : baseEnd_3314336 < baseStart_3314336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314345 : List Nat := [1, 2, 1, 1, 1, 1, 2, 6, 3, 4]
def baseStart_3314345 : Nat := 118140960795 + 3314345 * 2 ^ 59
def prefixEnd_3314345 : Nat := 4983230072969 + 3 ^ 40 * 3314345 * 2
def baseEnd_3314345 : Nat := 1134568026550626895763407

theorem tailTrace_3314345 : CollatzResearch.WordTrace tailWord_3314345 prefixEnd_3314345 1134568026550626895763407 := by
  unfold tailWord_3314345
  simp only [CollatzResearch.WordTrace]
  refine ⟨120884093177701584905960489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80589395451801056603973659 120884093177701584905960489)
  ·
    refine ⟨90663069883276188679470367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120884093177701584905960489 90663069883276188679470367)
    ·
      refine ⟨135994604824914283019205551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90663069883276188679470367 135994604824914283019205551)
      ·
        refine ⟨203991907237371424528808327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135994604824914283019205551 203991907237371424528808327)
        ·
          refine ⟨305987860856057136793212491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203991907237371424528808327 305987860856057136793212491)
          ·
            refine ⟨458981791284085705189818737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305987860856057136793212491 458981791284085705189818737)
            ·
              refine ⟨344236343463064278892364053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458981791284085705189818737 344236343463064278892364053)
              ·
                refine ⟨16136078599831138073079565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 344236343463064278892364053 16136078599831138073079565)
                ·
                  refine ⟨6051029474936676777404837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16136078599831138073079565 6051029474936676777404837)
                  ·
                    refine ⟨1134568026550626895763407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6051029474936676777404837 1134568026550626895763407)
                    ·
                      rfl

theorem cell22_3314345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 4].length) (baseStart_3314345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314345 prefixEnd_3314345 := by exact prefixLift 3314345
  have htrace : WordTrace (prefixWord ++ tailWord_3314345) baseStart_3314345 baseEnd_3314345 := by
    simpa [prefixWord, tailWord_3314345, baseEnd_3314345] using wordTrace_append hprefix tailTrace_3314345
  have hstable : (prefixWord ++ tailWord_3314345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314345).length < 2 ^ (prefixWord ++ tailWord_3314345).sum := by decide
  have hdescent : baseEnd_3314345 < baseStart_3314345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314362 : List Nat := [3, 1, 1, 1, 2, 3, 2, 4, 1, 4]
def baseStart_3314362 : Nat := 118140960795 + 3314362 * 2 ^ 59
def prefixEnd_3314362 : Nat := 4983230072969 + 3 ^ 40 * 3314362 * 2
def baseEnd_3314362 : Nat := 1134573845998044518088355

theorem tailTrace_3314362 : CollatzResearch.WordTrace tailWord_3314362 prefixEnd_3314362 1134573845998044518088355 := by
  unfold tailWord_3314362
  simp only [CollatzResearch.WordTrace]
  refine ⟨30221178304659999202332335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80589808812426664539552893 30221178304659999202332335)
  ·
    refine ⟨45331767456989998803498503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30221178304659999202332335 45331767456989998803498503)
    ·
      refine ⟨67997651185484998205247755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45331767456989998803498503 67997651185484998205247755)
      ·
        refine ⟨101996476778227497307871633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67997651185484998205247755 101996476778227497307871633)
        ·
          refine ⟨76497357583670622980903725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101996476778227497307871633 76497357583670622980903725)
          ·
            refine ⟨28686509093876483617838897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76497357583670622980903725 28686509093876483617838897)
            ·
              refine ⟨21514881820407362713379173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28686509093876483617838897 21514881820407362713379173)
              ·
                refine ⟨4034040341326380508758595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21514881820407362713379173 4034040341326380508758595)
                ·
                  refine ⟨6051060511989570763137893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034040341326380508758595 6051060511989570763137893)
                  ·
                    refine ⟨1134573845998044518088355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6051060511989570763137893 1134573845998044518088355)
                    ·
                      rfl

theorem cell22_3314362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_3314362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314362 prefixEnd_3314362 := by exact prefixLift 3314362
  have htrace : WordTrace (prefixWord ++ tailWord_3314362) baseStart_3314362 baseEnd_3314362 := by
    simpa [prefixWord, tailWord_3314362, baseEnd_3314362] using wordTrace_append hprefix tailTrace_3314362
  have hstable : (prefixWord ++ tailWord_3314362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314362).length < 2 ^ (prefixWord ++ tailWord_3314362).sum := by decide
  have hdescent : baseEnd_3314362 < baseStart_3314362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314375 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3314375 : Nat := 118140960795 + 3314375 * 2 ^ 59
def prefixEnd_3314375 : Nat := 4983230072969 + 3 ^ 40 * 3314375 * 2
def baseEnd_3314375 : Nat := 1134578296163716817513315

theorem tailTrace_3314375 : CollatzResearch.WordTrace tailWord_3314375 prefixEnd_3314375 1134578296163716817513315 := by
  unfold tailWord_3314375
  simp only [CollatzResearch.WordTrace]
  refine ⟨120885187367592900029552579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80590124911728600019701719 120885187367592900029552579)
  ·
    refine ⟨181327781051389350044328869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120885187367592900029552579 181327781051389350044328869)
    ·
      refine ⟨33998958947135503133311663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181327781051389350044328869 33998958947135503133311663)
      ·
        refine ⟨50998438420703254699967495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33998958947135503133311663 50998438420703254699967495)
        ·
          refine ⟨76497657631054882049951243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50998438420703254699967495 76497657631054882049951243)
          ·
            refine ⟨114746486446582323074926865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76497657631054882049951243 114746486446582323074926865)
            ·
              refine ⟨86059864834936742306195149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114746486446582323074926865 86059864834936742306195149)
              ·
                refine ⟨32272449313101278364823181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86059864834936742306195149 32272449313101278364823181)
                ·
                  refine ⟨12102168492412979386808693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32272449313101278364823181 12102168492412979386808693)
                  ·
                    refine ⟨1134578296163716817513315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12102168492412979386808693 1134578296163716817513315)
                    ·
                      rfl

theorem cell22_3314375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3314375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314375 prefixEnd_3314375 := by exact prefixLift 3314375
  have htrace : WordTrace (prefixWord ++ tailWord_3314375) baseStart_3314375 baseEnd_3314375 := by
    simpa [prefixWord, tailWord_3314375, baseEnd_3314375] using wordTrace_append hprefix tailTrace_3314375
  have hstable : (prefixWord ++ tailWord_3314375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314375).length < 2 ^ (prefixWord ++ tailWord_3314375).sum := by decide
  have hdescent : baseEnd_3314375 < baseStart_3314375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314422 : List Nat := [5, 1, 1, 1, 1, 2, 3, 8]
def baseStart_3314422 : Nat := 118140960795 + 3314422 * 2 ^ 59
def prefixEnd_3314422 : Nat := 4983230072969 + 3 ^ 40 * 3314422 * 2
def baseEnd_3314422 : Nat := 126066042802691595732019

theorem tailTrace_3314422 : CollatzResearch.WordTrace tailWord_3314422 prefixEnd_3314422 126066042802691595732019 := by
  unfold tailWord_3314422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555431349901414191032095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80591267732281751371009013 7555431349901414191032095)
  ·
    refine ⟨11333147024852121286548143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7555431349901414191032095 11333147024852121286548143)
    ·
      refine ⟨16999720537278181929822215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11333147024852121286548143 16999720537278181929822215)
      ·
        refine ⟨25499580805917272894733323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16999720537278181929822215 25499580805917272894733323)
        ·
          refine ⟨38249371208875909342099985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25499580805917272894733323 38249371208875909342099985)
          ·
            refine ⟨28687028406656932006574989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38249371208875909342099985 28687028406656932006574989)
            ·
              refine ⟨10757635652496349502465621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28687028406656932006574989 10757635652496349502465621)
              ·
                refine ⟨126066042802691595732019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10757635652496349502465621 126066042802691595732019)
                ·
                  rfl

theorem cell22_3314422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_3314422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314422 prefixEnd_3314422 := by exact prefixLift 3314422
  have htrace : WordTrace (prefixWord ++ tailWord_3314422) baseStart_3314422 baseEnd_3314422 := by
    simpa [prefixWord, tailWord_3314422, baseEnd_3314422] using wordTrace_append hprefix tailTrace_3314422
  have hstable : (prefixWord ++ tailWord_3314422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314422).length < 2 ^ (prefixWord ++ tailWord_3314422).sum := by decide
  have hdescent : baseEnd_3314422 < baseStart_3314422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314435 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 1, 8]
def baseStart_3314435 : Nat := 118140960795 + 3314435 * 2 ^ 59
def prefixEnd_3314435 : Nat := 4983230072969 + 3 ^ 40 * 3314435 * 2
def baseEnd_3314435 : Nat := 1134598835389896661013131

theorem tailTrace_3314435 : CollatzResearch.WordTrace tailWord_3314435 prefixEnd_3314435 1134598835389896661013131 := by
  unfold tailWord_3314435
  simp only [CollatzResearch.WordTrace]
  refine ⟨120887375747375530276736759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80591583831583686851157839 120887375747375530276736759)
  ·
    refine ⟨181331063621063295415105139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120887375747375530276736759 181331063621063295415105139)
    ·
      refine ⟨271996595431594943122657709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181331063621063295415105139 271996595431594943122657709)
      ·
        refine ⟨101998723286848103670996641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271996595431594943122657709 101998723286848103670996641)
        ·
          refine ⟨76499042465136077753247481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101998723286848103670996641 76499042465136077753247481)
          ·
            refine ⟨57374281848852058314935611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76499042465136077753247481 57374281848852058314935611)
            ·
              refine ⟨86061422773278087472403417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57374281848852058314935611 86061422773278087472403417)
              ·
                refine ⟨64546067079958565604302563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86061422773278087472403417 64546067079958565604302563)
                ·
                  refine ⟨96819100619937848406453845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64546067079958565604302563 96819100619937848406453845)
                  ·
                    refine ⟨1134598835389896661013131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96819100619937848406453845 1134598835389896661013131)
                    ·
                      rfl

theorem cell22_3314435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_3314435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314435 prefixEnd_3314435 := by exact prefixLift 3314435
  have htrace : WordTrace (prefixWord ++ tailWord_3314435) baseStart_3314435 baseEnd_3314435 := by
    simpa [prefixWord, tailWord_3314435, baseEnd_3314435] using wordTrace_append hprefix tailTrace_3314435
  have hstable : (prefixWord ++ tailWord_3314435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314435).length < 2 ^ (prefixWord ++ tailWord_3314435).sum := by decide
  have hdescent : baseEnd_3314435 < baseStart_3314435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314437 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 5, 3]
def baseStart_3314437 : Nat := 118140960795 + 3314437 * 2 ^ 59
def prefixEnd_3314437 : Nat := 4983230072969 + 3 ^ 40 * 3314437 * 2
def baseEnd_3314437 : Nat := 1134599520030769322463125

theorem tailTrace_3314437 : CollatzResearch.WordTrace tailWord_3314437 prefixEnd_3314437 1134599520030769322463125 := by
  unfold tailWord_3314437
  simp only [CollatzResearch.WordTrace]
  refine ⟨120887448693368284618309565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80591632462245523078873043 120887448693368284618309565)
  ·
    refine ⟨45332793260013106731866087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120887448693368284618309565 45332793260013106731866087)
    ·
      refine ⟨67999189890019660097799131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45332793260013106731866087 67999189890019660097799131)
      ·
        refine ⟨101998784835029490146698697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67999189890019660097799131 101998784835029490146698697)
        ·
          refine ⟨76499088626272117610024023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101998784835029490146698697 76499088626272117610024023)
          ·
            refine ⟨114748632939408176415036035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76499088626272117610024023 114748632939408176415036035)
            ·
              refine ⟨172122949409112264622554053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114748632939408176415036035 172122949409112264622554053)
              ·
                refine ⟨32273053014208549616728885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172122949409112264622554053 32273053014208549616728885)
                ·
                  refine ⟨3025598720082051526568333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32273053014208549616728885 3025598720082051526568333)
                  ·
                    refine ⟨1134599520030769322463125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3025598720082051526568333 1134599520030769322463125)
                    ·
                      rfl

theorem cell22_3314437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_3314437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314437 prefixEnd_3314437 := by exact prefixLift 3314437
  have htrace : WordTrace (prefixWord ++ tailWord_3314437) baseStart_3314437 baseEnd_3314437 := by
    simpa [prefixWord, tailWord_3314437, baseEnd_3314437] using wordTrace_append hprefix tailTrace_3314437
  have hstable : (prefixWord ++ tailWord_3314437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314437).length < 2 ^ (prefixWord ++ tailWord_3314437).sum := by decide
  have hdescent : baseEnd_3314437 < baseStart_3314437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314578 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3314578 : Nat := 118140960795 + 3314578 * 2 ^ 59
def prefixEnd_3314578 : Nat := 4983230072969 + 3 ^ 40 * 3314578 * 2
def baseEnd_3314578 : Nat := 1134647787212291954687693

theorem tailTrace_3314578 : CollatzResearch.WordTrace tailWord_3314578 prefixEnd_3314578 1134647787212291954687693 := by
  unfold tailWord_3314578
  simp only [CollatzResearch.WordTrace]
  refine ⟨30223147846464366424798097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80595060923904977132794925 30223147846464366424798097)
  ·
    refine ⟨22667360884848274818598573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30223147846464366424798097 22667360884848274818598573)
    ·
      refine ⟨8500260331818103056974465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22667360884848274818598573 8500260331818103056974465)
      ·
        refine ⟨6375195248863577292730849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8500260331818103056974465 6375195248863577292730849)
        ·
          refine ⟨4781396436647682969548137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6375195248863577292730849 4781396436647682969548137)
          ·
            refine ⟨3586047327485762227161103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4781396436647682969548137 3586047327485762227161103)
            ·
              refine ⟨5379070991228643340741655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586047327485762227161103 5379070991228643340741655)
              ·
                refine ⟨8068606486842965011112483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5379070991228643340741655 8068606486842965011112483)
                ·
                  refine ⟨12102909730264447516668725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8068606486842965011112483 12102909730264447516668725)
                  ·
                    refine ⟨1134647787212291954687693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12102909730264447516668725 1134647787212291954687693)
                    ·
                      rfl

theorem cell22_3314578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3314578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314578 prefixEnd_3314578 := by exact prefixLift 3314578
  have htrace : WordTrace (prefixWord ++ tailWord_3314578) baseStart_3314578 baseEnd_3314578 := by
    simpa [prefixWord, tailWord_3314578, baseEnd_3314578] using wordTrace_append hprefix tailTrace_3314578
  have hstable : (prefixWord ++ tailWord_3314578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314578).length < 2 ^ (prefixWord ++ tailWord_3314578).sum := by decide
  have hdescent : baseEnd_3314578 < baseStart_3314578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314591 : List Nat := [1, 1, 2, 5, 2, 3, 2, 6]
def baseStart_3314591 : Nat := 118140960795 + 3314591 * 2 ^ 59
def prefixEnd_3314591 : Nat := 4983230072969 + 3 ^ 40 * 3314591 * 2
def baseEnd_3314591 : Nat := 126072470819773806012517

theorem tailTrace_3314591 : CollatzResearch.WordTrace tailWord_3314591 prefixEnd_3314591 126072470819773806012517 := by
  unfold tailWord_3314591
  simp only [CollatzResearch.WordTrace]
  refine ⟨120893065534810368919415627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80595377023206912612943751 120893065534810368919415627)
  ·
    refine ⟨181339598302215553379123441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120893065534810368919415627 181339598302215553379123441)
    ·
      refine ⟨136004698726661665034342581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181339598302215553379123441 136004698726661665034342581)
      ·
        refine ⟨12750440505624531096969617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 136004698726661665034342581 12750440505624531096969617)
        ·
          refine ⟨9562830379218398322727213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12750440505624531096969617 9562830379218398322727213)
          ·
            refine ⟨3586061392206899371022705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9562830379218398322727213 3586061392206899371022705)
            ·
              refine ⟨2689546044155174528267029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586061392206899371022705 2689546044155174528267029)
              ·
                refine ⟨126072470819773806012517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2689546044155174528267029 126072470819773806012517)
                ·
                  rfl

theorem cell22_3314591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 6].length) (baseStart_3314591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314591 prefixEnd_3314591 := by exact prefixLift 3314591
  have htrace : WordTrace (prefixWord ++ tailWord_3314591) baseStart_3314591 baseEnd_3314591 := by
    simpa [prefixWord, tailWord_3314591, baseEnd_3314591] using wordTrace_append hprefix tailTrace_3314591
  have hstable : (prefixWord ++ tailWord_3314591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314591).length < 2 ^ (prefixWord ++ tailWord_3314591).sum := by decide
  have hdescent : baseEnd_3314591 < baseStart_3314591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314614 : List Nat := [5, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_3314614 : Nat := 118140960795 + 3314614 * 2 ^ 59
def prefixEnd_3314614 : Nat := 4983230072969 + 3 ^ 40 * 3314614 * 2
def baseEnd_3314614 : Nat := 378220036915999953595861

theorem tailTrace_3314614 : CollatzResearch.WordTrace tailWord_3314614 prefixEnd_3314614 378220036915999953595861 := by
  unfold tailWord_3314614
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555869025857940240468931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80595936275818029231668597 7555869025857940240468931)
  ·
    refine ⟨11333803538786910360703397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7555869025857940240468931 11333803538786910360703397)
    ·
      refine ⟨2125088163522545692631887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11333803538786910360703397 2125088163522545692631887)
      ·
        refine ⟨3187632245283818538947831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2125088163522545692631887 3187632245283818538947831)
        ·
          refine ⟨4781448367925727808421747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187632245283818538947831 4781448367925727808421747)
          ·
            refine ⟨7172172551888591712632621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781448367925727808421747 7172172551888591712632621)
            ·
              refine ⟨2689564706958221892237233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7172172551888591712632621 2689564706958221892237233)
              ·
                refine ⟨2017173530218666419177925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689564706958221892237233 2017173530218666419177925)
                ·
                  refine ⟨378220036915999953595861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017173530218666419177925 378220036915999953595861)
                  ·
                    rfl

theorem cell22_3314614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_3314614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314614 prefixEnd_3314614 := by exact prefixLift 3314614
  have htrace : WordTrace (prefixWord ++ tailWord_3314614) baseStart_3314614 baseEnd_3314614 := by
    simpa [prefixWord, tailWord_3314614, baseEnd_3314614] using wordTrace_append hprefix tailTrace_3314614
  have hstable : (prefixWord ++ tailWord_3314614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314614).length < 2 ^ (prefixWord ++ tailWord_3314614).sum := by decide
  have hdescent : baseEnd_3314614 < baseStart_3314614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314674 : List Nat := [3, 2, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_3314674 : Nat := 118140960795 + 3314674 * 2 ^ 59
def prefixEnd_3314674 : Nat := 4983230072969 + 3 ^ 40 * 3314674 * 2
def baseEnd_3314674 : Nat := 1134680649974179704287399

theorem tailTrace_3314674 : CollatzResearch.WordTrace tailWord_3314674 prefixEnd_3314674 1134680649974179704287399 := by
  unfold tailWord_3314674
  simp only [CollatzResearch.WordTrace]
  refine ⟨30224023198377418523671769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80597395195673116063124717 30224023198377418523671769)
  ·
    refine ⟨22668017398783063892753827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30224023198377418523671769 22668017398783063892753827)
    ·
      refine ⟨34002026098174595839130741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22668017398783063892753827 34002026098174595839130741)
      ·
        refine ⟨3187689946703868359918507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34002026098174595839130741 3187689946703868359918507)
        ·
          refine ⟨4781534920055802539877761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187689946703868359918507 4781534920055802539877761)
          ·
            refine ⟨3586151190041851904908321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4781534920055802539877761 3586151190041851904908321)
            ·
              refine ⟨2689613392531388928681241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586151190041851904908321 2689613392531388928681241)
              ·
                refine ⟨2017210044398541696510931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689613392531388928681241 2017210044398541696510931)
                ·
                  refine ⟨3025815066597812544766397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017210044398541696510931 3025815066597812544766397)
                  ·
                    refine ⟨1134680649974179704287399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3025815066597812544766397 1134680649974179704287399)
                    ·
                      rfl

theorem cell22_3314674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_3314674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314674 prefixEnd_3314674 := by exact prefixLift 3314674
  have htrace : WordTrace (prefixWord ++ tailWord_3314674) baseStart_3314674 baseEnd_3314674 := by
    simpa [prefixWord, tailWord_3314674, baseEnd_3314674] using wordTrace_append hprefix tailTrace_3314674
  have hstable : (prefixWord ++ tailWord_3314674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314674).length < 2 ^ (prefixWord ++ tailWord_3314674).sum := by decide
  have hdescent : baseEnd_3314674 < baseStart_3314674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314681 : List Nat := [1, 2, 1, 3, 1, 3, 3, 4, 4]
def baseStart_3314681 : Nat := 118140960795 + 3314681 * 2 ^ 59
def prefixEnd_3314681 : Nat := 4983230072969 + 3 ^ 40 * 3314681 * 2
def baseEnd_3314681 : Nat := 378227682072411339787459

theorem tailTrace_3314681 : CollatzResearch.WordTrace tailWord_3314681 prefixEnd_3314681 378227682072411339787459 := by
  unfold tailWord_3314681
  simp only [CollatzResearch.WordTrace]
  refine ⟨120896348104484314290191897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80597565402989542860127931 120896348104484314290191897)
  ·
    refine ⟨90672261078363235717643923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120896348104484314290191897 90672261078363235717643923)
    ·
      refine ⟨136008391617544853576465885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90672261078363235717643923 136008391617544853576465885)
      ·
        refine ⟨51003146856579320091174707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136008391617544853576465885 51003146856579320091174707)
        ·
          refine ⟨76504720284868980136762061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51003146856579320091174707 76504720284868980136762061)
          ·
            refine ⟨28689270106825867551285773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76504720284868980136762061 28689270106825867551285773)
            ·
              refine ⟨10758476290059700331732165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28689270106825867551285773 10758476290059700331732165)
              ·
                refine ⟨2017214304386193812199781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10758476290059700331732165 2017214304386193812199781)
                ·
                  refine ⟨378227682072411339787459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017214304386193812199781 378227682072411339787459)
                  ·
                    rfl

theorem cell22_3314681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 4, 4].length) (baseStart_3314681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314681 prefixEnd_3314681 := by exact prefixLift 3314681
  have htrace : WordTrace (prefixWord ++ tailWord_3314681) baseStart_3314681 baseEnd_3314681 := by
    simpa [prefixWord, tailWord_3314681, baseEnd_3314681] using wordTrace_append hprefix tailTrace_3314681
  have hstable : (prefixWord ++ tailWord_3314681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314681).length < 2 ^ (prefixWord ++ tailWord_3314681).sum := by decide
  have hdescent : baseEnd_3314681 < baseStart_3314681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314696 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 1, 5]
def baseStart_3314696 : Nat := 118140960795 + 3314696 * 2 ^ 59
def prefixEnd_3314696 : Nat := 4983230072969 + 3 ^ 40 * 3314696 * 2
def baseEnd_3314696 : Nat := 1134688181023778980237331

theorem tailTrace_3314696 : CollatzResearch.WordTrace tailWord_3314696 prefixEnd_3314696 1134688181023778980237331 := by
  unfold tailWord_3314696
  simp only [CollatzResearch.WordTrace]
  refine ⟨60448447599714985925993971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80597930132953314567991961 60448447599714985925993971)
  ·
    refine ⟨90672671399572478888990957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60448447599714985925993971 90672671399572478888990957)
    ·
      refine ⟨34002251774839679583371609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90672671399572478888990957 34002251774839679583371609)
      ·
        refine ⟨25501688831129759687528707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34002251774839679583371609 25501688831129759687528707)
        ·
          refine ⟨38252533246694639531293061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25501688831129759687528707 38252533246694639531293061)
          ·
            refine ⟨7172349983755244912117449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38252533246694639531293061 7172349983755244912117449)
            ·
              refine ⟨5379262487816433684088087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7172349983755244912117449 5379262487816433684088087)
              ·
                refine ⟨8068893731724650526132131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5379262487816433684088087 8068893731724650526132131)
                ·
                  refine ⟨12103340597586975789198197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8068893731724650526132131 12103340597586975789198197)
                  ·
                    refine ⟨1134688181023778980237331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12103340597586975789198197 1134688181023778980237331)
                    ·
                      rfl

theorem cell22_3314696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_3314696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314696 prefixEnd_3314696 := by exact prefixLift 3314696
  have htrace : WordTrace (prefixWord ++ tailWord_3314696) baseStart_3314696 baseEnd_3314696 := by
    simpa [prefixWord, tailWord_3314696, baseEnd_3314696] using wordTrace_append hprefix tailTrace_3314696
  have hstable : (prefixWord ++ tailWord_3314696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314696).length < 2 ^ (prefixWord ++ tailWord_3314696).sum := by decide
  have hdescent : baseEnd_3314696 < baseStart_3314696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314711 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 1, 6]
def baseStart_3314711 : Nat := 118140960795 + 3314711 * 2 ^ 59
def prefixEnd_3314711 : Nat := 4983230072969 + 3 ^ 40 * 3314711 * 2
def baseEnd_3314711 : Nat := 1134693315830323941112285

theorem tailTrace_3314711 : CollatzResearch.WordTrace tailWord_3314711 prefixEnd_3314711 1134693315830323941112285 := by
  unfold tailWord_3314711
  simp only [CollatzResearch.WordTrace]
  refine ⟨120897442294375629413783987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80598294862917086275855991 120897442294375629413783987)
  ·
    refine ⟨181346163441563444120675981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120897442294375629413783987 181346163441563444120675981)
    ·
      refine ⟨68004811290586291545253493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181346163441563444120675981 68004811290586291545253493)
      ·
        refine ⟨6375451058492464832367515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68004811290586291545253493 6375451058492464832367515)
        ·
          refine ⟨9563176587738697248551273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375451058492464832367515 9563176587738697248551273)
          ·
            refine ⟨7172382440804022936413455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9563176587738697248551273 7172382440804022936413455)
            ·
              refine ⟨10758573661206034404620183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7172382440804022936413455 10758573661206034404620183)
              ·
                refine ⟨16137860491809051606930275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10758573661206034404620183 16137860491809051606930275)
                ·
                  refine ⟨24206790737713577410395413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16137860491809051606930275 24206790737713577410395413)
                  ·
                    refine ⟨1134693315830323941112285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24206790737713577410395413 1134693315830323941112285)
                    ·
                      rfl

theorem cell22_3314711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_3314711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314711 prefixEnd_3314711 := by exact prefixLift 3314711
  have htrace : WordTrace (prefixWord ++ tailWord_3314711) baseStart_3314711 baseEnd_3314711 := by
    simpa [prefixWord, tailWord_3314711, baseEnd_3314711] using wordTrace_append hprefix tailTrace_3314711
  have hstable : (prefixWord ++ tailWord_3314711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314711).length < 2 ^ (prefixWord ++ tailWord_3314711).sum := by decide
  have hdescent : baseEnd_3314711 < baseStart_3314711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314717 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_3314717 : Nat := 118140960795 + 3314717 * 2 ^ 59
def prefixEnd_3314717 : Nat := 4983230072969 + 3 ^ 40 * 3314717 * 2
def baseEnd_3314717 : Nat := 1134695369752941925462267

theorem tailTrace_3314717 : CollatzResearch.WordTrace tailWord_3314717 prefixEnd_3314717 1134695369752941925462267 := by
  unfold tailWord_3314717
  simp only [CollatzResearch.WordTrace]
  refine ⟨120897661132353892438502405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80598440754902594959001603 120897661132353892438502405)
  ·
    refine ⟨22668311462316354832219201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120897661132353892438502405 22668311462316354832219201)
    ·
      refine ⟨17001233596737266124164401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22668311462316354832219201 17001233596737266124164401)
      ·
        refine ⟨12750925197552949593123301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17001233596737266124164401 12750925197552949593123301)
        ·
          refine ⟨2390798474541178048710619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12750925197552949593123301 2390798474541178048710619)
          ·
            refine ⟨3586197711811767073065929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2390798474541178048710619 3586197711811767073065929)
            ·
              refine ⟨2689648283858825304799447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3586197711811767073065929 2689648283858825304799447)
              ·
                refine ⟨4034472425788237957199171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2689648283858825304799447 4034472425788237957199171)
                ·
                  refine ⟨6051708638682356935798757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034472425788237957199171 6051708638682356935798757)
                  ·
                    refine ⟨1134695369752941925462267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6051708638682356935798757 1134695369752941925462267)
                    ·
                      rfl

theorem cell22_3314717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_3314717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314717 prefixEnd_3314717 := by exact prefixLift 3314717
  have htrace : WordTrace (prefixWord ++ tailWord_3314717) baseStart_3314717 baseEnd_3314717 := by
    simpa [prefixWord, tailWord_3314717, baseEnd_3314717] using wordTrace_append hprefix tailTrace_3314717
  have hstable : (prefixWord ++ tailWord_3314717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314717).length < 2 ^ (prefixWord ++ tailWord_3314717).sum := by decide
  have hdescent : baseEnd_3314717 < baseStart_3314717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314769 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 1, 7]
def baseStart_3314769 : Nat := 118140960795 + 3314769 * 2 ^ 59
def prefixEnd_3314769 : Nat := 4983230072969 + 3 ^ 40 * 3314769 * 2
def baseEnd_3314769 : Nat := 1134713170415631123162107

theorem tailTrace_3314769 : CollatzResearch.WordTrace tailWord_3314769 prefixEnd_3314769 1134713170415631123162107 := by
  unfold tailWord_3314769
  simp only [CollatzResearch.WordTrace]
  refine ⟨120899557728165505319395361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80599705152110336879596907 120899557728165505319395361)
  ·
    refine ⟨90674668296124128989546521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120899557728165505319395361 90674668296124128989546521)
    ·
      refine ⟨68006001222093096742159891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90674668296124128989546521 68006001222093096742159891)
      ·
        refine ⟨102009001833139645113239837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68006001222093096742159891 102009001833139645113239837)
        ·
          refine ⟨38253375687427366917464939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102009001833139645113239837 38253375687427366917464939)
          ·
            refine ⟨57380063531141050376197409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38253375687427366917464939 57380063531141050376197409)
            ·
              refine ⟨43035047648355787782148057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57380063531141050376197409 43035047648355787782148057)
              ·
                refine ⟨32276285736266840836611043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43035047648355787782148057 32276285736266840836611043)
                ·
                  refine ⟨48414428604400261254916565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32276285736266840836611043 48414428604400261254916565)
                  ·
                    refine ⟨1134713170415631123162107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48414428604400261254916565 1134713170415631123162107)
                    ·
                      rfl

theorem cell22_3314769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_3314769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314769 prefixEnd_3314769 := by exact prefixLift 3314769
  have htrace : WordTrace (prefixWord ++ tailWord_3314769) baseStart_3314769 baseEnd_3314769 := by
    simpa [prefixWord, tailWord_3314769, baseEnd_3314769] using wordTrace_append hprefix tailTrace_3314769
  have hstable : (prefixWord ++ tailWord_3314769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314769).length < 2 ^ (prefixWord ++ tailWord_3314769).sum := by decide
  have hdescent : baseEnd_3314769 < baseStart_3314769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314792 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 3, 3]
def baseStart_3314792 : Nat := 118140960795 + 3314792 * 2 ^ 59
def prefixEnd_3314792 : Nat := 4983230072969 + 3 ^ 40 * 3314792 * 2
def baseEnd_3314792 : Nat := 1134721043785666729837037

theorem tailTrace_3314792 : CollatzResearch.WordTrace tailWord_3314792 prefixEnd_3314792 1134721043785666729837037 := by
  unfold tailWord_3314792
  simp only [CollatzResearch.WordTrace]
  refine ⟨60450198303541090123741315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80600264404721453498321753 60450198303541090123741315)
  ·
    refine ⟨90675297455311635185611973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60450198303541090123741315 90675297455311635185611973)
    ·
      refine ⟨17001618272870931597302245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90675297455311635185611973 17001618272870931597302245)
      ·
        refine ⟨3187803426163299674494171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17001618272870931597302245 3187803426163299674494171)
        ·
          refine ⟨4781705139244949511741257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187803426163299674494171 4781705139244949511741257)
          ·
            refine ⟨3586278854433712133805943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4781705139244949511741257 3586278854433712133805943)
            ·
              refine ⟨5379418281650568200708915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586278854433712133805943 5379418281650568200708915)
              ·
                refine ⟨8069127422475852301063373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5379418281650568200708915 8069127422475852301063373)
                ·
                  refine ⟨3025922783428444612898765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8069127422475852301063373 3025922783428444612898765)
                  ·
                    refine ⟨1134721043785666729837037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3025922783428444612898765 1134721043785666729837037)
                    ·
                      rfl

theorem cell22_3314792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_3314792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314792 prefixEnd_3314792 := by exact prefixLift 3314792
  have htrace : WordTrace (prefixWord ++ tailWord_3314792) baseStart_3314792 baseEnd_3314792 := by
    simpa [prefixWord, tailWord_3314792, baseEnd_3314792] using wordTrace_append hprefix tailTrace_3314792
  have hstable : (prefixWord ++ tailWord_3314792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314792).length < 2 ^ (prefixWord ++ tailWord_3314792).sum := by decide
  have hdescent : baseEnd_3314792 < baseStart_3314792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314805 : List Nat := [1, 3, 4, 3, 1, 1, 1, 3, 5]
def baseStart_3314805 : Nat := 118140960795 + 3314805 * 2 ^ 59
def prefixEnd_3314805 : Nat := 4983230072969 + 3 ^ 40 * 3314805 * 2
def baseEnd_3314805 : Nat := 378241831317113009753999

theorem tailTrace_3314805 : CollatzResearch.WordTrace tailWord_3314805 prefixEnd_3314805 378241831317113009753999 := by
  unfold tailWord_3314805
  simp only [CollatzResearch.WordTrace]
  refine ⟨120900870756035083467705869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80600580504023388978470579 120900870756035083467705869)
  ·
    refine ⟨45337826533513156300389701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120900870756035083467705869 45337826533513156300389701)
    ·
      refine ⟨8500842475033716806323069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45337826533513156300389701 8500842475033716806323069)
      ·
        refine ⟨3187815928137643802371151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8500842475033716806323069 3187815928137643802371151)
        ·
          refine ⟨4781723892206465703556727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187815928137643802371151 4781723892206465703556727)
          ·
            refine ⟨7172585838309698555335091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781723892206465703556727 7172585838309698555335091)
            ·
              refine ⟨10758878757464547833002637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7172585838309698555335091 10758878757464547833002637)
              ·
                refine ⟨4034579534049205437375989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10758878757464547833002637 4034579534049205437375989)
                ·
                  refine ⟨378241831317113009753999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4034579534049205437375989 378241831317113009753999)
                  ·
                    rfl

theorem cell22_3314805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_3314805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314805 prefixEnd_3314805 := by exact prefixLift 3314805
  have htrace : WordTrace (prefixWord ++ tailWord_3314805) baseStart_3314805 baseEnd_3314805 := by
    simpa [prefixWord, tailWord_3314805, baseEnd_3314805] using wordTrace_append hprefix tailTrace_3314805
  have hstable : (prefixWord ++ tailWord_3314805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314805).length < 2 ^ (prefixWord ++ tailWord_3314805).sum := by decide
  have hdescent : baseEnd_3314805 < baseStart_3314805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314865 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 2, 3]
def baseStart_3314865 : Nat := 118140960795 + 3314865 * 2 ^ 59
def prefixEnd_3314865 : Nat := 4983230072969 + 3 ^ 40 * 3314865 * 2
def baseEnd_3314865 : Nat := 1134746033177518872761813

theorem tailTrace_3314865 : CollatzResearch.WordTrace tailWord_3314865 prefixEnd_3314865 1134746033177518872761813 := by
  unfold tailWord_3314865
  simp only [CollatzResearch.WordTrace]
  refine ⟨120903059135817713714890049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80602039423878475809926699 120903059135817713714890049)
  ·
    refine ⟨90677294351863285286167537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120903059135817713714890049 90677294351863285286167537)
    ·
      refine ⟨68007970763897463964625653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90677294351863285286167537 68007970763897463964625653)
      ·
        refine ⟨6375747259115387246683655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68007970763897463964625653 6375747259115387246683655)
        ·
          refine ⟨9563620888673080870025483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6375747259115387246683655 9563620888673080870025483)
          ·
            refine ⟨14345431333009621305038225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9563620888673080870025483 14345431333009621305038225)
            ·
              refine ⟨10759073499757215978778669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14345431333009621305038225 10759073499757215978778669)
              ·
                refine ⟨4034652562408955992042001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10759073499757215978778669 4034652562408955992042001)
                ·
                  refine ⟨3025989421806716994031501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4034652562408955992042001 3025989421806716994031501)
                  ·
                    refine ⟨1134746033177518872761813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3025989421806716994031501 1134746033177518872761813)
                    ·
                      rfl

theorem cell22_3314865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_3314865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314865 prefixEnd_3314865 := by exact prefixLift 3314865
  have htrace : WordTrace (prefixWord ++ tailWord_3314865) baseStart_3314865 baseEnd_3314865 := by
    simpa [prefixWord, tailWord_3314865, baseEnd_3314865] using wordTrace_append hprefix tailTrace_3314865
  have hstable : (prefixWord ++ tailWord_3314865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314865).length < 2 ^ (prefixWord ++ tailWord_3314865).sum := by decide
  have hdescent : baseEnd_3314865 < baseStart_3314865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314880 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 2, 4]
def baseStart_3314880 : Nat := 118140960795 + 3314880 * 2 ^ 59
def prefixEnd_3314880 : Nat := 4983230072969 + 3 ^ 40 * 3314880 * 2
def baseEnd_3314880 : Nat := 1134751167984063833636767

theorem tailTrace_3314880 : CollatzResearch.WordTrace tailWord_3314880 prefixEnd_3314880 1134751167984063833636767 := by
  unfold tailWord_3314880
  simp only [CollatzResearch.WordTrace]
  refine ⟨60451803115381685638343047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80602404153842247517790729 60451803115381685638343047)
  ·
    refine ⟨90677704673072528457514571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60451803115381685638343047 90677704673072528457514571)
    ·
      refine ⟨136016557009608792686271857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90677704673072528457514571 136016557009608792686271857)
      ·
        refine ⟨102012417757206594514703893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136016557009608792686271857 102012417757206594514703893)
        ·
          refine ⟨4781832082369059117876745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 102012417757206594514703893 4781832082369059117876745)
          ·
            refine ⟨3586374061776794338407559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4781832082369059117876745 3586374061776794338407559)
            ·
              refine ⟨5379561092665191507611339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586374061776794338407559 5379561092665191507611339)
              ·
                refine ⟨8069341638997787261417009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5379561092665191507611339 8069341638997787261417009)
                ·
                  refine ⟨6052006229248340446062757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8069341638997787261417009 6052006229248340446062757)
                  ·
                    refine ⟨1134751167984063833636767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052006229248340446062757 1134751167984063833636767)
                    ·
                      rfl

theorem cell22_3314880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 2, 4].length) (baseStart_3314880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314880 prefixEnd_3314880 := by exact prefixLift 3314880
  have htrace : WordTrace (prefixWord ++ tailWord_3314880) baseStart_3314880 baseEnd_3314880 := by
    simpa [prefixWord, tailWord_3314880, baseEnd_3314880] using wordTrace_append hprefix tailTrace_3314880
  have hstable : (prefixWord ++ tailWord_3314880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314880).length < 2 ^ (prefixWord ++ tailWord_3314880).sum := by decide
  have hdescent : baseEnd_3314880 < baseStart_3314880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314953 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 1, 4]
def baseStart_3314953 : Nat := 118140960795 + 3314953 * 2 ^ 59
def prefixEnd_3314953 : Nat := 4983230072969 + 3 ^ 40 * 3314953 * 2
def baseEnd_3314953 : Nat := 1134776157375915976561543

theorem tailTrace_3314953 : CollatzResearch.WordTrace tailWord_3314953 prefixEnd_3314953 1134776157375915976561543 := by
  unfold tailWord_3314953
  simp only [CollatzResearch.WordTrace]
  refine ⟨120906268759498904744093513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80604179172999269829395675 120906268759498904744093513)
  ·
    refine ⟨90679701569624178558070135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120906268759498904744093513 90679701569624178558070135)
    ·
      refine ⟨136019552354436267837105203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90679701569624178558070135 136019552354436267837105203)
      ·
        refine ⟨204029328531654401755657805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136019552354436267837105203 204029328531654401755657805)
        ·
          refine ⟨76510998199370400658371677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204029328531654401755657805 76510998199370400658371677)
          ·
            refine ⟨28691624324763900246889379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76510998199370400658371677 28691624324763900246889379)
            ·
              refine ⟨43037436487145850370334069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28691624324763900246889379 43037436487145850370334069)
              ·
                refine ⟨4034759670669923472218819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43037436487145850370334069 4034759670669923472218819)
                ·
                  refine ⟨6052139506004885208328229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4034759670669923472218819 6052139506004885208328229)
                  ·
                    refine ⟨1134776157375915976561543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052139506004885208328229 1134776157375915976561543)
                    ·
                      rfl

theorem cell22_3314953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 4].length) (baseStart_3314953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314953 prefixEnd_3314953 := by exact prefixLift 3314953
  have htrace : WordTrace (prefixWord ++ tailWord_3314953) baseStart_3314953 baseEnd_3314953 := by
    simpa [prefixWord, tailWord_3314953, baseEnd_3314953] using wordTrace_append hprefix tailTrace_3314953
  have hstable : (prefixWord ++ tailWord_3314953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314953).length < 2 ^ (prefixWord ++ tailWord_3314953).sum := by decide
  have hdescent : baseEnd_3314953 < baseStart_3314953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3314968 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 6]
def baseStart_3314968 : Nat := 118140960795 + 3314968 * 2 ^ 59
def prefixEnd_3314968 : Nat := 4983230072969 + 3 ^ 40 * 3314968 * 2
def baseEnd_3314968 : Nat := 378260430727486979145499

theorem tailTrace_3314968 : CollatzResearch.WordTrace tailWord_3314968 prefixEnd_3314968 378260430727486979145499 := by
  unfold tailWord_3314968
  simp only [CollatzResearch.WordTrace]
  refine ⟨60453407927222281152944779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80604543902963041537259705 60453407927222281152944779)
  ·
    refine ⟨90680111890833421729417169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60453407927222281152944779 90680111890833421729417169)
    ·
      refine ⟨68010083918125066297062877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90680111890833421729417169 68010083918125066297062877)
      ·
        refine ⟨25503781469296899861398579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68010083918125066297062877 25503781469296899861398579)
        ·
          refine ⟨38255672203945349792097869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25503781469296899861398579 38255672203945349792097869)
          ·
            refine ⟨14345877076479506172036701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38255672203945349792097869 14345877076479506172036701)
            ·
              refine ⟨5379703903679814814513763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14345877076479506172036701 5379703903679814814513763)
              ·
                refine ⟨8069555855519722221770645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5379703903679814814513763 8069555855519722221770645)
                ·
                  refine ⟨378260430727486979145499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8069555855519722221770645 378260430727486979145499)
                  ·
                    rfl

theorem cell22_3314968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_3314968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3314968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3314968 prefixEnd_3314968 := by exact prefixLift 3314968
  have htrace : WordTrace (prefixWord ++ tailWord_3314968) baseStart_3314968 baseEnd_3314968 := by
    simpa [prefixWord, tailWord_3314968, baseEnd_3314968] using wordTrace_append hprefix tailTrace_3314968
  have hstable : (prefixWord ++ tailWord_3314968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3314968).length < 2 ^ (prefixWord ++ tailWord_3314968).sum := by decide
  have hdescent : baseEnd_3314968 < baseStart_3314968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3314968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315045 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 3, 3]
def baseStart_3315045 : Nat := 118140960795 + 3315045 * 2 ^ 59
def prefixEnd_3315045 : Nat := 4983230072969 + 3 ^ 40 * 3315045 * 2
def baseEnd_3315045 : Nat := 1134807650856058403261261

theorem tailTrace_3315045 : CollatzResearch.WordTrace tailWord_3315045 prefixEnd_3315045 1134807650856058403261261 := by
  unfold tailWord_3315045
  simp only [CollatzResearch.WordTrace]
  refine ⟨120909624275165604456442589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80606416183443736304295059 120909624275165604456442589)
  ·
    refine ⟨45341109103187101671165971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120909624275165604456442589 45341109103187101671165971)
    ·
      refine ⟨68011663654780652506748957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45341109103187101671165971 68011663654780652506748957)
      ·
        refine ⟨25504373870542744690030859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68011663654780652506748957 25504373870542744690030859)
        ·
          refine ⟨38256560805814117035046289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25504373870542744690030859 38256560805814117035046289)
          ·
            refine ⟨28692420604360587776284717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38256560805814117035046289 28692420604360587776284717)
            ·
              refine ⟨10759657726635220416106769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28692420604360587776284717 10759657726635220416106769)
              ·
                refine ⟨8069743294976415312080077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10759657726635220416106769 8069743294976415312080077)
                ·
                  refine ⟨3026153735616155742030029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8069743294976415312080077 3026153735616155742030029)
                  ·
                    refine ⟨1134807650856058403261261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026153735616155742030029 1134807650856058403261261)
                    ·
                      rfl

theorem cell22_3315045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_3315045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315045 prefixEnd_3315045 := by exact prefixLift 3315045
  have htrace : WordTrace (prefixWord ++ tailWord_3315045) baseStart_3315045 baseEnd_3315045 := by
    simpa [prefixWord, tailWord_3315045, baseEnd_3315045] using wordTrace_append hprefix tailTrace_3315045
  have hstable : (prefixWord ++ tailWord_3315045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315045).length < 2 ^ (prefixWord ++ tailWord_3315045).sum := by decide
  have hdescent : baseEnd_3315045 < baseStart_3315045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315058 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_3315058 : Nat := 118140960795 + 3315058 * 2 ^ 59
def prefixEnd_3315058 : Nat := 4983230072969 + 3 ^ 40 * 3315058 * 2
def baseEnd_3315058 : Nat := 378270700340576900895407

theorem tailTrace_3315058 : CollatzResearch.WordTrace tailWord_3315058 prefixEnd_3315058 378270700340576900895407 := by
  unfold tailWord_3315058
  simp only [CollatzResearch.WordTrace]
  refine ⟨30227524606029626919166457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80606732282745671784443885 30227524606029626919166457)
  ·
    refine ⟨22670643454522220189374843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30227524606029626919166457 22670643454522220189374843)
    ·
      refine ⟨34005965181783330284062265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22670643454522220189374843 34005965181783330284062265)
      ·
        refine ⟨25504473886337497713046699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34005965181783330284062265 25504473886337497713046699)
        ·
          refine ⟨38256710829506246569570049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25504473886337497713046699 38256710829506246569570049)
          ·
            refine ⟨28692533122129684927177537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38256710829506246569570049 28692533122129684927177537)
            ·
              refine ⟨21519399841597263695383153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28692533122129684927177537 21519399841597263695383153)
              ·
                refine ⟨16139549881197947771537365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21519399841597263695383153 16139549881197947771537365)
                ·
                  refine ⟨378270700340576900895407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16139549881197947771537365 378270700340576900895407)
                  ·
                    rfl

theorem cell22_3315058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_3315058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315058 prefixEnd_3315058 := by exact prefixLift 3315058
  have htrace : WordTrace (prefixWord ++ tailWord_3315058) baseStart_3315058 baseEnd_3315058 := by
    simpa [prefixWord, tailWord_3315058, baseEnd_3315058] using wordTrace_append hprefix tailTrace_3315058
  have hstable : (prefixWord ++ tailWord_3315058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315058).length < 2 ^ (prefixWord ++ tailWord_3315058).sum := by decide
  have hdescent : baseEnd_3315058 < baseStart_3315058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315075 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 5]
def baseStart_3315075 : Nat := 118140960795 + 3315075 * 2 ^ 59
def prefixEnd_3315075 : Nat := 4983230072969 + 3 ^ 40 * 3315075 * 2
def baseEnd_3315075 : Nat := 378272640156382775003723

theorem tailTrace_3315075 : CollatzResearch.WordTrace tailWord_3315075 prefixEnd_3315075 378272640156382775003723 := by
  unfold tailWord_3315075
  simp only [CollatzResearch.WordTrace]
  refine ⟨120910718465056919580034679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80607145643371279720023119 120910718465056919580034679)
  ·
    refine ⟨181366077697585379370052019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120910718465056919580034679 181366077697585379370052019)
    ·
      refine ⟨272049116546378069055078029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181366077697585379370052019 272049116546378069055078029)
      ·
        refine ⟨102018418704891775895654261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272049116546378069055078029 102018418704891775895654261)
        ·
          refine ⟨9564226753583603990217587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102018418704891775895654261 9564226753583603990217587)
          ·
            refine ⟨14346340130375405985326381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564226753583603990217587 14346340130375405985326381)
            ·
              refine ⟨5379877548890777244497393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14346340130375405985326381 5379877548890777244497393)
              ·
                refine ⟨4034908161668082933373045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5379877548890777244497393 4034908161668082933373045)
                ·
                  refine ⟨378272640156382775003723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4034908161668082933373045 378272640156382775003723)
                  ·
                    rfl

theorem cell22_3315075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 5].length) (baseStart_3315075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315075 prefixEnd_3315075 := by exact prefixLift 3315075
  have htrace : WordTrace (prefixWord ++ tailWord_3315075) baseStart_3315075 baseEnd_3315075 := by
    simpa [prefixWord, tailWord_3315075, baseEnd_3315075] using wordTrace_append hprefix tailTrace_3315075
  have hstable : (prefixWord ++ tailWord_3315075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315075).length < 2 ^ (prefixWord ++ tailWord_3315075).sum := by decide
  have hdescent : baseEnd_3315075 < baseStart_3315075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315120 : List Nat := [2, 1, 1, 1, 2, 1, 1, 9, 4]
def baseStart_3315120 : Nat := 118140960795 + 3315120 * 2 ^ 59
def prefixEnd_3315120 : Nat := 4983230072969 + 3 ^ 40 * 3315120 * 2
def baseEnd_3315120 : Nat := 378277774962927735878677

theorem tailTrace_3315120 : CollatzResearch.WordTrace tailWord_3315120 prefixEnd_3315120 378277774962927735878677 := by
  unfold tailWord_3315120
  simp only [CollatzResearch.WordTrace]
  refine ⟨60456179874946946132711407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80608239833262594843615209 60456179874946946132711407)
  ·
    refine ⟨90684269812420419199067111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60456179874946946132711407 90684269812420419199067111)
    ·
      refine ⟨136026404718630628798600667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90684269812420419199067111 136026404718630628798600667)
      ·
        refine ⟨204039607077945943197901001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136026404718630628798600667 204039607077945943197901001)
        ·
          refine ⟨153029705308459457398425751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204039607077945943197901001 153029705308459457398425751)
          ·
            refine ⟨229544557962689186097638627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153029705308459457398425751 229544557962689186097638627)
            ·
              refine ⟨344316836944033779146457941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229544557962689186097638627 344316836944033779146457941)
              ·
                refine ⟨2017481466468947924686277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 344316836944033779146457941 2017481466468947924686277)
                ·
                  refine ⟨378277774962927735878677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017481466468947924686277 378277774962927735878677)
                  ·
                    rfl

theorem cell22_3315120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 9, 4].length) (baseStart_3315120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315120 prefixEnd_3315120 := by exact prefixLift 3315120
  have htrace : WordTrace (prefixWord ++ tailWord_3315120) baseStart_3315120 baseEnd_3315120 := by
    simpa [prefixWord, tailWord_3315120, baseEnd_3315120] using wordTrace_append hprefix tailTrace_3315120
  have hstable : (prefixWord ++ tailWord_3315120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315120).length < 2 ^ (prefixWord ++ tailWord_3315120).sum := by decide
  have hdescent : baseEnd_3315120 < baseStart_3315120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315156 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_3315156 : Nat := 118140960795 + 3315156 * 2 ^ 59
def prefixEnd_3315156 : Nat := 4983230072969 + 3 ^ 40 * 3315156 * 2
def baseEnd_3315156 : Nat := 1134845648424491113735921

theorem tailTrace_3315156 : CollatzResearch.WordTrace tailWord_3315156 prefixEnd_3315156 1134845648424491113735921 := by
  unfold tailWord_3315156
  simp only [CollatzResearch.WordTrace]
  refine ⟨60456836388881735206866661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80609115185175646942488881 60456836388881735206866661)
  ·
    refine ⟨11335656822915325351287499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60456836388881735206866661 11335656822915325351287499)
    ·
      refine ⟨17003485234372988026931249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11335656822915325351287499 17003485234372988026931249)
      ·
        refine ⟨12752613925779741020198437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17003485234372988026931249 12752613925779741020198437)
        ·
          refine ⟨2391115111083701441287207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12752613925779741020198437 2391115111083701441287207)
          ·
            refine ⟨3586672666625552161930811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391115111083701441287207 3586672666625552161930811)
            ·
              refine ⟨5380008999938328242896217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586672666625552161930811 5380008999938328242896217)
              ·
                refine ⟨4035006749953746182172163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5380008999938328242896217 4035006749953746182172163)
                ·
                  refine ⟨6052510124930619273258245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035006749953746182172163 6052510124930619273258245)
                  ·
                    refine ⟨1134845648424491113735921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052510124930619273258245 1134845648424491113735921)
                    ·
                      rfl

theorem cell22_3315156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_3315156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315156 prefixEnd_3315156 := by exact prefixLift 3315156
  have htrace : WordTrace (prefixWord ++ tailWord_3315156) baseStart_3315156 baseEnd_3315156 := by
    simpa [prefixWord, tailWord_3315156, baseEnd_3315156] using wordTrace_append hprefix tailTrace_3315156
  have hstable : (prefixWord ++ tailWord_3315156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315156).length < 2 ^ (prefixWord ++ tailWord_3315156).sum := by decide
  have hdescent : baseEnd_3315156 < baseStart_3315156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315165 : List Nat := [1, 4, 3, 1, 1, 2, 2, 8]
def baseStart_3315165 : Nat := 118140960795 + 3315165 * 2 ^ 59
def prefixEnd_3315165 : Nat := 4983230072969 + 3 ^ 40 * 3315165 * 2
def baseEnd_3315165 : Nat := 126094303256490898917877

theorem tailTrace_3315165 : CollatzResearch.WordTrace tailWord_3315165 prefixEnd_3315165 126094303256490898917877 := by
  unfold tailWord_3315165
  simp only [CollatzResearch.WordTrace]
  refine ⟨120914001034730864950810949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80609334023153909967207299 120914001034730864950810949)
  ·
    refine ⟨22671375194012037178277053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120914001034730864950810949 22671375194012037178277053)
    ·
      refine ⟨8501765697754513941853895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22671375194012037178277053 8501765697754513941853895)
      ·
        refine ⟨12752648546631770912780843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8501765697754513941853895 12752648546631770912780843)
        ·
          refine ⟨19128972819947656369171265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12752648546631770912780843 19128972819947656369171265)
          ·
            refine ⟨14346729614960742276878449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19128972819947656369171265 14346729614960742276878449)
            ·
              refine ⟨10760047211220556707658837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14346729614960742276878449 10760047211220556707658837)
              ·
                refine ⟨126094303256490898917877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10760047211220556707658837 126094303256490898917877)
                ·
                  rfl

theorem cell22_3315165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 8].length) (baseStart_3315165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315165 prefixEnd_3315165 := by exact prefixLift 3315165
  have htrace : WordTrace (prefixWord ++ tailWord_3315165) baseStart_3315165 baseEnd_3315165 := by
    simpa [prefixWord, tailWord_3315165, baseEnd_3315165] using wordTrace_append hprefix tailTrace_3315165
  have hstable : (prefixWord ++ tailWord_3315165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315165).length < 2 ^ (prefixWord ++ tailWord_3315165).sum := by decide
  have hdescent : baseEnd_3315165 < baseStart_3315165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315180 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 7, 3]
def baseStart_3315180 : Nat := 118140960795 + 3315180 * 2 ^ 59
def prefixEnd_3315180 : Nat := 4983230072969 + 3 ^ 40 * 3315180 * 2
def baseEnd_3315180 : Nat := 1134853864114963051135847

theorem tailTrace_3315180 : CollatzResearch.WordTrace tailWord_3315180 prefixEnd_3315180 1134853864114963051135847 := by
  unfold tailWord_3315180
  simp only [CollatzResearch.WordTrace]
  refine ⟨60457274064838261256303497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80609698753117681675071329 60457274064838261256303497)
  ·
    refine ⟨45342955548628695942227623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60457274064838261256303497 45342955548628695942227623)
    ·
      refine ⟨68014433322943043913341435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45342955548628695942227623 68014433322943043913341435)
      ·
        refine ⟨102021649984414565870012153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68014433322943043913341435 102021649984414565870012153)
        ·
          refine ⟨76516237488310924402509115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102021649984414565870012153 76516237488310924402509115)
          ·
            refine ⟨114774356232466386603763673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76516237488310924402509115 114774356232466386603763673)
            ·
              refine ⟨86080767174349789952822755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114774356232466386603763673 86080767174349789952822755)
              ·
                refine ⟨129121150761524684929234133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86080767174349789952822755 129121150761524684929234133)
                ·
                  refine ⟨3026276970973234803028925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 129121150761524684929234133 3026276970973234803028925)
                  ·
                    refine ⟨1134853864114963051135847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026276970973234803028925 1134853864114963051135847)
                    ·
                      rfl

theorem cell22_3315180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_3315180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315180 prefixEnd_3315180 := by exact prefixLift 3315180
  have htrace : WordTrace (prefixWord ++ tailWord_3315180) baseStart_3315180 baseEnd_3315180 := by
    simpa [prefixWord, tailWord_3315180, baseEnd_3315180] using wordTrace_append hprefix tailTrace_3315180
  have hstable : (prefixWord ++ tailWord_3315180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315180).length < 2 ^ (prefixWord ++ tailWord_3315180).sum := by decide
  have hdescent : baseEnd_3315180 < baseStart_3315180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315214 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_3315214 : Nat := 118140960795 + 3315214 * 2 ^ 59
def prefixEnd_3315214 : Nat := 4983230072969 + 3 ^ 40 * 3315214 * 2
def baseEnd_3315214 : Nat := 1134865503009798295785743

theorem tailTrace_3315214 : CollatzResearch.WordTrace tailWord_3315214 prefixEnd_3315214 1134865503009798295785743 := by
  unfold tailWord_3315214
  simp only [CollatzResearch.WordTrace]
  refine ⟨15114473526444168289918087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80610525474368897546229797 15114473526444168289918087)
  ·
    refine ⟨22671710289666252434877131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15114473526444168289918087 22671710289666252434877131)
    ·
      refine ⟨34007565434499378652315697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22671710289666252434877131 34007565434499378652315697)
      ·
        refine ⟨25505674075874533989236773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34007565434499378652315697 25505674075874533989236773)
        ·
          refine ⟨4782313889226475122981895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25505674075874533989236773 4782313889226475122981895)
          ·
            refine ⟨7173470833839712684472843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782313889226475122981895 7173470833839712684472843)
            ·
              refine ⟨10760206250759569026709265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173470833839712684472843 10760206250759569026709265)
              ·
                refine ⟨8070154688069676770031949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10760206250759569026709265 8070154688069676770031949)
                ·
                  refine ⟨3026308008026128788761981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8070154688069676770031949 3026308008026128788761981)
                  ·
                    refine ⟨1134865503009798295785743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026308008026128788761981 1134865503009798295785743)
                    ·
                      rfl

theorem cell22_3315214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_3315214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315214 prefixEnd_3315214 := by exact prefixLift 3315214
  have htrace : WordTrace (prefixWord ++ tailWord_3315214) baseStart_3315214 baseEnd_3315214 := by
    simpa [prefixWord, tailWord_3315214, baseEnd_3315214] using wordTrace_append hprefix tailTrace_3315214
  have hstable : (prefixWord ++ tailWord_3315214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315214).length < 2 ^ (prefixWord ++ tailWord_3315214).sum := by decide
  have hdescent : baseEnd_3315214 < baseStart_3315214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315255 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 6]
def baseStart_3315255 : Nat := 118140960795 + 3315255 * 2 ^ 59
def prefixEnd_3315255 : Nat := 4983230072969 + 3 ^ 40 * 3315255 * 2
def baseEnd_3315255 : Nat := 378293179382562618503539

theorem tailTrace_3315255 : CollatzResearch.WordTrace tailWord_3315255 prefixEnd_3315255 378293179382562618503539 := by
  unfold tailWord_3315255
  simp only [CollatzResearch.WordTrace]
  refine ⟨120917283604404810321587219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80611522402936540214391479 120917283604404810321587219)
  ·
    refine ⟨181375925406607215482380829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120917283604404810321587219 181375925406607215482380829)
    ·
      refine ⟨68015972027477705805892811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181375925406607215482380829 68015972027477705805892811)
      ·
        refine ⟨102023958041216558708839217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68015972027477705805892811 102023958041216558708839217)
        ·
          refine ⟨76517968530912419031629413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102023958041216558708839217 76517968530912419031629413)
          ·
            refine ⟨14347119099546078568430515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76517968530912419031629413 14347119099546078568430515)
            ·
              refine ⟨21520678649319117852645773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14347119099546078568430515 21520678649319117852645773)
              ·
                refine ⟨8070254493494669194742165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21520678649319117852645773 8070254493494669194742165)
                ·
                  refine ⟨378293179382562618503539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8070254493494669194742165 378293179382562618503539)
                  ·
                    rfl

theorem cell22_3315255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 6].length) (baseStart_3315255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315255 prefixEnd_3315255 := by exact prefixLift 3315255
  have htrace : WordTrace (prefixWord ++ tailWord_3315255) baseStart_3315255 baseEnd_3315255 := by
    simpa [prefixWord, tailWord_3315255, baseEnd_3315255] using wordTrace_append hprefix tailTrace_3315255
  have hstable : (prefixWord ++ tailWord_3315255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315255).length < 2 ^ (prefixWord ++ tailWord_3315255).sum := by decide
  have hdescent : baseEnd_3315255 < baseStart_3315255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315287 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 4, 3]
def baseStart_3315287 : Nat := 118140960795 + 3315287 * 2 ^ 59
def prefixEnd_3315287 : Nat := 4983230072969 + 3 ^ 40 * 3315287 * 2
def baseEnd_3315287 : Nat := 1134890492401650438710519

theorem tailTrace_3315287 : CollatzResearch.WordTrace tailWord_3315287 prefixEnd_3315287 1134890492401650438710519 := by
  unfold tailWord_3315287
  simp only [CollatzResearch.WordTrace]
  refine ⟨120918450740288879786752115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80612300493525919857834743 120918450740288879786752115)
  ·
    refine ⟨181377676110433319680128173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120918450740288879786752115 181377676110433319680128173)
    ·
      refine ⟨68016628541412494880048065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181377676110433319680128173 68016628541412494880048065)
      ·
        refine ⟨51012471406059371160036049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68016628541412494880048065 51012471406059371160036049)
        ·
          refine ⟨38259353554544528370027037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51012471406059371160036049 38259353554544528370027037)
          ·
            refine ⟨14347257582954198138760139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38259353554544528370027037 14347257582954198138760139)
            ·
              refine ⟨21520886374431297208140209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14347257582954198138760139 21520886374431297208140209)
              ·
                refine ⟨16140664780823472906105157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21520886374431297208140209 16140664780823472906105157)
                ·
                  refine ⟨3026374646404401169894717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16140664780823472906105157 3026374646404401169894717)
                  ·
                    refine ⟨1134890492401650438710519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026374646404401169894717 1134890492401650438710519)
                    ·
                      rfl

theorem cell22_3315287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_3315287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315287 prefixEnd_3315287 := by exact prefixLift 3315287
  have htrace : WordTrace (prefixWord ++ tailWord_3315287) baseStart_3315287 baseEnd_3315287 := by
    simpa [prefixWord, tailWord_3315287, baseEnd_3315287] using wordTrace_append hprefix tailTrace_3315287
  have hstable : (prefixWord ++ tailWord_3315287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315287).length < 2 ^ (prefixWord ++ tailWord_3315287).sum := by decide
  have hdescent : baseEnd_3315287 < baseStart_3315287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315300 : List Nat := [2, 3, 1, 1, 2, 3, 10]
def baseStart_3315300 : Nat := 118140960795 + 3315300 * 2 ^ 59
def prefixEnd_3315300 : Nat := 4983230072969 + 3 ^ 40 * 3315300 * 2
def baseEnd_3315300 : Nat := 42033146021011953264277

theorem tailTrace_3315300 : CollatzResearch.WordTrace tailWord_3315300 prefixEnd_3315300 42033146021011953264277 := by
  unfold tailWord_3315300
  simp only [CollatzResearch.WordTrace]
  refine ⟨60459462444620891503487677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80612616592827855337983569 60459462444620891503487677)
  ·
    refine ⟨22672298416732834313807879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60459462444620891503487677 22672298416732834313807879)
    ·
      refine ⟨34008447625099251470711819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22672298416732834313807879 34008447625099251470711819)
      ·
        refine ⟨51012671437648877206067729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34008447625099251470711819 51012671437648877206067729)
        ·
          refine ⟨38259503578236657904550797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51012671437648877206067729 38259503578236657904550797)
          ·
            refine ⟨14347313841838746714206549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38259503578236657904550797 14347313841838746714206549)
            ·
              refine ⟨42033146021011953264277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14347313841838746714206549 42033146021011953264277)
              ·
                rfl

theorem cell22_3315300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 10].length) (baseStart_3315300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315300 prefixEnd_3315300 := by exact prefixLift 3315300
  have htrace : WordTrace (prefixWord ++ tailWord_3315300) baseStart_3315300 baseEnd_3315300 := by
    simpa [prefixWord, tailWord_3315300, baseEnd_3315300] using wordTrace_append hprefix tailTrace_3315300
  have hstable : (prefixWord ++ tailWord_3315300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315300).length < 2 ^ (prefixWord ++ tailWord_3315300).sum := by decide
  have hdescent : baseEnd_3315300 < baseStart_3315300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315304 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 4, 3]
def baseStart_3315304 : Nat := 118140960795 + 3315304 * 2 ^ 59
def prefixEnd_3315304 : Nat := 4983230072969 + 3 ^ 40 * 3315304 * 2
def baseEnd_3315304 : Nat := 1134896311849068061035467

theorem tailTrace_3315304 : CollatzResearch.WordTrace tailWord_3315304 prefixEnd_3315304 1134896311849068061035467 := by
  unfold tailWord_3315304
  simp only [CollatzResearch.WordTrace]
  refine ⟨60459535390613645845060483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80612713854151527793413977 60459535390613645845060483)
  ·
    refine ⟨90689303085920468767590725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60459535390613645845060483 90689303085920468767590725)
    ·
      refine ⟨17004244328610087893923261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90689303085920468767590725 17004244328610087893923261)
      ·
        refine ⟨6376591623228782960221223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17004244328610087893923261 6376591623228782960221223)
        ·
          refine ⟨9564887434843174440331835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376591623228782960221223 9564887434843174440331835)
          ·
            refine ⟨14347331152264761660497753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564887434843174440331835 14347331152264761660497753)
            ·
              refine ⟨10760498364198571245373315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14347331152264761660497753 10760498364198571245373315)
              ·
                refine ⟨16140747546297856868059973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10760498364198571245373315 16140747546297856868059973)
                ·
                  refine ⟨3026390164930848162761245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16140747546297856868059973 3026390164930848162761245)
                  ·
                    refine ⟨1134896311849068061035467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026390164930848162761245 1134896311849068061035467)
                    ·
                      rfl

theorem cell22_3315304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_3315304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315304 prefixEnd_3315304 := by exact prefixLift 3315304
  have htrace : WordTrace (prefixWord ++ tailWord_3315304) baseStart_3315304 baseEnd_3315304 := by
    simpa [prefixWord, tailWord_3315304, baseEnd_3315304] using wordTrace_append hprefix tailTrace_3315304
  have hstable : (prefixWord ++ tailWord_3315304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315304).length < 2 ^ (prefixWord ++ tailWord_3315304).sum := by decide
  have hdescent : baseEnd_3315304 < baseStart_3315304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315306 : List Nat := [3, 1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_3315306 : Nat := 118140960795 + 3315306 * 2 ^ 59
def prefixEnd_3315306 : Nat := 4983230072969 + 3 ^ 40 * 3315306 * 2
def baseEnd_3315306 : Nat := 378298998829980240828487

theorem tailTrace_3315306 : CollatzResearch.WordTrace tailWord_3315306 prefixEnd_3315306 378298998829980240828487 := by
  unfold tailWord_3315306
  simp only [CollatzResearch.WordTrace]
  refine ⟨30229785931805011507923443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80612762484813364021129181 30229785931805011507923443)
  ·
    refine ⟨45344678897707517261885165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30229785931805011507923443 45344678897707517261885165)
    ·
      refine ⟨17004254586640318973206937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45344678897707517261885165 17004254586640318973206937)
      ·
        refine ⟨12753190939980239229905203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17004254586640318973206937 12753190939980239229905203)
        ·
          refine ⟨19129786409970358844857805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12753190939980239229905203 19129786409970358844857805)
          ·
            refine ⟨7173669903738884566821677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19129786409970358844857805 7173669903738884566821677)
            ·
              refine ⟨2690126213902081712558129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7173669903738884566821677 2690126213902081712558129)
              ·
                refine ⟨2017594660426561284418597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690126213902081712558129 2017594660426561284418597)
                ·
                  refine ⟨378298998829980240828487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017594660426561284418597 378298998829980240828487)
                  ·
                    rfl

theorem cell22_3315306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_3315306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315306 prefixEnd_3315306 := by exact prefixLift 3315306
  have htrace : WordTrace (prefixWord ++ tailWord_3315306) baseStart_3315306 baseEnd_3315306 := by
    simpa [prefixWord, tailWord_3315306, baseEnd_3315306] using wordTrace_append hprefix tailTrace_3315306
  have hstable : (prefixWord ++ tailWord_3315306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315306).length < 2 ^ (prefixWord ++ tailWord_3315306).sum := by decide
  have hdescent : baseEnd_3315306 < baseStart_3315306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315317 : List Nat := [1, 3, 4, 2, 1, 1, 1, 9]
def baseStart_3315317 : Nat := 118140960795 + 3315317 * 2 ^ 59
def prefixEnd_3315317 : Nat := 4983230072969 + 3 ^ 40 * 3315317 * 2
def baseEnd_3315317 : Nat := 126100084668304484495603

theorem tailTrace_3315317 : CollatzResearch.WordTrace tailWord_3315317 prefixEnd_3315317 126100084668304484495603 := by
  unfold tailWord_3315317
  simp only [CollatzResearch.WordTrace]
  refine ⟨120919544930180194910344205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80613029953453463273562803 120919544930180194910344205)
  ·
    refine ⟨45344829348817573091379077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120919544930180194910344205 45344829348817573091379077)
    ·
      refine ⟨8502155502903294954633577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45344829348817573091379077 8502155502903294954633577)
      ·
        refine ⟨6376616627177471215975183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8502155502903294954633577 6376616627177471215975183)
        ·
          refine ⟨9564924940766206823962775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6376616627177471215975183 9564924940766206823962775)
          ·
            refine ⟨14347387411149310235944163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564924940766206823962775 14347387411149310235944163)
            ·
              refine ⟨21521081116723965353916245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14347387411149310235944163 21521081116723965353916245)
              ·
                refine ⟨126100084668304484495603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21521081116723965353916245 126100084668304484495603)
                ·
                  rfl

theorem cell22_3315317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 9].length) (baseStart_3315317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315317 prefixEnd_3315317 := by exact prefixLift 3315317
  have htrace : WordTrace (prefixWord ++ tailWord_3315317) baseStart_3315317 baseEnd_3315317 := by
    simpa [prefixWord, tailWord_3315317, baseEnd_3315317] using wordTrace_append hprefix tailTrace_3315317
  have hstable : (prefixWord ++ tailWord_3315317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315317).length < 2 ^ (prefixWord ++ tailWord_3315317).sum := by decide
  have hdescent : baseEnd_3315317 < baseStart_3315317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315336 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 2, 4]
def baseStart_3315336 : Nat := 118140960795 + 3315336 * 2 ^ 59
def prefixEnd_3315336 : Nat := 4983230072969 + 3 ^ 40 * 3315336 * 2
def baseEnd_3315336 : Nat := 1134907266103030644235369

theorem tailTrace_3315336 : CollatzResearch.WordTrace tailWord_3315336 prefixEnd_3315336 1134907266103030644235369 := by
  unfold tailWord_3315336
  simp only [CollatzResearch.WordTrace]
  refine ⟨60460118958555680577642931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80613491944740907436857241 60460118958555680577642931)
  ·
    refine ⟨90690178437833520866464397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60460118958555680577642931 90690178437833520866464397)
    ·
      refine ⟨34008816914187570324924149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90690178437833520866464397 34008816914187570324924149)
      ·
        refine ⟨3188326585705084717961639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34008816914187570324924149 3188326585705084717961639)
        ·
          refine ⟨4782489878557627076942459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188326585705084717961639 4782489878557627076942459)
          ·
            refine ⟨7173734817836440615413689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4782489878557627076942459 7173734817836440615413689)
            ·
              refine ⟨5380301113377330461560267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7173734817836440615413689 5380301113377330461560267)
              ·
                refine ⟨8070451670065995692340401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5380301113377330461560267 8070451670065995692340401)
                ·
                  refine ⟨6052838752549496769255301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8070451670065995692340401 6052838752549496769255301)
                  ·
                    refine ⟨1134907266103030644235369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052838752549496769255301 1134907266103030644235369)
                    ·
                      rfl

theorem cell22_3315336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_3315336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315336 prefixEnd_3315336 := by exact prefixLift 3315336
  have htrace : WordTrace (prefixWord ++ tailWord_3315336) baseStart_3315336 baseEnd_3315336 := by
    simpa [prefixWord, tailWord_3315336, baseEnd_3315336] using wordTrace_append hprefix tailTrace_3315336
  have hstable : (prefixWord ++ tailWord_3315336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315336).length < 2 ^ (prefixWord ++ tailWord_3315336).sum := by decide
  have hdescent : baseEnd_3315336 < baseStart_3315336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315345 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 7]
def baseStart_3315345 : Nat := 118140960795 + 3315345 * 2 ^ 59
def prefixEnd_3315345 : Nat := 4983230072969 + 3 ^ 40 * 3315345 * 2
def baseEnd_3315345 : Nat := 378303448995652540253447

theorem tailTrace_3315345 : CollatzResearch.WordTrace tailWord_3315345 prefixEnd_3315345 378303448995652540253447 := by
  unfold tailWord_3315345
  simp only [CollatzResearch.WordTrace]
  refine ⟨120920566174078755692363489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80613710782719170461575659 120920566174078755692363489)
  ·
    refine ⟨90690424630559066769272617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120920566174078755692363489 90690424630559066769272617)
    ·
      refine ⟨68017818472919300076954463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90690424630559066769272617 68017818472919300076954463)
      ·
        refine ⟨102026727709378950115431695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68017818472919300076954463 102026727709378950115431695)
        ·
          refine ⟨153040091564068425173147543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102026727709378950115431695 153040091564068425173147543)
          ·
            refine ⟨229560137346102637759721315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153040091564068425173147543 229560137346102637759721315)
            ·
              refine ⟨344340206019153956639581973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229560137346102637759721315 344340206019153956639581973)
              ·
                refine ⟨16140947157147841717480405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 344340206019153956639581973 16140947157147841717480405)
                ·
                  refine ⟨378303448995652540253447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16140947157147841717480405 378303448995652540253447)
                  ·
                    rfl

theorem cell22_3315345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 7].length) (baseStart_3315345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315345 prefixEnd_3315345 := by exact prefixLift 3315345
  have htrace : WordTrace (prefixWord ++ tailWord_3315345) baseStart_3315345 baseEnd_3315345 := by
    simpa [prefixWord, tailWord_3315345, baseEnd_3315345] using wordTrace_append hprefix tailTrace_3315345
  have hstable : (prefixWord ++ tailWord_3315345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315345).length < 2 ^ (prefixWord ++ tailWord_3315345).sum := by decide
  have hdescent : baseEnd_3315345 < baseStart_3315345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315368 : List Nat := [2, 1, 7, 1, 1, 2, 1, 7]
def baseStart_3315368 : Nat := 118140960795 + 3315368 * 2 ^ 59
def prefixEnd_3315368 : Nat := 4983230072969 + 3 ^ 40 * 3315368 * 2
def baseEnd_3315368 : Nat := 126102024484110358603919

theorem tailTrace_3315368 : CollatzResearch.WordTrace tailWord_3315368 prefixEnd_3315368 126102024484110358603919 := by
  unfold tailWord_3315368
  simp only [CollatzResearch.WordTrace]
  refine ⟨60460702526497715310225379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80614270035330287080300505 60460702526497715310225379)
  ·
    refine ⟨90691053789746572965338069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60460702526497715310225379 90691053789746572965338069)
    ·
      refine ⟨2125571573197185303875111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 90691053789746572965338069 2125571573197185303875111)
      ·
        refine ⟨3188357359795777955812667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2125571573197185303875111 3188357359795777955812667)
        ·
          refine ⟨4782536039693666933719001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188357359795777955812667 4782536039693666933719001)
          ·
            refine ⟨3586902029770250200289251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4782536039693666933719001 3586902029770250200289251)
            ·
              refine ⟨5380353044655375300433877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586902029770250200289251 5380353044655375300433877)
              ·
                refine ⟨126102024484110358603919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5380353044655375300433877 126102024484110358603919)
                ·
                  rfl

theorem cell22_3315368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 7].length) (baseStart_3315368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315368 prefixEnd_3315368 := by exact prefixLift 3315368
  have htrace : WordTrace (prefixWord ++ tailWord_3315368) baseStart_3315368 baseEnd_3315368 := by
    simpa [prefixWord, tailWord_3315368, baseEnd_3315368] using wordTrace_append hprefix tailTrace_3315368
  have hstable : (prefixWord ++ tailWord_3315368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315368).length < 2 ^ (prefixWord ++ tailWord_3315368).sum := by decide
  have hdescent : baseEnd_3315368 < baseStart_3315368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315392 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_3315392 : Nat := 118140960795 + 3315392 * 2 ^ 59
def prefixEnd_3315392 : Nat := 4983230072969 + 3 ^ 40 * 3315392 * 2
def baseEnd_3315392 : Nat := 1134926436047465164835197

theorem tailTrace_3315392 : CollatzResearch.WordTrace tailWord_3315392 prefixEnd_3315392 1134926436047465164835197 := by
  unfold tailWord_3315392
  simp only [CollatzResearch.WordTrace]
  refine ⟨60461140202454241359662215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80614853603272321812882953 60461140202454241359662215)
  ·
    refine ⟨90691710303681362039493323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60461140202454241359662215 90691710303681362039493323)
    ·
      refine ⟨136037565455522043059239985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90691710303681362039493323 136037565455522043059239985)
      ·
        refine ⟨102028174091641532294429989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136037565455522043059239985 102028174091641532294429989)
        ·
          refine ⟨19130282642182787305205623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102028174091641532294429989 19130282642182787305205623)
          ·
            refine ⟨28695423963274180957808435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19130282642182787305205623 28695423963274180957808435)
            ·
              refine ⟨43043135944911271436712653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28695423963274180957808435 43043135944911271436712653)
              ·
                refine ⟨16141175979341726788767245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43043135944911271436712653 16141175979341726788767245)
                ·
                  refine ⟨6052940992253147545787717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16141175979341726788767245 6052940992253147545787717)
                  ·
                    refine ⟨1134926436047465164835197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052940992253147545787717 1134926436047465164835197)
                    ·
                      rfl

theorem cell22_3315392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_3315392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315392 prefixEnd_3315392 := by exact prefixLift 3315392
  have htrace : WordTrace (prefixWord ++ tailWord_3315392) baseStart_3315392 baseEnd_3315392 := by
    simpa [prefixWord, tailWord_3315392, baseEnd_3315392] using wordTrace_append hprefix tailTrace_3315392
  have hstable : (prefixWord ++ tailWord_3315392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315392).length < 2 ^ (prefixWord ++ tailWord_3315392).sum := by decide
  have hdescent : baseEnd_3315392 < baseStart_3315392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315409 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 1, 4]
def baseStart_3315409 : Nat := 118140960795 + 3315409 * 2 ^ 59
def prefixEnd_3315409 : Nat := 4983230072969 + 3 ^ 40 * 3315409 * 2
def baseEnd_3315409 : Nat := 1134932255494882787160145

theorem tailTrace_3315409 : CollatzResearch.WordTrace tailWord_3315409 prefixEnd_3315409 1134932255494882787160145 := by
  unfold tailWord_3315409
  simp only [CollatzResearch.WordTrace]
  refine ⟨120922900445846894622693281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80615266963897929748462187 120922900445846894622693281)
  ·
    refine ⟨90692175334385170967019961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120922900445846894622693281 90692175334385170967019961)
    ·
      refine ⟨68019131500788878225264971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90692175334385170967019961 68019131500788878225264971)
      ·
        refine ⟨102028697251183317337897457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68019131500788878225264971 102028697251183317337897457)
        ·
          refine ⟨76521522938387488003423093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102028697251183317337897457 76521522938387488003423093)
          ·
            refine ⟨7173892775473827000320915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76521522938387488003423093 7173892775473827000320915)
            ·
              refine ⟨10760839163210740500481373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7173892775473827000320915 10760839163210740500481373)
              ·
                refine ⟨4035314686204027687680515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10760839163210740500481373 4035314686204027687680515)
                ·
                  refine ⟨6052972029306041531520773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035314686204027687680515 6052972029306041531520773)
                  ·
                    refine ⟨1134932255494882787160145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6052972029306041531520773 1134932255494882787160145)
                    ·
                      rfl

theorem cell22_3315409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_3315409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315409 prefixEnd_3315409 := by exact prefixLift 3315409
  have htrace : WordTrace (prefixWord ++ tailWord_3315409) baseStart_3315409 baseEnd_3315409 := by
    simpa [prefixWord, tailWord_3315409, baseEnd_3315409] using wordTrace_append hprefix tailTrace_3315409
  have hstable : (prefixWord ++ tailWord_3315409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315409).length < 2 ^ (prefixWord ++ tailWord_3315409).sum := by decide
  have hdescent : baseEnd_3315409 < baseStart_3315409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315424 : List Nat := [2, 1, 1, 3, 1, 2, 4, 4, 4]
def baseStart_3315424 : Nat := 118140960795 + 3315424 * 2 ^ 59
def prefixEnd_3315424 : Nat := 4983230072969 + 3 ^ 40 * 3315424 * 2
def baseEnd_3315424 : Nat := 378312463433809249345033

theorem tailTrace_3315424 : CollatzResearch.WordTrace tailWord_3315424 prefixEnd_3315424 378312463433809249345033 := by
  unfold tailWord_3315424
  simp only [CollatzResearch.WordTrace]
  refine ⟨60461723770396276092244663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80615631693861701456326217 60461723770396276092244663)
  ·
    refine ⟨90692585655594414138366995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60461723770396276092244663 90692585655594414138366995)
    ·
      refine ⟨136038878483391621207550493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90692585655594414138366995 136038878483391621207550493)
      ·
        refine ⟨51014579431271857952831435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136038878483391621207550493 51014579431271857952831435)
        ·
          refine ⟨76521869146907786929247153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51014579431271857952831435 76521869146907786929247153)
          ·
            refine ⟨57391401860180840196935365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76521869146907786929247153 57391401860180840196935365)
            ·
              refine ⟨10760887848783907536925381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57391401860180840196935365 10760887848783907536925381)
              ·
                refine ⟨2017666471646982663173509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10760887848783907536925381 2017666471646982663173509)
                ·
                  refine ⟨378312463433809249345033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017666471646982663173509 378312463433809249345033)
                  ·
                    rfl

theorem cell22_3315424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 4, 4].length) (baseStart_3315424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315424 prefixEnd_3315424 := by exact prefixLift 3315424
  have htrace : WordTrace (prefixWord ++ tailWord_3315424) baseStart_3315424 baseEnd_3315424 := by
    simpa [prefixWord, tailWord_3315424, baseEnd_3315424] using wordTrace_append hprefix tailTrace_3315424
  have hstable : (prefixWord ++ tailWord_3315424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315424).length < 2 ^ (prefixWord ++ tailWord_3315424).sum := by decide
  have hdescent : baseEnd_3315424 < baseStart_3315424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315452 : List Nat := [2, 2, 2, 1, 3, 1, 3, 8]
def baseStart_3315452 : Nat := 118140960795 + 3315452 * 2 ^ 59
def prefixEnd_3315452 : Nat := 4983230072969 + 3 ^ 40 * 3315452 * 2
def baseEnd_3315452 : Nat := 126105219474849445370557

theorem tailTrace_3315452 : CollatzResearch.WordTrace tailWord_3315452 prefixEnd_3315452 126105219474849445370557 := by
  unfold tailWord_3315452
  simp only [CollatzResearch.WordTrace]
  refine ⟨60462234392345556483254305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80616312523127408644339073 60462234392345556483254305)
  ·
    refine ⟨45346675794259167362440729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60462234392345556483254305 45346675794259167362440729)
    ·
      refine ⟨34010006845694375521830547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45346675794259167362440729 34010006845694375521830547)
      ·
        refine ⟨51015010268541563282745821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34010006845694375521830547 51015010268541563282745821)
        ·
          refine ⟨19130628850703086231029683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51015010268541563282745821 19130628850703086231029683)
          ·
            refine ⟨28695943276054629346544525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19130628850703086231029683 28695943276054629346544525)
            ·
              refine ⟨10760978728520486004954197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28695943276054629346544525 10760978728520486004954197)
              ·
                refine ⟨126105219474849445370557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10760978728520486004954197 126105219474849445370557)
                ·
                  rfl

theorem cell22_3315452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 8].length) (baseStart_3315452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315452 prefixEnd_3315452 := by exact prefixLift 3315452
  have htrace : WordTrace (prefixWord ++ tailWord_3315452) baseStart_3315452 baseEnd_3315452 := by
    simpa [prefixWord, tailWord_3315452, baseEnd_3315452] using wordTrace_append hprefix tailTrace_3315452
  have hstable : (prefixWord ++ tailWord_3315452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315452).length < 2 ^ (prefixWord ++ tailWord_3315452).sum := by decide
  have hdescent : baseEnd_3315452 < baseStart_3315452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315559 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 6]
def baseStart_3315559 : Nat := 118140960795 + 3315559 * 2 ^ 59
def prefixEnd_3315559 : Nat := 4983230072969 + 3 ^ 40 * 3315559 * 2
def baseEnd_3315559 : Nat := 378327867853444131969895

theorem tailTrace_3315559 : CollatzResearch.WordTrace tailWord_3315559 prefixEnd_3315559 378327867853444131969895 := by
  unfold tailWord_3315559
  simp only [CollatzResearch.WordTrace]
  refine ⟨120928371395303470240653731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80618914263535646827102487 120928371395303470240653731)
  ·
    refine ⟨181392557092955205360980597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120928371395303470240653731 181392557092955205360980597)
    ·
      refine ⟨17005552227464550502591931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 181392557092955205360980597 17005552227464550502591931)
      ·
        refine ⟨25508328341196825753887897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17005552227464550502591931 25508328341196825753887897)
        ·
          refine ⟨19131246255897619315415923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25508328341196825753887897 19131246255897619315415923)
          ·
            refine ⟨28696869383846428973123885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19131246255897619315415923 28696869383846428973123885)
            ·
              refine ⟨10761326018942410864921457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28696869383846428973123885 10761326018942410864921457)
              ·
                refine ⟨8070994514206808148691093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10761326018942410864921457 8070994514206808148691093)
                ·
                  refine ⟨378327867853444131969895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8070994514206808148691093 378327867853444131969895)
                  ·
                    rfl

theorem cell22_3315559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 6].length) (baseStart_3315559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315559 prefixEnd_3315559 := by exact prefixLift 3315559
  have htrace : WordTrace (prefixWord ++ tailWord_3315559) baseStart_3315559 baseEnd_3315559 := by
    simpa [prefixWord, tailWord_3315559, baseEnd_3315559] using wordTrace_append hprefix tailTrace_3315559
  have hstable : (prefixWord ++ tailWord_3315559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315559).length < 2 ^ (prefixWord ++ tailWord_3315559).sum := by decide
  have hdescent : baseEnd_3315559 < baseStart_3315559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315589 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 4, 4]
def baseStart_3315589 : Nat := 118140960795 + 3315589 * 2 ^ 59
def prefixEnd_3315589 : Nat := 4983230072969 + 3 ^ 40 * 3315589 * 2
def baseEnd_3315589 : Nat := 1134993873173422317659593

theorem tailTrace_3315589 : CollatzResearch.WordTrace tailWord_3315589 prefixEnd_3315589 1134993873173422317659593 := by
  unfold tailWord_3315589
  simp only [CollatzResearch.WordTrace]
  refine ⟨120929465585194785364245821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80619643723463190242830547 120929465585194785364245821)
  ·
    refine ⟨45348549594448044511592183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120929465585194785364245821 45348549594448044511592183)
    ·
      refine ⟨68022824391672066767388275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45348549594448044511592183 68022824391672066767388275)
      ·
        refine ⟨102034236587508100151082413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68022824391672066767388275 102034236587508100151082413)
        ·
          refine ⟨38262838720315537556655905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102034236587508100151082413 38262838720315537556655905)
          ·
            refine ⟨28697129040236653167491929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38262838720315537556655905 28697129040236653167491929)
            ·
              refine ⟨21522846780177489875618947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28697129040236653167491929 21522846780177489875618947)
              ·
                refine ⟨32284270170266234813428421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21522846780177489875618947 32284270170266234813428421)
                ·
                  refine ⟨6053300656924919027517829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32284270170266234813428421 6053300656924919027517829)
                  ·
                    refine ⟨1134993873173422317659593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6053300656924919027517829 1134993873173422317659593)
                    ·
                      rfl

theorem cell22_3315589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_3315589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315589 prefixEnd_3315589 := by exact prefixLift 3315589
  have htrace : WordTrace (prefixWord ++ tailWord_3315589) baseStart_3315589 baseEnd_3315589 := by
    simpa [prefixWord, tailWord_3315589, baseEnd_3315589] using wordTrace_append hprefix tailTrace_3315589
  have hstable : (prefixWord ++ tailWord_3315589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315589).length < 2 ^ (prefixWord ++ tailWord_3315589).sum := by decide
  have hdescent : baseEnd_3315589 < baseStart_3315589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315664 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_3315664 : Nat := 118140960795 + 3315664 * 2 ^ 59
def prefixEnd_3315664 : Nat := 4983230072969 + 3 ^ 40 * 3315664 * 2
def baseEnd_3315664 : Nat := 1135019547206147122034363

theorem tailTrace_3315664 : CollatzResearch.WordTrace tailWord_3315664 prefixEnd_3315664 1135019547206147122034363 := by
  unfold tailWord_3315664
  simp only [CollatzResearch.WordTrace]
  refine ⟨60466100529961536586613023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80621467373282048782150697 60466100529961536586613023)
  ·
    refine ⟨90699150794942304879919535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60466100529961536586613023 90699150794942304879919535)
    ·
      refine ⟨136048726192413457319879303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90699150794942304879919535 136048726192413457319879303)
      ·
        refine ⟨204073089288620185979818955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136048726192413457319879303 204073089288620185979818955)
        ·
          refine ⟨306109633932930278969728433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204073089288620185979818955 306109633932930278969728433)
          ·
            refine ⟨229582225449697709227296325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306109633932930278969728433 229582225449697709227296325)
            ·
              refine ⟨43046667271818320480118061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229582225449697709227296325 43046667271818320480118061)
              ·
                refine ⟨16142500226931870180044273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43046667271818320480118061 16142500226931870180044273)
                ·
                  refine ⟨12106875170198902635033205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16142500226931870180044273 12106875170198902635033205)
                  ·
                    refine ⟨1135019547206147122034363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12106875170198902635033205 1135019547206147122034363)
                    ·
                      rfl

theorem cell22_3315664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_3315664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315664 prefixEnd_3315664 := by exact prefixLift 3315664
  have htrace : WordTrace (prefixWord ++ tailWord_3315664) baseStart_3315664 baseEnd_3315664 := by
    simpa [prefixWord, tailWord_3315664, baseEnd_3315664] using wordTrace_append hprefix tailTrace_3315664
  have hstable : (prefixWord ++ tailWord_3315664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315664).length < 2 ^ (prefixWord ++ tailWord_3315664).sum := by decide
  have hdescent : baseEnd_3315664 < baseStart_3315664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315696 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 1, 4]
def baseStart_3315696 : Nat := 118140960795 + 3315696 * 2 ^ 59
def prefixEnd_3315696 : Nat := 4983230072969 + 3 ^ 40 * 3315696 * 2
def baseEnd_3315696 : Nat := 1135030501460109705234265

theorem tailTrace_3315696 : CollatzResearch.WordTrace tailWord_3315696 prefixEnd_3315696 1135030501460109705234265 := by
  unfold tailWord_3315696
  simp only [CollatzResearch.WordTrace]
  refine ⟨60466684097903571319195471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80622245463871428425593961 60466684097903571319195471)
  ·
    refine ⟨90700026146855356978793207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60466684097903571319195471 90700026146855356978793207)
    ·
      refine ⟨136050039220283035468189811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90700026146855356978793207 136050039220283035468189811)
      ·
        refine ⟨204075058830424553202284717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136050039220283035468189811 204075058830424553202284717)
        ·
          refine ⟨76528147061409207450856769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204075058830424553202284717 76528147061409207450856769)
          ·
            refine ⟨57396110296056905588142577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76528147061409207450856769 57396110296056905588142577)
            ·
              refine ⟨43047082722042679191106933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57396110296056905588142577 43047082722042679191106933)
              ·
                refine ⟨4035664005191501174166275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43047082722042679191106933 4035664005191501174166275)
                ·
                  refine ⟨6053496007787251761249413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035664005191501174166275 6053496007787251761249413)
                  ·
                    refine ⟨1135030501460109705234265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6053496007787251761249413 1135030501460109705234265)
                    ·
                      rfl

theorem cell22_3315696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_3315696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315696 prefixEnd_3315696 := by exact prefixLift 3315696
  have htrace : WordTrace (prefixWord ++ tailWord_3315696) baseStart_3315696 baseEnd_3315696 := by
    simpa [prefixWord, tailWord_3315696, baseEnd_3315696] using wordTrace_append hprefix tailTrace_3315696
  have hstable : (prefixWord ++ tailWord_3315696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315696).length < 2 ^ (prefixWord ++ tailWord_3315696).sum := by decide
  have hdescent : baseEnd_3315696 < baseStart_3315696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315745 : List Nat := [1, 2, 3, 2, 4, 1, 2, 3, 4]
def baseStart_3315745 : Nat := 118140960795 + 3315745 * 2 ^ 59
def prefixEnd_3315745 : Nat := 4983230072969 + 3 ^ 40 * 3315745 * 2
def baseEnd_3315745 : Nat := 378349091720496636919705

theorem tailTrace_3315745 : CollatzResearch.WordTrace tailWord_3315745 prefixEnd_3315745 378349091720496636919705 := by
  unfold tailWord_3315745
  simp only [CollatzResearch.WordTrace]
  refine ⟨120935155372629624006924689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80623436915086416004616459 120935155372629624006924689)
  ·
    refine ⟨90701366529472218005193517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120935155372629624006924689 90701366529472218005193517)
    ·
      refine ⟨34013012448552081751947569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90701366529472218005193517 34013012448552081751947569)
      ·
        refine ⟨25509759336414061313960677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34013012448552081751947569 25509759336414061313960677)
        ·
          refine ⟨4783079875577636496367627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25509759336414061313960677 4783079875577636496367627)
          ·
            refine ⟨7174619813366454744551441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4783079875577636496367627 7174619813366454744551441)
            ·
              refine ⟨5380964860024841058413581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7174619813366454744551441 5380964860024841058413581)
              ·
                refine ⟨2017861822509315396905093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5380964860024841058413581 2017861822509315396905093)
                ·
                  refine ⟨378349091720496636919705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2017861822509315396905093 378349091720496636919705)
                  ·
                    rfl

theorem cell22_3315745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 3, 4].length) (baseStart_3315745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315745 prefixEnd_3315745 := by exact prefixLift 3315745
  have htrace : WordTrace (prefixWord ++ tailWord_3315745) baseStart_3315745 baseEnd_3315745 := by
    simpa [prefixWord, tailWord_3315745, baseEnd_3315745] using wordTrace_append hprefix tailTrace_3315745
  have hstable : (prefixWord ++ tailWord_3315745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315745).length < 2 ^ (prefixWord ++ tailWord_3315745).sum := by decide
  have hdescent : baseEnd_3315745 < baseStart_3315745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315760 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 2, 3]
def baseStart_3315760 : Nat := 118140960795 + 3315760 * 2 ^ 59
def prefixEnd_3315760 : Nat := 4983230072969 + 3 ^ 40 * 3315760 * 2
def baseEnd_3315760 : Nat := 1135052409968034871634069

theorem tailTrace_3315760 : CollatzResearch.WordTrace tailWord_3315760 prefixEnd_3315760 1135052409968034871634069 := by
  unfold tailWord_3315760
  simp only [CollatzResearch.WordTrace]
  refine ⟨60467851233787640784360367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80623801645050187712480489 60467851233787640784360367)
  ·
    refine ⟨90701776850681461176540551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60467851233787640784360367 90701776850681461176540551)
    ·
      refine ⟨136052665276022191764810827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90701776850681461176540551 136052665276022191764810827)
      ·
        refine ⟨204078997914033287647216241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136052665276022191764810827 204078997914033287647216241)
        ·
          refine ⟨153059248435524965735412181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204078997914033287647216241 153059248435524965735412181)
          ·
            refine ⟨3587326135207616384423723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 153059248435524965735412181 3587326135207616384423723)
            ·
              refine ⟨5380989202811424576635585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587326135207616384423723 5380989202811424576635585)
              ·
                refine ⟨4035741902108568432476689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5380989202811424576635585 4035741902108568432476689)
                ·
                  refine ⟨3026806426581426324357517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4035741902108568432476689 3026806426581426324357517)
                  ·
                    refine ⟨1135052409968034871634069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026806426581426324357517 1135052409968034871634069)
                    ·
                      rfl

theorem cell22_3315760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2, 3].length) (baseStart_3315760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315760 prefixEnd_3315760 := by exact prefixLift 3315760
  have htrace : WordTrace (prefixWord ++ tailWord_3315760) baseStart_3315760 baseEnd_3315760 := by
    simpa [prefixWord, tailWord_3315760, baseEnd_3315760] using wordTrace_append hprefix tailTrace_3315760
  have hstable : (prefixWord ++ tailWord_3315760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315760).length < 2 ^ (prefixWord ++ tailWord_3315760).sum := by decide
  have hdescent : baseEnd_3315760 < baseStart_3315760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315771 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 7, 3]
def baseStart_3315771 : Nat := 118140960795 + 3315771 * 2 ^ 59
def prefixEnd_3315771 : Nat := 4983230072969 + 3 ^ 40 * 3315771 * 2
def baseEnd_3315771 : Nat := 1135056175492834509609035

theorem tailTrace_3315771 : CollatzResearch.WordTrace tailWord_3315771 prefixEnd_3315771 1135056175492834509609035 := by
  unfold tailWord_3315771
  simp only [CollatzResearch.WordTrace]
  refine ⟨120936103670535430447371167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80624069113690286964914111 120936103670535430447371167)
  ·
    refine ⟨181404155505803145671056751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120936103670535430447371167 181404155505803145671056751)
    ·
      refine ⟨272106233258704718506585127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181404155505803145671056751 272106233258704718506585127)
      ·
        refine ⟨408159349888057077759877691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272106233258704718506585127 408159349888057077759877691)
        ·
          refine ⟨612239024832085616639816537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408159349888057077759877691 612239024832085616639816537)
          ·
            refine ⟨459179268624064212479862403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612239024832085616639816537 459179268624064212479862403)
            ·
              refine ⟨688768902936096318719793605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459179268624064212479862403 688768902936096318719793605)
              ·
                refine ⟨129144169300518059759961301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 688768902936096318719793605 129144169300518059759961301)
                ·
                  refine ⟨3026816467980892025624093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 129144169300518059759961301 3026816467980892025624093)
                  ·
                    refine ⟨1135056175492834509609035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026816467980892025624093 1135056175492834509609035)
                    ·
                      rfl

theorem cell22_3315771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 3].length) (baseStart_3315771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315771 prefixEnd_3315771 := by exact prefixLift 3315771
  have htrace : WordTrace (prefixWord ++ tailWord_3315771) baseStart_3315771 baseEnd_3315771 := by
    simpa [prefixWord, tailWord_3315771, baseEnd_3315771] using wordTrace_append hprefix tailTrace_3315771
  have hstable : (prefixWord ++ tailWord_3315771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315771).length < 2 ^ (prefixWord ++ tailWord_3315771).sum := by decide
  have hdescent : baseEnd_3315771 < baseStart_3315771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315777 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 2, 3]
def baseStart_3315777 : Nat := 118140960795 + 3315777 * 2 ^ 59
def prefixEnd_3315777 : Nat := 4983230072969 + 3 ^ 40 * 3315777 * 2
def baseEnd_3315777 : Nat := 1135058229415452493959017

theorem tailTrace_3315777 : CollatzResearch.WordTrace tailWord_3315777 prefixEnd_3315777 1135058229415452493959017 := by
  unfold tailWord_3315777
  simp only [CollatzResearch.WordTrace]
  refine ⟨120936322508513693472089585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80624215005675795648059723 120936322508513693472089585)
  ·
    refine ⟨90702241881385270104067189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120936322508513693472089585 90702241881385270104067189)
    ·
      refine ⟨8503335176379869072256299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90702241881385270104067189 8503335176379869072256299)
      ·
        refine ⟨12755002764569803608384449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8503335176379869072256299 12755002764569803608384449)
        ·
          refine ⟨9566252073427352706288337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12755002764569803608384449 9566252073427352706288337)
          ·
            refine ⟨7174689055070514529716253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9566252073427352706288337 7174689055070514529716253)
            ·
              refine ⟨2690508395651442948643595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7174689055070514529716253 2690508395651442948643595)
              ·
                refine ⟨4035762593477164422965393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2690508395651442948643595 4035762593477164422965393)
                ·
                  refine ⟨3026821945107873317224045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4035762593477164422965393 3026821945107873317224045)
                  ·
                    refine ⟨1135058229415452493959017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026821945107873317224045 1135058229415452493959017)
                    ·
                      rfl

theorem cell22_3315777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_3315777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315777 prefixEnd_3315777 := by exact prefixLift 3315777
  have htrace : WordTrace (prefixWord ++ tailWord_3315777) baseStart_3315777 baseEnd_3315777 := by
    simpa [prefixWord, tailWord_3315777, baseEnd_3315777] using wordTrace_append hprefix tailTrace_3315777
  have hstable : (prefixWord ++ tailWord_3315777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315777).length < 2 ^ (prefixWord ++ tailWord_3315777).sum := by decide
  have hdescent : baseEnd_3315777 < baseStart_3315777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315788 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 3, 3]
def baseStart_3315788 : Nat := 118140960795 + 3315788 * 2 ^ 59
def prefixEnd_3315788 : Nat := 4983230072969 + 3 ^ 40 * 3315788 * 2
def baseEnd_3315788 : Nat := 1135061994940252131933983

theorem tailTrace_3315788 : CollatzResearch.WordTrace tailWord_3315788 prefixEnd_3315788 1135061994940252131933983 := by
  unfold tailWord_3315788
  simp only [CollatzResearch.WordTrace]
  refine ⟨60468361855736921175370009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80624482474315894900493345 60468361855736921175370009)
  ·
    refine ⟨45351271391802690881527507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60468361855736921175370009 45351271391802690881527507)
    ·
      refine ⟨68026907087704036322291261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45351271391802690881527507 68026907087704036322291261)
      ·
        refine ⟨25510090157889013620859223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68026907087704036322291261 25510090157889013620859223)
        ·
          refine ⟨38265135236833520431288835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25510090157889013620859223 38265135236833520431288835)
          ·
            refine ⟨57397702855250280646933253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38265135236833520431288835 57397702855250280646933253)
            ·
              refine ⟨10762069285359427621299985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57397702855250280646933253 10762069285359427621299985)
              ·
                refine ⟨8071551964019570715974989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10762069285359427621299985 8071551964019570715974989)
                ·
                  refine ⟨3026831986507339018490621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8071551964019570715974989 3026831986507339018490621)
                  ·
                    refine ⟨1135061994940252131933983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026831986507339018490621 1135061994940252131933983)
                    ·
                      rfl

theorem cell22_3315788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_3315788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315788 prefixEnd_3315788 := by exact prefixLift 3315788
  have htrace : WordTrace (prefixWord ++ tailWord_3315788) baseStart_3315788 baseEnd_3315788 := by
    simpa [prefixWord, tailWord_3315788, baseEnd_3315788] using wordTrace_append hprefix tailTrace_3315788
  have hstable : (prefixWord ++ tailWord_3315788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315788).length < 2 ^ (prefixWord ++ tailWord_3315788).sum := by decide
  have hdescent : baseEnd_3315788 < baseStart_3315788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315895 : List Nat := [1, 1, 3, 1, 4, 2, 2, 3, 2, 3]
def baseStart_3315895 : Nat := 118140960795 + 3315895 * 2 ^ 59
def prefixEnd_3315895 : Nat := 4983230072969 + 3 ^ 40 * 3315895 * 2
def baseEnd_3315895 : Nat := 1135098623226939519508655

theorem tailTrace_3315895 : CollatzResearch.WordTrace tailWord_3315895 prefixEnd_3315895 1135098623226939519508655 := by
  unfold tailWord_3315895
  simp only [CollatzResearch.WordTrace]
  refine ⟨120940626322086199624885139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80627084214724133083256759 120940626322086199624885139)
  ·
    refine ⟨181410939483129299437327709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120940626322086199624885139 181410939483129299437327709)
    ·
      refine ⟨68029102306173487288997891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181410939483129299437327709 68029102306173487288997891)
      ·
        refine ⟨102043653459260230933496837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68029102306173487288997891 102043653459260230933496837)
        ·
          refine ⟨19133185023611293300030657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102043653459260230933496837 19133185023611293300030657)
          ·
            refine ⟨14349888767708469975022993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19133185023611293300030657 14349888767708469975022993)
            ·
              refine ⟨10762416575781352481267245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14349888767708469975022993 10762416575781352481267245)
              ·
                refine ⟨4035906215918007180475217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10762416575781352481267245 4035906215918007180475217)
                ·
                  refine ⟨3026929661938505385356413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4035906215918007180475217 3026929661938505385356413)
                  ·
                    refine ⟨1135098623226939519508655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3026929661938505385356413 1135098623226939519508655)
                    ·
                      rfl

theorem cell22_3315895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_3315895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315895 prefixEnd_3315895 := by exact prefixLift 3315895
  have htrace : WordTrace (prefixWord ++ tailWord_3315895) baseStart_3315895 baseEnd_3315895 := by
    simpa [prefixWord, tailWord_3315895, baseEnd_3315895] using wordTrace_append hprefix tailTrace_3315895
  have hstable : (prefixWord ++ tailWord_3315895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315895).length < 2 ^ (prefixWord ++ tailWord_3315895).sum := by decide
  have hdescent : baseEnd_3315895 < baseStart_3315895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315916 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 1, 4]
def baseStart_3315916 : Nat := 118140960795 + 3315916 * 2 ^ 59
def prefixEnd_3315916 : Nat := 4983230072969 + 3 ^ 40 * 3315916 * 2
def baseEnd_3315916 : Nat := 1135105811956102464733591

theorem tailTrace_3315916 : CollatzResearch.WordTrace tailWord_3315916 prefixEnd_3315916 1135105811956102464733591 := by
  unfold tailWord_3315916
  simp only [CollatzResearch.WordTrace]
  refine ⟨60470696127505060105699801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80627594836673413474266401 60470696127505060105699801)
  ·
    refine ⟨45353022095628795079274851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60470696127505060105699801 45353022095628795079274851)
    ·
      refine ⟨68029533143443192618912277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45353022095628795079274851 68029533143443192618912277)
      ·
        refine ⟨3188884366098899654011513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68029533143443192618912277 3188884366098899654011513)
        ·
          refine ⟨2391663274574174740508635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3188884366098899654011513 2391663274574174740508635)
          ·
            refine ⟨3587494911861262110762953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391663274574174740508635 3587494911861262110762953)
            ·
              refine ⟨2690621183895946583072215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3587494911861262110762953 2690621183895946583072215)
              ·
                refine ⟨4035931775843919874608323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2690621183895946583072215 4035931775843919874608323)
                ·
                  refine ⟨6053897663765879811912485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4035931775843919874608323 6053897663765879811912485)
                  ·
                    refine ⟨1135105811956102464733591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6053897663765879811912485 1135105811956102464733591)
                    ·
                      rfl

theorem cell22_3315916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_3315916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315916 prefixEnd_3315916 := by exact prefixLift 3315916
  have htrace : WordTrace (prefixWord ++ tailWord_3315916) baseStart_3315916 baseEnd_3315916 := by
    simpa [prefixWord, tailWord_3315916, baseEnd_3315916] using wordTrace_append hprefix tailTrace_3315916
  have hstable : (prefixWord ++ tailWord_3315916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315916).length < 2 ^ (prefixWord ++ tailWord_3315916).sum := by decide
  have hdescent : baseEnd_3315916 < baseStart_3315916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315953 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 5]
def baseStart_3315953 : Nat := 118140960795 + 3315953 * 2 ^ 59
def prefixEnd_3315953 : Nat := 4983230072969 + 3 ^ 40 * 3315953 * 2
def baseEnd_3315953 : Nat := 378372825937415567186159

theorem tailTrace_3315953 : CollatzResearch.WordTrace tailWord_3315953 prefixEnd_3315953 378372825937415567186159 := by
  unfold tailWord_3315953
  simp only [CollatzResearch.WordTrace]
  refine ⟨120942741755876075530496513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80628494503917383686997675 120942741755876075530496513)
  ·
    refine ⟨90707056316907056647872385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120942741755876075530496513 90707056316907056647872385)
    ·
      refine ⟨68030292237680292485904289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90707056316907056647872385 68030292237680292485904289)
      ·
        refine ⟨51022719178260219364428217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68030292237680292485904289 51022719178260219364428217)
        ·
          refine ⟨38267039383695164523321163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51022719178260219364428217 38267039383695164523321163)
          ·
            refine ⟨57400559075542746784981745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38267039383695164523321163 57400559075542746784981745)
            ·
              refine ⟨43050419306657060088736309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57400559075542746784981745 43050419306657060088736309)
              ·
                refine ⟨4035976809999099383319029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43050419306657060088736309 4035976809999099383319029)
                ·
                  refine ⟨378372825937415567186159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4035976809999099383319029 378372825937415567186159)
                  ·
                    rfl

theorem cell22_3315953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 5].length) (baseStart_3315953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315953 prefixEnd_3315953 := by exact prefixLift 3315953
  have htrace : WordTrace (prefixWord ++ tailWord_3315953) baseStart_3315953 baseEnd_3315953 := by
    simpa [prefixWord, tailWord_3315953, baseEnd_3315953] using wordTrace_append hprefix tailTrace_3315953
  have hstable : (prefixWord ++ tailWord_3315953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315953).length < 2 ^ (prefixWord ++ tailWord_3315953).sum := by decide
  have hdescent : baseEnd_3315953 < baseStart_3315953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3315970 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3315970 : Nat := 118140960795 + 3315970 * 2 ^ 59
def prefixEnd_3315970 : Nat := 4983230072969 + 3 ^ 40 * 3315970 * 2
def baseEnd_3315970 : Nat := 378374765753221441294475

theorem tailTrace_3315970 : CollatzResearch.WordTrace tailWord_3315970 prefixEnd_3315970 378374765753221441294475 := by
  unfold tailWord_3315970
  simp only [CollatzResearch.WordTrace]
  refine ⟨30235840449203621858466341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80628907864542991622576909 30235840449203621858466341)
  ·
    refine ⟨5669220084225679098462439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30235840449203621858466341 5669220084225679098462439)
    ·
      refine ⟨8503830126338518647693659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5669220084225679098462439 8503830126338518647693659)
      ·
        refine ⟨12755745189507777971540489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8503830126338518647693659 12755745189507777971540489)
        ·
          refine ⟨9566808892130833478655367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12755745189507777971540489 9566808892130833478655367)
          ·
            refine ⟨14350213338196250217983051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9566808892130833478655367 14350213338196250217983051)
            ·
              refine ⟨21525320007294375326974577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14350213338196250217983051 21525320007294375326974577)
              ·
                refine ⟨16143990005470781495230933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21525320007294375326974577 16143990005470781495230933)
                ·
                  refine ⟨378374765753221441294475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16143990005470781495230933 378374765753221441294475)
                  ·
                    rfl

theorem cell22_3315970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3315970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3315970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3315970 prefixEnd_3315970 := by exact prefixLift 3315970
  have htrace : WordTrace (prefixWord ++ tailWord_3315970) baseStart_3315970 baseEnd_3315970 := by
    simpa [prefixWord, tailWord_3315970, baseEnd_3315970] using wordTrace_append hprefix tailTrace_3315970
  have hstable : (prefixWord ++ tailWord_3315970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3315970).length < 2 ^ (prefixWord ++ tailWord_3315970).sum := by decide
  have hdescent : baseEnd_3315970 < baseStart_3315970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3315970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316030 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_3316030 : Nat := 118140960795 + 3316030 * 2 ^ 59
def prefixEnd_3316030 : Nat := 4983230072969 + 3 ^ 40 * 3316030 * 2
def baseEnd_3316030 : Nat := 1135144836485844167383241

theorem tailTrace_3316030 : CollatzResearch.WordTrace tailWord_3316030 prefixEnd_3316030 1135144836485844167383241 := by
  unfold tailWord_3316030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15118193772074639710131193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80630366784398078454033029 15118193772074639710131193)
  ·
    refine ⟨11338645329055979782598395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15118193772074639710131193 11338645329055979782598395)
    ·
      refine ⟨17007967993583969673897593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11338645329055979782598395 17007967993583969673897593)
      ·
        refine ⟨12755975995187977255423195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17007967993583969673897593 12755975995187977255423195)
        ·
          refine ⟨19133963992781965883134793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12755975995187977255423195 19133963992781965883134793)
          ·
            refine ⟨14350472994586474412351095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19133963992781965883134793 14350472994586474412351095)
            ·
              refine ⟨21525709491879711618526643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14350472994586474412351095 21525709491879711618526643)
              ·
                refine ⟨32288564237819567427789965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21525709491879711618526643 32288564237819567427789965)
                ·
                  refine ⟨12108211589182337785421237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32288564237819567427789965 12108211589182337785421237)
                  ·
                    refine ⟨1135144836485844167383241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12108211589182337785421237 1135144836485844167383241)
                    ·
                      rfl

theorem cell22_3316030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_3316030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316030 prefixEnd_3316030 := by exact prefixLift 3316030
  have htrace : WordTrace (prefixWord ++ tailWord_3316030) baseStart_3316030 baseEnd_3316030 := by
    simpa [prefixWord, tailWord_3316030, baseEnd_3316030] using wordTrace_append hprefix tailTrace_3316030
  have hstable : (prefixWord ++ tailWord_3316030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316030).length < 2 ^ (prefixWord ++ tailWord_3316030).sum := by decide
  have hdescent : baseEnd_3316030 < baseStart_3316030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316049 : List Nat := [1, 2, 2, 1, 4, 4, 2, 2, 4]
def baseStart_3316049 : Nat := 118140960795 + 3316049 * 2 ^ 59
def prefixEnd_3316049 : Nat := 4983230072969 + 3 ^ 40 * 3316049 * 2
def baseEnd_3316049 : Nat := 378383780191378150386061

theorem tailTrace_3316049 : CollatzResearch.WordTrace tailWord_3316049 prefixEnd_3316049 378383780191378150386061 := by
  unfold tailWord_3316049
  simp only [CollatzResearch.WordTrace]
  refine ⟨120946243163528283925991201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80630828775685522617327467 120946243163528283925991201)
  ·
    refine ⟨90709682372646212944493401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120946243163528283925991201 90709682372646212944493401)
    ·
      refine ⟨68032261779484659708370051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90709682372646212944493401 68032261779484659708370051)
      ·
        refine ⟨102048392669226989562555077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68032261779484659708370051 102048392669226989562555077)
        ·
          refine ⟨19134073625480060542979077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102048392669226989562555077 19134073625480060542979077)
          ·
            refine ⟨3587638804777511351808577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19134073625480060542979077 3587638804777511351808577)
            ·
              refine ⟨2690729103583133513856433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3587638804777511351808577 2690729103583133513856433)
              ·
                refine ⟨2018046827687350135392325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690729103583133513856433 2018046827687350135392325)
                ·
                  refine ⟨378383780191378150386061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018046827687350135392325 378383780191378150386061)
                  ·
                    rfl

theorem cell22_3316049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 2, 4].length) (baseStart_3316049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316049 prefixEnd_3316049 := by exact prefixLift 3316049
  have htrace : WordTrace (prefixWord ++ tailWord_3316049) baseStart_3316049 baseEnd_3316049 := by
    simpa [prefixWord, tailWord_3316049, baseEnd_3316049] using wordTrace_append hprefix tailTrace_3316049
  have hstable : (prefixWord ++ tailWord_3316049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316049).length < 2 ^ (prefixWord ++ tailWord_3316049).sum := by decide
  have hdescent : baseEnd_3316049 < baseStart_3316049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316058 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_3316058 : Nat := 118140960795 + 3316058 * 2 ^ 59
def prefixEnd_3316058 : Nat := 4983230072969 + 3 ^ 40 * 3316058 * 2
def baseEnd_3316058 : Nat := 1135154421458061427683155

theorem tailTrace_3316058 : CollatzResearch.WordTrace tailWord_3316058 prefixEnd_3316058 1135154421458061427683155 := by
  unfold tailWord_3316058
  simp only [CollatzResearch.WordTrace]
  refine ⟨30236642855123919615767207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80631047613663785642045885 30236642855123919615767207)
  ·
    refine ⟨45354964282685879423650811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30236642855123919615767207 45354964282685879423650811)
    ·
      refine ⟨68032446424028819135476217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45354964282685879423650811 68032446424028819135476217)
      ·
        refine ⟨51024334818021614351607163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68032446424028819135476217 51024334818021614351607163)
        ·
          refine ⟨76536502227032421527410745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51024334818021614351607163 76536502227032421527410745)
          ·
            refine ⟨57402376670274316145558059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76536502227032421527410745 57402376670274316145558059)
            ·
              refine ⟨86103565005411474218337089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57402376670274316145558059 86103565005411474218337089)
              ·
                refine ⟨64577673754058605663752817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86103565005411474218337089 64577673754058605663752817)
                ·
                  refine ⟨48433255315543954247814613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64577673754058605663752817 48433255315543954247814613)
                  ·
                    refine ⟨1135154421458061427683155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48433255315543954247814613 1135154421458061427683155)
                    ·
                      rfl

theorem cell22_3316058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_3316058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316058 prefixEnd_3316058 := by exact prefixLift 3316058
  have htrace : WordTrace (prefixWord ++ tailWord_3316058) baseStart_3316058 baseEnd_3316058 := by
    simpa [prefixWord, tailWord_3316058, baseEnd_3316058] using wordTrace_append hprefix tailTrace_3316058
  have hstable : (prefixWord ++ tailWord_3316058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316058).length < 2 ^ (prefixWord ++ tailWord_3316058).sum := by decide
  have hdescent : baseEnd_3316058 < baseStart_3316058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316073 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 2, 6]
def baseStart_3316073 : Nat := 118140960795 + 3316073 * 2 ^ 59
def prefixEnd_3316073 : Nat := 4983230072969 + 3 ^ 40 * 3316073 * 2
def baseEnd_3316073 : Nat := 1135159556264606388558109

theorem tailTrace_3316073 : CollatzResearch.WordTrace tailWord_3316073 prefixEnd_3316073 1135159556264606388558109 := by
  unfold tailWord_3316073
  simp only [CollatzResearch.WordTrace]
  refine ⟨120947118515441336024864873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80631412343627557349909915 120947118515441336024864873)
  ·
    refine ⟨90710338886581002018648655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120947118515441336024864873 90710338886581002018648655)
    ·
      refine ⟨136065508329871503027972983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90710338886581002018648655 136065508329871503027972983)
      ·
        refine ⟨204098262494807254541959475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136065508329871503027972983 204098262494807254541959475)
        ·
          refine ⟨306147393742210881812939213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204098262494807254541959475 306147393742210881812939213)
          ·
            refine ⟨114805272653329080679852205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306147393742210881812939213 114805272653329080679852205)
            ·
              refine ⟨43051977244998405254944577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114805272653329080679852205 43051977244998405254944577)
              ·
                refine ⟨32288982933748803941208433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43051977244998405254944577 32288982933748803941208433)
                ·
                  refine ⟨24216737200311602955906325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32288982933748803941208433 24216737200311602955906325)
                  ·
                    refine ⟨1135159556264606388558109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24216737200311602955906325 1135159556264606388558109)
                    ·
                      rfl

theorem cell22_3316073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 6].length) (baseStart_3316073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316073 prefixEnd_3316073 := by exact prefixLift 3316073
  have htrace : WordTrace (prefixWord ++ tailWord_3316073) baseStart_3316073 baseEnd_3316073 := by
    simpa [prefixWord, tailWord_3316073, baseEnd_3316073] using wordTrace_append hprefix tailTrace_3316073
  have hstable : (prefixWord ++ tailWord_3316073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316073).length < 2 ^ (prefixWord ++ tailWord_3316073).sum := by decide
  have hdescent : baseEnd_3316073 < baseStart_3316073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316075 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 3, 3]
def baseStart_3316075 : Nat := 118140960795 + 3316075 * 2 ^ 59
def prefixEnd_3316075 : Nat := 4983230072969 + 3 ^ 40 * 3316075 * 2
def baseEnd_3316075 : Nat := 1135160240905479050008103

theorem tailTrace_3316075 : CollatzResearch.WordTrace tailWord_3316075 prefixEnd_3316075 1135160240905479050008103 := by
  unfold tailWord_3316075
  simp only [CollatzResearch.WordTrace]
  refine ⟨120947191461434090366437679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80631460974289393577625119 120947191461434090366437679)
  ·
    refine ⟨181420787192151135549656519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120947191461434090366437679 181420787192151135549656519)
    ·
      refine ⟨272131180788226703324484779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181420787192151135549656519 272131180788226703324484779)
      ·
        refine ⟨408196771182340054986727169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272131180788226703324484779 408196771182340054986727169)
        ·
          refine ⟨306147578386755041240045377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408196771182340054986727169 306147578386755041240045377)
          ·
            refine ⟨229610683790066280930034033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 306147578386755041240045377 229610683790066280930034033)
            ·
              refine ⟨172208012842549710697525525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229610683790066280930034033 172208012842549710697525525)
              ·
                refine ⟨8072250601994517688946509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172208012842549710697525525 8072250601994517688946509)
                ·
                  refine ⟨3027093975747944133354941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8072250601994517688946509 3027093975747944133354941)
                  ·
                    refine ⟨1135160240905479050008103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3027093975747944133354941 1135160240905479050008103)
                    ·
                      rfl

theorem cell22_3316075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 3].length) (baseStart_3316075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316075 prefixEnd_3316075 := by exact prefixLift 3316075
  have htrace : WordTrace (prefixWord ++ tailWord_3316075) baseStart_3316075 baseEnd_3316075 := by
    simpa [prefixWord, tailWord_3316075, baseEnd_3316075] using wordTrace_append hprefix tailTrace_3316075
  have hstable : (prefixWord ++ tailWord_3316075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316075).length < 2 ^ (prefixWord ++ tailWord_3316075).sum := by decide
  have hdescent : baseEnd_3316075 < baseStart_3316075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316098 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3316098 : Nat := 118140960795 + 3316098 * 2 ^ 59
def prefixEnd_3316098 : Nat := 4983230072969 + 3 ^ 40 * 3316098 * 2
def baseEnd_3316098 : Nat := 1135168114275514656683033

theorem tailTrace_3316098 : CollatzResearch.WordTrace tailWord_3316098 prefixEnd_3316098 1135168114275514656683033 := by
  unfold tailWord_3316098
  simp only [CollatzResearch.WordTrace]
  refine ⟨30237007585087691323631237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80632020226900510196349965 30237007585087691323631237)
  ·
    refine ⟨5669438922203942123180857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30237007585087691323631237 5669438922203942123180857)
    ·
      refine ⟨4252079191652956592385643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5669438922203942123180857 4252079191652956592385643)
      ·
        refine ⟨6378118787479434888578465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4252079191652956592385643 6378118787479434888578465)
        ·
          refine ⟨4783589090609576166433849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6378118787479434888578465 4783589090609576166433849)
          ·
            refine ⟨3587691817957182124825387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4783589090609576166433849 3587691817957182124825387)
            ·
              refine ⟨5381537726935773187238081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587691817957182124825387 5381537726935773187238081)
              ·
                refine ⟨4036153295201829890428561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5381537726935773187238081 4036153295201829890428561)
                ·
                  refine ⟨3027114971401372417821421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4036153295201829890428561 3027114971401372417821421)
                  ·
                    refine ⟨1135168114275514656683033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3027114971401372417821421 1135168114275514656683033)
                    ·
                      rfl

theorem cell22_3316098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3316098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316098 prefixEnd_3316098 := by exact prefixLift 3316098
  have htrace : WordTrace (prefixWord ++ tailWord_3316098) baseStart_3316098 baseEnd_3316098 := by
    simpa [prefixWord, tailWord_3316098, baseEnd_3316098] using wordTrace_append hprefix tailTrace_3316098
  have hstable : (prefixWord ++ tailWord_3316098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316098).length < 2 ^ (prefixWord ++ tailWord_3316098).sum := by decide
  have hdescent : baseEnd_3316098 < baseStart_3316098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316105 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 7]
def baseStart_3316105 : Nat := 118140960795 + 3316105 * 2 ^ 59
def prefixEnd_3316105 : Nat := 4983230072969 + 3 ^ 40 * 3316105 * 2
def baseEnd_3316105 : Nat := 378390170172856323919337

theorem tailTrace_3316105 : CollatzResearch.WordTrace tailWord_3316105 prefixEnd_3316105 378390170172856323919337 := by
  unfold tailWord_3316105
  simp only [CollatzResearch.WordTrace]
  refine ⟨120948285651325405490029769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80632190434216936993353179 120948285651325405490029769)
  ·
    refine ⟨90711214238494054117522327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120948285651325405490029769 90711214238494054117522327)
    ·
      refine ⟨136066821357741081176283491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90711214238494054117522327 136066821357741081176283491)
      ·
        refine ⟨204100232036611621764425237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136066821357741081176283491 204100232036611621764425237)
        ·
          refine ⟨9567198376716169770207433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 204100232036611621764425237 9567198376716169770207433)
          ·
            refine ⟨7175398782537127327655575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9567198376716169770207433 7175398782537127327655575)
            ·
              refine ⟨10763098173805690991483363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7175398782537127327655575 10763098173805690991483363)
              ·
                refine ⟨16144647260708536487225045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10763098173805690991483363 16144647260708536487225045)
                ·
                  refine ⟨378390170172856323919337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16144647260708536487225045 378390170172856323919337)
                  ·
                    rfl

theorem cell22_3316105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 7].length) (baseStart_3316105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316105 prefixEnd_3316105 := by exact prefixLift 3316105
  have htrace : WordTrace (prefixWord ++ tailWord_3316105) baseStart_3316105 baseEnd_3316105 := by
    simpa [prefixWord, tailWord_3316105, baseEnd_3316105] using wordTrace_append hprefix tailTrace_3316105
  have hstable : (prefixWord ++ tailWord_3316105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316105).length < 2 ^ (prefixWord ++ tailWord_3316105).sum := by decide
  have hdescent : baseEnd_3316105 < baseStart_3316105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316167 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 6]
def baseStart_3316167 : Nat := 118140960795 + 3316167 * 2 ^ 59
def prefixEnd_3316167 : Nat := 4983230072969 + 3 ^ 40 * 3316167 * 2
def baseEnd_3316167 : Nat := 378397244795207158902607

theorem tailTrace_3316167 : CollatzResearch.WordTrace tailWord_3316167 prefixEnd_3316167 378397244795207158902607 := by
  unfold tailWord_3316167
  simp only [CollatzResearch.WordTrace]
  refine ⟨120950546977100790078786755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80633697984733860052524503 120950546977100790078786755)
  ·
    refine ⟨181425820465651185118180133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120950546977100790078786755 181425820465651185118180133)
    ·
      refine ⟨34017341337309597209658775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181425820465651185118180133 34017341337309597209658775)
      ·
        refine ⟨51026012005964395814488163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34017341337309597209658775 51026012005964395814488163)
        ·
          refine ⟨76539018008946593721732245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51026012005964395814488163 76539018008946593721732245)
          ·
            refine ⟨3587766469169371580706199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 76539018008946593721732245 3587766469169371580706199)
            ·
              refine ⟨5381649703754057371059299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587766469169371580706199 5381649703754057371059299)
              ·
                refine ⟨8072474555631086056588949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381649703754057371059299 8072474555631086056588949)
                ·
                  refine ⟨378397244795207158902607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8072474555631086056588949 378397244795207158902607)
                  ·
                    rfl

theorem cell22_3316167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 6].length) (baseStart_3316167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316167 prefixEnd_3316167 := by exact prefixLift 3316167
  have htrace : WordTrace (prefixWord ++ tailWord_3316167) baseStart_3316167 baseEnd_3316167 := by
    simpa [prefixWord, tailWord_3316167, baseEnd_3316167] using wordTrace_append hprefix tailTrace_3316167
  have hstable : (prefixWord ++ tailWord_3316167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316167).length < 2 ^ (prefixWord ++ tailWord_3316167).sum := by decide
  have hdescent : baseEnd_3316167 < baseStart_3316167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316227 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 3, 3]
def baseStart_3316227 : Nat := 118140960795 + 3316227 * 2 ^ 59
def prefixEnd_3316227 : Nat := 4983230072969 + 3 ^ 40 * 3316227 * 2
def baseEnd_3316227 : Nat := 1135212273611801320207637

theorem tailTrace_3316227 : CollatzResearch.WordTrace tailWord_3316227 prefixEnd_3316227 1135212273611801320207637 := by
  unfold tailWord_3316227
  simp only [CollatzResearch.WordTrace]
  refine ⟨120952735356883420325970935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80635156904588946883980623 120952735356883420325970935)
  ·
    refine ⟨181429103035325130488956403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120952735356883420325970935 181429103035325130488956403)
    ·
      refine ⟨272143654552987695733434605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181429103035325130488956403 272143654552987695733434605)
      ·
        refine ⟨102053870457370385900037977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 272143654552987695733434605 102053870457370385900037977)
        ·
          refine ⟨76540402843027789425028483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102053870457370385900037977 76540402843027789425028483)
          ·
            refine ⟨114810604264541684137542725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76540402843027789425028483 114810604264541684137542725)
            ·
              refine ⟨21526988299601565775789261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114810604264541684137542725 21526988299601565775789261)
              ·
                refine ⟨8072620612350587165920973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21526988299601565775789261 8072620612350587165920973)
                ·
                  refine ⟨3027232729631470187220365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8072620612350587165920973 3027232729631470187220365)
                  ·
                    refine ⟨1135212273611801320207637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3027232729631470187220365 1135212273611801320207637)
                    ·
                      rfl

theorem cell22_3316227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 3].length) (baseStart_3316227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316227 prefixEnd_3316227 := by exact prefixLift 3316227
  have htrace : WordTrace (prefixWord ++ tailWord_3316227) baseStart_3316227 baseEnd_3316227 := by
    simpa [prefixWord, tailWord_3316227, baseEnd_3316227] using wordTrace_append hprefix tailTrace_3316227
  have hstable : (prefixWord ++ tailWord_3316227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316227).length < 2 ^ (prefixWord ++ tailWord_3316227).sum := by decide
  have hdescent : baseEnd_3316227 < baseStart_3316227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316255 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 3, 7]
def baseStart_3316255 : Nat := 118140960795 + 3316255 * 2 ^ 59
def prefixEnd_3316255 : Nat := 4983230072969 + 3 ^ 40 * 3316255 * 2
def baseEnd_3316255 : Nat := 1135221858584018580507551

theorem tailTrace_3316255 : CollatzResearch.WordTrace tailWord_3316255 prefixEnd_3316255 1135221858584018580507551 := by
  unfold tailWord_3316255
  simp only [CollatzResearch.WordTrace]
  refine ⟨120953756600781981107990219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80635837733854654071993479 120953756600781981107990219)
  ·
    refine ⟨181430634901172971661985329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120953756600781981107990219 181430634901172971661985329)
    ·
      refine ⟨136072976175879728746488997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181430634901172971661985329 136072976175879728746488997)
      ·
        refine ⟨25513683032977449139966687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136072976175879728746488997 25513683032977449139966687)
        ·
          refine ⟨38270524549466173709950031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25513683032977449139966687 38270524549466173709950031)
          ·
            refine ⟨57405786824199260564925047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38270524549466173709950031 57405786824199260564925047)
            ·
              refine ⟨86108680236298890847387571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57405786824199260564925047 86108680236298890847387571)
              ·
                refine ⟨129163020354448336271081357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86108680236298890847387571 129163020354448336271081357)
                ·
                  refine ⟨48436132632918126101655509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129163020354448336271081357 48436132632918126101655509)
                  ·
                    refine ⟨1135221858584018580507551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48436132632918126101655509 1135221858584018580507551)
                    ·
                      rfl

theorem cell22_3316255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_3316255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316255 prefixEnd_3316255 := by exact prefixLift 3316255
  have htrace : WordTrace (prefixWord ++ tailWord_3316255) baseStart_3316255 baseEnd_3316255 := by
    simpa [prefixWord, tailWord_3316255, baseEnd_3316255] using wordTrace_append hprefix tailTrace_3316255
  have hstable : (prefixWord ++ tailWord_3316255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316255).length < 2 ^ (prefixWord ++ tailWord_3316255).sum := by decide
  have hdescent : baseEnd_3316255 < baseStart_3316255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316278 : List Nat := [5, 1, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3316278 : Nat := 118140960795 + 3316278 * 2 ^ 59
def prefixEnd_3316278 : Nat := 4983230072969 + 3 ^ 40 * 3316278 * 2
def baseEnd_3316278 : Nat := 1135229731954054187182481

theorem tailTrace_3316278 : CollatzResearch.WordTrace tailWord_3316278 prefixEnd_3316278 1135229731954054187182481 := by
  unfold tailWord_3316278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7559662217481166002254843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 80636396986465770690718325 7559662217481166002254843)
  ·
    refine ⟨11339493326221749003382265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7559662217481166002254843 11339493326221749003382265)
    ·
      refine ⟨8504619994666311752536699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11339493326221749003382265 8504619994666311752536699)
      ·
        refine ⟨12756929991999467628805049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8504619994666311752536699 12756929991999467628805049)
        ·
          refine ⟨9567697493999600721603787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12756929991999467628805049 9567697493999600721603787)
          ·
            refine ⟨14351546240999401082405681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9567697493999600721603787 14351546240999401082405681)
            ·
              refine ⟨10763659680749550811804261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14351546240999401082405681 10763659680749550811804261)
              ·
                refine ⟨2018186190140540777213299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10763659680749550811804261 2018186190140540777213299)
                ·
                  refine ⟨3027279285210811165819949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018186190140540777213299 3027279285210811165819949)
                  ·
                    refine ⟨1135229731954054187182481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3027279285210811165819949 1135229731954054187182481)
                    ·
                      rfl

theorem cell22_3316278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3316278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316278 prefixEnd_3316278 := by exact prefixLift 3316278
  have htrace : WordTrace (prefixWord ++ tailWord_3316278) baseStart_3316278 baseEnd_3316278 := by
    simpa [prefixWord, tailWord_3316278, baseEnd_3316278] using wordTrace_append hprefix tailTrace_3316278
  have hstable : (prefixWord ++ tailWord_3316278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316278).length < 2 ^ (prefixWord ++ tailWord_3316278).sum := by decide
  have hdescent : baseEnd_3316278 < baseStart_3316278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316302 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_3316302 : Nat := 118140960795 + 3316302 * 2 ^ 59
def prefixEnd_3316302 : Nat := 4983230072969 + 3 ^ 40 * 3316302 * 2
def baseEnd_3316302 : Nat := 378412649214842041527469

theorem tailTrace_3316302 : CollatzResearch.WordTrace tailWord_3316302 prefixEnd_3316302 378412649214842041527469 := by
  unfold tailWord_3316302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15119433853951463516868895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80636980554407805423300773 15119433853951463516868895)
  ·
    refine ⟨22679150780927195275303343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15119433853951463516868895 22679150780927195275303343)
    ·
      refine ⟨34018726171390792912955015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22679150780927195275303343 34018726171390792912955015)
      ·
        refine ⟨51028089257086189369432523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34018726171390792912955015 51028089257086189369432523)
        ·
          refine ⟨76542133885629284054148785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51028089257086189369432523 76542133885629284054148785)
          ·
            refine ⟨57406600414221963040611589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76542133885629284054148785 57406600414221963040611589)
            ·
              refine ⟨10763737577666618070114673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57406600414221963040611589 10763737577666618070114673)
              ·
                refine ⟨8072803183249963552586005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10763737577666618070114673 8072803183249963552586005)
                ·
                  refine ⟨378412649214842041527469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8072803183249963552586005 378412649214842041527469)
                  ·
                    rfl

theorem cell22_3316302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_3316302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316302 prefixEnd_3316302 := by exact prefixLift 3316302
  have htrace : WordTrace (prefixWord ++ tailWord_3316302) baseStart_3316302 baseEnd_3316302 := by
    simpa [prefixWord, tailWord_3316302, baseEnd_3316302] using wordTrace_append hprefix tailTrace_3316302
  have hstable : (prefixWord ++ tailWord_3316302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316302).length < 2 ^ (prefixWord ++ tailWord_3316302).sum := by decide
  have hdescent : baseEnd_3316302 < baseStart_3316302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316332 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_3316332 : Nat := 118140960795 + 3316332 * 2 ^ 59
def prefixEnd_3316332 : Nat := 4983230072969 + 3 ^ 40 * 3316332 * 2
def baseEnd_3316332 : Nat := 1135248217257616046332315

theorem tailTrace_3316332 : CollatzResearch.WordTrace tailWord_3316332 prefixEnd_3316332 1135248217257616046332315 := by
  unfold tailWord_3316332
  simp only [CollatzResearch.WordTrace]
  refine ⟨60478282510751511629271625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80637710014335348839028833 60478282510751511629271625)
  ·
    refine ⟨45358711883063633721953719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60478282510751511629271625 45358711883063633721953719)
    ·
      refine ⟨68038067824595450582930579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45358711883063633721953719 68038067824595450582930579)
      ·
        refine ⟨102057101736893175874395869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68038067824595450582930579 102057101736893175874395869)
        ·
          refine ⟨38271413151334940952898451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102057101736893175874395869 38271413151334940952898451)
          ·
            refine ⟨57407119727002411429347677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38271413151334940952898451 57407119727002411429347677)
            ·
              refine ⟨21527669897625904286005379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57407119727002411429347677 21527669897625904286005379)
              ·
                refine ⟨32291504846438856429008069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21527669897625904286005379 32291504846438856429008069)
                ·
                  refine ⟨6054657158707285580439013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32291504846438856429008069 6054657158707285580439013)
                  ·
                    refine ⟨1135248217257616046332315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6054657158707285580439013 1135248217257616046332315)
                    ·
                      rfl

theorem cell22_3316332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_3316332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316332 prefixEnd_3316332 := by exact prefixLift 3316332
  have htrace : WordTrace (prefixWord ++ tailWord_3316332) baseStart_3316332 baseEnd_3316332 := by
    simpa [prefixWord, tailWord_3316332, baseEnd_3316332] using wordTrace_append hprefix tailTrace_3316332
  have hstable : (prefixWord ++ tailWord_3316332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316332).length < 2 ^ (prefixWord ++ tailWord_3316332).sum := by decide
  have hdescent : baseEnd_3316332 < baseStart_3316332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316336 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 6]
def baseStart_3316336 : Nat := 118140960795 + 3316336 * 2 ^ 59
def prefixEnd_3316336 : Nat := 4983230072969 + 3 ^ 40 * 3316336 * 2
def baseEnd_3316336 : Nat := 378416528846453789744101

theorem tailTrace_3316336 : CollatzResearch.WordTrace tailWord_3316336 prefixEnd_3316336 378416528846453789744101 := by
  unfold tailWord_3316336
  simp only [CollatzResearch.WordTrace]
  refine ⟨60478355456744265970844431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80637807275659021294459241 60478355456744265970844431)
  ·
    refine ⟨90717533185116398956266647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60478355456744265970844431 90717533185116398956266647)
    ·
      refine ⟨136076299777674598434399971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90717533185116398956266647 136076299777674598434399971)
      ·
        refine ⟨204114449666511897651599957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136076299777674598434399971 204114449666511897651599957)
        ·
          refine ⟨2391966207029436300604687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 204114449666511897651599957 2391966207029436300604687)
          ·
            refine ⟨3587949310544154450907031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391966207029436300604687 3587949310544154450907031)
            ·
              refine ⟨5381923965816231676360547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3587949310544154450907031 5381923965816231676360547)
              ·
                refine ⟨8072885948724347514540821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5381923965816231676360547 8072885948724347514540821)
                ·
                  refine ⟨378416528846453789744101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8072885948724347514540821 378416528846453789744101)
                  ·
                    rfl

theorem cell22_3316336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 6].length) (baseStart_3316336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316336 prefixEnd_3316336 := by exact prefixLift 3316336
  have htrace : WordTrace (prefixWord ++ tailWord_3316336) baseStart_3316336 baseEnd_3316336 := by
    simpa [prefixWord, tailWord_3316336, baseEnd_3316336] using wordTrace_append hprefix tailTrace_3316336
  have hstable : (prefixWord ++ tailWord_3316336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316336).length < 2 ^ (prefixWord ++ tailWord_3316336).sum := by decide
  have hdescent : baseEnd_3316336 < baseStart_3316336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316484 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 1, 6]
def baseStart_3316484 : Nat := 118140960795 + 3316484 * 2 ^ 59
def prefixEnd_3316484 : Nat := 4983230072969 + 3 ^ 40 * 3316484 * 2
def baseEnd_3316484 : Nat := 1135300249963938316531849

theorem tailTrace_3316484 : CollatzResearch.WordTrace tailWord_3316484 prefixEnd_3316484 1135300249963938316531849 := by
  unfold tailWord_3316484
  simp only [CollatzResearch.WordTrace]
  refine ⟨60481054458476176609038253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80641405944634902145384337 60481054458476176609038253)
  ·
    refine ⟨22680395421928566228389345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60481054458476176609038253 22680395421928566228389345)
    ·
      refine ⟨17010296566446424671292009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22680395421928566228389345 17010296566446424671292009)
      ·
        refine ⟨12757722424834818503469007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17010296566446424671292009 12757722424834818503469007)
        ·
          refine ⟨19136583637252227755203511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12757722424834818503469007 19136583637252227755203511)
          ·
            refine ⟨28704875455878341632805267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19136583637252227755203511 28704875455878341632805267)
            ·
              refine ⟨43057313183817512449207901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28704875455878341632805267 43057313183817512449207901)
              ·
                refine ⟨16146492443931567168452963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43057313183817512449207901 16146492443931567168452963)
                ·
                  refine ⟨24219738665897350752679445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16146492443931567168452963 24219738665897350752679445)
                  ·
                    refine ⟨1135300249963938316531849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24219738665897350752679445 1135300249963938316531849)
                    ·
                      rfl

theorem cell22_3316484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_3316484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316484 prefixEnd_3316484 := by exact prefixLift 3316484
  have htrace : WordTrace (prefixWord ++ tailWord_3316484) baseStart_3316484 baseEnd_3316484 := by
    simpa [prefixWord, tailWord_3316484, baseEnd_3316484] using wordTrace_append hprefix tailTrace_3316484
  have hstable : (prefixWord ++ tailWord_3316484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316484).length < 2 ^ (prefixWord ++ tailWord_3316484).sum := by decide
  have hdescent : baseEnd_3316484 < baseStart_3316484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316488 : List Nat := [2, 1, 3, 2, 2, 4, 1, 3, 4]
def baseStart_3316488 : Nat := 118140960795 + 3316488 * 2 ^ 59
def prefixEnd_3316488 : Nat := 4983230072969 + 3 ^ 40 * 3316488 * 2
def baseEnd_3316488 : Nat := 378433873081894546477279

theorem tailTrace_3316488 : CollatzResearch.WordTrace tailWord_3316488 prefixEnd_3316488 378433873081894546477279 := by
  unfold tailWord_3316488
  simp only [CollatzResearch.WordTrace]
  refine ⟨60481127404468930950611059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80641503205958574600814745 60481127404468930950611059)
  ·
    refine ⟨90721691106703396425916589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60481127404468930950611059 90721691106703396425916589)
    ·
      refine ⟨34020634165013773659718721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90721691106703396425916589 34020634165013773659718721)
      ·
        refine ⟨25515475623760330244789041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34020634165013773659718721 25515475623760330244789041)
        ·
          refine ⟨19136606717820247683591781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25515475623760330244789041 19136606717820247683591781)
          ·
            refine ⟨3588113759591296440673459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19136606717820247683591781 3588113759591296440673459)
            ·
              refine ⟨5382170639386944661010189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588113759591296440673459 5382170639386944661010189)
              ·
                refine ⟨2018313989770104247878821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5382170639386944661010189 2018313989770104247878821)
                ·
                  refine ⟨378433873081894546477279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018313989770104247878821 378433873081894546477279)
                  ·
                    rfl

theorem cell22_3316488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 3, 4].length) (baseStart_3316488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316488 prefixEnd_3316488 := by exact prefixLift 3316488
  have htrace : WordTrace (prefixWord ++ tailWord_3316488) baseStart_3316488 baseEnd_3316488 := by
    simpa [prefixWord, tailWord_3316488, baseEnd_3316488] using wordTrace_append hprefix tailTrace_3316488
  have hstable : (prefixWord ++ tailWord_3316488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316488).length < 2 ^ (prefixWord ++ tailWord_3316488).sum := by decide
  have hdescent : baseEnd_3316488 < baseStart_3316488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316516 : List Nat := [2, 3, 1, 3, 3, 1, 2, 7]
def baseStart_3316516 : Nat := 118140960795 + 3316516 * 2 ^ 59
def prefixEnd_3316516 : Nat := 4983230072969 + 3 ^ 40 * 3316516 * 2
def baseEnd_3316516 : Nat := 126145689357544544414639

theorem tailTrace_3316516 : CollatzResearch.WordTrace tailWord_3316516 prefixEnd_3316516 126145689357544544414639 := by
  unfold tailWord_3316516
  simp only [CollatzResearch.WordTrace]
  refine ⟨60481638026418211341620701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80642184035224281788827601 60481638026418211341620701)
  ·
    refine ⟨22680614259906829253107763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60481638026418211341620701 22680614259906829253107763)
    ·
      refine ⟨34020921389860243879661645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22680614259906829253107763 34020921389860243879661645)
      ·
        refine ⟨12757845521197591454873117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34020921389860243879661645 12757845521197591454873117)
        ·
          refine ⟨4784192070449096795577419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12757845521197591454873117 4784192070449096795577419)
          ·
            refine ⟨7176288105673645193366129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784192070449096795577419 7176288105673645193366129)
            ·
              refine ⟨5382216079255233895024597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7176288105673645193366129 5382216079255233895024597)
              ·
                refine ⟨126145689357544544414639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5382216079255233895024597 126145689357544544414639)
                ·
                  rfl

theorem cell22_3316516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 7].length) (baseStart_3316516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316516 prefixEnd_3316516 := by exact prefixLift 3316516
  have htrace : WordTrace (prefixWord ++ tailWord_3316516) baseStart_3316516 baseEnd_3316516 := by
    simpa [prefixWord, tailWord_3316516, baseEnd_3316516] using wordTrace_append hprefix tailTrace_3316516
  have hstable : (prefixWord ++ tailWord_3316516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316516).length < 2 ^ (prefixWord ++ tailWord_3316516).sum := by decide
  have hdescent : baseEnd_3316516 < baseStart_3316516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316649 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_3316649 : Nat := 118140960795 + 3316649 * 2 ^ 59
def prefixEnd_3316649 : Nat := 4983230072969 + 3 ^ 40 * 3316649 * 2
def baseEnd_3316649 : Nat := 1135356732835932886156343

theorem tailTrace_3316649 : CollatzResearch.WordTrace tailWord_3316649 prefixEnd_3316649 1135356732835932886156343 := by
  unfold tailWord_3316649
  simp only [CollatzResearch.WordTrace]
  refine ⟨120968126961354586397833001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80645417974236390931888667 120968126961354586397833001)
  ·
    refine ⟨90726095221015939798374751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120968126961354586397833001 90726095221015939798374751)
    ·
      refine ⟨136089142831523909697562127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90726095221015939798374751 136089142831523909697562127)
      ·
        refine ⟨204133714247285864546343191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136089142831523909697562127 204133714247285864546343191)
        ·
          refine ⟨306200571370928796819514787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204133714247285864546343191 306200571370928796819514787)
          ·
            refine ⟨459300857056393195229272181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306200571370928796819514787 459300857056393195229272181)
            ·
              refine ⟨43059455349036862052744267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 459300857056393195229272181 43059455349036862052744267)
              ·
                refine ⟨64589183023555293079116401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43059455349036862052744267 64589183023555293079116401)
                ·
                  refine ⟨48441887267666469809337301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64589183023555293079116401 48441887267666469809337301)
                  ·
                    refine ⟨1135356732835932886156343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48441887267666469809337301 1135356732835932886156343)
                    ·
                      rfl

theorem cell22_3316649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_3316649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316649 prefixEnd_3316649 := by exact prefixLift 3316649
  have htrace : WordTrace (prefixWord ++ tailWord_3316649) baseStart_3316649 baseEnd_3316649 := by
    simpa [prefixWord, tailWord_3316649, baseEnd_3316649] using wordTrace_append hprefix tailTrace_3316649
  have hstable : (prefixWord ++ tailWord_3316649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316649).length < 2 ^ (prefixWord ++ tailWord_3316649).sum := by decide
  have hdescent : baseEnd_3316649 < baseStart_3316649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316657 : List Nat := [1, 2, 2, 4, 4, 1, 1, 3, 4]
def baseStart_3316657 : Nat := 118140960795 + 3316657 * 2 ^ 59
def prefixEnd_3316657 : Nat := 4983230072969 + 3 ^ 40 * 3316657 * 2
def baseEnd_3316657 : Nat := 378453157133141177318773

theorem tailTrace_3316657 : CollatzResearch.WordTrace tailWord_3316657 prefixEnd_3316657 378453157133141177318773 := by
  unfold tailWord_3316657
  simp only [CollatzResearch.WordTrace]
  refine ⟨120968418745325603764124225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80645612496883735842749483 120968418745325603764124225)
  ·
    refine ⟨90726314058994202823093169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120968418745325603764124225 90726314058994202823093169)
    ·
      refine ⟨68044735544245652117319877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90726314058994202823093169 68044735544245652117319877)
      ·
        refine ⟨12758387914546059771997477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68044735544245652117319877 12758387914546059771997477)
        ·
          refine ⟨2392197733977386207249527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12758387914546059771997477 2392197733977386207249527)
          ·
            refine ⟨3588296600966079310874291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392197733977386207249527 3588296600966079310874291)
            ·
              refine ⟨5382444901449118966311437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588296600966079310874291 5382444901449118966311437)
              ·
                refine ⟨2018416838043419612366789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5382444901449118966311437 2018416838043419612366789)
                ·
                  refine ⟨378453157133141177318773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018416838043419612366789 378453157133141177318773)
                  ·
                    rfl

theorem cell22_3316657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 3, 4].length) (baseStart_3316657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316657 prefixEnd_3316657 := by exact prefixLift 3316657
  have htrace : WordTrace (prefixWord ++ tailWord_3316657) baseStart_3316657 baseEnd_3316657 := by
    simpa [prefixWord, tailWord_3316657, baseEnd_3316657] using wordTrace_append hprefix tailTrace_3316657
  have hstable : (prefixWord ++ tailWord_3316657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316657).length < 2 ^ (prefixWord ++ tailWord_3316657).sum := by decide
  have hdescent : baseEnd_3316657 < baseStart_3316657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316683 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 3, 3]
def baseStart_3316683 : Nat := 118140960795 + 3316683 * 2 ^ 59
def prefixEnd_3316683 : Nat := 4983230072969 + 3 ^ 40 * 3316683 * 2
def baseEnd_3316683 : Nat := 1135368371730768130806239

theorem tailTrace_3316683 : CollatzResearch.WordTrace tailWord_3316683 prefixEnd_3316683 1135368371730768130806239 := by
  unfold tailWord_3316683
  simp only [CollatzResearch.WordTrace]
  refine ⟨120969367043231410204570703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80646244695487606803047135 120969367043231410204570703)
  ·
    refine ⟨181454050564847115306856055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120969367043231410204570703 181454050564847115306856055)
    ·
      refine ⟨272181075847270672960284083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181454050564847115306856055 272181075847270672960284083)
      ·
        refine ⟨408271613770906009440426125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272181075847270672960284083 408271613770906009440426125)
        ·
          refine ⟨153101855164089753540159797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 408271613770906009440426125 153101855164089753540159797)
          ·
            refine ⟨14353298921633414394389981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153101855164089753540159797 14353298921633414394389981)
            ·
              refine ⟨5382487095612530397896243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14353298921633414394389981 5382487095612530397896243)
              ·
                refine ⟨8073730643418795596844365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5382487095612530397896243 8073730643418795596844365)
                ·
                  refine ⟨3027648991282048348816637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8073730643418795596844365 3027648991282048348816637)
                  ·
                    refine ⟨1135368371730768130806239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3027648991282048348816637 1135368371730768130806239)
                    ·
                      rfl

theorem cell22_3316683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 3].length) (baseStart_3316683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316683 prefixEnd_3316683 := by exact prefixLift 3316683
  have htrace : WordTrace (prefixWord ++ tailWord_3316683) baseStart_3316683 baseEnd_3316683 := by
    simpa [prefixWord, tailWord_3316683, baseEnd_3316683] using wordTrace_append hprefix tailTrace_3316683
  have hstable : (prefixWord ++ tailWord_3316683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316683).length < 2 ^ (prefixWord ++ tailWord_3316683).sum := by decide
  have hdescent : baseEnd_3316683 < baseStart_3316683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316734 : List Nat := [4, 2, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_3316734 : Nat := 118140960795 + 3316734 * 2 ^ 59
def prefixEnd_3316734 : Nat := 4983230072969 + 3 ^ 40 * 3316734 * 2
def baseEnd_3316734 : Nat := 1135385830073020997781083

theorem tailTrace_3316734 : CollatzResearch.WordTrace tailWord_3316734 prefixEnd_3316734 1135385830073020997781083 := by
  unfold tailWord_3316734
  simp only [CollatzResearch.WordTrace]
  refine ⟨15121403395755830739334657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80647484777364430609784837 15121403395755830739334657)
  ·
    refine ⟨11341052546816873054500993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15121403395755830739334657 11341052546816873054500993)
    ·
      refine ⟨8505789410112654790875745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11341052546816873054500993 8505789410112654790875745)
      ·
        refine ⟨6379342057584491093156809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8505789410112654790875745 6379342057584491093156809)
        ·
          refine ⟨4784506543188368319867607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6379342057584491093156809 4784506543188368319867607)
          ·
            refine ⟨7176759814782552479801411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784506543188368319867607 7176759814782552479801411)
            ·
              refine ⟨10765139722173828719702117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7176759814782552479801411 10765139722173828719702117)
              ·
                refine ⟨2018463697907592884944147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10765139722173828719702117 2018463697907592884944147)
                ·
                  refine ⟨3027695546861389327416221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018463697907592884944147 3027695546861389327416221)
                  ·
                    refine ⟨1135385830073020997781083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3027695546861389327416221 1135385830073020997781083)
                    ·
                      rfl

theorem cell22_3316734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_3316734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316734 prefixEnd_3316734 := by exact prefixLift 3316734
  have htrace : WordTrace (prefixWord ++ tailWord_3316734) baseStart_3316734 baseEnd_3316734 := by
    simpa [prefixWord, tailWord_3316734, baseEnd_3316734] using wordTrace_append hprefix tailTrace_3316734
  have hstable : (prefixWord ++ tailWord_3316734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316734).length < 2 ^ (prefixWord ++ tailWord_3316734).sum := by decide
  have hdescent : baseEnd_3316734 < baseStart_3316734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316741 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 6]
def baseStart_3316741 : Nat := 118140960795 + 3316741 * 2 ^ 59
def prefixEnd_3316741 : Nat := 4983230072969 + 3 ^ 40 * 3316741 * 2
def baseEnd_3316741 : Nat := 378462742105358437618687

theorem tailTrace_3316741 : CollatzResearch.WordTrace tailWord_3316741 prefixEnd_3316741 378462742105358437618687 := by
  unfold tailWord_3316741
  simp only [CollatzResearch.WordTrace]
  refine ⟨120971482477021286110182077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80647654984680857406788051 120971482477021286110182077)
  ·
    refine ⟨45364305928882982291318279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120971482477021286110182077 45364305928882982291318279)
    ·
      refine ⟨68046458893324473436977419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45364305928882982291318279 68046458893324473436977419)
      ·
        refine ⟨102069688339986710155466129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68046458893324473436977419 102069688339986710155466129)
        ·
          refine ⟨76552266254990032616599597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102069688339986710155466129 76552266254990032616599597)
          ·
            refine ⟨28707099845621262231224849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76552266254990032616599597 28707099845621262231224849)
            ·
              refine ⟨21530324884215946673418637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28707099845621262231224849 21530324884215946673418637)
              ·
                refine ⟨8073871831580980002531989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21530324884215946673418637 8073871831580980002531989)
                ·
                  refine ⟨378462742105358437618687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8073871831580980002531989 378462742105358437618687)
                  ·
                    rfl

theorem cell22_3316741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_3316741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316741 prefixEnd_3316741 := by exact prefixLift 3316741
  have htrace : WordTrace (prefixWord ++ tailWord_3316741) baseStart_3316741 baseEnd_3316741 := by
    simpa [prefixWord, tailWord_3316741, baseEnd_3316741] using wordTrace_append hprefix tailTrace_3316741
  have hstable : (prefixWord ++ tailWord_3316741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316741).length < 2 ^ (prefixWord ++ tailWord_3316741).sum := by decide
  have hdescent : baseEnd_3316741 < baseStart_3316741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316773 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 4, 3]
def baseStart_3316773 : Nat := 118140960795 + 3316773 * 2 ^ 59
def prefixEnd_3316773 : Nat := 4983230072969 + 3 ^ 40 * 3316773 * 2
def baseEnd_3316773 : Nat := 1135399180570037896055963

theorem tailTrace_3316773 : CollatzResearch.WordTrace tailWord_3316773 prefixEnd_3316773 1135399180570037896055963 := by
  unfold tailWord_3316773
  simp only [CollatzResearch.WordTrace]
  refine ⟨120972649612905355575346973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80648433075270237050231315 120972649612905355575346973)
  ·
    refine ⟨45364743604839508340755115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120972649612905355575346973 45364743604839508340755115)
    ·
      refine ⟨68047115407259262511132673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45364743604839508340755115 68047115407259262511132673)
      ·
        refine ⟨51035336555444446883349505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68047115407259262511132673 51035336555444446883349505)
        ·
          refine ⟨38276502416583335162512129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51035336555444446883349505 38276502416583335162512129)
          ·
            refine ⟨28707376812437501371884097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38276502416583335162512129 28707376812437501371884097)
            ·
              refine ⟨21530532609328126028913073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28707376812437501371884097 21530532609328126028913073)
              ·
                refine ⟨16147899456996094521684805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21530532609328126028913073 16147899456996094521684805)
                ·
                  refine ⟨3027731148186767722815901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16147899456996094521684805 3027731148186767722815901)
                  ·
                    refine ⟨1135399180570037896055963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3027731148186767722815901 1135399180570037896055963)
                    ·
                      rfl

theorem cell22_3316773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_3316773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316773 prefixEnd_3316773 := by exact prefixLift 3316773
  have htrace : WordTrace (prefixWord ++ tailWord_3316773) baseStart_3316773 baseEnd_3316773 := by
    simpa [prefixWord, tailWord_3316773, baseEnd_3316773] using wordTrace_append hprefix tailTrace_3316773
  have hstable : (prefixWord ++ tailWord_3316773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316773).length < 2 ^ (prefixWord ++ tailWord_3316773).sum := by decide
  have hdescent : baseEnd_3316773 < baseStart_3316773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316786 : List Nat := [3, 2, 1, 1, 2, 2, 11]
def baseStart_3316786 : Nat := 118140960795 + 3316786 * 2 ^ 59
def prefixEnd_3316786 : Nat := 4983230072969 + 3 ^ 40 * 3316786 * 2
def baseEnd_3316786 : Nat := 42051986323544822054849

theorem tailTrace_3316786 : CollatzResearch.WordTrace tailWord_3316786 prefixEnd_3316786 42051986323544822054849 := by
  unfold tailWord_3316786
  simp only [CollatzResearch.WordTrace]
  refine ⟨30243280940464564698892553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80648749174572172530380141 30243280940464564698892553)
  ·
    refine ⟨22682460705348423524169415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30243280940464564698892553 22682460705348423524169415)
    ·
      refine ⟨34023691058022635286254123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22682460705348423524169415 34023691058022635286254123)
      ·
        refine ⟨51035536587033952929381185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34023691058022635286254123 51035536587033952929381185)
        ·
          refine ⟨38276652440275464697035889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51035536587033952929381185 38276652440275464697035889)
          ·
            refine ⟨28707489330206598522776917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38276652440275464697035889 28707489330206598522776917)
            ·
              refine ⟨42051986323544822054849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28707489330206598522776917 42051986323544822054849)
              ·
                rfl

theorem cell22_3316786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 11].length) (baseStart_3316786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316786 prefixEnd_3316786 := by exact prefixLift 3316786
  have htrace : WordTrace (prefixWord ++ tailWord_3316786) baseStart_3316786 baseEnd_3316786 := by
    simpa [prefixWord, tailWord_3316786, baseEnd_3316786] using wordTrace_append hprefix tailTrace_3316786
  have hstable : (prefixWord ++ tailWord_3316786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316786).length < 2 ^ (prefixWord ++ tailWord_3316786).sum := by decide
  have hdescent : baseEnd_3316786 < baseStart_3316786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316807 : List Nat := [1, 1, 4, 1, 3, 3, 3, 1, 2, 3]
def baseStart_3316807 : Nat := 118140960795 + 3316807 * 2 ^ 59
def prefixEnd_3316807 : Nat := 4983230072969 + 3 ^ 40 * 3316807 * 2
def baseEnd_3316807 : Nat := 1135410819464873140705859

theorem tailTrace_3316807 : CollatzResearch.WordTrace tailWord_3316807 prefixEnd_3316807 1135410819464873140705859 := by
  unfold tailWord_3316807
  simp only [CollatzResearch.WordTrace]
  refine ⟨120973889694782179382084675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80649259796521452921389783 120973889694782179382084675)
  ·
    refine ⟨181460834542173269073127013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120973889694782179382084675 181460834542173269073127013)
    ·
      refine ⟨34023906476657487951211315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 181460834542173269073127013 34023906476657487951211315)
      ·
        refine ⟨51035859714986231926816973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34023906476657487951211315 51035859714986231926816973)
        ·
          refine ⟨19138447393119836972556365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51035859714986231926816973 19138447393119836972556365)
          ·
            refine ⟨7176917772419938864708637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19138447393119836972556365 7176917772419938864708637)
            ·
              refine ⟨2691344164657477074265739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7176917772419938864708637 2691344164657477074265739)
              ·
                refine ⟨4037016246986215611398609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691344164657477074265739 4037016246986215611398609)
                ·
                  refine ⟨3027762185239661708548957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4037016246986215611398609 3027762185239661708548957)
                  ·
                    refine ⟨1135410819464873140705859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3027762185239661708548957 1135410819464873140705859)
                    ·
                      rfl

theorem cell22_3316807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_3316807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316807 prefixEnd_3316807 := by exact prefixLift 3316807
  have htrace : WordTrace (prefixWord ++ tailWord_3316807) baseStart_3316807 baseEnd_3316807 := by
    simpa [prefixWord, tailWord_3316807, baseEnd_3316807] using wordTrace_append hprefix tailTrace_3316807
  have hstable : (prefixWord ++ tailWord_3316807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316807).length < 2 ^ (prefixWord ++ tailWord_3316807).sum := by decide
  have hdescent : baseEnd_3316807 < baseStart_3316807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316816 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 2, 6]
def baseStart_3316816 : Nat := 118140960795 + 3316816 * 2 ^ 59
def prefixEnd_3316816 : Nat := 4983230072969 + 3 ^ 40 * 3316816 * 2
def baseEnd_3316816 : Nat := 1135413900348800117230831

theorem tailTrace_3316816 : CollatzResearch.WordTrace tailWord_3316816 prefixEnd_3316816 1135413900348800117230831 := by
  unfold tailWord_3316816
  simp only [CollatzResearch.WordTrace]
  refine ⟨60487108975874786959581151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80649478634499715946108201 60487108975874786959581151)
  ·
    refine ⟨90730663463812180439371727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60487108975874786959581151 90730663463812180439371727)
    ·
      refine ⟨136095995195718270659057591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90730663463812180439371727 136095995195718270659057591)
      ·
        refine ⟨204143992793577405988586387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136095995195718270659057591 204143992793577405988586387)
        ·
          refine ⟨306215989190366108982879581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204143992793577405988586387 306215989190366108982879581)
          ·
            refine ⟨114830995946387290868579843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 306215989190366108982879581 114830995946387290868579843)
            ·
              refine ⟨172246493919580936302869765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114830995946387290868579843 172246493919580936302869765)
              ·
                refine ⟨32296217609921425556788081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172246493919580936302869765 32296217609921425556788081)
                ·
                  refine ⟨24222163207441069167591061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32296217609921425556788081 24222163207441069167591061)
                  ·
                    refine ⟨1135413900348800117230831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24222163207441069167591061 1135413900348800117230831)
                    ·
                      rfl

theorem cell22_3316816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 2, 6].length) (baseStart_3316816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316816 prefixEnd_3316816 := by exact prefixLift 3316816
  have htrace : WordTrace (prefixWord ++ tailWord_3316816) baseStart_3316816 baseEnd_3316816 := by
    simpa [prefixWord, tailWord_3316816, baseEnd_3316816] using wordTrace_append hprefix tailTrace_3316816
  have hstable : (prefixWord ++ tailWord_3316816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316816).length < 2 ^ (prefixWord ++ tailWord_3316816).sum := by decide
  have hdescent : baseEnd_3316816 < baseStart_3316816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316831 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 9]
def baseStart_3316831 : Nat := 118140960795 + 3316831 * 2 ^ 59
def prefixEnd_3316831 : Nat := 4983230072969 + 3 ^ 40 * 3316831 * 2
def baseEnd_3316831 : Nat := 378473011718448359368595

theorem tailTrace_3316831 : CollatzResearch.WordTrace tailWord_3316831 prefixEnd_3316831 378473011718448359368595 := by
  unfold tailWord_3316831
  simp only [CollatzResearch.WordTrace]
  refine ⟨120974765046695231480958347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80649843364463487653972231 120974765046695231480958347)
  ·
    refine ⟨181462147570042847221437521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120974765046695231480958347 181462147570042847221437521)
    ·
      refine ⟨136096610677532135416078141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 181462147570042847221437521 136096610677532135416078141)
      ·
        refine ⟨51036229004074550781029303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136096610677532135416078141 51036229004074550781029303)
        ·
          refine ⟨76554343506111826171543955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51036229004074550781029303 76554343506111826171543955)
          ·
            refine ⟨114831515259167739257315933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76554343506111826171543955 114831515259167739257315933)
            ·
              refine ⟨43061818222187902221493475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114831515259167739257315933 43061818222187902221493475)
              ·
                refine ⟨64592727333281853332240213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43061818222187902221493475 64592727333281853332240213)
                ·
                  refine ⟨378473011718448359368595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64592727333281853332240213 378473011718448359368595)
                  ·
                    rfl

theorem cell22_3316831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 9].length) (baseStart_3316831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316831 prefixEnd_3316831 := by exact prefixLift 3316831
  have htrace : WordTrace (prefixWord ++ tailWord_3316831) baseStart_3316831 baseEnd_3316831 := by
    simpa [prefixWord, tailWord_3316831, baseEnd_3316831] using wordTrace_append hprefix tailTrace_3316831
  have hstable : (prefixWord ++ tailWord_3316831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316831).length < 2 ^ (prefixWord ++ tailWord_3316831).sum := by decide
  have hdescent : baseEnd_3316831 < baseStart_3316831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316848 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 5]
def baseStart_3316848 : Nat := 118140960795 + 3316848 * 2 ^ 59
def prefixEnd_3316848 : Nat := 4983230072969 + 3 ^ 40 * 3316848 * 2
def baseEnd_3316848 : Nat := 378474951534254233476911

theorem tailTrace_3316848 : CollatzResearch.WordTrace tailWord_3316848 prefixEnd_3316848 378474951534254233476911 := by
  unfold tailWord_3316848
  simp only [CollatzResearch.WordTrace]
  refine ⟨60487692543816821692163599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80650256725089095589551465 60487692543816821692163599)
  ·
    refine ⟨90731538815725232538245399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60487692543816821692163599 90731538815725232538245399)
    ·
      refine ⟨136097308223587848807368099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90731538815725232538245399 136097308223587848807368099)
      ·
        refine ⟨204145962335381773211052149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136097308223587848807368099 204145962335381773211052149)
        ·
          refine ⟨19138683968942041238536139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 204145962335381773211052149 19138683968942041238536139)
          ·
            refine ⟨28708025953413061857804209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19138683968942041238536139 28708025953413061857804209)
            ·
              refine ⟨21531019465059796393353157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28708025953413061857804209 21531019465059796393353157)
              ·
                refine ⟨4037066149698711823753717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21531019465059796393353157 4037066149698711823753717)
                ·
                  refine ⟨378474951534254233476911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4037066149698711823753717 378474951534254233476911)
                  ·
                    rfl

theorem cell22_3316848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 5].length) (baseStart_3316848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316848 prefixEnd_3316848 := by exact prefixLift 3316848
  have htrace : WordTrace (prefixWord ++ tailWord_3316848) baseStart_3316848 baseEnd_3316848 := by
    simpa [prefixWord, tailWord_3316848, baseEnd_3316848] using wordTrace_append hprefix tailTrace_3316848
  have hstable : (prefixWord ++ tailWord_3316848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316848).length < 2 ^ (prefixWord ++ tailWord_3316848).sum := by decide
  have hdescent : baseEnd_3316848 < baseStart_3316848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3316865 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 5]
def baseStart_3316865 : Nat := 118140960795 + 3316865 * 2 ^ 59
def prefixEnd_3316865 : Nat := 4983230072969 + 3 ^ 40 * 3316865 * 2
def baseEnd_3316865 : Nat := 378476891350060107585227

theorem tailTrace_3316865 : CollatzResearch.WordTrace tailWord_3316865 prefixEnd_3316865 378476891350060107585227 := by
  unfold tailWord_3316865
  simp only [CollatzResearch.WordTrace]
  refine ⟨120976005128572055287696049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80650670085714703525130699 120976005128572055287696049)
  ·
    refine ⟨90732003846429041465772037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120976005128572055287696049 90732003846429041465772037)
    ·
      refine ⟨17012250721205445274832257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90732003846429041465772037 17012250721205445274832257)
      ·
        refine ⟨12759188040904083956124193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17012250721205445274832257 12759188040904083956124193)
        ·
          refine ⟨9569391030678062967093145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12759188040904083956124193 9569391030678062967093145)
          ·
            refine ⟨7177043273008547225319859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9569391030678062967093145 7177043273008547225319859)
            ·
              refine ⟨10765564909512820837979789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7177043273008547225319859 10765564909512820837979789)
              ·
                refine ⟨4037086841067307814242421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10765564909512820837979789 4037086841067307814242421)
                ·
                  refine ⟨378476891350060107585227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4037086841067307814242421 378476891350060107585227)
                  ·
                    rfl

theorem cell22_3316865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_3316865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3316865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3316865 prefixEnd_3316865 := by exact prefixLift 3316865
  have htrace : WordTrace (prefixWord ++ tailWord_3316865) baseStart_3316865 baseEnd_3316865 := by
    simpa [prefixWord, tailWord_3316865, baseEnd_3316865] using wordTrace_append hprefix tailTrace_3316865
  have hstable : (prefixWord ++ tailWord_3316865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3316865).length < 2 ^ (prefixWord ++ tailWord_3316865).sum := by decide
  have hdescent : baseEnd_3316865 < baseStart_3316865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3316865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317004 : List Nat := [2, 2, 1, 2, 2, 3, 3, 3, 1, 3]
def baseStart_3317004 : Nat := 118140960795 + 3317004 * 2 ^ 59
def prefixEnd_3317004 : Nat := 4983230072969 + 3 ^ 40 * 3317004 * 2
def baseEnd_3317004 : Nat := 1135478256590830293530255

theorem tailTrace_3317004 : CollatzResearch.WordTrace tailWord_3317004 prefixEnd_3317004 1135478256590830293530255 := by
  unfold tailWord_3317004
  simp only [CollatzResearch.WordTrace]
  refine ⟨60490537437534241013503033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80654049916712321351337377 60490537437534241013503033)
  ·
    refine ⟨45367903078150680760127275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60490537437534241013503033 45367903078150680760127275)
    ·
      refine ⟨68051854617226021140190913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45367903078150680760127275 68051854617226021140190913)
      ·
        refine ⟨51038890962919515855143185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68051854617226021140190913 51038890962919515855143185)
        ·
          refine ⟨38279168222189636891357389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51038890962919515855143185 38279168222189636891357389)
          ·
            refine ⟨14354688083321113834259021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38279168222189636891357389 14354688083321113834259021)
            ·
              refine ⟨5383008031245417687847133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14354688083321113834259021 5383008031245417687847133)
              ·
                refine ⟨2018628011717031632942675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5383008031245417687847133 2018628011717031632942675)
                ·
                  refine ⟨3027942017575547449414013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018628011717031632942675 3027942017575547449414013)
                  ·
                    refine ⟨1135478256590830293530255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3027942017575547449414013 1135478256590830293530255)
                    ·
                      rfl

theorem cell22_3317004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 3, 1, 3].length) (baseStart_3317004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317004 prefixEnd_3317004 := by exact prefixLift 3317004
  have htrace : WordTrace (prefixWord ++ tailWord_3317004) baseStart_3317004 baseEnd_3317004 := by
    simpa [prefixWord, tailWord_3317004, baseEnd_3317004] using wordTrace_append hprefix tailTrace_3317004
  have hstable : (prefixWord ++ tailWord_3317004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317004).length < 2 ^ (prefixWord ++ tailWord_3317004).sum := by decide
  have hdescent : baseEnd_3317004 < baseStart_3317004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317034 : List Nat := [3, 1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_3317034 : Nat := 118140960795 + 3317034 * 2 ^ 59
def prefixEnd_3317034 : Nat := 4983230072969 + 3 ^ 40 * 3317034 * 2
def baseEnd_3317034 : Nat := 378496175401306738426721

theorem tailTrace_3317034 : CollatzResearch.WordTrace tailWord_3317034 prefixEnd_3317034 378496175401306738426721 := by
  unfold tailWord_3317034
  simp only [CollatzResearch.WordTrace]
  refine ⟨30245542266239949287649539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 80654779376639864767065437 30245542266239949287649539)
  ·
    refine ⟨45368313399359923931474309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30245542266239949287649539 45368313399359923931474309)
    ·
      refine ⟨8506558762379985737151433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45368313399359923931474309 8506558762379985737151433)
      ·
        refine ⟨6379919071784989302863575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8506558762379985737151433 6379919071784989302863575)
        ·
          refine ⟨9569878607677483954295363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6379919071784989302863575 9569878607677483954295363)
          ·
            refine ⟨14354817911516225931443045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9569878607677483954295363 14354817911516225931443045)
            ·
              refine ⟨2691528358409292362145571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14354817911516225931443045 2691528358409292362145571)
              ·
                refine ⟨4037292537613938543218357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2691528358409292362145571 4037292537613938543218357)
                ·
                  refine ⟨378496175401306738426721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4037292537613938543218357 378496175401306738426721)
                  ·
                    rfl

theorem cell22_3317034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_3317034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317034 prefixEnd_3317034 := by exact prefixLift 3317034
  have htrace : WordTrace (prefixWord ++ tailWord_3317034) baseStart_3317034 baseEnd_3317034 := by
    simpa [prefixWord, tailWord_3317034, baseEnd_3317034] using wordTrace_append hprefix tailTrace_3317034
  have hstable : (prefixWord ++ tailWord_3317034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317034).length < 2 ^ (prefixWord ++ tailWord_3317034).sum := by decide
  have hdescent : baseEnd_3317034 < baseStart_3317034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317075 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 2, 4]
def baseStart_3317075 : Nat := 118140960795 + 3317075 * 2 ^ 59
def prefixEnd_3317075 : Nat := 4983230072969 + 3 ^ 40 * 3317075 * 2
def baseEnd_3317075 : Nat := 1135502561341809775005037

theorem tailTrace_3317075 : CollatzResearch.WordTrace tailWord_3317075 prefixEnd_3317075 1135502561341809775005037 := by
  unfold tailWord_3317075
  simp only [CollatzResearch.WordTrace]
  refine ⟨120983664457811261152840679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80655776305207507435227119 120983664457811261152840679)
  ·
    refine ⟨181475496686716891729261019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120983664457811261152840679 181475496686716891729261019)
    ·
      refine ⟨272213245030075337593891529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181475496686716891729261019 272213245030075337593891529)
      ·
        refine ⟨204159933772556503195418647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 272213245030075337593891529 204159933772556503195418647)
        ·
          refine ⟨306239900658834754793127971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204159933772556503195418647 306239900658834754793127971)
          ·
            refine ⟨459359850988252132189691957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306239900658834754793127971 459359850988252132189691957)
            ·
              refine ⟨43064986030148637392783621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 459359850988252132189691957 43064986030148637392783621)
              ·
                refine ⟨8074684880652869511146929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43064986030148637392783621 8074684880652869511146929)
                ·
                  refine ⟨6056013660489652133360197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8074684880652869511146929 6056013660489652133360197)
                  ·
                    refine ⟨1135502561341809775005037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6056013660489652133360197 1135502561341809775005037)
                    ·
                      rfl

theorem cell22_3317075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 4].length) (baseStart_3317075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317075 prefixEnd_3317075 := by exact prefixLift 3317075
  have htrace : WordTrace (prefixWord ++ tailWord_3317075) baseStart_3317075 baseEnd_3317075 := by
    simpa [prefixWord, tailWord_3317075, baseEnd_3317075] using wordTrace_append hprefix tailTrace_3317075
  have hstable : (prefixWord ++ tailWord_3317075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317075).length < 2 ^ (prefixWord ++ tailWord_3317075).sum := by decide
  have hdescent : baseEnd_3317075 < baseStart_3317075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317079 : List Nat := [1, 1, 3, 2, 3, 2, 4, 2, 4]
def baseStart_3317079 : Nat := 118140960795 + 3317079 * 2 ^ 59
def prefixEnd_3317079 : Nat := 4983230072969 + 3 ^ 40 * 3317079 * 2
def baseEnd_3317079 : Nat := 378501310207851699301675

theorem tailTrace_3317079 : CollatzResearch.WordTrace tailWord_3317079 prefixEnd_3317079 378501310207851699301675 := by
  unfold tailWord_3317079
  simp only [CollatzResearch.WordTrace]
  refine ⟨120983810349796769835986291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80655873566531179890657527 120983810349796769835986291)
  ·
    refine ⟨181475715524695154753979437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120983810349796769835986291 181475715524695154753979437)
    ·
      refine ⟨68053393321760683032742289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 181475715524695154753979437 68053393321760683032742289)
      ·
        refine ⟨51040044991320512274556717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68053393321760683032742289 51040044991320512274556717)
        ·
          refine ⟨19140016871745192102958769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51040044991320512274556717 19140016871745192102958769)
          ·
            refine ⟨14355012653808894077219077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19140016871745192102958769 14355012653808894077219077)
            ·
              refine ⟨2691564872589167639478577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14355012653808894077219077 2691564872589167639478577)
              ·
                refine ⟨2018673654441875729608933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2691564872589167639478577 2018673654441875729608933)
                ·
                  refine ⟨378501310207851699301675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018673654441875729608933 378501310207851699301675)
                  ·
                    rfl

theorem cell22_3317079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 2, 4].length) (baseStart_3317079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317079 prefixEnd_3317079 := by exact prefixLift 3317079
  have htrace : WordTrace (prefixWord ++ tailWord_3317079) baseStart_3317079 baseEnd_3317079 := by
    simpa [prefixWord, tailWord_3317079, baseEnd_3317079] using wordTrace_append hprefix tailTrace_3317079
  have hstable : (prefixWord ++ tailWord_3317079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317079).length < 2 ^ (prefixWord ++ tailWord_3317079).sum := by decide
  have hdescent : baseEnd_3317079 < baseStart_3317079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317173 : List Nat := [1, 3, 3, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3317173 : Nat := 118140960795 + 3317173 * 2 ^ 59
def prefixEnd_3317173 : Nat := 4983230072969 + 3 ^ 40 * 3317173 * 2
def baseEnd_3317173 : Nat := 1135536108744570186054737

theorem tailTrace_3317173 : CollatzResearch.WordTrace tailWord_3317173 prefixEnd_3317173 1135536108744570186054737 := by
  unfold tailWord_3317173
  simp only [CollatzResearch.WordTrace]
  refine ⟨120987238811456223889908173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80658159207637482593272115 120987238811456223889908173)
  ·
    refine ⟨45370214554296083958715565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120987238811456223889908173 45370214554296083958715565)
    ·
      refine ⟨17013830457861031484518337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45370214554296083958715565 17013830457861031484518337)
      ·
        refine ⟨12760372843395773613388753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17013830457861031484518337 12760372843395773613388753)
        ·
          refine ⟨9570279632546830210041565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12760372843395773613388753 9570279632546830210041565)
          ·
            refine ⟨3588854862205061328765587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9570279632546830210041565 3588854862205061328765587)
            ·
              refine ⟨5383282293307591993148381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588854862205061328765587 5383282293307591993148381)
              ·
                refine ⟨2018730859990346997430643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5383282293307591993148381 2018730859990346997430643)
                ·
                  refine ⟨3028096289985520496145965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018730859990346997430643 3028096289985520496145965)
                  ·
                    refine ⟨1135536108744570186054737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3028096289985520496145965 1135536108744570186054737)
                    ·
                      rfl

theorem cell22_3317173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3317173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317173 prefixEnd_3317173 := by exact prefixLift 3317173
  have htrace : WordTrace (prefixWord ++ tailWord_3317173) baseStart_3317173 baseEnd_3317173 := by
    simpa [prefixWord, tailWord_3317173, baseEnd_3317173] using wordTrace_append hprefix tailTrace_3317173
  have hstable : (prefixWord ++ tailWord_3317173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317173).length < 2 ^ (prefixWord ++ tailWord_3317173).sum := by decide
  have hdescent : baseEnd_3317173 < baseStart_3317173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317182 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_3317182 : Nat := 118140960795 + 3317182 * 2 ^ 59
def prefixEnd_3317182 : Nat := 4983230072969 + 3 ^ 40 * 3317182 * 2
def baseEnd_3317182 : Nat := 1135539189628497162579709

theorem tailTrace_3317182 : CollatzResearch.WordTrace tailWord_3317182 prefixEnd_3317182 1135539189628497162579709 := by
  unfold tailWord_3317182
  simp only [CollatzResearch.WordTrace]
  refine ⟨15123445883552952303373225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 80658378045615745617990533 15123445883552952303373225)
  ·
    refine ⟨11342584412664714227529919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15123445883552952303373225 11342584412664714227529919)
    ·
      refine ⟨17013876618997071341294879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11342584412664714227529919 17013876618997071341294879)
      ·
        refine ⟨25520814928495607011942319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17013876618997071341294879 25520814928495607011942319)
        ·
          refine ⟨38281222392743410517913479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25520814928495607011942319 38281222392743410517913479)
          ·
            refine ⟨57421833589115115776870219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38281222392743410517913479 57421833589115115776870219)
            ·
              refine ⟨86132750383672673665305329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57421833589115115776870219 86132750383672673665305329)
              ·
                refine ⟨64599562787754505248978997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86132750383672673665305329 64599562787754505248978997)
                ·
                  refine ⟨6056209011351984867091781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64599562787754505248978997 6056209011351984867091781)
                  ·
                    refine ⟨1135539189628497162579709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6056209011351984867091781 1135539189628497162579709)
                    ·
                      rfl

theorem cell22_3317182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_3317182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317182 prefixEnd_3317182 := by exact prefixLift 3317182
  have htrace : WordTrace (prefixWord ++ tailWord_3317182) baseStart_3317182 baseEnd_3317182 := by
    simpa [prefixWord, tailWord_3317182, baseEnd_3317182] using wordTrace_append hprefix tailTrace_3317182
  have hstable : (prefixWord ++ tailWord_3317182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317182).length < 2 ^ (prefixWord ++ tailWord_3317182).sum := by decide
  have hdescent : baseEnd_3317182 < baseStart_3317182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317259 : List Nat := [1, 1, 1, 1, 8, 2, 1, 7]
def baseStart_3317259 : Nat := 118140960795 + 3317259 * 2 ^ 59
def prefixEnd_3317259 : Nat := 4983230072969 + 3 ^ 40 * 3317259 * 2
def baseEnd_3317259 : Nat := 126173949811343847600497

theorem tailTrace_3317259 : CollatzResearch.WordTrace tailWord_3317259 prefixEnd_3317259 126173949811343847600497 := by
  unfold tailWord_3317259
  simp only [CollatzResearch.WordTrace]
  refine ⟨120990375489144660577538831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 80660250326096440385025887 120990375489144660577538831)
  ·
    refine ⟨181485563233716990866308247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120990375489144660577538831 181485563233716990866308247)
    ·
      refine ⟨272228344850575486299462371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181485563233716990866308247 272228344850575486299462371)
      ·
        refine ⟨408342517275863229449193557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272228344850575486299462371 408342517275863229449193557)
        ·
          refine ⟨4785263874326522220107737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 408342517275863229449193557 4785263874326522220107737)
          ·
            refine ⟨3588947905744891665080803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4785263874326522220107737 3588947905744891665080803)
            ·
              refine ⟨5383421858617337497621205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588947905744891665080803 5383421858617337497621205)
              ·
                refine ⟨126173949811343847600497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5383421858617337497621205 126173949811343847600497)
                ·
                  rfl

theorem cell22_3317259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 7].length) (baseStart_3317259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317259 prefixEnd_3317259 := by exact prefixLift 3317259
  have htrace : WordTrace (prefixWord ++ tailWord_3317259) baseStart_3317259 baseEnd_3317259 := by
    simpa [prefixWord, tailWord_3317259, baseEnd_3317259] using wordTrace_append hprefix tailTrace_3317259
  have hstable : (prefixWord ++ tailWord_3317259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317259).length < 2 ^ (prefixWord ++ tailWord_3317259).sum := by decide
  have hdescent : baseEnd_3317259 < baseStart_3317259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3317304 : List Nat := [2, 1, 2, 1, 4, 2, 3, 2, 5]
def baseStart_3317304 : Nat := 118140960795 + 3317304 * 2 ^ 59
def prefixEnd_3317304 : Nat := 4983230072969 + 3 ^ 40 * 3317304 * 2
def baseEnd_3317304 : Nat := 378526984240576503676445

theorem tailTrace_3317304 : CollatzResearch.WordTrace tailWord_3317304 prefixEnd_3317304 378526984240576503676445 := by
  unfold tailWord_3317304
  simp only [CollatzResearch.WordTrace]
  refine ⟨60496008386990816631463483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 80661344515987755508617977 60496008386990816631463483)
  ·
    refine ⟨90744012580486224947195225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60496008386990816631463483 90744012580486224947195225)
    ·
      refine ⟨68058009435364668710396419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90744012580486224947195225 68058009435364668710396419)
      ·
        refine ⟨102087014153047003065594629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68058009435364668710396419 102087014153047003065594629)
        ·
          refine ⟨19141315153696313074798993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102087014153047003065594629 19141315153696313074798993)
          ·
            refine ⟨14355986365272234806099245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19141315153696313074798993 14355986365272234806099245)
            ·
              refine ⟨5383494886977088052287217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14355986365272234806099245 5383494886977088052287217)
              ·
                refine ⟨4037621165232816039215413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5383494886977088052287217 4037621165232816039215413)
                ·
                  refine ⟨378526984240576503676445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4037621165232816039215413 378526984240576503676445)
                  ·
                    rfl

theorem cell22_3317304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_3317304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3317304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3317304 prefixEnd_3317304 := by exact prefixLift 3317304
  have htrace : WordTrace (prefixWord ++ tailWord_3317304) baseStart_3317304 baseEnd_3317304 := by
    simpa [prefixWord, tailWord_3317304, baseEnd_3317304] using wordTrace_append hprefix tailTrace_3317304
  have hstable : (prefixWord ++ tailWord_3317304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3317304).length < 2 ^ (prefixWord ++ tailWord_3317304).sum := by decide
  have hdescent : baseEnd_3317304 < baseStart_3317304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3317304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
