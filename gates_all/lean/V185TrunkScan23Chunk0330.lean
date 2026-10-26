import V185TrunkScan23Chunk0329

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1950879 : List Nat := [1, 1, 2, 6, 2, 1, 3, 1, 6]
def baseStart_1950879 : Nat := 118140960795 + 1950879 * 2 ^ 59
def prefixEnd_1950879 : Nat := 4983230072969 + 3 ^ 40 * 1950879 * 2
def baseEnd_1950879 : Nat := 111304291751419767848953

theorem tailTrace_1950879 : CollatzResearch.WordTrace tailWord_1950879 prefixEnd_1950879 111304291751419767848953 := by
  unfold tailWord_1950879
  simp only [CollatzResearch.WordTrace]
  refine ⟨71154402699306041452207691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47436268466204027634805127 71154402699306041452207691)
  ·
    refine ⟨106731604048959062178311537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71154402699306041452207691 106731604048959062178311537)
    ·
      refine ⟨80048703036719296633733653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106731604048959062178311537 80048703036719296633733653)
      ·
        refine ⟨3752282954846217029706265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80048703036719296633733653 3752282954846217029706265)
        ·
          refine ⟨2814212216134662772279699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3752282954846217029706265 2814212216134662772279699)
          ·
            refine ⟨4221318324201994158419549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814212216134662772279699 4221318324201994158419549)
            ·
              refine ⟨1582994371575747809407331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4221318324201994158419549 1582994371575747809407331)
              ·
                refine ⟨2374491557363621714110997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1582994371575747809407331 2374491557363621714110997)
                ·
                  refine ⟨111304291751419767848953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2374491557363621714110997 111304291751419767848953)
                  ·
                    rfl

theorem cell23_1950879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 1, 6].length) (baseStart_1950879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950879 prefixEnd_1950879 := by exact prefixLift 1950879
  have htrace : WordTrace (prefixWord ++ tailWord_1950879) baseStart_1950879 baseEnd_1950879 := by
    simpa [prefixWord, tailWord_1950879, baseEnd_1950879] using wordTrace_append hprefix tailTrace_1950879
  have hstable : (prefixWord ++ tailWord_1950879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950879).length < 2 ^ (prefixWord ++ tailWord_1950879).sum := by decide
  have hdescent : baseEnd_1950879 < baseStart_1950879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950895 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 4]
def baseStart_1950895 : Nat := 118140960795 + 1950895 * 2 ^ 59
def prefixEnd_1950895 : Nat := 4983230072969 + 3 ^ 40 * 1950895 * 2
def baseEnd_1950895 : Nat := 1001746841453249848040503

theorem tailTrace_1950895 : CollatzResearch.WordTrace tailWord_1950895 prefixEnd_1950895 1001746841453249848040503 := by
  unfold tailWord_1950895
  simp only [CollatzResearch.WordTrace]
  refine ⟨71154986267248076184790139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47436657511498717456526759 71154986267248076184790139)
  ·
    refine ⟨106732479400872114277185209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71154986267248076184790139 106732479400872114277185209)
    ·
      refine ⟨80049359550654085707888907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106732479400872114277185209 80049359550654085707888907)
      ·
        refine ⟨120074039325981128561833361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80049359550654085707888907 120074039325981128561833361)
        ·
          refine ⟨90055529494485846421375021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120074039325981128561833361 90055529494485846421375021)
          ·
            refine ⟨33770823560432192408015633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90055529494485846421375021 33770823560432192408015633)
            ·
              refine ⟨25328117670324144306011725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33770823560432192408015633 25328117670324144306011725)
              ·
                refine ⟨9498044126371554114754397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25328117670324144306011725 9498044126371554114754397)
                ·
                  refine ⟨3561766547389332793032899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9498044126371554114754397 3561766547389332793032899)
                  ·
                    refine ⟨5342649821083999189549349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3561766547389332793032899 5342649821083999189549349)
                    ·
                      refine ⟨1001746841453249848040503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5342649821083999189549349 1001746841453249848040503)
                      ·
                        rfl

theorem cell23_1950895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 4].length) (baseStart_1950895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950895 prefixEnd_1950895 := by exact prefixLift 1950895
  have htrace : WordTrace (prefixWord ++ tailWord_1950895) baseStart_1950895 baseEnd_1950895 := by
    simpa [prefixWord, tailWord_1950895, baseEnd_1950895] using wordTrace_append hprefix tailTrace_1950895
  have hstable : (prefixWord ++ tailWord_1950895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950895).length < 2 ^ (prefixWord ++ tailWord_1950895).sum := by decide
  have hdescent : baseEnd_1950895 < baseStart_1950895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950916 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_1950916 : Nat := 118140960795 + 1950916 * 2 ^ 59
def prefixEnd_1950916 : Nat := 4983230072969 + 3 ^ 40 * 1950916 * 2
def baseEnd_1950916 : Nat := 1001757624546994265877907

theorem tailTrace_1950916 : CollatzResearch.WordTrace tailWord_1950916 prefixEnd_1950916 1001757624546994265877907 := by
  unfold tailWord_1950916
  simp only [CollatzResearch.WordTrace]
  refine ⟨35577876100085998385652301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47437168133447997847536401 35577876100085998385652301)
  ·
    refine ⟨13341703537532249394619613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35577876100085998385652301 13341703537532249394619613)
    ·
      refine ⟨5003138826574593522982355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13341703537532249394619613 5003138826574593522982355)
      ·
        refine ⟨7504708239861890284473533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5003138826574593522982355 7504708239861890284473533)
        ·
          refine ⟨2814265589948208856677575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7504708239861890284473533 2814265589948208856677575)
          ·
            refine ⟨4221398384922313285016363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814265589948208856677575 4221398384922313285016363)
            ·
              refine ⟨6332097577383469927524545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221398384922313285016363 6332097577383469927524545)
              ·
                refine ⟨4749073183037602445643409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6332097577383469927524545 4749073183037602445643409)
                ·
                  refine ⟨3561804887278201834232557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4749073183037602445643409 3561804887278201834232557)
                  ·
                    refine ⟨1335676832729325687837209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3561804887278201834232557 1335676832729325687837209)
                    ·
                      refine ⟨1001757624546994265877907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335676832729325687837209 1001757624546994265877907)
                      ·
                        rfl

theorem cell23_1950916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_1950916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950916 prefixEnd_1950916 := by exact prefixLift 1950916
  have htrace : WordTrace (prefixWord ++ tailWord_1950916) baseStart_1950916 baseEnd_1950916 := by
    simpa [prefixWord, tailWord_1950916, baseEnd_1950916] using wordTrace_append hprefix tailTrace_1950916
  have hstable : (prefixWord ++ tailWord_1950916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950916).length < 2 ^ (prefixWord ++ tailWord_1950916).sum := by decide
  have hdescent : baseEnd_1950916 < baseStart_1950916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950922 : List Nat := [3, 1, 2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_1950922 : Nat := 118140960795 + 1950922 * 2 ^ 59
def prefixEnd_1950922 : Nat := 4983230072969 + 3 ^ 40 * 1950922 * 2
def baseEnd_1950922 : Nat := 333920235143640414134293

theorem tailTrace_1950922 : CollatzResearch.WordTrace tailWord_1950922 prefixEnd_1950922 333920235143640414134293 := by
  unfold tailWord_1950922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17788992759537564949005755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47437314025433506530682013 17788992759537564949005755)
  ·
    refine ⟨26683489139306347423508633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17788992759537564949005755 26683489139306347423508633)
    ·
      refine ⟨20012616854479760567631475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26683489139306347423508633 20012616854479760567631475)
      ·
        refine ⟨30018925281719640851447213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20012616854479760567631475 30018925281719640851447213)
        ·
          refine ⟨11257096980644865319292705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30018925281719640851447213 11257096980644865319292705)
          ·
            refine ⟨8442822735483648989469529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11257096980644865319292705 8442822735483648989469529)
            ·
              refine ⟨6332117051612736742102147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8442822735483648989469529 6332117051612736742102147)
              ·
                refine ⟨9498175577419105113153221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6332117051612736742102147 9498175577419105113153221)
                ·
                  refine ⟨1780907920766082208716229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9498175577419105113153221 1780907920766082208716229)
                  ·
                    refine ⟨333920235143640414134293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1780907920766082208716229 333920235143640414134293)
                    ·
                      rfl

theorem cell23_1950922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_1950922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950922 prefixEnd_1950922 := by exact prefixLift 1950922
  have htrace : WordTrace (prefixWord ++ tailWord_1950922) baseStart_1950922 baseEnd_1950922 := by
    simpa [prefixWord, tailWord_1950922, baseEnd_1950922] using wordTrace_append hprefix tailTrace_1950922
  have hstable : (prefixWord ++ tailWord_1950922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950922).length < 2 ^ (prefixWord ++ tailWord_1950922).sum := by decide
  have hdescent : baseEnd_1950922 < baseStart_1950922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950949 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1950949 : Nat := 118140960795 + 1950949 * 2 ^ 59
def prefixEnd_1950949 : Nat := 4983230072969 + 3 ^ 40 * 1950949 * 2
def baseEnd_1950949 : Nat := 1001774569408592636765255

theorem tailTrace_1950949 : CollatzResearch.WordTrace tailWord_1950949 prefixEnd_1950949 1001774569408592636765255 := by
  unfold tailWord_1950949
  simp only [CollatzResearch.WordTrace]
  refine ⟨71156955809052443407255901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47437970539368295604837267 71156955809052443407255901)
  ·
    refine ⟨26683858428394666277720963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71156955809052443407255901 26683858428394666277720963)
    ·
      refine ⟨40025787642591999416581445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26683858428394666277720963 40025787642591999416581445)
      ·
        refine ⟨7504835182985999890609021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40025787642591999416581445 7504835182985999890609021)
        ·
          refine ⟨2814313193619749958978383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7504835182985999890609021 2814313193619749958978383)
          ·
            refine ⟨4221469790429624938467575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814313193619749958978383 4221469790429624938467575)
            ·
              refine ⟨6332204685644437407701363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221469790429624938467575 6332204685644437407701363)
              ·
                refine ⟨9498307028466656111552045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6332204685644437407701363 9498307028466656111552045)
                ·
                  refine ⟨3561865135674996041832017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9498307028466656111552045 3561865135674996041832017)
                  ·
                    refine ⟨2671398851756247031374013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3561865135674996041832017 2671398851756247031374013)
                    ·
                      refine ⟨1001774569408592636765255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2671398851756247031374013 1001774569408592636765255)
                      ·
                        rfl

theorem cell23_1950949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1950949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950949 prefixEnd_1950949 := by exact prefixLift 1950949
  have htrace : WordTrace (prefixWord ++ tailWord_1950949) baseStart_1950949 baseEnd_1950949 := by
    simpa [prefixWord, tailWord_1950949, baseEnd_1950949] using wordTrace_append hprefix tailTrace_1950949
  have hstable : (prefixWord ++ tailWord_1950949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950949).length < 2 ^ (prefixWord ++ tailWord_1950949).sum := by decide
  have hdescent : baseEnd_1950949 < baseStart_1950949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950979 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 2, 1, 3]
def baseStart_1950979 : Nat := 118140960795 + 1950979 * 2 ^ 59
def prefixEnd_1950979 : Nat := 4983230072969 + 3 ^ 40 * 1950979 * 2
def baseEnd_1950979 : Nat := 1001789973828227519390117

theorem tailTrace_1950979 : CollatzResearch.WordTrace tailWord_1950979 prefixEnd_1950979 1001789973828227519390117 := by
  unfold tailWord_1950979
  simp only [CollatzResearch.WordTrace]
  refine ⟨71158049998943758530847991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47438699999295839020565327 71158049998943758530847991)
  ·
    refine ⟨106737074998415637796271987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71158049998943758530847991 106737074998415637796271987)
    ·
      refine ⟨160105612497623456694407981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106737074998415637796271987 160105612497623456694407981)
      ·
        refine ⟨60039604686608796260402993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160105612497623456694407981 60039604686608796260402993)
        ·
          refine ⟨45029703514956597195302245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60039604686608796260402993 45029703514956597195302245)
          ·
            refine ⟨8443069409054361974119171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45029703514956597195302245 8443069409054361974119171)
            ·
              refine ⟨12664604113581542961178757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443069409054361974119171 12664604113581542961178757)
              ·
                refine ⟨2374613271296539305221017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12664604113581542961178757 2374613271296539305221017)
                ·
                  refine ⟨1780959953472404478915763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2374613271296539305221017 1780959953472404478915763)
                  ·
                    refine ⟨2671439930208606718373645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1780959953472404478915763 2671439930208606718373645)
                    ·
                      refine ⟨1001789973828227519390117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2671439930208606718373645 1001789973828227519390117)
                      ·
                        rfl

theorem cell23_1950979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_1950979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950979 prefixEnd_1950979 := by exact prefixLift 1950979
  have htrace : WordTrace (prefixWord ++ tailWord_1950979) baseStart_1950979 baseEnd_1950979 := by
    simpa [prefixWord, tailWord_1950979, baseEnd_1950979] using wordTrace_append hprefix tailTrace_1950979
  have hstable : (prefixWord ++ tailWord_1950979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950979).length < 2 ^ (prefixWord ++ tailWord_1950979).sum := by decide
  have hdescent : baseEnd_1950979 < baseStart_1950979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950980 : List Nat := [2, 3, 2, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_1950980 : Nat := 118140960795 + 1950980 * 2 ^ 59
def prefixEnd_1950980 : Nat := 4983230072969 + 3 ^ 40 * 1950980 * 2
def baseEnd_1950980 : Nat := 1001790487308882015477613

theorem tailTrace_1950980 : CollatzResearch.WordTrace tailWord_1950980 prefixEnd_1950980 1001790487308882015477613 := by
  unfold tailWord_1950980
  simp only [CollatzResearch.WordTrace]
  refine ⟨35579043235970067850817197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47438724314626757134422929 35579043235970067850817197)
  ·
    refine ⟨13342141213488775444056449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35579043235970067850817197 13342141213488775444056449)
    ·
      refine ⟨10006605910116581583042337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13342141213488775444056449 10006605910116581583042337)
      ·
        refine ⟨7504954432587436187281753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10006605910116581583042337 7504954432587436187281753)
        ·
          refine ⟨5628715824440577140461315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7504954432587436187281753 5628715824440577140461315)
          ·
            refine ⟨8443073736660865710691973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628715824440577140461315 8443073736660865710691973)
            ·
              refine ⟨1583076325623912320754745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8443073736660865710691973 1583076325623912320754745)
              ·
                refine ⟨1187307244217934240566059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583076325623912320754745 1187307244217934240566059)
                ·
                  refine ⟨1780960866326901360849089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187307244217934240566059 1780960866326901360849089)
                  ·
                    refine ⟨1335720649745176020636817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1780960866326901360849089 1335720649745176020636817)
                    ·
                      refine ⟨1001790487308882015477613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335720649745176020636817 1001790487308882015477613)
                      ·
                        rfl

theorem cell23_1950980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_1950980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950980 prefixEnd_1950980 := by exact prefixLift 1950980
  have htrace : WordTrace (prefixWord ++ tailWord_1950980) baseStart_1950980 baseEnd_1950980 := by
    simpa [prefixWord, tailWord_1950980, baseEnd_1950980] using wordTrace_append hprefix tailTrace_1950980
  have hstable : (prefixWord ++ tailWord_1950980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950980).length < 2 ^ (prefixWord ++ tailWord_1950980).sum := by decide
  have hdescent : baseEnd_1950980 < baseStart_1950980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1950985 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_1950985 : Nat := 118140960795 + 1950985 * 2 ^ 59
def prefixEnd_1950985 : Nat := 4983230072969 + 3 ^ 40 * 1950985 * 2
def baseEnd_1950985 : Nat := 1001793054712154495915089

theorem tailTrace_1950985 : CollatzResearch.WordTrace tailWord_1950985 prefixEnd_1950985 1001793054712154495915089 := by
  unfold tailWord_1950985
  simp only [CollatzResearch.WordTrace]
  refine ⟨71158268836922021555566409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47438845891281347703710939 71158268836922021555566409)
  ·
    refine ⟨53368701627691516166674807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71158268836922021555566409 53368701627691516166674807)
    ·
      refine ⟨80053052441537274250012211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53368701627691516166674807 80053052441537274250012211)
      ·
        refine ⟨120079578662305911375018317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80053052441537274250012211 120079578662305911375018317)
        ·
          refine ⟨45029841998364716765631869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120079578662305911375018317 45029841998364716765631869)
          ·
            refine ⟨16886190749386768787111951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45029841998364716765631869 16886190749386768787111951)
            ·
              refine ⟨25329286124080153180667927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16886190749386768787111951 25329286124080153180667927)
              ·
                refine ⟨37993929186120229771001891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25329286124080153180667927 37993929186120229771001891)
                ·
                  refine ⟨56990893779180344656502837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37993929186120229771001891 56990893779180344656502837)
                  ·
                    refine ⟨5342896291798157311547141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56990893779180344656502837 5342896291798157311547141)
                    ·
                      refine ⟨1001793054712154495915089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5342896291798157311547141 1001793054712154495915089)
                      ·
                        rfl

theorem cell23_1950985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_1950985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1950985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1950985 prefixEnd_1950985 := by exact prefixLift 1950985
  have htrace : WordTrace (prefixWord ++ tailWord_1950985) baseStart_1950985 baseEnd_1950985 := by
    simpa [prefixWord, tailWord_1950985, baseEnd_1950985] using wordTrace_append hprefix tailTrace_1950985
  have hstable : (prefixWord ++ tailWord_1950985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1950985).length < 2 ^ (prefixWord ++ tailWord_1950985).sum := by decide
  have hdescent : baseEnd_1950985 < baseStart_1950985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1950985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951036 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 4, 2, 2]
def baseStart_1951036 : Nat := 118140960795 + 1951036 * 2 ^ 59
def prefixEnd_1951036 : Nat := 4983230072969 + 3 ^ 40 * 1951036 * 2
def baseEnd_1951036 : Nat := 1001819242225533796377355

theorem tailTrace_1951036 : CollatzResearch.WordTrace tailWord_1951036 prefixEnd_1951036 1001819242225533796377355 := by
  unfold tailWord_1951036
  simp only [CollatzResearch.WordTrace]
  refine ⟨35580064479868628632836481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47440085973158171510448641 35580064479868628632836481)
  ·
    refine ⟨26685048359901471474627361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35580064479868628632836481 26685048359901471474627361)
    ·
      refine ⟨20013786269926103605970521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26685048359901471474627361 20013786269926103605970521)
      ·
        refine ⟨15010339702444577704477891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20013786269926103605970521 15010339702444577704477891)
        ·
          refine ⟨22515509553666866556716837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15010339702444577704477891 22515509553666866556716837)
          ·
            refine ⟨4221658041312537479384407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22515509553666866556716837 4221658041312537479384407)
            ·
              refine ⟨6332487061968806219076611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4221658041312537479384407 6332487061968806219076611)
              ·
                refine ⟨9498730592953209328614917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6332487061968806219076611 9498730592953209328614917)
                ·
                  refine ⟨1781011986178726749115297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9498730592953209328614917 1781011986178726749115297)
                  ·
                    refine ⟨1335758989634045061836473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1781011986178726749115297 1335758989634045061836473)
                    ·
                      refine ⟨1001819242225533796377355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335758989634045061836473 1001819242225533796377355)
                      ·
                        rfl

theorem cell23_1951036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_1951036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951036 prefixEnd_1951036 := by exact prefixLift 1951036
  have htrace : WordTrace (prefixWord ++ tailWord_1951036) baseStart_1951036 baseEnd_1951036 := by
    simpa [prefixWord, tailWord_1951036, baseEnd_1951036] using wordTrace_append hprefix tailTrace_1951036
  have hstable : (prefixWord ++ tailWord_1951036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951036).length < 2 ^ (prefixWord ++ tailWord_1951036).sum := by decide
  have hdescent : baseEnd_1951036 < baseStart_1951036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951072 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 1, 7]
def baseStart_1951072 : Nat := 118140960795 + 1951072 * 2 ^ 59
def prefixEnd_1951072 : Nat := 4983230072969 + 3 ^ 40 * 1951072 * 2
def baseEnd_1951072 : Nat := 333945909176365218509063

theorem tailTrace_1951072 : CollatzResearch.WordTrace tailWord_1951072 prefixEnd_1951072 333945909176365218509063 := by
  unfold tailWord_1951072
  simp only [CollatzResearch.WordTrace]
  refine ⟨35580720993803417706991735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47440961325071223609322313 35580720993803417706991735)
  ·
    refine ⟨53371081490705126560487603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35580720993803417706991735 53371081490705126560487603)
    ·
      refine ⟨80056622236057689840731405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53371081490705126560487603 80056622236057689840731405)
      ·
        refine ⟨30021233338521633690274277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80056622236057689840731405 30021233338521633690274277)
        ·
          refine ⟨5628981250972806316926427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30021233338521633690274277 5628981250972806316926427)
          ·
            refine ⟨8443471876459209475389641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628981250972806316926427 8443471876459209475389641)
            ·
              refine ⟨6332603907344407106542231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8443471876459209475389641 6332603907344407106542231)
              ·
                refine ⟨9498905861016610659813347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6332603907344407106542231 9498905861016610659813347)
                ·
                  refine ⟨14248358791524915989720021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9498905861016610659813347 14248358791524915989720021)
                  ·
                    refine ⟨333945909176365218509063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14248358791524915989720021 333945909176365218509063)
                    ·
                      rfl

theorem cell23_1951072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_1951072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951072 prefixEnd_1951072 := by exact prefixLift 1951072
  have htrace : WordTrace (prefixWord ++ tailWord_1951072) baseStart_1951072 baseEnd_1951072 := by
    simpa [prefixWord, tailWord_1951072, baseEnd_1951072] using wordTrace_append hprefix tailTrace_1951072
  have hstable : (prefixWord ++ tailWord_1951072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951072).length < 2 ^ (prefixWord ++ tailWord_1951072).sum := by decide
  have hdescent : baseEnd_1951072 < baseStart_1951072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951076 : List Nat := [2, 3, 1, 1, 3, 4, 1, 3, 5]
def baseStart_1951076 : Nat := 118140960795 + 1951076 * 2 ^ 59
def prefixEnd_1951076 : Nat := 4983230072969 + 3 ^ 40 * 1951076 * 2
def baseEnd_1951076 : Nat := 111315531272412626653019

theorem tailTrace_1951076 : CollatzResearch.WordTrace tailWord_1951076 prefixEnd_1951076 111315531272412626653019 := by
  unfold tailWord_1951076
  simp only [CollatzResearch.WordTrace]
  refine ⟨35580793939796172048564541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47441058586394896064752721 35580793939796172048564541)
  ·
    refine ⟨13342797727423564518211703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35580793939796172048564541 13342797727423564518211703)
    ·
      refine ⟨20014196591135346777317555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13342797727423564518211703 20014196591135346777317555)
      ·
        refine ⟨30021294886703020165976333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20014196591135346777317555 30021294886703020165976333)
        ·
          refine ⟨11257985582513632562241125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30021294886703020165976333 11257985582513632562241125)
          ·
            refine ⟨2110872296721306105420211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11257985582513632562241125 2110872296721306105420211)
            ·
              refine ⟨3166308445081959158130317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2110872296721306105420211 3166308445081959158130317)
              ·
                refine ⟨1187365666905734684298869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3166308445081959158130317 1187365666905734684298869)
                ·
                  refine ⟨111315531272412626653019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1187365666905734684298869 111315531272412626653019)
                  ·
                    rfl

theorem cell23_1951076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_1951076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951076 prefixEnd_1951076 := by exact prefixLift 1951076
  have htrace : WordTrace (prefixWord ++ tailWord_1951076) baseStart_1951076 baseEnd_1951076 := by
    simpa [prefixWord, tailWord_1951076, baseEnd_1951076] using wordTrace_append hprefix tailTrace_1951076
  have hstable : (prefixWord ++ tailWord_1951076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951076).length < 2 ^ (prefixWord ++ tailWord_1951076).sum := by decide
  have hdescent : baseEnd_1951076 < baseStart_1951076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951093 : List Nat := [1, 3, 4, 1, 3, 1, 3, 2, 5]
def baseStart_1951093 : Nat := 118140960795 + 1951093 * 2 ^ 59
def prefixEnd_1951093 : Nat := 4983230072969 + 3 ^ 40 * 1951093 * 2
def baseEnd_1951093 : Nat := 111316501180315563707177

theorem tailTrace_1951093 : CollatzResearch.WordTrace tailWord_1951093 prefixEnd_1951093 111316501180315563707177 := by
  unfold tailWord_1951093
  simp only [CollatzResearch.WordTrace]
  refine ⟨71162207920530756000497933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47441471947020504000331955 71162207920530756000497933)
  ·
    refine ⟨26685827970199033500186725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71162207920530756000497933 26685827970199033500186725)
    ·
      refine ⟨5003592744412318781285011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26685827970199033500186725 5003592744412318781285011)
      ·
        refine ⟨7505389116618478171927517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5003592744412318781285011 7505389116618478171927517)
        ·
          refine ⟨2814520918731929314472819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7505389116618478171927517 2814520918731929314472819)
          ·
            refine ⟨4221781378097893971709229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814520918731929314472819 4221781378097893971709229)
            ·
              refine ⟨1583168016786710239390961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4221781378097893971709229 1583168016786710239390961)
              ·
                refine ⟨1187376012590032679543221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1583168016786710239390961 1187376012590032679543221)
                ·
                  refine ⟨111316501180315563707177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1187376012590032679543221 111316501180315563707177)
                  ·
                    rfl

theorem cell23_1951093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_1951093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951093 prefixEnd_1951093 := by exact prefixLift 1951093
  have htrace : WordTrace (prefixWord ++ tailWord_1951093) baseStart_1951093 baseEnd_1951093 := by
    simpa [prefixWord, tailWord_1951093, baseEnd_1951093] using wordTrace_append hprefix tailTrace_1951093
  have hstable : (prefixWord ++ tailWord_1951093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951093).length < 2 ^ (prefixWord ++ tailWord_1951093).sum := by decide
  have hdescent : baseEnd_1951093 < baseStart_1951093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951109 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 2, 4, 2]
def baseStart_1951109 : Nat := 118140960795 + 1951109 * 2 ^ 59
def prefixEnd_1951109 : Nat := 4983230072969 + 3 ^ 40 * 1951109 * 2
def baseEnd_1951109 : Nat := 1001856726313312010764519

theorem tailTrace_1951109 : CollatzResearch.WordTrace tailWord_1951109 prefixEnd_1951109 1001856726313312010764519 := by
  unfold tailWord_1951109
  simp only [CollatzResearch.WordTrace]
  refine ⟨71162791488472790733080381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47441860992315193822053587 71162791488472790733080381)
  ·
    refine ⟨26686046808177296524905143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71162791488472790733080381 26686046808177296524905143)
    ·
      refine ⟨40029070212265944787357715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26686046808177296524905143 40029070212265944787357715)
      ·
        refine ⟨60043605318398917181036573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40029070212265944787357715 60043605318398917181036573)
        ·
          refine ⟨22516351994399593942888715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60043605318398917181036573 22516351994399593942888715)
          ·
            refine ⟨33774527991599390914333073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22516351994399593942888715 33774527991599390914333073)
            ·
              refine ⟨25330895993699543185749805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33774527991599390914333073 25330895993699543185749805)
              ·
                refine ⟨9499085997637328694656177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25330895993699543185749805 9499085997637328694656177)
                ·
                  refine ⟨7124314498227996520992133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9499085997637328694656177 7124314498227996520992133)
                  ·
                    refine ⟨1335808968417749347686025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7124314498227996520992133 1335808968417749347686025)
                    ·
                      refine ⟨1001856726313312010764519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335808968417749347686025 1001856726313312010764519)
                      ·
                        rfl

theorem cell23_1951109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_1951109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951109 prefixEnd_1951109 := by exact prefixLift 1951109
  have htrace : WordTrace (prefixWord ++ tailWord_1951109) baseStart_1951109 baseEnd_1951109 := by
    simpa [prefixWord, tailWord_1951109, baseEnd_1951109] using wordTrace_append hprefix tailTrace_1951109
  have hstable : (prefixWord ++ tailWord_1951109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951109).length < 2 ^ (prefixWord ++ tailWord_1951109).sum := by decide
  have hdescent : baseEnd_1951109 < baseStart_1951109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951129 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 2, 2, 3]
def baseStart_1951129 : Nat := 118140960795 + 1951129 * 2 ^ 59
def prefixEnd_1951129 : Nat := 4983230072969 + 3 ^ 40 * 1951129 * 2
def baseEnd_1951129 : Nat := 1001866995926401932514427

theorem tailTrace_1951129 : CollatzResearch.WordTrace tailWord_1951129 prefixEnd_1951129 1001866995926401932514427 := by
  unfold tailWord_1951129
  simp only [CollatzResearch.WordTrace]
  refine ⟨71163520948400334148808441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47442347298933556099205627 71163520948400334148808441)
  ·
    refine ⟨53372640711300250611606331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71163520948400334148808441 53372640711300250611606331)
    ·
      refine ⟨80058961066950375917409497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53372640711300250611606331 80058961066950375917409497)
      ·
        refine ⟨60044220800212781938057123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80058961066950375917409497 60044220800212781938057123)
        ·
          refine ⟨90066331200319172907085685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60044220800212781938057123 90066331200319172907085685)
          ·
            refine ⟨8443718550029922460039283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90066331200319172907085685 8443718550029922460039283)
            ·
              refine ⟨12665577825044883690058925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443718550029922460039283 12665577825044883690058925)
              ·
                refine ⟨4749591684391831383772097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12665577825044883690058925 4749591684391831383772097)
                ·
                  refine ⟨3562193763293873537829073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4749591684391831383772097 3562193763293873537829073)
                  ·
                    refine ⟨2671645322470405153371805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3562193763293873537829073 2671645322470405153371805)
                    ·
                      refine ⟨1001866995926401932514427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2671645322470405153371805 1001866995926401932514427)
                      ·
                        rfl

theorem cell23_1951129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_1951129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951129 prefixEnd_1951129 := by exact prefixLift 1951129
  have htrace : WordTrace (prefixWord ++ tailWord_1951129) baseStart_1951129 baseEnd_1951129 := by
    simpa [prefixWord, tailWord_1951129, baseEnd_1951129] using wordTrace_append hprefix tailTrace_1951129
  have hstable : (prefixWord ++ tailWord_1951129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951129).length < 2 ^ (prefixWord ++ tailWord_1951129).sum := by decide
  have hdescent : baseEnd_1951129 < baseStart_1951129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951136 : List Nat := [2, 1, 1, 4, 1, 2, 2, 5, 1, 4]
def baseStart_1951136 : Nat := 118140960795 + 1951136 * 2 ^ 59
def prefixEnd_1951136 : Nat := 4983230072969 + 3 ^ 40 * 1951136 * 2
def baseEnd_1951136 : Nat := 333956863430327801708965

theorem tailTrace_1951136 : CollatzResearch.WordTrace tailWord_1951136 prefixEnd_1951136 333956863430327801708965 := by
  unfold tailWord_1951136
  simp only [CollatzResearch.WordTrace]
  refine ⟨35581888129687487172156631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47442517506249982896208841 35581888129687487172156631)
  ·
    refine ⟨53372832194531230758234947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35581888129687487172156631 53372832194531230758234947)
    ·
      refine ⟨80059248291796846137352421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53372832194531230758234947 80059248291796846137352421)
      ·
        refine ⟨15011109054711908650753579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80059248291796846137352421 15011109054711908650753579)
        ·
          refine ⟨22516663582067862976130369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15011109054711908650753579 22516663582067862976130369)
          ·
            refine ⟨16887497686550897232097777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22516663582067862976130369 16887497686550897232097777)
            ·
              refine ⟨12665623264913172924073333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16887497686550897232097777 12665623264913172924073333)
              ·
                refine ⟨1187402181085609961631875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12665623264913172924073333 1187402181085609961631875)
                ·
                  refine ⟨1781103271628414942447813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187402181085609961631875 1781103271628414942447813)
                  ·
                    refine ⟨333956863430327801708965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1781103271628414942447813 333956863430327801708965)
                    ·
                      rfl

theorem cell23_1951136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 1, 4].length) (baseStart_1951136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951136 prefixEnd_1951136 := by exact prefixLift 1951136
  have htrace : WordTrace (prefixWord ++ tailWord_1951136) baseStart_1951136 baseEnd_1951136 := by
    simpa [prefixWord, tailWord_1951136, baseEnd_1951136] using wordTrace_append hprefix tailTrace_1951136
  have hstable : (prefixWord ++ tailWord_1951136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951136).length < 2 ^ (prefixWord ++ tailWord_1951136).sum := by decide
  have hdescent : baseEnd_1951136 < baseStart_1951136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951176 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_1951176 : Nat := 118140960795 + 1951176 * 2 ^ 59
def prefixEnd_1951176 : Nat := 4983230072969 + 3 ^ 40 * 1951176 * 2
def baseEnd_1951176 : Nat := 1001891129517163248626711

theorem tailTrace_1951176 : CollatzResearch.WordTrace tailWord_1951176 prefixEnd_1951176 1001891129517163248626711 := by
  unfold tailWord_1951176
  simp only [CollatzResearch.WordTrace]
  refine ⟨35582617589615030587884691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47443490119486707450512921 35582617589615030587884691)
  ·
    refine ⟨53373926384422545881827037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35582617589615030587884691 53373926384422545881827037)
    ·
      refine ⟨20015222394158454705685139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53373926384422545881827037 20015222394158454705685139)
      ·
        refine ⟨30022833591237682058527709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20015222394158454705685139 30022833591237682058527709)
        ·
          refine ⟨11258562596714130771947891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30022833591237682058527709 11258562596714130771947891)
          ·
            refine ⟨16887843895071196157921837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11258562596714130771947891 16887843895071196157921837)
            ·
              refine ⟨6332941460651698559220689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16887843895071196157921837 6332941460651698559220689)
              ·
                refine ⟨4749706095488773919415517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6332941460651698559220689 4749706095488773919415517)
                ·
                  refine ⟨1781139785808290219780819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4749706095488773919415517 1781139785808290219780819)
                  ·
                    refine ⟨2671709678712435329671229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1781139785808290219780819 2671709678712435329671229)
                    ·
                      refine ⟨1001891129517163248626711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2671709678712435329671229 1001891129517163248626711)
                      ·
                        rfl

theorem cell23_1951176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_1951176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951176 prefixEnd_1951176 := by exact prefixLift 1951176
  have htrace : WordTrace (prefixWord ++ tailWord_1951176) baseStart_1951176 baseEnd_1951176 := by
    simpa [prefixWord, tailWord_1951176, baseEnd_1951176] using wordTrace_append hprefix tailTrace_1951176
  have hstable : (prefixWord ++ tailWord_1951176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951176).length < 2 ^ (prefixWord ++ tailWord_1951176).sum := by decide
  have hdescent : baseEnd_1951176 < baseStart_1951176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951193 : List Nat := [1, 2, 1, 2, 4, 2, 1, 5, 1, 1, 3]
def baseStart_1951193 : Nat := 118140960795 + 1951193 * 2 ^ 59
def prefixEnd_1951193 : Nat := 4983230072969 + 3 ^ 40 * 1951193 * 2
def baseEnd_1951193 : Nat := 1001899858688289682114133

theorem tailTrace_1951193 : CollatzResearch.WordTrace tailWord_1951193 prefixEnd_1951193 1001899858688289682114133 := by
  unfold tailWord_1951193
  simp only [CollatzResearch.WordTrace]
  refine ⟨71165855220168473079138233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47443903480112315386092155 71165855220168473079138233)
  ·
    refine ⟨53374391415126354809353675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71165855220168473079138233 53374391415126354809353675)
    ·
      refine ⟨80061587122689532214030513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53374391415126354809353675 80061587122689532214030513)
      ·
        refine ⟨60046190342017149160522885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80061587122689532214030513 60046190342017149160522885)
        ·
          refine ⟨11258660689128215467598041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60046190342017149160522885 11258660689128215467598041)
          ·
            refine ⟨8443995516846161600698531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11258660689128215467598041 8443995516846161600698531)
            ·
              refine ⟨12665993275269242401047797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443995516846161600698531 12665993275269242401047797)
              ·
                refine ⟨1187436869556491475098231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12665993275269242401047797 1187436869556491475098231)
                ·
                  refine ⟨1781155304334737212647347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187436869556491475098231 1781155304334737212647347)
                  ·
                    refine ⟨2671732956502105818971021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1781155304334737212647347 2671732956502105818971021)
                    ·
                      refine ⟨1001899858688289682114133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2671732956502105818971021 1001899858688289682114133)
                      ·
                        rfl

theorem cell23_1951193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 1, 1, 3].length) (baseStart_1951193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951193 prefixEnd_1951193 := by exact prefixLift 1951193
  have htrace : WordTrace (prefixWord ++ tailWord_1951193) baseStart_1951193 baseEnd_1951193 := by
    simpa [prefixWord, tailWord_1951193, baseEnd_1951193] using wordTrace_append hprefix tailTrace_1951193
  have hstable : (prefixWord ++ tailWord_1951193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951193).length < 2 ^ (prefixWord ++ tailWord_1951193).sum := by decide
  have hdescent : baseEnd_1951193 < baseStart_1951193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951219 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 3]
def baseStart_1951219 : Nat := 118140960795 + 1951219 * 2 ^ 59
def prefixEnd_1951219 : Nat := 4983230072969 + 3 ^ 40 * 1951219 * 2
def baseEnd_1951219 : Nat := 1001913209185306580389013

theorem tailTrace_1951219 : CollatzResearch.WordTrace tailWord_1951219 prefixEnd_1951219 1001913209185306580389013 := by
  unfold tailWord_1951219
  simp only [CollatzResearch.WordTrace]
  refine ⟨71166803518074279519584711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47444535678716186346389807 71166803518074279519584711)
  ·
    refine ⟨106750205277111419279377067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71166803518074279519584711 106750205277111419279377067)
    ·
      refine ⟨160125307915667128919065601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106750205277111419279377067 160125307915667128919065601)
      ·
        refine ⟨120093980936750346689299201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160125307915667128919065601 120093980936750346689299201)
        ·
          refine ⟨90070485702562760016974401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120093980936750346689299201 90070485702562760016974401)
          ·
            refine ⟨67552864276922070012730801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90070485702562760016974401 67552864276922070012730801)
            ·
              refine ⟨50664648207691552509548101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67552864276922070012730801 50664648207691552509548101)
              ·
                refine ⟨9499621538942166095540269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50664648207691552509548101 9499621538942166095540269)
                ·
                  refine ⟨3562358077103312285827601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9499621538942166095540269 3562358077103312285827601)
                  ·
                    refine ⟨2671768557827484214370701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3562358077103312285827601 2671768557827484214370701)
                    ·
                      refine ⟨1001913209185306580389013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2671768557827484214370701 1001913209185306580389013)
                      ·
                        rfl

theorem cell23_1951219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 3].length) (baseStart_1951219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951219 prefixEnd_1951219 := by exact prefixLift 1951219
  have htrace : WordTrace (prefixWord ++ tailWord_1951219) baseStart_1951219 baseEnd_1951219 := by
    simpa [prefixWord, tailWord_1951219, baseEnd_1951219] using wordTrace_append hprefix tailTrace_1951219
  have hstable : (prefixWord ++ tailWord_1951219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951219).length < 2 ^ (prefixWord ++ tailWord_1951219).sum := by decide
  have hdescent : baseEnd_1951219 < baseStart_1951219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951229 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_1951229 : Nat := 118140960795 + 1951229 * 2 ^ 59
def prefixEnd_1951229 : Nat := 4983230072969 + 3 ^ 40 * 1951229 * 2
def baseEnd_1951229 : Nat := 1001918343991851541263967

theorem tailTrace_1951229 : CollatzResearch.WordTrace tailWord_1951229 prefixEnd_1951229 1001918343991851541263967 := by
  unfold tailWord_1951229
  simp only [CollatzResearch.WordTrace]
  refine ⟨71167168248038051227448741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47444778832025367484965827 71167168248038051227448741)
  ·
    refine ⟨13343844046507134605146639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71167168248038051227448741 13343844046507134605146639)
    ·
      refine ⟨20015766069760701907719959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13343844046507134605146639 20015766069760701907719959)
      ·
        refine ⟨30023649104641052861579939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20015766069760701907719959 30023649104641052861579939)
        ·
          refine ⟨45035473656961579292369909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30023649104641052861579939 45035473656961579292369909)
          ·
            refine ⟨4222075655340148058659679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45035473656961579292369909 4222075655340148058659679)
            ·
              refine ⟨6333113483010222087989519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4222075655340148058659679 6333113483010222087989519)
              ·
                refine ⟨9499670224515333131984279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6333113483010222087989519 9499670224515333131984279)
                ·
                  refine ⟨14249505336772999697976419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9499670224515333131984279 14249505336772999697976419)
                  ·
                    refine ⟨21374258005159499546964629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14249505336772999697976419 21374258005159499546964629)
                    ·
                      refine ⟨1001918343991851541263967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21374258005159499546964629 1001918343991851541263967)
                      ·
                        rfl

theorem cell23_1951229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_1951229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951229 prefixEnd_1951229 := by exact prefixLift 1951229
  have htrace : WordTrace (prefixWord ++ tailWord_1951229) baseStart_1951229 baseEnd_1951229 := by
    simpa [prefixWord, tailWord_1951229, baseEnd_1951229] using wordTrace_append hprefix tailTrace_1951229
  have hstable : (prefixWord ++ tailWord_1951229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951229).length < 2 ^ (prefixWord ++ tailWord_1951229).sum := by decide
  have hdescent : baseEnd_1951229 < baseStart_1951229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951230 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1951230 : Nat := 118140960795 + 1951230 * 2 ^ 59
def prefixEnd_1951230 : Nat := 4983230072969 + 3 ^ 40 * 1951230 * 2
def baseEnd_1951230 : Nat := 333972952490835345783821

theorem tailTrace_1951230 : CollatzResearch.WordTrace tailWord_1951230 prefixEnd_1951230 333972952490835345783821 := by
  unfold tailWord_1951230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8895900590129303549779393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47444803147356285598823429 8895900590129303549779393)
  ·
    refine ⟨6671925442596977662334545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8895900590129303549779393 6671925442596977662334545)
    ·
      refine ⟨5003944081947733246750909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6671925442596977662334545 5003944081947733246750909)
      ·
        refine ⟨1876479030730399967531591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5003944081947733246750909 1876479030730399967531591)
        ·
          refine ⟨2814718546095599951297387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1876479030730399967531591 2814718546095599951297387)
          ·
            refine ⟨4222077819143399926946081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814718546095599951297387 4222077819143399926946081)
            ·
              refine ⟨3166558364357549945209561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4222077819143399926946081 3166558364357549945209561)
              ·
                refine ⟨2374918773268162458907171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3166558364357549945209561 2374918773268162458907171)
                ·
                  refine ⟨3562378159902243688360757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374918773268162458907171 3562378159902243688360757)
                  ·
                    refine ⟨333972952490835345783821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3562378159902243688360757 333972952490835345783821)
                    ·
                      rfl

theorem cell23_1951230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1951230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951230 prefixEnd_1951230 := by exact prefixLift 1951230
  have htrace : WordTrace (prefixWord ++ tailWord_1951230) baseStart_1951230 baseEnd_1951230 := by
    simpa [prefixWord, tailWord_1951230, baseEnd_1951230] using wordTrace_append hprefix tailTrace_1951230
  have hstable : (prefixWord ++ tailWord_1951230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951230).length < 2 ^ (prefixWord ++ tailWord_1951230).sum := by decide
  have hdescent : baseEnd_1951230 < baseStart_1951230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951233 : List Nat := [1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_1951233 : Nat := 118140960795 + 1951233 * 2 ^ 59
def prefixEnd_1951233 : Nat := 4983230072969 + 3 ^ 40 * 1951233 * 2
def baseEnd_1951233 : Nat := 1001920397914469525613949

theorem tailTrace_1951233 : CollatzResearch.WordTrace tailWord_1951233 prefixEnd_1951233 1001920397914469525613949 := by
  unfold tailWord_1951233
  simp only [CollatzResearch.WordTrace]
  refine ⟨71167314140023559910594353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47444876093349039940396235 71167314140023559910594353)
  ·
    refine ⟨53375485605017669932945765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71167314140023559910594353 53375485605017669932945765)
    ·
      refine ⟨10007903550940813112427331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53375485605017669932945765 10007903550940813112427331)
      ·
        refine ⟨15011855326411219668640997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10007903550940813112427331 15011855326411219668640997)
        ·
          refine ⟨2814722873702103687870187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15011855326411219668640997 2814722873702103687870187)
          ·
            refine ⟨4222084310553155531805281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2814722873702103687870187 4222084310553155531805281)
            ·
              refine ⟨3166563232914866648853961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4222084310553155531805281 3166563232914866648853961)
              ·
                refine ⟨2374922424686149986640471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3166563232914866648853961 2374922424686149986640471)
                ·
                  refine ⟨3562383637029224979960707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2374922424686149986640471 3562383637029224979960707)
                  ·
                    refine ⟨5343575455543837469941061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3562383637029224979960707 5343575455543837469941061)
                    ·
                      refine ⟨1001920397914469525613949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5343575455543837469941061 1001920397914469525613949)
                      ·
                        rfl

theorem cell23_1951233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_1951233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951233 prefixEnd_1951233 := by exact prefixLift 1951233
  have htrace : WordTrace (prefixWord ++ tailWord_1951233) baseStart_1951233 baseEnd_1951233 := by
    simpa [prefixWord, tailWord_1951233, baseEnd_1951233] using wordTrace_append hprefix tailTrace_1951233
  have hstable : (prefixWord ++ tailWord_1951233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951233).length < 2 ^ (prefixWord ++ tailWord_1951233).sum := by decide
  have hdescent : baseEnd_1951233 < baseStart_1951233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951239 : List Nat := [1, 1, 4, 3, 2, 2, 1, 9]
def baseStart_1951239 : Nat := 118140960795 + 1951239 * 2 ^ 59
def prefixEnd_1951239 : Nat := 4983230072969 + 3 ^ 40 * 1951239 * 2
def baseEnd_1951239 : Nat := 37108276992533203782923

theorem tailTrace_1951239 : CollatzResearch.WordTrace tailWord_1951239 prefixEnd_1951239 37108276992533203782923 := by
  unfold tailWord_1951239
  simp only [CollatzResearch.WordTrace]
  refine ⟨71167532978001822935312771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47445021985334548623541847 71167532978001822935312771)
  ·
    refine ⟨106751299467002734402969157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71167532978001822935312771 106751299467002734402969157)
    ·
      refine ⟨20015868650063012700556717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106751299467002734402969157 20015868650063012700556717)
      ·
        refine ⟨7505950743773629762708769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20015868650063012700556717 7505950743773629762708769)
        ·
          refine ⟨5629463057830222322031577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7505950743773629762708769 5629463057830222322031577)
          ·
            refine ⟨4222097293372666741523683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5629463057830222322031577 4222097293372666741523683)
            ·
              refine ⟨6333145940059000112285525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4222097293372666741523683 6333145940059000112285525)
              ·
                refine ⟨37108276992533203782923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6333145940059000112285525 37108276992533203782923)
                ·
                  rfl

theorem cell23_1951239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 9].length) (baseStart_1951239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951239 prefixEnd_1951239 := by exact prefixLift 1951239
  have htrace : WordTrace (prefixWord ++ tailWord_1951239) baseStart_1951239 baseEnd_1951239 := by
    simpa [prefixWord, tailWord_1951239, baseEnd_1951239] using wordTrace_append hprefix tailTrace_1951239
  have hstable : (prefixWord ++ tailWord_1951239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951239).length < 2 ^ (prefixWord ++ tailWord_1951239).sum := by decide
  have hdescent : baseEnd_1951239 < baseStart_1951239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951249 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 3]
def baseStart_1951249 : Nat := 118140960795 + 1951249 * 2 ^ 59
def prefixEnd_1951249 : Nat := 4983230072969 + 3 ^ 40 * 1951249 * 2
def baseEnd_1951249 : Nat := 1001928613604941463013875

theorem tailTrace_1951249 : CollatzResearch.WordTrace tailWord_1951249 prefixEnd_1951249 1001928613604941463013875 := by
  unfold tailWord_1951249
  simp only [CollatzResearch.WordTrace]
  refine ⟨71167897707965594643176801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47445265138643729762117867 71167897707965594643176801)
  ·
    refine ⟨53375923280974195982382601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71167897707965594643176801 53375923280974195982382601)
    ·
      refine ⟨40031942460730646986786951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53375923280974195982382601 40031942460730646986786951)
      ·
        refine ⟨60047913691095970480180427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40031942460730646986786951 60047913691095970480180427)
        ·
          refine ⟨90071870536643955720270641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60047913691095970480180427 90071870536643955720270641)
          ·
            refine ⟨67553902902482966790202981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90071870536643955720270641 67553902902482966790202981)
            ·
              refine ⟨12666356794215556273163059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67553902902482966790202981 12666356794215556273163059)
              ·
                refine ⟨18999535191323334409744589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12666356794215556273163059 18999535191323334409744589)
                ·
                  refine ⟨7124825696746250403654221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18999535191323334409744589 7124825696746250403654221)
                  ·
                    refine ⟨2671809636279843901370333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7124825696746250403654221 2671809636279843901370333)
                    ·
                      refine ⟨1001928613604941463013875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2671809636279843901370333 1001928613604941463013875)
                      ·
                        rfl

theorem cell23_1951249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_1951249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951249 prefixEnd_1951249 := by exact prefixLift 1951249
  have htrace : WordTrace (prefixWord ++ tailWord_1951249) baseStart_1951249 baseEnd_1951249 := by
    simpa [prefixWord, tailWord_1951249, baseEnd_1951249] using wordTrace_append hprefix tailTrace_1951249
  have hstable : (prefixWord ++ tailWord_1951249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951249).length < 2 ^ (prefixWord ++ tailWord_1951249).sum := by decide
  have hdescent : baseEnd_1951249 < baseStart_1951249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951256 : List Nat := [2, 1, 2, 3, 5, 1, 9]
def baseStart_1951256 : Nat := 118140960795 + 1951256 * 2 ^ 59
def prefixEnd_1951256 : Nat := 4983230072969 + 3 ^ 40 * 1951256 * 2
def baseEnd_1951256 : Nat := 12369533431722505378103

theorem tailTrace_1951256 : CollatzResearch.WordTrace tailWord_1951256 prefixEnd_1951256 12369533431722505378103 := by
  unfold tailWord_1951256
  simp only [CollatzResearch.WordTrace]
  refine ⟨35584076509470117419340811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47445435345960156559121081 35584076509470117419340811)
  ·
    refine ⟨53376114764205176129011217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35584076509470117419340811 53376114764205176129011217)
    ·
      refine ⟨40032086073153882096758413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53376114764205176129011217 40032086073153882096758413)
      ·
        refine ⟨15012032277432705786284405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40032086073153882096758413 15012032277432705786284405)
        ·
          refine ⟨1407378026009316167464163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15012032277432705786284405 1407378026009316167464163)
          ·
            refine ⟨2111067039013974251196245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407378026009316167464163 2111067039013974251196245)
            ·
              refine ⟨12369533431722505378103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2111067039013974251196245 12369533431722505378103)
              ·
                rfl

theorem cell23_1951256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 9].length) (baseStart_1951256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951256 prefixEnd_1951256 := by exact prefixLift 1951256
  have htrace : WordTrace (prefixWord ++ tailWord_1951256) baseStart_1951256 baseEnd_1951256 := by
    simpa [prefixWord, tailWord_1951256, baseEnd_1951256] using wordTrace_append hprefix tailTrace_1951256
  have hstable : (prefixWord ++ tailWord_1951256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951256).length < 2 ^ (prefixWord ++ tailWord_1951256).sum := by decide
  have hdescent : baseEnd_1951256 < baseStart_1951256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951267 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 3, 2, 2]
def baseStart_1951267 : Nat := 118140960795 + 1951267 * 2 ^ 59
def prefixEnd_1951267 : Nat := 4983230072969 + 3 ^ 40 * 1951267 * 2
def baseEnd_1951267 : Nat := 1001937856256722392588793

theorem tailTrace_1951267 : CollatzResearch.WordTrace tailWord_1951267 prefixEnd_1951267 1001937856256722392588793 := by
  unfold tailWord_1951267
  simp only [CollatzResearch.WordTrace]
  refine ⟨71168554221900383717332055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47445702814600255811554703 71168554221900383717332055)
  ·
    refine ⟨106752831332850575575998083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71168554221900383717332055 106752831332850575575998083)
    ·
      refine ⟨160129246999275863363997125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106752831332850575575998083 160129246999275863363997125)
      ·
        refine ⟨30024233812364224380749461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160129246999275863363997125 30024233812364224380749461)
        ·
          refine ⟨1407385959954573017847631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30024233812364224380749461 1407385959954573017847631)
          ·
            refine ⟨2111078939931859526771447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407385959954573017847631 2111078939931859526771447)
            ·
              refine ⟨3166618409897789290157171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2111078939931859526771447 3166618409897789290157171)
              ·
                refine ⟨4749927614846683935235757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3166618409897789290157171 4749927614846683935235757)
                ·
                  refine ⟨1781222855567506475713409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4749927614846683935235757 1781222855567506475713409)
                  ·
                    refine ⟨1335917141675629856785057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1781222855567506475713409 1335917141675629856785057)
                    ·
                      refine ⟨1001937856256722392588793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1335917141675629856785057 1001937856256722392588793)
                      ·
                        rfl

theorem cell23_1951267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_1951267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951267 prefixEnd_1951267 := by exact prefixLift 1951267
  have htrace : WordTrace (prefixWord ++ tailWord_1951267) baseStart_1951267 baseEnd_1951267 := by
    simpa [prefixWord, tailWord_1951267, baseEnd_1951267] using wordTrace_append hprefix tailTrace_1951267
  have hstable : (prefixWord ++ tailWord_1951267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951267).length < 2 ^ (prefixWord ++ tailWord_1951267).sum := by decide
  have hdescent : baseEnd_1951267 < baseStart_1951267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951283 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 3]
def baseStart_1951283 : Nat := 118140960795 + 1951283 * 2 ^ 59
def prefixEnd_1951283 : Nat := 4983230072969 + 3 ^ 40 * 1951283 * 2
def baseEnd_1951283 : Nat := 1001946071947194329988719

theorem tailTrace_1951283 : CollatzResearch.WordTrace tailWord_1951283 prefixEnd_1951283 1001946071947194329988719 := by
  unfold tailWord_1951283
  simp only [CollatzResearch.WordTrace]
  refine ⟨71169137789842418449914503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47446091859894945633276335 71169137789842418449914503)
  ·
    refine ⟨106753706684763627674871755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71169137789842418449914503 106753706684763627674871755)
    ·
      refine ⟨160130560027145441512307633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106753706684763627674871755 160130560027145441512307633)
      ·
        refine ⟨120097920020359081134230725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160130560027145441512307633 120097920020359081134230725)
        ·
          refine ⟨22518360003817327712668261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120097920020359081134230725 22518360003817327712668261)
          ·
            refine ⟨4222192500715748946125299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22518360003817327712668261 4222192500715748946125299)
            ·
              refine ⟨6333288751073623419187949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4222192500715748946125299 6333288751073623419187949)
              ·
                refine ⟨2374983281652608782195481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6333288751073623419187949 2374983281652608782195481)
                ·
                  refine ⟨1781237461239456586646611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2374983281652608782195481 1781237461239456586646611)
                  ·
                    refine ⟨2671856191859184879969917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1781237461239456586646611 2671856191859184879969917)
                    ·
                      refine ⟨1001946071947194329988719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2671856191859184879969917 1001946071947194329988719)
                      ·
                        rfl

theorem cell23_1951283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 2, 1, 3].length) (baseStart_1951283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951283 prefixEnd_1951283 := by exact prefixLift 1951283
  have htrace : WordTrace (prefixWord ++ tailWord_1951283) baseStart_1951283 baseEnd_1951283 := by
    simpa [prefixWord, tailWord_1951283, baseEnd_1951283] using wordTrace_append hprefix tailTrace_1951283
  have hstable : (prefixWord ++ tailWord_1951283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951283).length < 2 ^ (prefixWord ++ tailWord_1951283).sum := by decide
  have hdescent : baseEnd_1951283 < baseStart_1951283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951329 : List Nat := [1, 2, 3, 1, 1, 3, 2, 3, 7]
def baseStart_1951329 : Nat := 118140960795 + 1951329 * 2 ^ 59
def prefixEnd_1951329 : Nat := 4983230072969 + 3 ^ 40 * 1951329 * 2
def baseEnd_1951329 : Nat := 111329965784144572223723

theorem tailTrace_1951329 : CollatzResearch.WordTrace tailWord_1951329 prefixEnd_1951329 111329965784144572223723 := by
  unfold tailWord_1951329
  simp only [CollatzResearch.WordTrace]
  refine ⟨71170815547675768306089041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47447210365117178870726027 71170815547675768306089041)
  ·
    refine ⟨53378111660756826229566781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71170815547675768306089041 53378111660756826229566781)
    ·
      refine ⟨20016791872783809836087543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53378111660756826229566781 20016791872783809836087543)
      ·
        refine ⟨30025187809175714754131315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20016791872783809836087543 30025187809175714754131315)
        ·
          refine ⟨45037781713763572131196973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30025187809175714754131315 45037781713763572131196973)
          ·
            refine ⟨16889168142661339549198865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45037781713763572131196973 16889168142661339549198865)
            ·
              refine ⟨12666876106996004661899149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16889168142661339549198865 12666876106996004661899149)
              ·
                refine ⟨4750078540123501748212181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12666876106996004661899149 4750078540123501748212181)
                ·
                  refine ⟨111329965784144572223723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4750078540123501748212181 111329965784144572223723)
                  ·
                    rfl

theorem cell23_1951329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 7].length) (baseStart_1951329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951329 prefixEnd_1951329 := by exact prefixLift 1951329
  have htrace : WordTrace (prefixWord ++ tailWord_1951329) baseStart_1951329 baseEnd_1951329 := by
    simpa [prefixWord, tailWord_1951329, baseEnd_1951329] using wordTrace_append hprefix tailTrace_1951329
  have hstable : (prefixWord ++ tailWord_1951329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951329).length < 2 ^ (prefixWord ++ tailWord_1951329).sum := by decide
  have hdescent : baseEnd_1951329 < baseStart_1951329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951336 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1951336 : Nat := 118140960795 + 1951336 * 2 ^ 59
def prefixEnd_1951336 : Nat := 4983230072969 + 3 ^ 40 * 1951336 * 2
def baseEnd_1951336 : Nat := 1001973286421882622625975

theorem tailTrace_1951336 : CollatzResearch.WordTrace tailWord_1951336 prefixEnd_1951336 1001973286421882622625975 := by
  unfold tailWord_1951336
  simp only [CollatzResearch.WordTrace]
  refine ⟨35585535429325204250796931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47447380572433605667729241 35585535429325204250796931)
  ·
    refine ⟨53378303143987806376195397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35585535429325204250796931 53378303143987806376195397)
    ·
      refine ⟨10008431839497713695536637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53378303143987806376195397 10008431839497713695536637)
      ·
        refine ⟨3753161939811642635826239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10008431839497713695536637 3753161939811642635826239)
        ·
          refine ⟨5629742909717463953739359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3753161939811642635826239 5629742909717463953739359)
          ·
            refine ⟨8444614364576195930609039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5629742909717463953739359 8444614364576195930609039)
            ·
              refine ⟨12666921546864293895913559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8444614364576195930609039 12666921546864293895913559)
              ·
                refine ⟨19000382320296440843870339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12666921546864293895913559 19000382320296440843870339)
                ·
                  refine ⟨28500573480444661265805509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19000382320296440843870339 28500573480444661265805509)
                  ·
                    refine ⟨5343857527583373987338533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28500573480444661265805509 5343857527583373987338533)
                    ·
                      refine ⟨1001973286421882622625975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5343857527583373987338533 1001973286421882622625975)
                      ·
                        rfl

theorem cell23_1951336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1951336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951336 prefixEnd_1951336 := by exact prefixLift 1951336
  have htrace : WordTrace (prefixWord ++ tailWord_1951336) baseStart_1951336 baseEnd_1951336 := by
    simpa [prefixWord, tailWord_1951336, baseEnd_1951336] using wordTrace_append hprefix tailTrace_1951336
  have hstable : (prefixWord ++ tailWord_1951336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951336).length < 2 ^ (prefixWord ++ tailWord_1951336).sum := by decide
  have hdescent : baseEnd_1951336 < baseStart_1951336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951346 : List Nat := [3, 2, 1, 2, 3, 2, 1, 2, 7]
def baseStart_1951346 : Nat := 118140960795 + 1951346 * 2 ^ 59
def prefixEnd_1951346 : Nat := 4983230072969 + 3 ^ 40 * 1951346 * 2
def baseEnd_1951346 : Nat := 111330935692047509277881

theorem tailTrace_1951346 : CollatzResearch.WordTrace tailWord_1951346 prefixEnd_1951346 111330935692047509277881 := by
  unfold tailWord_1951346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17792858897153545052364473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47447623725742786806305261 17792858897153545052364473)
  ·
    refine ⟨13344644172865158789273355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17792858897153545052364473 13344644172865158789273355)
    ·
      refine ⟨20016966259297738183910033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13344644172865158789273355 20016966259297738183910033)
      ·
        refine ⟨15012724694473303637932525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20016966259297738183910033 15012724694473303637932525)
        ·
          refine ⟨5629771760427488864224697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15012724694473303637932525 5629771760427488864224697)
          ·
            refine ⟨4222328820320616648168523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5629771760427488864224697 4222328820320616648168523)
            ·
              refine ⟨6333493230480924972252785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4222328820320616648168523 6333493230480924972252785)
              ·
                refine ⟨4750119922860693729189589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6333493230480924972252785 4750119922860693729189589)
                ·
                  refine ⟨111330935692047509277881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4750119922860693729189589 111330935692047509277881)
                  ·
                    rfl

theorem cell23_1951346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_1951346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951346 prefixEnd_1951346 := by exact prefixLift 1951346
  have htrace : WordTrace (prefixWord ++ tailWord_1951346) baseStart_1951346 baseEnd_1951346 := by
    simpa [prefixWord, tailWord_1951346, baseEnd_1951346] using wordTrace_append hprefix tailTrace_1951346
  have hstable : (prefixWord ++ tailWord_1951346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951346).length < 2 ^ (prefixWord ++ tailWord_1951346).sum := by decide
  have hdescent : baseEnd_1951346 < baseStart_1951346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951369 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_1951369 : Nat := 118140960795 + 1951369 * 2 ^ 59
def prefixEnd_1951369 : Nat := 4983230072969 + 3 ^ 40 * 1951369 * 2
def baseEnd_1951369 : Nat := 1001990231283480993513323

theorem tailTrace_1951369 : CollatzResearch.WordTrace tailWord_1951369 prefixEnd_1951369 1001990231283480993513323 := by
  unfold tailWord_1951369
  simp only [CollatzResearch.WordTrace]
  refine ⟨71172274467530855137545161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47448182978353903425030107 71172274467530855137545161)
  ·
    refine ⟨53379205850648141353158871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71172274467530855137545161 53379205850648141353158871)
    ·
      refine ⟨80068808775972212029738307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53379205850648141353158871 80068808775972212029738307)
      ·
        refine ⟨120103213163958318044607461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80068808775972212029738307 120103213163958318044607461)
        ·
          refine ⟨22519352468242184633363899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120103213163958318044607461 22519352468242184633363899)
          ·
            refine ⟨33779028702363276950045849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22519352468242184633363899 33779028702363276950045849)
            ·
              refine ⟨25334271526772457712534387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33779028702363276950045849 25334271526772457712534387)
              ·
                refine ⟨38001407290158686568801581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25334271526772457712534387 38001407290158686568801581)
                ·
                  refine ⟨14250527733809507463300593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38001407290158686568801581 14250527733809507463300593)
                  ·
                    refine ⟨10687895800357130597475445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14250527733809507463300593 10687895800357130597475445)
                    ·
                      refine ⟨1001990231283480993513323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10687895800357130597475445 1001990231283480993513323)
                      ·
                        rfl

theorem cell23_1951369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_1951369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951369 prefixEnd_1951369 := by exact prefixLift 1951369
  have htrace : WordTrace (prefixWord ++ tailWord_1951369) baseStart_1951369 baseEnd_1951369 := by
    simpa [prefixWord, tailWord_1951369, baseEnd_1951369] using wordTrace_append hprefix tailTrace_1951369
  have hstable : (prefixWord ++ tailWord_1951369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951369).length < 2 ^ (prefixWord ++ tailWord_1951369).sum := by decide
  have hdescent : baseEnd_1951369 < baseStart_1951369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951379 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 4]
def baseStart_1951379 : Nat := 118140960795 + 1951379 * 2 ^ 59
def prefixEnd_1951379 : Nat := 4983230072969 + 3 ^ 40 * 1951379 * 2
def baseEnd_1951379 : Nat := 1001995366090025954388277

theorem tailTrace_1951379 : CollatzResearch.WordTrace tailWord_1951379 prefixEnd_1951379 1001995366090025954388277 := by
  unfold tailWord_1951379
  simp only [CollatzResearch.WordTrace]
  refine ⟨71172639197494626845409191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47448426131663084563606127 71172639197494626845409191)
  ·
    refine ⟨106758958796241940268113787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71172639197494626845409191 106758958796241940268113787)
    ·
      refine ⟨160138438194362910402170681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106758958796241940268113787 160138438194362910402170681)
      ·
        refine ⟨120103828645772182801628011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160138438194362910402170681 120103828645772182801628011)
        ·
          refine ⟨180155742968658274202442017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120103828645772182801628011 180155742968658274202442017)
          ·
            refine ⟨135116807226493705651831513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180155742968658274202442017 135116807226493705651831513)
            ·
              refine ⟨101337605419870279238873635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135116807226493705651831513 101337605419870279238873635)
              ·
                refine ⟨152006408129805418858310453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101337605419870279238873635 152006408129805418858310453)
                ·
                  refine ⟨14250600762169258017966605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152006408129805418858310453 14250600762169258017966605)
                  ·
                    refine ⟨5343975285813471756737477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14250600762169258017966605 5343975285813471756737477)
                    ·
                      refine ⟨1001995366090025954388277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5343975285813471756737477 1001995366090025954388277)
                      ·
                        rfl

theorem cell23_1951379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_1951379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951379 prefixEnd_1951379 := by exact prefixLift 1951379
  have htrace : WordTrace (prefixWord ++ tailWord_1951379) baseStart_1951379 baseEnd_1951379 := by
    simpa [prefixWord, tailWord_1951379, baseEnd_1951379] using wordTrace_append hprefix tailTrace_1951379
  have hstable : (prefixWord ++ tailWord_1951379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951379).length < 2 ^ (prefixWord ++ tailWord_1951379).sum := by decide
  have hdescent : baseEnd_1951379 < baseStart_1951379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951396 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1951396 : Nat := 118140960795 + 1951396 * 2 ^ 59
def prefixEnd_1951396 : Nat := 4983230072969 + 3 ^ 40 * 1951396 * 2
def baseEnd_1951396 : Nat := 1002004095261152387875699

theorem tailTrace_1951396 : CollatzResearch.WordTrace tailWord_1951396 prefixEnd_1951396 1002004095261152387875699 := by
  unfold tailWord_1951396
  simp only [CollatzResearch.WordTrace]
  refine ⟨35586629619216519374389021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47448839492288692499185361 35586629619216519374389021)
  ·
    refine ⟨13344986107206194765395883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35586629619216519374389021 13344986107206194765395883)
    ·
      refine ⟨20017479160809292148093825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13344986107206194765395883 20017479160809292148093825)
      ·
        refine ⟨15013109370606969111070369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20017479160809292148093825 15013109370606969111070369)
        ·
          refine ⟨11259832027955226833302777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15013109370606969111070369 11259832027955226833302777)
          ·
            refine ⟨8444874020966420124977083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11259832027955226833302777 8444874020966420124977083)
            ·
              refine ⟨12667311031449630187465625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8444874020966420124977083 12667311031449630187465625)
              ·
                refine ⟨9500483273587222640599219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12667311031449630187465625 9500483273587222640599219)
                ·
                  refine ⟨14250724910380833960898829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9500483273587222640599219 14250724910380833960898829)
                  ·
                    refine ⟨5344021841392812735337061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14250724910380833960898829 5344021841392812735337061)
                    ·
                      refine ⟨1002004095261152387875699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5344021841392812735337061 1002004095261152387875699)
                      ·
                        rfl

theorem cell23_1951396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1951396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951396 prefixEnd_1951396 := by exact prefixLift 1951396
  have htrace : WordTrace (prefixWord ++ tailWord_1951396) baseStart_1951396 baseEnd_1951396 := by
    simpa [prefixWord, tailWord_1951396, baseEnd_1951396] using wordTrace_append hprefix tailTrace_1951396
  have hstable : (prefixWord ++ tailWord_1951396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951396).length < 2 ^ (prefixWord ++ tailWord_1951396).sum := by decide
  have hdescent : baseEnd_1951396 < baseStart_1951396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951416 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 6, 2, 3]
def baseStart_1951416 : Nat := 118140960795 + 1951416 * 2 ^ 59
def prefixEnd_1951416 : Nat := 4983230072969 + 3 ^ 40 * 1951416 * 2
def baseEnd_1951416 : Nat := 1002014364874242309625607

theorem tailTrace_1951416 : CollatzResearch.WordTrace tailWord_1951416 prefixEnd_1951416 1002014364874242309625607 := by
  unfold tailWord_1951416
  simp only [CollatzResearch.WordTrace]
  refine ⟨35586994349180291082253051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47449325798907054776337401 35586994349180291082253051)
  ·
    refine ⟨53380491523770436623379577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35586994349180291082253051 53380491523770436623379577)
    ·
      refine ⟨40035368642827827467534683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53380491523770436623379577 40035368642827827467534683)
      ·
        refine ⟨60053052964241741201302025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40035368642827827467534683 60053052964241741201302025)
        ·
          refine ⟨45039789723181305900976519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60053052964241741201302025 45039789723181305900976519)
          ·
            refine ⟨67559684584771958851464779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45039789723181305900976519 67559684584771958851464779)
            ·
              refine ⟨101339526877157938277197169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67559684584771958851464779 101339526877157938277197169)
              ·
                refine ⟨76004645157868453707897877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101339526877157938277197169 76004645157868453707897877)
                ·
                  refine ⟨3562717741775083767557713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76004645157868453707897877 3562717741775083767557713)
                  ·
                    refine ⟨2672038306331312825668285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3562717741775083767557713 2672038306331312825668285)
                    ·
                      refine ⟨1002014364874242309625607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2672038306331312825668285 1002014364874242309625607)
                      ·
                        rfl

theorem cell23_1951416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_1951416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951416 prefixEnd_1951416 := by exact prefixLift 1951416
  have htrace : WordTrace (prefixWord ++ tailWord_1951416) baseStart_1951416 baseEnd_1951416 := by
    simpa [prefixWord, tailWord_1951416, baseEnd_1951416] using wordTrace_append hprefix tailTrace_1951416
  have hstable : (prefixWord ++ tailWord_1951416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951416).length < 2 ^ (prefixWord ++ tailWord_1951416).sum := by decide
  have hdescent : baseEnd_1951416 < baseStart_1951416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951439 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_1951439 : Nat := 118140960795 + 1951439 * 2 ^ 59
def prefixEnd_1951439 : Nat := 4983230072969 + 3 ^ 40 * 1951439 * 2
def baseEnd_1951439 : Nat := 1002026174929295719638001

theorem tailTrace_1951439 : CollatzResearch.WordTrace tailWord_1951439 prefixEnd_1951439 1002026174929295719638001 := by
  unfold tailWord_1951439
  simp only [CollatzResearch.WordTrace]
  refine ⟨71174827577277257092593371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47449885051518171395062247 71174827577277257092593371)
  ·
    refine ⟨106762241365915885638890057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71174827577277257092593371 106762241365915885638890057)
    ·
      refine ⟨80071681024436914229167543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106762241365915885638890057 80071681024436914229167543)
      ·
        refine ⟨120107521536655371343751315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80071681024436914229167543 120107521536655371343751315)
        ·
          refine ⟨180161282304983057015626973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120107521536655371343751315 180161282304983057015626973)
          ·
            refine ⟨67560480864368646380860115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180161282304983057015626973 67560480864368646380860115)
            ·
              refine ⟨101340721296552969571290173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67560480864368646380860115 101340721296552969571290173)
              ·
                refine ⟨38002770486207363589233815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101340721296552969571290173 38002770486207363589233815)
                ·
                  refine ⟨57004155729311045383850723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38002770486207363589233815 57004155729311045383850723)
                  ·
                    refine ⟨85506233593966568075776085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57004155729311045383850723 85506233593966568075776085)
                    ·
                      refine ⟨1002026174929295719638001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 85506233593966568075776085 1002026174929295719638001)
                      ·
                        rfl

theorem cell23_1951439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_1951439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951439 prefixEnd_1951439 := by exact prefixLift 1951439
  have htrace : WordTrace (prefixWord ++ tailWord_1951439) baseStart_1951439 baseEnd_1951439 := by
    simpa [prefixWord, tailWord_1951439, baseEnd_1951439] using wordTrace_append hprefix tailTrace_1951439
  have hstable : (prefixWord ++ tailWord_1951439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951439).length < 2 ^ (prefixWord ++ tailWord_1951439).sum := by decide
  have hdescent : baseEnd_1951439 < baseStart_1951439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951496 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 3, 6]
def baseStart_1951496 : Nat := 118140960795 + 1951496 * 2 ^ 59
def prefixEnd_1951496 : Nat := 4983230072969 + 3 ^ 40 * 1951496 * 2
def baseEnd_1951496 : Nat := 334018481108867332208413

theorem tailTrace_1951496 : CollatzResearch.WordTrace tailWord_1951496 prefixEnd_1951496 334018481108867332208413 := by
  unfold tailWord_1951496
  simp only [CollatzResearch.WordTrace]
  refine ⟨35588453269035377913709171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47451271025380503884945561 35588453269035377913709171)
  ·
    refine ⟨53382679903553066870563757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35588453269035377913709171 53382679903553066870563757)
    ·
      refine ⟨20018504963832400076461409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53382679903553066870563757 20018504963832400076461409)
      ·
        refine ⟨15013878722874300057346057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20018504963832400076461409 15013878722874300057346057)
        ·
          refine ⟨11260409042155725043009543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15013878722874300057346057 11260409042155725043009543)
          ·
            refine ⟨16890613563233587564514315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11260409042155725043009543 16890613563233587564514315)
            ·
              refine ⟨25335920344850381346771473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16890613563233587564514315 25335920344850381346771473)
              ·
                refine ⟨19001940258637786010078605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25335920344850381346771473 19001940258637786010078605)
                ·
                  refine ⟨7125727596989169753779477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19001940258637786010078605 7125727596989169753779477)
                  ·
                    refine ⟨334018481108867332208413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7125727596989169753779477 334018481108867332208413)
                    ·
                      rfl

theorem cell23_1951496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_1951496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951496 prefixEnd_1951496 := by exact prefixLift 1951496
  have htrace : WordTrace (prefixWord ++ tailWord_1951496) baseStart_1951496 baseEnd_1951496 := by
    simpa [prefixWord, tailWord_1951496, baseEnd_1951496] using wordTrace_append hprefix tailTrace_1951496
  have hstable : (prefixWord ++ tailWord_1951496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951496).length < 2 ^ (prefixWord ++ tailWord_1951496).sum := by decide
  have hdescent : baseEnd_1951496 < baseStart_1951496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951523 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 3]
def baseStart_1951523 : Nat := 118140960795 + 1951523 * 2 ^ 59
def prefixEnd_1951523 : Nat := 4983230072969 + 3 ^ 40 * 1951523 * 2
def baseEnd_1951523 : Nat := 1002069307304273390987615

theorem tailTrace_1951523 : CollatzResearch.WordTrace tailWord_1951523 prefixEnd_1951523 1002069307304273390987615 := by
  unfold tailWord_1951523
  simp only [CollatzResearch.WordTrace]
  refine ⟨71177891308972939438651223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47451927539315292959100815 71177891308972939438651223)
  ·
    refine ⟨106766836963459409157976835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71177891308972939438651223 106766836963459409157976835)
    ·
      refine ⟨160150255445189113736965253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106766836963459409157976835 160150255445189113736965253)
      ·
        refine ⟨30028172895972958825680985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160150255445189113736965253 30028172895972958825680985)
        ·
          refine ⟨22521129671979719119260739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30028172895972958825680985 22521129671979719119260739)
          ·
            refine ⟨33781694507969578678891109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22521129671979719119260739 33781694507969578678891109)
            ·
              refine ⟨6334067720244296002292083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33781694507969578678891109 6334067720244296002292083)
              ·
                refine ⟨9501101580366444003438125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6334067720244296002292083 9501101580366444003438125)
                ·
                  refine ⟨3562913092637416501289297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9501101580366444003438125 3562913092637416501289297)
                  ·
                    refine ⟨2672184819478062375966973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3562913092637416501289297 2672184819478062375966973)
                    ·
                      refine ⟨1002069307304273390987615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2672184819478062375966973 1002069307304273390987615)
                      ·
                        rfl

theorem cell23_1951523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_1951523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951523 prefixEnd_1951523 := by exact prefixLift 1951523
  have htrace : WordTrace (prefixWord ++ tailWord_1951523) baseStart_1951523 baseEnd_1951523 := by
    simpa [prefixWord, tailWord_1951523, baseEnd_1951523] using wordTrace_append hprefix tailTrace_1951523
  have hstable : (prefixWord ++ tailWord_1951523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951523).length < 2 ^ (prefixWord ++ tailWord_1951523).sum := by decide
  have hdescent : baseEnd_1951523 < baseStart_1951523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951534 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_1951534 : Nat := 118140960795 + 1951534 * 2 ^ 59
def prefixEnd_1951534 : Nat := 4983230072969 + 3 ^ 40 * 1951534 * 2
def baseEnd_1951534 : Nat := 334024985197157615983355

theorem tailTrace_1951534 : CollatzResearch.WordTrace tailWord_1951534 prefixEnd_1951534 334024985197157615983355 := by
  unfold tailWord_1951534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8897286563991636039662707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47452195007955392211534437 8897286563991636039662707)
  ·
    refine ⟨13345929845987454059494061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8897286563991636039662707 13345929845987454059494061)
    ·
      refine ⟨5004723692245295272310273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13345929845987454059494061 5004723692245295272310273)
      ·
        refine ⟨3753542769183971454232705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5004723692245295272310273 3753542769183971454232705)
        ·
          refine ⟨2815157076887978590674529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3753542769183971454232705 2815157076887978590674529)
          ·
            refine ⟨2111367807665983943005897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2815157076887978590674529 2111367807665983943005897)
            ·
              refine ⟨1583525855749487957254423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2111367807665983943005897 1583525855749487957254423)
              ·
                refine ⟨2375288783624231935881635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583525855749487957254423 2375288783624231935881635)
                ·
                  refine ⟨3562933175436347903822453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375288783624231935881635 3562933175436347903822453)
                  ·
                    refine ⟨334024985197157615983355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3562933175436347903822453 334024985197157615983355)
                    ·
                      rfl

theorem cell23_1951534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_1951534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951534 prefixEnd_1951534 := by exact prefixLift 1951534
  have htrace : WordTrace (prefixWord ++ tailWord_1951534) baseStart_1951534 baseEnd_1951534 := by
    simpa [prefixWord, tailWord_1951534, baseEnd_1951534] using wordTrace_append hprefix tailTrace_1951534
  have hstable : (prefixWord ++ tailWord_1951534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951534).length < 2 ^ (prefixWord ++ tailWord_1951534).sum := by decide
  have hdescent : baseEnd_1951534 < baseStart_1951534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951537 : List Nat := [1, 2, 2, 3, 2, 4, 2, 1, 1, 1, 4]
def baseStart_1951537 : Nat := 118140960795 + 1951537 * 2 ^ 59
def prefixEnd_1951537 : Nat := 4983230072969 + 3 ^ 40 * 1951537 * 2
def baseEnd_1951537 : Nat := 1002076496033436336212551

theorem tailTrace_1951537 : CollatzResearch.WordTrace tailWord_1951537 prefixEnd_1951537 1002076496033436336212551 := by
  unfold tailWord_1951537
  simp only [CollatzResearch.WordTrace]
  refine ⟨71178401930922219829660865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47452267953948146553107243 71178401930922219829660865)
  ·
    refine ⟨53383801448191664872245649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71178401930922219829660865 53383801448191664872245649)
    ·
      refine ⟨40037851086143748654184237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53383801448191664872245649 40037851086143748654184237)
      ·
        refine ⟨15014194157303905745319089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40037851086143748654184237 15014194157303905745319089)
        ·
          refine ⟨11260645617977929308989317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15014194157303905745319089 11260645617977929308989317)
          ·
            refine ⟨2111371053370861745435497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11260645617977929308989317 2111371053370861745435497)
            ·
              refine ⟨1583528290028146309076623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2111371053370861745435497 1583528290028146309076623)
              ·
                refine ⟨2375292435042219463614935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583528290028146309076623 2375292435042219463614935)
                ·
                  refine ⟨3562938652563329195422403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375292435042219463614935 3562938652563329195422403)
                  ·
                    refine ⟨5344407978844993793133605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3562938652563329195422403 5344407978844993793133605)
                    ·
                      refine ⟨1002076496033436336212551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5344407978844993793133605 1002076496033436336212551)
                      ·
                        rfl

theorem cell23_1951537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_1951537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951537 prefixEnd_1951537 := by exact prefixLift 1951537
  have htrace : WordTrace (prefixWord ++ tailWord_1951537) baseStart_1951537 baseEnd_1951537 := by
    simpa [prefixWord, tailWord_1951537, baseEnd_1951537] using wordTrace_append hprefix tailTrace_1951537
  have hstable : (prefixWord ++ tailWord_1951537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951537).length < 2 ^ (prefixWord ++ tailWord_1951537).sum := by decide
  have hdescent : baseEnd_1951537 < baseStart_1951537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951570 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_1951570 : Nat := 118140960795 + 1951570 * 2 ^ 59
def prefixEnd_1951570 : Nat := 4983230072969 + 3 ^ 40 * 1951570 * 2
def baseEnd_1951570 : Nat := 1002093440895034707099899

theorem tailTrace_1951570 : CollatzResearch.WordTrace tailWord_1951570 prefixEnd_1951570 1002093440895034707099899 := by
  unfold tailWord_1951570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17794901384950666616403041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47453070359868444310408109 17794901384950666616403041)
  ·
    refine ⟨13346176038712999962302281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17794901384950666616403041 13346176038712999962302281)
    ·
      refine ⟨10009632029034749971726711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13346176038712999962302281 10009632029034749971726711)
      ·
        refine ⟨15014448043552124957590067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10009632029034749971726711 15014448043552124957590067)
        ·
          refine ⟨22521672065328187436385101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15014448043552124957590067 22521672065328187436385101)
          ·
            refine ⟨8445627024498070288644413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22521672065328187436385101 8445627024498070288644413)
            ·
              refine ⟨3167110134186776358241655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8445627024498070288644413 3167110134186776358241655)
              ·
                refine ⟨4750665201280164537362483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167110134186776358241655 4750665201280164537362483)
                ·
                  refine ⟨7125997801920246806043725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4750665201280164537362483 7125997801920246806043725)
                  ·
                    refine ⟨2672249175720092552266397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7125997801920246806043725 2672249175720092552266397)
                    ·
                      refine ⟨1002093440895034707099899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2672249175720092552266397 1002093440895034707099899)
                      ·
                        rfl

theorem cell23_1951570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_1951570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951570 prefixEnd_1951570 := by exact prefixLift 1951570
  have htrace : WordTrace (prefixWord ++ tailWord_1951570) baseStart_1951570 baseEnd_1951570 := by
    simpa [prefixWord, tailWord_1951570, baseEnd_1951570] using wordTrace_append hprefix tailTrace_1951570
  have hstable : (prefixWord ++ tailWord_1951570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951570).length < 2 ^ (prefixWord ++ tailWord_1951570).sum := by decide
  have hdescent : baseEnd_1951570 < baseStart_1951570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951588 : List Nat := [2, 3, 1, 1, 6, 1, 1, 3, 1, 2, 2]
def baseStart_1951588 : Nat := 118140960795 + 1951588 * 2 ^ 59
def prefixEnd_1951588 : Nat := 4983230072969 + 3 ^ 40 * 1951588 * 2
def baseEnd_1951588 : Nat := 1002102683546815636674817

theorem tailTrace_1951588 : CollatzResearch.WordTrace tailWord_1951588 prefixEnd_1951588 1002102683546815636674817 := by
  unfold tailWord_1951588
  simp only [CollatzResearch.WordTrace]
  refine ⟨35590131026868727769883709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47453508035824970359844945 35590131026868727769883709)
  ·
    refine ⟨13346299135075772913706391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35590131026868727769883709 13346299135075772913706391)
    ·
      refine ⟨20019448702613659370559587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13346299135075772913706391 20019448702613659370559587)
      ·
        refine ⟨30029173053920489055839381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20019448702613659370559587 30029173053920489055839381)
        ·
          refine ⟨1407617486902522924492471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30029173053920489055839381 1407617486902522924492471)
          ·
            refine ⟨2111426230353784386738707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1407617486902522924492471 2111426230353784386738707)
            ·
              refine ⟨3167139345530676580108061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2111426230353784386738707 3167139345530676580108061)
              ·
                refine ⟨1187677254574003717540523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3167139345530676580108061 1187677254574003717540523)
                ·
                  refine ⟨1781515881861005576310785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187677254574003717540523 1781515881861005576310785)
                  ·
                    refine ⟨1336136911395754182233089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1781515881861005576310785 1336136911395754182233089)
                    ·
                      refine ⟨1002102683546815636674817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336136911395754182233089 1002102683546815636674817)
                      ·
                        rfl

theorem cell23_1951588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_1951588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951588 prefixEnd_1951588 := by exact prefixLift 1951588
  have htrace : WordTrace (prefixWord ++ tailWord_1951588) baseStart_1951588 baseEnd_1951588 := by
    simpa [prefixWord, tailWord_1951588, baseEnd_1951588] using wordTrace_append hprefix tailTrace_1951588
  have hstable : (prefixWord ++ tailWord_1951588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951588).length < 2 ^ (prefixWord ++ tailWord_1951588).sum := by decide
  have hdescent : baseEnd_1951588 < baseStart_1951588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951597 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_1951597 : Nat := 118140960795 + 1951597 * 2 ^ 59
def prefixEnd_1951597 : Nat := 4983230072969 + 3 ^ 40 * 1951597 * 2
def baseEnd_1951597 : Nat := 1002107304872706101462275

theorem tailTrace_1951597 : CollatzResearch.WordTrace tailWord_1951597 prefixEnd_1951597 1002107304872706101462275 := by
  unfold tailWord_1951597
  simp only [CollatzResearch.WordTrace]
  refine ⟨71180590310704850076845045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47453726873803233384563363 71180590310704850076845045)
  ·
    refine ⟨6673180341628579694704223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71180590310704850076845045 6673180341628579694704223)
    ·
      refine ⟨10009770512442869542056335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6673180341628579694704223 10009770512442869542056335)
      ·
        refine ⟨15014655768664304313084503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10009770512442869542056335 15014655768664304313084503)
        ·
          refine ⟨22521983652996456469626755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15014655768664304313084503 22521983652996456469626755)
          ·
            refine ⟨33782975479494684704440133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22521983652996456469626755 33782975479494684704440133)
            ·
              refine ⟨6334307902405253382082525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33782975479494684704440133 6334307902405253382082525)
              ·
                refine ⟨2375365463401970018280947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6334307902405253382082525 2375365463401970018280947)
                ·
                  refine ⟨3563048195102955027421421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375365463401970018280947 3563048195102955027421421)
                  ·
                    refine ⟨1336143073163608135283033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3563048195102955027421421 1336143073163608135283033)
                    ·
                      refine ⟨1002107304872706101462275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336143073163608135283033 1002107304872706101462275)
                      ·
                        rfl

theorem cell23_1951597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_1951597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951597 prefixEnd_1951597 := by exact prefixLift 1951597
  have htrace : WordTrace (prefixWord ++ tailWord_1951597) baseStart_1951597 baseEnd_1951597 := by
    simpa [prefixWord, tailWord_1951597, baseEnd_1951597] using wordTrace_append hprefix tailTrace_1951597
  have hstable : (prefixWord ++ tailWord_1951597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951597).length < 2 ^ (prefixWord ++ tailWord_1951597).sum := by decide
  have hdescent : baseEnd_1951597 < baseStart_1951597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951613 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_1951613 : Nat := 118140960795 + 1951613 * 2 ^ 59
def prefixEnd_1951613 : Nat := 4983230072969 + 3 ^ 40 * 1951613 * 2
def baseEnd_1951613 : Nat := 1002115520563178038862201

theorem tailTrace_1951613 : CollatzResearch.WordTrace tailWord_1951613 prefixEnd_1951613 1002115520563178038862201 := by
  unfold tailWord_1951613
  simp only [CollatzResearch.WordTrace]
  refine ⟨71181173878646884809427493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47454115919097923206284995 71181173878646884809427493)
  ·
    refine ⟨13346470102246290901767655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71181173878646884809427493 13346470102246290901767655)
    ·
      refine ⟨20019705153369436352651483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13346470102246290901767655 20019705153369436352651483)
      ·
        refine ⟨30029557730054154528977225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20019705153369436352651483 30029557730054154528977225)
        ·
          refine ⟨22522168297540615896732919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30029557730054154528977225 22522168297540615896732919)
          ·
            refine ⟨33783252446310923845099379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22522168297540615896732919 33783252446310923845099379)
            ·
              refine ⟨50674878669466385767649069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33783252446310923845099379 50674878669466385767649069)
              ·
                refine ⟨19003079501049894662868401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50674878669466385767649069 19003079501049894662868401)
                ·
                  refine ⟨14252309625787420997151301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19003079501049894662868401 14252309625787420997151301)
                  ·
                    refine ⟨2672308054835141436965869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14252309625787420997151301 2672308054835141436965869)
                    ·
                      refine ⟨1002115520563178038862201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2672308054835141436965869 1002115520563178038862201)
                      ·
                        rfl

theorem cell23_1951613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_1951613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951613 prefixEnd_1951613 := by exact prefixLift 1951613
  have htrace : WordTrace (prefixWord ++ tailWord_1951613) baseStart_1951613 baseEnd_1951613 := by
    simpa [prefixWord, tailWord_1951613, baseEnd_1951613] using wordTrace_append hprefix tailTrace_1951613
  have hstable : (prefixWord ++ tailWord_1951613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951613).length < 2 ^ (prefixWord ++ tailWord_1951613).sum := by decide
  have hdescent : baseEnd_1951613 < baseStart_1951613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951663 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 2, 5]
def baseStart_1951663 : Nat := 118140960795 + 1951663 * 2 ^ 59
def prefixEnd_1951663 : Nat := 4983230072969 + 3 ^ 40 * 1951663 * 2
def baseEnd_1951663 : Nat := 334047064865300947745657

theorem tailTrace_1951663 : CollatzResearch.WordTrace tailWord_1951663 prefixEnd_1951663 334047064865300947745657 := by
  unfold tailWord_1951663
  simp only [CollatzResearch.WordTrace]
  refine ⟨71182997528465743348747643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47455331685643828899165095 71182997528465743348747643)
  ·
    refine ⟨106774496292698615023121465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71182997528465743348747643 106774496292698615023121465)
    ·
      refine ⟨80080872219523961267341099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106774496292698615023121465 80080872219523961267341099)
      ·
        refine ⟨120121308329285941901011649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80080872219523961267341099 120121308329285941901011649)
        ·
          refine ⟨90090981246964456425758737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120121308329285941901011649 90090981246964456425758737)
          ·
            refine ⟨67568235935223342319319053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90090981246964456425758737 67568235935223342319319053)
            ·
              refine ⟨25338088475708753369744645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67568235935223342319319053 25338088475708753369744645)
              ·
                refine ⟨4750891589195391256827121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25338088475708753369744645 4750891589195391256827121)
                ·
                  refine ⟨3563168691896543442620341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4750891589195391256827121 3563168691896543442620341)
                  ·
                    refine ⟨334047064865300947745657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3563168691896543442620341 334047064865300947745657)
                    ·
                      rfl

theorem cell23_1951663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_1951663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951663 prefixEnd_1951663 := by exact prefixLift 1951663
  have htrace : WordTrace (prefixWord ++ tailWord_1951663) baseStart_1951663 baseEnd_1951663 := by
    simpa [prefixWord, tailWord_1951663, baseEnd_1951663] using wordTrace_append hprefix tailTrace_1951663
  have hstable : (prefixWord ++ tailWord_1951663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951663).length < 2 ^ (prefixWord ++ tailWord_1951663).sum := by decide
  have hdescent : baseEnd_1951663 < baseStart_1951663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951673 : List Nat := [1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1951673 : Nat := 118140960795 + 1951673 * 2 ^ 59
def prefixEnd_1951673 : Nat := 4983230072969 + 3 ^ 40 * 1951673 * 2
def baseEnd_1951673 : Nat := 1002146329402447804111925

theorem tailTrace_1951673 : CollatzResearch.WordTrace tailWord_1951673 prefixEnd_1951673 1002146329402447804111925 := by
  unfold tailWord_1951673
  simp only [CollatzResearch.WordTrace]
  refine ⟨71183362258429515056611673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47455574838953010037741115 71183362258429515056611673)
  ·
    refine ⟨53387521693822136292458755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71183362258429515056611673 53387521693822136292458755)
    ·
      refine ⟨80081282540733204438688133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53387521693822136292458755 80081282540733204438688133)
      ·
        refine ⟨15015240476387475832254025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80081282540733204438688133 15015240476387475832254025)
        ·
          refine ⟨11261430357290606874190519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15015240476387475832254025 11261430357290606874190519)
          ·
            refine ⟨16892145535935910311285779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11261430357290606874190519 16892145535935910311285779)
            ·
              refine ⟨25338218303903865466928669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16892145535935910311285779 25338218303903865466928669)
              ·
                refine ⟨9501831863963949550098251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25338218303903865466928669 9501831863963949550098251)
                ·
                  refine ⟨14252747795945924325147377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9501831863963949550098251 14252747795945924325147377)
                  ·
                    refine ⟨10689560846959443243860533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14252747795945924325147377 10689560846959443243860533)
                    ·
                      refine ⟨1002146329402447804111925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10689560846959443243860533 1002146329402447804111925)
                      ·
                        rfl

theorem cell23_1951673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1951673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951673 prefixEnd_1951673 := by exact prefixLift 1951673
  have htrace : WordTrace (prefixWord ++ tailWord_1951673) baseStart_1951673 baseEnd_1951673 := by
    simpa [prefixWord, tailWord_1951673, baseEnd_1951673] using wordTrace_append hprefix tailTrace_1951673
  have hstable : (prefixWord ++ tailWord_1951673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951673).length < 2 ^ (prefixWord ++ tailWord_1951673).sum := by decide
  have hdescent : baseEnd_1951673 < baseStart_1951673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951700 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1951700 : Nat := 118140960795 + 1951700 * 2 ^ 59
def prefixEnd_1951700 : Nat := 4983230072969 + 3 ^ 40 * 1951700 * 2
def baseEnd_1951700 : Nat := 1002160193380119198474301

theorem tailTrace_1951700 : CollatzResearch.WordTrace tailWord_1951700 prefixEnd_1951700 1002160193380119198474301 := by
  unfold tailWord_1951700
  simp only [CollatzResearch.WordTrace]
  refine ⟨35592173514665849333922277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47456231352887799111896369 35592173514665849333922277)
  ·
    refine ⟨6673532533999846750110427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35592173514665849333922277 6673532533999846750110427)
    ·
      refine ⟨10010298800999770125165641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6673532533999846750110427 10010298800999770125165641)
      ·
        refine ⟨7507724100749827593874231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10010298800999770125165641 7507724100749827593874231)
        ·
          refine ⟨11261586151124741390811347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7507724100749827593874231 11261586151124741390811347)
          ·
            refine ⟨16892379226687112086217021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11261586151124741390811347 16892379226687112086217021)
            ·
              refine ⟨6334642210007667032331383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16892379226687112086217021 6334642210007667032331383)
              ·
                refine ⟨9501963315011500548497075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6334642210007667032331383 9501963315011500548497075)
                ·
                  refine ⟨14252944972517250822745613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9501963315011500548497075 14252944972517250822745613)
                  ·
                    refine ⟨5344854364693969058529605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14252944972517250822745613 5344854364693969058529605)
                    ·
                      refine ⟨1002160193380119198474301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5344854364693969058529605 1002160193380119198474301)
                      ·
                        rfl

theorem cell23_1951700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1951700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951700 prefixEnd_1951700 := by exact prefixLift 1951700
  have htrace : WordTrace (prefixWord ++ tailWord_1951700) baseStart_1951700 baseEnd_1951700 := by
    simpa [prefixWord, tailWord_1951700, baseEnd_1951700] using wordTrace_append hprefix tailTrace_1951700
  have hstable : (prefixWord ++ tailWord_1951700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951700).length < 2 ^ (prefixWord ++ tailWord_1951700).sum := by decide
  have hdescent : baseEnd_1951700 < baseStart_1951700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951713 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_1951713 : Nat := 118140960795 + 1951713 * 2 ^ 59
def prefixEnd_1951713 : Nat := 4983230072969 + 3 ^ 40 * 1951713 * 2
def baseEnd_1951713 : Nat := 1002166868628627647611741

theorem tailTrace_1951713 : CollatzResearch.WordTrace tailWord_1951713 prefixEnd_1951713 1002166868628627647611741 := by
  unfold tailWord_1951713
  simp only [CollatzResearch.WordTrace]
  refine ⟨71184821178284601888067793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47456547452189734592045195 71184821178284601888067793)
  ·
    refine ⟨53388615883713451416050845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71184821178284601888067793 53388615883713451416050845)
    ·
      refine ⟨20020730956392544281019067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53388615883713451416050845 20020730956392544281019067)
      ·
        refine ⟨30031096434588816421528601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20020730956392544281019067 30031096434588816421528601)
        ·
          refine ⟨22523322325941612316146451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30031096434588816421528601 22523322325941612316146451)
          ·
            refine ⟨33784983488912418474219677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22523322325941612316146451 33784983488912418474219677)
            ·
              refine ⟨12669368808342156927832379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33784983488912418474219677 12669368808342156927832379)
              ·
                refine ⟨19004053212513235391748569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12669368808342156927832379 19004053212513235391748569)
                ·
                  refine ⟨14253039909384926543811427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19004053212513235391748569 14253039909384926543811427)
                  ·
                    refine ⟨21379559864077389815717141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14253039909384926543811427 21379559864077389815717141)
                    ·
                      refine ⟨1002166868628627647611741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21379559864077389815717141 1002166868628627647611741)
                      ·
                        rfl

theorem cell23_1951713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_1951713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951713 prefixEnd_1951713 := by exact prefixLift 1951713
  have htrace : WordTrace (prefixWord ++ tailWord_1951713) baseStart_1951713 baseEnd_1951713 := by
    simpa [prefixWord, tailWord_1951713, baseEnd_1951713] using wordTrace_append hprefix tailTrace_1951713
  have hstable : (prefixWord ++ tailWord_1951713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951713).length < 2 ^ (prefixWord ++ tailWord_1951713).sum := by decide
  have hdescent : baseEnd_1951713 < baseStart_1951713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951720 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1951720 : Nat := 118140960795 + 1951720 * 2 ^ 59
def prefixEnd_1951720 : Nat := 4983230072969 + 3 ^ 40 * 1951720 * 2
def baseEnd_1951720 : Nat := 1002170462993209120224209

theorem tailTrace_1951720 : CollatzResearch.WordTrace tailWord_1951720 prefixEnd_1951720 1002170462993209120224209 := by
  unfold tailWord_1951720
  simp only [CollatzResearch.WordTrace]
  refine ⟨35592538244629621041786307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47456717659506161389048409 35592538244629621041786307)
  ·
    refine ⟨53388807366944431562679461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35592538244629621041786307 53388807366944431562679461)
    ·
      refine ⟨10010401381302080918002399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53388807366944431562679461 10010401381302080918002399)
      ·
        refine ⟨15015602071953121377003599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10010401381302080918002399 15015602071953121377003599)
        ·
          refine ⟨22523403107929682065505399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15015602071953121377003599 22523403107929682065505399)
          ·
            refine ⟨33785104661894523098258099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22523403107929682065505399 33785104661894523098258099)
            ·
              refine ⟨50677656992841784647387149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33785104661894523098258099 50677656992841784647387149)
              ·
                refine ⟨19004121372315669242770181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50677656992841784647387149 19004121372315669242770181)
                ·
                  refine ⟨3563272757309187983019409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19004121372315669242770181 3563272757309187983019409)
                  ·
                    refine ⟨2672454567981890987264557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3563272757309187983019409 2672454567981890987264557)
                    ·
                      refine ⟨1002170462993209120224209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2672454567981890987264557 1002170462993209120224209)
                      ·
                        rfl

theorem cell23_1951720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1951720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951720 prefixEnd_1951720 := by exact prefixLift 1951720
  have htrace : WordTrace (prefixWord ++ tailWord_1951720) baseStart_1951720 baseEnd_1951720 := by
    simpa [prefixWord, tailWord_1951720, baseEnd_1951720] using wordTrace_append hprefix tailTrace_1951720
  have hstable : (prefixWord ++ tailWord_1951720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951720).length < 2 ^ (prefixWord ++ tailWord_1951720).sum := by decide
  have hdescent : baseEnd_1951720 < baseStart_1951720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951727 : List Nat := [1, 1, 2, 1, 4, 2, 1, 6, 1, 4]
def baseStart_1951727 : Nat := 118140960795 + 1951727 * 2 ^ 59
def prefixEnd_1951727 : Nat := 4983230072969 + 3 ^ 40 * 1951727 * 2
def baseEnd_1951727 : Nat := 334058019119263530945559

theorem tailTrace_1951727 : CollatzResearch.WordTrace tailWord_1951727 prefixEnd_1951727 334058019119263530945559 := by
  unfold tailWord_1951727
  simp only [CollatzResearch.WordTrace]
  refine ⟨71185331800233882279077435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47456887866822588186051623 71185331800233882279077435)
  ·
    refine ⟨106777997700350823418616153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71185331800233882279077435 106777997700350823418616153)
    ·
      refine ⟨80083498275263117563962115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106777997700350823418616153 80083498275263117563962115)
      ·
        refine ⟨120125247412894676345943173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80083498275263117563962115 120125247412894676345943173)
        ·
          refine ⟨22523483889917751814864345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120125247412894676345943173 22523483889917751814864345)
          ·
            refine ⟨16892612917438313861148259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22523483889917751814864345 16892612917438313861148259)
            ·
              refine ⟨25338919376157470791722389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16892612917438313861148259 25338919376157470791722389)
              ·
                refine ⟨1187761845757381443361987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25338919376157470791722389 1187761845757381443361987)
                ·
                  refine ⟨1781642768636072165042981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1187761845757381443361987 1781642768636072165042981)
                  ·
                    refine ⟨334058019119263530945559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1781642768636072165042981 334058019119263530945559)
                    ·
                      rfl

theorem cell23_1951727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 1, 4].length) (baseStart_1951727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951727 prefixEnd_1951727 := by exact prefixLift 1951727
  have htrace : WordTrace (prefixWord ++ tailWord_1951727) baseStart_1951727 baseEnd_1951727 := by
    simpa [prefixWord, tailWord_1951727, baseEnd_1951727] using wordTrace_append hprefix tailTrace_1951727
  have hstable : (prefixWord ++ tailWord_1951727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951727).length < 2 ^ (prefixWord ++ tailWord_1951727).sum := by decide
  have hdescent : baseEnd_1951727 < baseStart_1951727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951807 : List Nat := [1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 4]
def baseStart_1951807 : Nat := 118140960795 + 1951807 * 2 ^ 59
def prefixEnd_1951807 : Nat := 4983230072969 + 3 ^ 40 * 1951807 * 2
def baseEnd_1951807 : Nat := 1002215135810150279836309

theorem tailTrace_1951807 : CollatzResearch.WordTrace tailWord_1951807 prefixEnd_1951807 1002215135810150279836309 := by
  unfold tailWord_1951807
  simp only [CollatzResearch.WordTrace]
  refine ⟨71188249639944055941989675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47458833093296037294659783 71188249639944055941989675)
  ·
    refine ⟨106782374459916083912984513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71188249639944055941989675 106782374459916083912984513)
    ·
      refine ⟨80086780844937062934738385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106782374459916083912984513 80086780844937062934738385)
      ·
        refine ⟨60065085633702797201053789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80086780844937062934738385 60065085633702797201053789)
        ·
          refine ⟨22524407112638548950395171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60065085633702797201053789 22524407112638548950395171)
          ·
            refine ⟨33786610668957823425592757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22524407112638548950395171 33786610668957823425592757)
            ·
              refine ⟨3167494750214795946149321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33786610668957823425592757 3167494750214795946149321)
              ·
                refine ⟨2375621062661096959611991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3167494750214795946149321 2375621062661096959611991)
                ·
                  refine ⟨3563431593991645439417987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2375621062661096959611991 3563431593991645439417987)
                  ·
                    refine ⟨5345147390987468159126981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3563431593991645439417987 5345147390987468159126981)
                    ·
                      refine ⟨1002215135810150279836309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5345147390987468159126981 1002215135810150279836309)
                      ·
                        rfl

theorem cell23_1951807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_1951807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951807 prefixEnd_1951807 := by exact prefixLift 1951807
  have htrace : WordTrace (prefixWord ++ tailWord_1951807) baseStart_1951807 baseEnd_1951807 := by
    simpa [prefixWord, tailWord_1951807, baseEnd_1951807] using wordTrace_append hprefix tailTrace_1951807
  have hstable : (prefixWord ++ tailWord_1951807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951807).length < 2 ^ (prefixWord ++ tailWord_1951807).sum := by decide
  have hdescent : baseEnd_1951807 < baseStart_1951807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951820 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1951820 : Nat := 118140960795 + 1951820 * 2 ^ 59
def prefixEnd_1951820 : Nat := 4983230072969 + 3 ^ 40 * 1951820 * 2
def baseEnd_1951820 : Nat := 1002221811058658728973749

theorem tailTrace_1951820 : CollatzResearch.WordTrace tailWord_1951820 prefixEnd_1951820 1002221811058658728973749 := by
  unfold tailWord_1951820
  simp only [CollatzResearch.WordTrace]
  refine ⟨35594361894448479581106457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47459149192597972774808609 35594361894448479581106457)
  ·
    refine ⟨26695771420836359685829843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35594361894448479581106457 26695771420836359685829843)
    ·
      refine ⟨40043657131254539528744765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26695771420836359685829843 40043657131254539528744765)
      ·
        refine ⟨15016371424220452323279287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40043657131254539528744765 15016371424220452323279287)
        ·
          refine ⟨22524557136330678484918931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15016371424220452323279287 22524557136330678484918931)
          ·
            refine ⟨33786835704496017727378397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22524557136330678484918931 33786835704496017727378397)
            ·
              refine ⟨12670063389186006647766899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33786835704496017727378397 12670063389186006647766899)
              ·
                refine ⟨19005095083779009971650349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12670063389186006647766899 19005095083779009971650349)
                ·
                  refine ⟨7126910656417128739368881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19005095083779009971650349 7126910656417128739368881)
                  ·
                    refine ⟨5345182992312846554526661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7126910656417128739368881 5345182992312846554526661)
                    ·
                      refine ⟨1002221811058658728973749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5345182992312846554526661 1002221811058658728973749)
                      ·
                        rfl

theorem cell23_1951820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1951820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951820 prefixEnd_1951820 := by exact prefixLift 1951820
  have htrace : WordTrace (prefixWord ++ tailWord_1951820) baseStart_1951820 baseEnd_1951820 := by
    simpa [prefixWord, tailWord_1951820, baseEnd_1951820] using wordTrace_append hprefix tailTrace_1951820
  have hstable : (prefixWord ++ tailWord_1951820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951820).length < 2 ^ (prefixWord ++ tailWord_1951820).sum := by decide
  have hdescent : baseEnd_1951820 < baseStart_1951820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951857 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 1, 3, 3]
def baseStart_1951857 : Nat := 118140960795 + 1951857 * 2 ^ 59
def prefixEnd_1951857 : Nat := 4983230072969 + 3 ^ 40 * 1951857 * 2
def baseEnd_1951857 : Nat := 1002240809842875084211079

theorem tailTrace_1951857 : CollatzResearch.WordTrace tailWord_1951857 prefixEnd_1951857 1002240809842875084211079 := by
  unfold tailWord_1951857
  simp only [CollatzResearch.WordTrace]
  refine ⟨71190073289762914481309825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47460048859841942987539883 71190073289762914481309825)
  ·
    refine ⟨53392554967322185860982369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71190073289762914481309825 53392554967322185860982369)
    ·
      refine ⟨40044416225491639395736777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53392554967322185860982369 40044416225491639395736777)
      ·
        refine ⟨30033312169118729546802583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40044416225491639395736777 30033312169118729546802583)
        ·
          refine ⟨45049968253678094320203875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30033312169118729546802583 45049968253678094320203875)
          ·
            refine ⟨67574952380517141480305813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45049968253678094320203875 67574952380517141480305813)
            ·
              refine ⟨3167575892836741006889335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67574952380517141480305813 3167575892836741006889335)
              ·
                refine ⟨4751363839255111510334003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167575892836741006889335 4751363839255111510334003)
                ·
                  refine ⟨7127045758882667265501005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4751363839255111510334003 7127045758882667265501005)
                  ·
                    refine ⟨2672642159581000224562877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7127045758882667265501005 2672642159581000224562877)
                    ·
                      refine ⟨1002240809842875084211079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2672642159581000224562877 1002240809842875084211079)
                      ·
                        rfl

theorem cell23_1951857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_1951857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951857 prefixEnd_1951857 := by exact prefixLift 1951857
  have htrace : WordTrace (prefixWord ++ tailWord_1951857) baseStart_1951857 baseEnd_1951857 := by
    simpa [prefixWord, tailWord_1951857, baseEnd_1951857] using wordTrace_append hprefix tailTrace_1951857
  have hstable : (prefixWord ++ tailWord_1951857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951857).length < 2 ^ (prefixWord ++ tailWord_1951857).sum := by decide
  have hdescent : baseEnd_1951857 < baseStart_1951857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951897 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 3, 4, 2]
def baseStart_1951897 : Nat := 118140960795 + 1951897 * 2 ^ 59
def prefixEnd_1951897 : Nat := 4983230072969 + 3 ^ 40 * 1951897 * 2
def baseEnd_1951897 : Nat := 1002261349069054927710895

theorem tailTrace_1951897 : CollatzResearch.WordTrace tailWord_1951897 prefixEnd_1951897 1002261349069054927710895 := by
  unfold tailWord_1951897
  simp only [CollatzResearch.WordTrace]
  refine ⟨71191532209618001312765945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47461021473078667541843963 71191532209618001312765945)
  ·
    refine ⟨53393649157213500984574459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71191532209618001312765945 53393649157213500984574459)
    ·
      refine ⟨80090473735820251476861689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53393649157213500984574459 80090473735820251476861689)
      ·
        refine ⟨60067855301865188607646267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80090473735820251476861689 60067855301865188607646267)
        ·
          refine ⟨90101782952797782911469401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60067855301865188607646267 90101782952797782911469401)
          ·
            refine ⟨67576337214598337183602051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90101782952797782911469401 67576337214598337183602051)
            ·
              refine ⟨101364505821897505775403077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67576337214598337183602051 101364505821897505775403077)
              ·
                refine ⟨19005844841605782332888077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101364505821897505775403077 19005844841605782332888077)
                ·
                  refine ⟨7127191815602168374833029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19005844841605782332888077 7127191815602168374833029)
                  ·
                    refine ⟨1336348465425406570281193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7127191815602168374833029 1336348465425406570281193)
                    ·
                      refine ⟨1002261349069054927710895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336348465425406570281193 1002261349069054927710895)
                      ·
                        rfl

theorem cell23_1951897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_1951897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951897 prefixEnd_1951897 := by exact prefixLift 1951897
  have htrace : WordTrace (prefixWord ++ tailWord_1951897) baseStart_1951897 baseEnd_1951897 := by
    simpa [prefixWord, tailWord_1951897, baseEnd_1951897] using wordTrace_append hprefix tailTrace_1951897
  have hstable : (prefixWord ++ tailWord_1951897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951897).length < 2 ^ (prefixWord ++ tailWord_1951897).sum := by decide
  have hdescent : baseEnd_1951897 < baseStart_1951897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951908 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 2, 1, 3]
def baseStart_1951908 : Nat := 118140960795 + 1951908 * 2 ^ 59
def prefixEnd_1951908 : Nat := 4983230072969 + 3 ^ 40 * 1951908 * 2
def baseEnd_1951908 : Nat := 1002266997356254384673345

theorem tailTrace_1951908 : CollatzResearch.WordTrace tailWord_1951908 prefixEnd_1951908 1002266997356254384673345 := by
  unfold tailWord_1951908
  simp only [CollatzResearch.WordTrace]
  refine ⟨35595966706289075095708189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47461288941718766794277585 35595966706289075095708189)
  ·
    refine ⟨13348487514858403160890571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35595966706289075095708189 13348487514858403160890571)
    ·
      refine ⟨20022731272287604741335857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13348487514858403160890571 20022731272287604741335857)
      ·
        refine ⟨15017048454215703556001893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20022731272287604741335857 15017048454215703556001893)
        ·
          refine ⟨2815696585165444416750355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15017048454215703556001893 2815696585165444416750355)
          ·
            refine ⟨4223544877748166625125533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815696585165444416750355 4223544877748166625125533)
            ·
              refine ⟨1583829329155562484422075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4223544877748166625125533 1583829329155562484422075)
              ·
                refine ⟨2375743993733343726633113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583829329155562484422075 2375743993733343726633113)
                ·
                  refine ⟨1781807995300007794974835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2375743993733343726633113 1781807995300007794974835)
                  ·
                    refine ⟨2672711992950011692462253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1781807995300007794974835 2672711992950011692462253)
                    ·
                      refine ⟨1002266997356254384673345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2672711992950011692462253 1002266997356254384673345)
                      ·
                        rfl

theorem cell23_1951908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_1951908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951908 prefixEnd_1951908 := by exact prefixLift 1951908
  have htrace : WordTrace (prefixWord ++ tailWord_1951908) baseStart_1951908 baseEnd_1951908 := by
    simpa [prefixWord, tailWord_1951908, baseEnd_1951908] using wordTrace_append hprefix tailTrace_1951908
  have hstable : (prefixWord ++ tailWord_1951908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951908).length < 2 ^ (prefixWord ++ tailWord_1951908).sum := by decide
  have hdescent : baseEnd_1951908 < baseStart_1951908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951934 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1951934 : Nat := 118140960795 + 1951934 * 2 ^ 59
def prefixEnd_1951934 : Nat := 4983230072969 + 3 ^ 40 * 1951934 * 2
def baseEnd_1951934 : Nat := 1002280347853271282948225

theorem tailTrace_1951934 : CollatzResearch.WordTrace tailWord_1951934 prefixEnd_1951934 1002280347853271282948225 := by
  unfold tailWord_1951934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899110213810494578982857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47461921140322637754575237 8899110213810494578982857)
  ·
    refine ⟨6674332660357870934237143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8899110213810494578982857 6674332660357870934237143)
    ·
      refine ⟨10011498990536806401355715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6674332660357870934237143 10011498990536806401355715)
      ·
        refine ⟨15017248485805209602033573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10011498990536806401355715 15017248485805209602033573)
        ·
          refine ⟨2815734091088476800381295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15017248485805209602033573 2815734091088476800381295)
          ·
            refine ⟨4223601136632715200571943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2815734091088476800381295 4223601136632715200571943)
            ·
              refine ⟨6335401704949072800857915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4223601136632715200571943 6335401704949072800857915)
              ·
                refine ⟨9503102557423609201286873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6335401704949072800857915 9503102557423609201286873)
                ·
                  refine ⟨7127326918067706900965155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9503102557423609201286873 7127326918067706900965155)
                  ·
                    refine ⟨10690990377101560351447733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7127326918067706900965155 10690990377101560351447733)
                    ·
                      refine ⟨1002280347853271282948225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10690990377101560351447733 1002280347853271282948225)
                      ·
                        rfl

theorem cell23_1951934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1951934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951934 prefixEnd_1951934 := by exact prefixLift 1951934
  have htrace : WordTrace (prefixWord ++ tailWord_1951934) baseStart_1951934 baseEnd_1951934 := by
    simpa [prefixWord, tailWord_1951934, baseEnd_1951934] using wordTrace_append hprefix tailTrace_1951934
  have hstable : (prefixWord ++ tailWord_1951934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951934).length < 2 ^ (prefixWord ++ tailWord_1951934).sum := by decide
  have hdescent : baseEnd_1951934 < baseStart_1951934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951954 : List Nat := [3, 2, 2, 2, 1, 4, 1, 1, 7]
def baseStart_1951954 : Nat := 118140960795 + 1951954 * 2 ^ 59
def prefixEnd_1951954 : Nat := 4983230072969 + 3 ^ 40 * 1951954 * 2
def baseEnd_1951954 : Nat := 111365624162929022744237

theorem tailTrace_1951954 : CollatzResearch.WordTrace tailWord_1951954 prefixEnd_1951954 111365624162929022744237 := by
  unfold tailWord_1951954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17798402792602875011897729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47462407446941000031727277 17798402792602875011897729)
  ·
    refine ⟨13348802094452156258923297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17798402792602875011897729 13348802094452156258923297)
    ·
      refine ⟨10011601570839117194192473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13348802094452156258923297 10011601570839117194192473)
      ·
        refine ⟨7508701178129337895644355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10011601570839117194192473 7508701178129337895644355)
        ·
          refine ⟨11263051767194006843466533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7508701178129337895644355 11263051767194006843466533)
          ·
            refine ⟨2111822206348876283149975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11263051767194006843466533 2111822206348876283149975)
            ·
              refine ⟨3167733309523314424724963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2111822206348876283149975 3167733309523314424724963)
              ·
                refine ⟨4751599964284971637087445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167733309523314424724963 4751599964284971637087445)
                ·
                  refine ⟨111365624162929022744237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4751599964284971637087445 111365624162929022744237)
                  ·
                    rfl

theorem cell23_1951954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_1951954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951954 prefixEnd_1951954 := by exact prefixLift 1951954
  have htrace : WordTrace (prefixWord ++ tailWord_1951954) baseStart_1951954 baseEnd_1951954 := by
    simpa [prefixWord, tailWord_1951954, baseEnd_1951954] using wordTrace_append hprefix tailTrace_1951954
  have hstable : (prefixWord ++ tailWord_1951954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951954).length < 2 ^ (prefixWord ++ tailWord_1951954).sum := by decide
  have hdescent : baseEnd_1951954 < baseStart_1951954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1951965 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_1951965 : Nat := 118140960795 + 1951965 * 2 ^ 59
def prefixEnd_1951965 : Nat := 4983230072969 + 3 ^ 40 * 1951965 * 2
def baseEnd_1951965 : Nat := 1002296265753560661660583

theorem tailTrace_1951965 : CollatzResearch.WordTrace tailWord_1951965 prefixEnd_1951965 1002296265753560661660583 := by
  unfold tailWord_1951965
  simp only [CollatzResearch.WordTrace]
  refine ⟨71194012373371648926241349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47462674915581099284160899 71194012373371648926241349)
  ·
    refine ⟨13348877320007184173670253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71194012373371648926241349 13348877320007184173670253)
    ·
      refine ⟨5005828995002694065126345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13348877320007184173670253 5005828995002694065126345)
      ·
        refine ⟨3754371746252020548844759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5005828995002694065126345 3754371746252020548844759)
        ·
          refine ⟨5631557619378030823267139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754371746252020548844759 5631557619378030823267139)
          ·
            refine ⟨8447336429067046234900709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5631557619378030823267139 8447336429067046234900709)
            ·
              refine ⟨1583875580450071169043883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8447336429067046234900709 1583875580450071169043883)
              ·
                refine ⟨2375813370675106753565825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1583875580450071169043883 2375813370675106753565825)
                ·
                  refine ⟨1781860028006330065174369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2375813370675106753565825 1781860028006330065174369)
                  ·
                    refine ⟨1336395021004747548880777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1781860028006330065174369 1336395021004747548880777)
                    ·
                      refine ⟨1002296265753560661660583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336395021004747548880777 1002296265753560661660583)
                      ·
                        rfl

theorem cell23_1951965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_1951965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1951965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1951965 prefixEnd_1951965 := by exact prefixLift 1951965
  have htrace : WordTrace (prefixWord ++ tailWord_1951965) baseStart_1951965 baseEnd_1951965 := by
    simpa [prefixWord, tailWord_1951965, baseEnd_1951965] using wordTrace_append hprefix tailTrace_1951965
  have hstable : (prefixWord ++ tailWord_1951965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1951965).length < 2 ^ (prefixWord ++ tailWord_1951965).sum := by decide
  have hdescent : baseEnd_1951965 < baseStart_1951965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1951965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952014 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_1952014 : Nat := 118140960795 + 1952014 * 2 ^ 59
def prefixEnd_1952014 : Nat := 4983230072969 + 3 ^ 40 * 1952014 * 2
def baseEnd_1952014 : Nat := 334107142101876989982619

theorem tailTrace_1952014 : CollatzResearch.WordTrace tailWord_1952014 prefixEnd_1952014 334107142101876989982619 := by
  unfold tailWord_1952014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8899474943774266286846887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47463866366796086863183397 8899474943774266286846887)
  ·
    refine ⟨13349212415661399430270331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8899474943774266286846887 13349212415661399430270331)
    ·
      refine ⟨20023818623492099145405497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13349212415661399430270331 20023818623492099145405497)
      ·
        refine ⟨15017863967619074359054123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20023818623492099145405497 15017863967619074359054123)
        ·
          refine ⟨22526795951428611538581185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15017863967619074359054123 22526795951428611538581185)
          ·
            refine ⟨16895096963571458653935889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22526795951428611538581185 16895096963571458653935889)
            ·
              refine ⟨12671322722678593990451917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16895096963571458653935889 12671322722678593990451917)
              ·
                refine ⟨4751746021004472746419469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12671322722678593990451917 4751746021004472746419469)
                ·
                  refine ⟨1781904757876677279907301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4751746021004472746419469 1781904757876677279907301)
                  ·
                    refine ⟨334107142101876989982619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1781904757876677279907301 334107142101876989982619)
                    ·
                      rfl

theorem cell23_1952014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_1952014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952014 prefixEnd_1952014 := by exact prefixLift 1952014
  have htrace : WordTrace (prefixWord ++ tailWord_1952014) baseStart_1952014 baseEnd_1952014 := by
    simpa [prefixWord, tailWord_1952014, baseEnd_1952014] using wordTrace_append hprefix tailTrace_1952014
  have hstable : (prefixWord ++ tailWord_1952014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952014).length < 2 ^ (prefixWord ++ tailWord_1952014).sum := by decide
  have hdescent : baseEnd_1952014 < baseStart_1952014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952027 : List Nat := [1, 1, 1, 1, 1, 1, 8, 3, 6]
def baseStart_1952027 : Nat := 118140960795 + 1952027 * 2 ^ 59
def prefixEnd_1952027 : Nat := 4983230072969 + 3 ^ 40 * 1952027 * 2
def baseEnd_1952027 : Nat := 111369789061571046565033

theorem tailTrace_1952027 : CollatzResearch.WordTrace tailWord_1952027 prefixEnd_1952027 111369789061571046565033 := by
  unfold tailWord_1952027
  simp only [CollatzResearch.WordTrace]
  refine ⟨71196273699147033514998335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47464182466098022343332223 71196273699147033514998335)
  ·
    refine ⟨106794410548720550272497503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71196273699147033514998335 106794410548720550272497503)
    ·
      refine ⟨160191615823080825408746255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106794410548720550272497503 160191615823080825408746255)
      ·
        refine ⟨240287423734621238113119383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160191615823080825408746255 240287423734621238113119383)
        ·
          refine ⟨360431135601931857169679075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240287423734621238113119383 360431135601931857169679075)
          ·
            refine ⟨540646703402897785754518613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360431135601931857169679075 540646703402897785754518613)
            ·
              refine ⟨6335703555502708426810765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 540646703402897785754518613 6335703555502708426810765)
              ·
                refine ⟨2375888833313515660054037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6335703555502708426810765 2375888833313515660054037)
                ·
                  refine ⟨111369789061571046565033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2375888833313515660054037 111369789061571046565033)
                  ·
                    rfl

theorem cell23_1952027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 6].length) (baseStart_1952027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952027 prefixEnd_1952027 := by exact prefixLift 1952027
  have htrace : WordTrace (prefixWord ++ tailWord_1952027) baseStart_1952027 baseEnd_1952027 := by
    simpa [prefixWord, tailWord_1952027, baseEnd_1952027] using wordTrace_append hprefix tailTrace_1952027
  have hstable : (prefixWord ++ tailWord_1952027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952027).length < 2 ^ (prefixWord ++ tailWord_1952027).sum := by decide
  have hdescent : baseEnd_1952027 < baseStart_1952027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952071 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_1952071 : Nat := 118140960795 + 1952071 * 2 ^ 59
def prefixEnd_1952071 : Nat := 4983230072969 + 3 ^ 40 * 1952071 * 2
def baseEnd_1952071 : Nat := 1002350694702937246935095

theorem tailTrace_1952071 : CollatzResearch.WordTrace tailWord_1952071 prefixEnd_1952071 1002350694702937246935095 := by
  unfold tailWord_1952071
  simp only [CollatzResearch.WordTrace]
  refine ⟨71197878510987629029600067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47465252340658419353066711 71197878510987629029600067)
  ·
    refine ⟨106796817766481443544400101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71197878510987629029600067 106796817766481443544400101)
    ·
      refine ⟨20024403331215270664575019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106796817766481443544400101 20024403331215270664575019)
      ·
        refine ⟨30036604996822905996862529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20024403331215270664575019 30036604996822905996862529)
        ·
          refine ⟨22527453747617179497646897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30036604996822905996862529 22527453747617179497646897)
          ·
            refine ⟨16895590310712884623235173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22527453747617179497646897 16895590310712884623235173)
            ·
              refine ⟨3167923183258665866856595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16895590310712884623235173 3167923183258665866856595)
              ·
                refine ⟨4751884774887998800284893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3167923183258665866856595 4751884774887998800284893)
                ·
                  refine ⟨1781956790582999550106835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4751884774887998800284893 1781956790582999550106835)
                  ·
                    refine ⟨2672935185874499325160253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1781956790582999550106835 2672935185874499325160253)
                    ·
                      refine ⟨1002350694702937246935095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2672935185874499325160253 1002350694702937246935095)
                      ·
                        rfl

theorem cell23_1952071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_1952071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952071 prefixEnd_1952071 := by exact prefixLift 1952071
  have htrace : WordTrace (prefixWord ++ tailWord_1952071) baseStart_1952071 baseEnd_1952071 := by
    simpa [prefixWord, tailWord_1952071, baseEnd_1952071] using wordTrace_append hprefix tailTrace_1952071
  have hstable : (prefixWord ++ tailWord_1952071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952071).length < 2 ^ (prefixWord ++ tailWord_1952071).sum := by decide
  have hdescent : baseEnd_1952071 < baseStart_1952071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952114 : List Nat := [3, 2, 1, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1952114 : Nat := 118140960795 + 1952114 * 2 ^ 59
def prefixEnd_1952114 : Nat := 4983230072969 + 3 ^ 40 * 1952114 * 2
def baseEnd_1952114 : Nat := 1002372774371080578697397

theorem tailTrace_1952114 : CollatzResearch.WordTrace tailWord_1952114 prefixEnd_1952114 1002372774371080578697397 := by
  unfold tailWord_1952114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17799861712457961843353849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47466297899887898248943597 17799861712457961843353849)
  ·
    refine ⟨13349896284343471382515387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17799861712457961843353849 13349896284343471382515387)
    ·
      refine ⟨20024844426515207073773081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13349896284343471382515387 20024844426515207073773081)
      ·
        refine ⟨15018633319886405305329811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20024844426515207073773081 15018633319886405305329811)
        ·
          refine ⟨22527949979829607957994717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15018633319886405305329811 22527949979829607957994717)
          ·
            refine ⟨8447981242436102984248019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22527949979829607957994717 8447981242436102984248019)
            ·
              refine ⟨12671971863654154476372029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8447981242436102984248019 12671971863654154476372029)
              ·
                refine ⟨4751989448870307928639511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12671971863654154476372029 4751989448870307928639511)
                ·
                  refine ⟨7127984173305461892959267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4751989448870307928639511 7127984173305461892959267)
                  ·
                    refine ⟨10691976259958192839438901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7127984173305461892959267 10691976259958192839438901)
                    ·
                      refine ⟨1002372774371080578697397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10691976259958192839438901 1002372774371080578697397)
                      ·
                        rfl

theorem cell23_1952114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1952114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952114 prefixEnd_1952114 := by exact prefixLift 1952114
  have htrace : WordTrace (prefixWord ++ tailWord_1952114) baseStart_1952114 baseEnd_1952114 := by
    simpa [prefixWord, tailWord_1952114, baseEnd_1952114] using wordTrace_append hprefix tailTrace_1952114
  have hstable : (prefixWord ++ tailWord_1952114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952114).length < 2 ^ (prefixWord ++ tailWord_1952114).sum := by decide
  have hdescent : baseEnd_1952114 < baseStart_1952114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952148 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1952148 : Nat := 118140960795 + 1952148 * 2 ^ 59
def prefixEnd_1952148 : Nat := 4983230072969 + 3 ^ 40 * 1952148 * 2
def baseEnd_1952148 : Nat := 1002390232713333445672241

theorem tailTrace_1952148 : CollatzResearch.WordTrace tailWord_1952148 prefixEnd_1952148 1002390232713333445672241 := by
  unfold tailWord_1952148
  simp only [CollatzResearch.WordTrace]
  refine ⟨35600343465854335590076549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47467124621139114120102065 35600343465854335590076549)
  ·
    refine ⟨6675064399847687923139353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35600343465854335590076549 6675064399847687923139353)
    ·
      refine ⟨5006298299885765942354515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6675064399847687923139353 5006298299885765942354515)
      ·
        refine ⟨7509447449828648913531773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5006298299885765942354515 7509447449828648913531773)
        ·
          refine ⟨2816042793685743342574415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7509447449828648913531773 2816042793685743342574415)
          ·
            refine ⟨4224064190528615013861623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816042793685743342574415 4224064190528615013861623)
            ·
              refine ⟨6336096285792922520792435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224064190528615013861623 6336096285792922520792435)
              ·
                refine ⟨9504144428689383781188653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6336096285792922520792435 9504144428689383781188653)
                ·
                  refine ⟨3564054160758518917945745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9504144428689383781188653 3564054160758518917945745)
                  ·
                    refine ⟨2673040620568889188459309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3564054160758518917945745 2673040620568889188459309)
                    ·
                      refine ⟨1002390232713333445672241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2673040620568889188459309 1002390232713333445672241)
                      ·
                        rfl

theorem cell23_1952148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1952148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952148 prefixEnd_1952148 := by exact prefixLift 1952148
  have htrace : WordTrace (prefixWord ++ tailWord_1952148) baseStart_1952148 baseEnd_1952148 := by
    simpa [prefixWord, tailWord_1952148, baseEnd_1952148] using wordTrace_append hprefix tailTrace_1952148
  have hstable : (prefixWord ++ tailWord_1952148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952148).length < 2 ^ (prefixWord ++ tailWord_1952148).sum := by decide
  have hdescent : baseEnd_1952148 < baseStart_1952148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952158 : List Nat := [4, 3, 1, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1952158 : Nat := 118140960795 + 1952158 * 2 ^ 59
def prefixEnd_1952158 : Nat := 4983230072969 + 3 ^ 40 * 1952158 * 2
def baseEnd_1952158 : Nat := 1002395367519878406547195

theorem tailTrace_1952158 : CollatzResearch.WordTrace tailWord_1952158 prefixEnd_1952158 1002395367519878406547195 := by
  unfold tailWord_1952158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8900131457709055361002141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47467367774448295258678085 8900131457709055361002141)
  ·
    refine ⟨3337549296640895760375803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8900131457709055361002141 3337549296640895760375803)
    ·
      refine ⟨5006323944961343640563705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3337549296640895760375803 5006323944961343640563705)
      ·
        refine ⟨3754742958721007730422779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5006323944961343640563705 3754742958721007730422779)
        ·
          refine ⟨5632114438081511595634169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754742958721007730422779 5632114438081511595634169)
          ·
            refine ⟨4224085828561133696725627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5632114438081511595634169 4224085828561133696725627)
            ·
              refine ⟨6336128742841700545088441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224085828561133696725627 6336128742841700545088441)
              ·
                refine ⟨4752096557131275408816331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6336128742841700545088441 4752096557131275408816331)
                ·
                  refine ⟨7128144835696913113224497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752096557131275408816331 7128144835696913113224497)
                  ·
                    refine ⟨5346108626772684834918373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7128144835696913113224497 5346108626772684834918373)
                    ·
                      refine ⟨1002395367519878406547195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5346108626772684834918373 1002395367519878406547195)
                      ·
                        rfl

theorem cell23_1952158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1952158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952158 prefixEnd_1952158 := by exact prefixLift 1952158
  have htrace : WordTrace (prefixWord ++ tailWord_1952158) baseStart_1952158 baseEnd_1952158 := by
    simpa [prefixWord, tailWord_1952158, baseEnd_1952158] using wordTrace_append hprefix tailTrace_1952158
  have hstable : (prefixWord ++ tailWord_1952158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952158).length < 2 ^ (prefixWord ++ tailWord_1952158).sum := by decide
  have hdescent : baseEnd_1952158 < baseStart_1952158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952178 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_1952178 : Nat := 118140960795 + 1952178 * 2 ^ 59
def prefixEnd_1952178 : Nat := 4983230072969 + 3 ^ 40 * 1952178 * 2
def baseEnd_1952178 : Nat := 1002405637132968328297103

theorem tailTrace_1952178 : CollatzResearch.WordTrace tailWord_1952178 prefixEnd_1952178 1002405637132968328297103 := by
  unfold tailWord_1952178
  simp only [CollatzResearch.WordTrace]
  refine ⟨17800445280399996575936297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47467854081066657535830125 17800445280399996575936297)
  ·
    refine ⟨13350333960299997431952223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17800445280399996575936297 13350333960299997431952223)
    ·
      refine ⟨20025500940449996147928335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13350333960299997431952223 20025500940449996147928335)
      ·
        refine ⟨30038251410674994221892503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20025500940449996147928335 30038251410674994221892503)
        ·
          refine ⟨45057377116012491332838755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30038251410674994221892503 45057377116012491332838755)
          ·
            refine ⟨67586065674018736999258133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45057377116012491332838755 67586065674018736999258133)
            ·
              refine ⟨3168096828469628296840225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67586065674018736999258133 3168096828469628296840225)
              ·
                refine ⟨2376072621352221222630169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168096828469628296840225 2376072621352221222630169)
                ·
                  refine ⟨1782054466014165916972627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2376072621352221222630169 1782054466014165916972627)
                  ·
                    refine ⟨2673081699021248875458941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1782054466014165916972627 2673081699021248875458941)
                    ·
                      refine ⟨1002405637132968328297103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2673081699021248875458941 1002405637132968328297103)
                      ·
                        rfl

theorem cell23_1952178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_1952178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952178 prefixEnd_1952178 := by exact prefixLift 1952178
  have htrace : WordTrace (prefixWord ++ tailWord_1952178) baseStart_1952178 baseEnd_1952178 := by
    simpa [prefixWord, tailWord_1952178, baseEnd_1952178] using wordTrace_append hprefix tailTrace_1952178
  have hstable : (prefixWord ++ tailWord_1952178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952178).length < 2 ^ (prefixWord ++ tailWord_1952178).sum := by decide
  have hdescent : baseEnd_1952178 < baseStart_1952178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952188 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 3, 3, 2]
def baseStart_1952188 : Nat := 118140960795 + 1952188 * 2 ^ 59
def prefixEnd_1952188 : Nat := 4983230072969 + 3 ^ 40 * 1952188 * 2
def baseEnd_1952188 : Nat := 1002410771939513289172057

theorem tailTrace_1952188 : CollatzResearch.WordTrace tailWord_1952188 prefixEnd_1952188 1002410771939513289172057 := by
  unfold tailWord_1952188
  simp only [CollatzResearch.WordTrace]
  refine ⟨35601072925781879005804609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47468097234375838674406145 35601072925781879005804609)
  ·
    refine ⟨26700804694336409254353457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35601072925781879005804609 26700804694336409254353457)
    ·
      refine ⟨20025603520752306940765093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26700804694336409254353457 20025603520752306940765093)
      ·
        refine ⟨3754800660141057551393455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20025603520752306940765093 3754800660141057551393455)
        ·
          refine ⟨5632200990211586327090183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3754800660141057551393455 5632200990211586327090183)
          ·
            refine ⟨8448301485317379490635275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632200990211586327090183 8448301485317379490635275)
            ·
              refine ⟨12672452227976069235952913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8448301485317379490635275 12672452227976069235952913)
              ·
                refine ⟨9504339170982051926964685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12672452227976069235952913 9504339170982051926964685)
                ·
                  refine ⟨3564127189118269472611757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9504339170982051926964685 3564127189118269472611757)
                  ·
                    refine ⟨1336547695919351052229409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3564127189118269472611757 1336547695919351052229409)
                    ·
                      refine ⟨1002410771939513289172057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336547695919351052229409 1002410771939513289172057)
                      ·
                        rfl

theorem cell23_1952188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_1952188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952188 prefixEnd_1952188 := by exact prefixLift 1952188
  have htrace : WordTrace (prefixWord ++ tailWord_1952188) baseStart_1952188 baseEnd_1952188 := by
    simpa [prefixWord, tailWord_1952188, baseEnd_1952188] using wordTrace_append hprefix tailTrace_1952188
  have hstable : (prefixWord ++ tailWord_1952188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952188).length < 2 ^ (prefixWord ++ tailWord_1952188).sum := by decide
  have hdescent : baseEnd_1952188 < baseStart_1952188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952201 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 1, 4, 2]
def baseStart_1952201 : Nat := 118140960795 + 1952201 * 2 ^ 59
def prefixEnd_1952201 : Nat := 4983230072969 + 3 ^ 40 * 1952201 * 2
def baseEnd_1952201 : Nat := 1002417447188021738309497

theorem tailTrace_1952201 : CollatzResearch.WordTrace tailWord_1952201 prefixEnd_1952201 1002417447188021738309497 := by
  unfold tailWord_1952201
  simp only [CollatzResearch.WordTrace]
  refine ⟨71202620000516661231832457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47468413333677774154554971 71202620000516661231832457)
  ·
    refine ⟨53401965000387495923874343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71202620000516661231832457 53401965000387495923874343)
    ·
      refine ⟨80102947500581243885811515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53401965000387495923874343 80102947500581243885811515)
      ·
        refine ⟨120154421250871865828717273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80102947500581243885811515 120154421250871865828717273)
        ·
          refine ⟨90115815938153899371537955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120154421250871865828717273 90115815938153899371537955)
          ·
            refine ⟨135173723907230849057306933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90115815938153899371537955 135173723907230849057306933)
            ·
              refine ⟨12672536616302892099122525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135173723907230849057306933 12672536616302892099122525)
              ·
                refine ⟨4752201231113584537170947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12672536616302892099122525 4752201231113584537170947)
                ·
                  refine ⟨7128301846670376805756421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752201231113584537170947 7128301846670376805756421)
                  ·
                    refine ⟨1336556596250695651079329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7128301846670376805756421 1336556596250695651079329)
                    ·
                      refine ⟨1002417447188021738309497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336556596250695651079329 1002417447188021738309497)
                      ·
                        rfl

theorem cell23_1952201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 4, 2].length) (baseStart_1952201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952201 prefixEnd_1952201 := by exact prefixLift 1952201
  have htrace : WordTrace (prefixWord ++ tailWord_1952201) baseStart_1952201 baseEnd_1952201 := by
    simpa [prefixWord, tailWord_1952201, baseEnd_1952201] using wordTrace_append hprefix tailTrace_1952201
  have hstable : (prefixWord ++ tailWord_1952201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952201).length < 2 ^ (prefixWord ++ tailWord_1952201).sum := by decide
  have hdescent : baseEnd_1952201 < baseStart_1952201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952218 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2]
def baseStart_1952218 : Nat := 118140960795 + 1952218 * 2 ^ 59
def prefixEnd_1952218 : Nat := 4983230072969 + 3 ^ 40 * 1952218 * 2
def baseEnd_1952218 : Nat := 1002426176359148171796919

theorem tailTrace_1952218 : CollatzResearch.WordTrace tailWord_1952218 prefixEnd_1952218 1002426176359148171796919 := by
  unfold tailWord_1952218
  simp only [CollatzResearch.WordTrace]
  refine ⟨17800810010363768283800327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47468826694303382090134205 17800810010363768283800327)
  ·
    refine ⟨26701215015545652425700491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17800810010363768283800327 26701215015545652425700491)
    ·
      refine ⟨40051822523318478638550737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26701215015545652425700491 40051822523318478638550737)
      ·
        refine ⟨30038866892488858978913053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40051822523318478638550737 30038866892488858978913053)
        ·
          refine ⟨11264575084683322117092395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30038866892488858978913053 11264575084683322117092395)
          ·
            refine ⟨16896862627024983175638593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11264575084683322117092395 16896862627024983175638593)
            ·
              refine ⟨12672646970268737381728945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16896862627024983175638593 12672646970268737381728945)
              ·
                refine ⟨9504485227701553036296709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12672646970268737381728945 9504485227701553036296709)
                ·
                  refine ⟨1782090980194041194305633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9504485227701553036296709 1782090980194041194305633)
                  ·
                    refine ⟨1336568235145530895729225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1782090980194041194305633 1336568235145530895729225)
                    ·
                      refine ⟨1002426176359148171796919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336568235145530895729225 1002426176359148171796919)
                      ·
                        rfl

theorem cell23_1952218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_1952218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952218 prefixEnd_1952218 := by exact prefixLift 1952218
  have htrace : WordTrace (prefixWord ++ tailWord_1952218) baseStart_1952218 baseEnd_1952218 := by
    simpa [prefixWord, tailWord_1952218, baseEnd_1952218] using wordTrace_append hprefix tailTrace_1952218
  have hstable : (prefixWord ++ tailWord_1952218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952218).length < 2 ^ (prefixWord ++ tailWord_1952218).sum := by decide
  have hdescent : baseEnd_1952218 < baseStart_1952218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952241 : List Nat := [1, 2, 2, 2, 3, 1, 1, 6, 5]
def baseStart_1952241 : Nat := 118140960795 + 1952241 * 2 ^ 59
def prefixEnd_1952241 : Nat := 4983230072969 + 3 ^ 40 * 1952241 * 2
def baseEnd_1952241 : Nat := 111381998490466842423257

theorem tailTrace_1952241 : CollatzResearch.WordTrace tailWord_1952241 prefixEnd_1952241 111381998490466842423257 := by
  unfold tailWord_1952241
  simp only [CollatzResearch.WordTrace]
  refine ⟨71204078920371748063288577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47469385946914498708859051 71204078920371748063288577)
  ·
    refine ⟨53403059190278811047466433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71204078920371748063288577 53403059190278811047466433)
    ·
      refine ⟨40052294392709108285599825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53403059190278811047466433 40052294392709108285599825)
      ·
        refine ⟨30039220794531831214199869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40052294392709108285599825 30039220794531831214199869)
        ·
          refine ⟨11264707797949436705324951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30039220794531831214199869 11264707797949436705324951)
          ·
            refine ⟨16897061696924155057987427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11264707797949436705324951 16897061696924155057987427)
            ·
              refine ⟨25345592545386232586981141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16897061696924155057987427 25345592545386232586981141)
              ·
                refine ⟨1188074650564979652514741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25345592545386232586981141 1188074650564979652514741)
                ·
                  refine ⟨111381998490466842423257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188074650564979652514741 111381998490466842423257)
                  ·
                    rfl

theorem cell23_1952241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 6, 5].length) (baseStart_1952241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952241 prefixEnd_1952241 := by exact prefixLift 1952241
  have htrace : WordTrace (prefixWord ++ tailWord_1952241) baseStart_1952241 baseEnd_1952241 := by
    simpa [prefixWord, tailWord_1952241, baseEnd_1952241] using wordTrace_append hprefix tailTrace_1952241
  have hstable : (prefixWord ++ tailWord_1952241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952241).length < 2 ^ (prefixWord ++ tailWord_1952241).sum := by decide
  have hdescent : baseEnd_1952241 < baseStart_1952241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952261 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 2, 5, 2]
def baseStart_1952261 : Nat := 118140960795 + 1952261 * 2 ^ 59
def prefixEnd_1952261 : Nat := 4983230072969 + 3 ^ 40 * 1952261 * 2
def baseEnd_1952261 : Nat := 1002448256027291503559221

theorem tailTrace_1952261 : CollatzResearch.WordTrace tailWord_1952261 prefixEnd_1952261 1002448256027291503559221 := by
  unfold tailWord_1952261
  simp only [CollatzResearch.WordTrace]
  refine ⟨71204808380299291479016637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47469872253532860986011091 71204808380299291479016637)
  ·
    refine ⟨26701803142612234304631239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71204808380299291479016637 26701803142612234304631239)
    ·
      refine ⟨40052704713918351456946859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26701803142612234304631239 40052704713918351456946859)
      ·
        refine ⟨60079057070877527185420289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40052704713918351456946859 60079057070877527185420289)
        ·
          refine ⟨45059292803158145389065217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60079057070877527185420289 45059292803158145389065217)
          ·
            refine ⟨33794469602368609041798913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45059292803158145389065217 33794469602368609041798913)
            ·
              refine ⟨25345852201776456781349185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33794469602368609041798913 25345852201776456781349185)
              ·
                refine ⟨19009389151332342586011889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25345852201776456781349185 19009389151332342586011889)
                ·
                  refine ⟨14257041863499256939508917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19009389151332342586011889 14257041863499256939508917)
                  ·
                    refine ⟨1336597674703055338078961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14257041863499256939508917 1336597674703055338078961)
                    ·
                      refine ⟨1002448256027291503559221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336597674703055338078961 1002448256027291503559221)
                      ·
                        rfl

theorem cell23_1952261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_1952261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952261 prefixEnd_1952261 := by exact prefixLift 1952261
  have htrace : WordTrace (prefixWord ++ tailWord_1952261) baseStart_1952261 baseEnd_1952261 := by
    simpa [prefixWord, tailWord_1952261, baseEnd_1952261] using wordTrace_append hprefix tailTrace_1952261
  have hstable : (prefixWord ++ tailWord_1952261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952261).length < 2 ^ (prefixWord ++ tailWord_1952261).sum := by decide
  have hdescent : baseEnd_1952261 < baseStart_1952261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952264 : List Nat := [2, 1, 3, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_1952264 : Nat := 118140960795 + 1952264 * 2 ^ 59
def prefixEnd_1952264 : Nat := 4983230072969 + 3 ^ 40 * 1952264 * 2
def baseEnd_1952264 : Nat := 1002449796469254991821707

theorem tailTrace_1952264 : CollatzResearch.WordTrace tailWord_1952264 prefixEnd_1952264 1002449796469254991821707 := by
  unfold tailWord_1952264
  simp only [CollatzResearch.WordTrace]
  refine ⟨35602458899644211495687923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47469945199525615327583897 35602458899644211495687923)
  ·
    refine ⟨53403688349466317243531885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35602458899644211495687923 53403688349466317243531885)
    ·
      refine ⟨20026383131049868966324457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53403688349466317243531885 20026383131049868966324457)
      ·
        refine ⟨15019787348287401724743343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20026383131049868966324457 15019787348287401724743343)
        ·
          refine ⟨22529681022431102587115015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15019787348287401724743343 22529681022431102587115015)
          ·
            refine ⟨33794521533646653880672523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22529681022431102587115015 33794521533646653880672523)
            ·
              refine ⟨50691782300469980821008785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33794521533646653880672523 50691782300469980821008785)
              ·
                refine ⟨38018836725352485615756589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50691782300469980821008785 38018836725352485615756589)
                ·
                  refine ⟨14257063772007182105908721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38018836725352485615756589 14257063772007182105908721)
                  ·
                    refine ⟨10692797829005386579431541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14257063772007182105908721 10692797829005386579431541)
                    ·
                      refine ⟨1002449796469254991821707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10692797829005386579431541 1002449796469254991821707)
                      ·
                        rfl

theorem cell23_1952264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_1952264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952264 prefixEnd_1952264 := by exact prefixLift 1952264
  have htrace : WordTrace (prefixWord ++ tailWord_1952264) baseStart_1952264 baseEnd_1952264 := by
    simpa [prefixWord, tailWord_1952264, baseEnd_1952264] using wordTrace_append hprefix tailTrace_1952264
  have hstable : (prefixWord ++ tailWord_1952264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952264).length < 2 ^ (prefixWord ++ tailWord_1952264).sum := by decide
  have hdescent : baseEnd_1952264 < baseStart_1952264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952288 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 2, 5]
def baseStart_1952288 : Nat := 118140960795 + 1952288 * 2 ^ 59
def prefixEnd_1952288 : Nat := 4983230072969 + 3 ^ 40 * 1952288 * 2
def baseEnd_1952288 : Nat := 334154040001654299307199

theorem tailTrace_1952288 : CollatzResearch.WordTrace tailWord_1952288 prefixEnd_1952288 334154040001654299307199 := by
  unfold tailWord_1952288
  simp only [CollatzResearch.WordTrace]
  refine ⟨35602896575600737545124759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47470528767467650060166345 35602896575600737545124759)
  ·
    refine ⟨53404344863401106317687139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35602896575600737545124759 53404344863401106317687139)
    ·
      refine ⟨80106517295101659476530709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53404344863401106317687139 80106517295101659476530709)
      ·
        refine ⟨3754992998207890287962377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80106517295101659476530709 3754992998207890287962377)
        ·
          refine ⟨2816244748655917715971783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3754992998207890287962377 2816244748655917715971783)
          ·
            refine ⟨4224367122983876573957675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816244748655917715971783 4224367122983876573957675)
            ·
              refine ⟨6336550684475814860936513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224367122983876573957675 6336550684475814860936513)
              ·
                refine ⟨4752413013356861145702385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6336550684475814860936513 4752413013356861145702385)
                ·
                  refine ⟨3564309760017645859276789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4752413013356861145702385 3564309760017645859276789)
                  ·
                    refine ⟨334154040001654299307199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3564309760017645859276789 334154040001654299307199)
                    ·
                      rfl

theorem cell23_1952288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 5].length) (baseStart_1952288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952288 prefixEnd_1952288 := by exact prefixLift 1952288
  have htrace : WordTrace (prefixWord ++ tailWord_1952288) baseStart_1952288 baseEnd_1952288 := by
    simpa [prefixWord, tailWord_1952288, baseEnd_1952288] using wordTrace_append hprefix tailTrace_1952288
  have hstable : (prefixWord ++ tailWord_1952288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952288).length < 2 ^ (prefixWord ++ tailWord_1952288).sum := by decide
  have hdescent : baseEnd_1952288 < baseStart_1952288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952291 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 4]
def baseStart_1952291 : Nat := 118140960795 + 1952291 * 2 ^ 59
def prefixEnd_1952291 : Nat := 4983230072969 + 3 ^ 40 * 1952291 * 2
def baseEnd_1952291 : Nat := 1002463660446926386184083

theorem tailTrace_1952291 : CollatzResearch.WordTrace tailWord_1952291 prefixEnd_1952291 1002463660446926386184083 := by
  unfold tailWord_1952291
  simp only [CollatzResearch.WordTrace]
  refine ⟨71205902570190606602608727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47470601713460404401739151 71205902570190606602608727)
  ·
    refine ⟨106808853855285909903913091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71205902570190606602608727 106808853855285909903913091)
    ·
      refine ⟨160213280782928864855869637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106808853855285909903913091 160213280782928864855869637)
      ·
        refine ⟨30039990146799162160475557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160213280782928864855869637 30039990146799162160475557)
        ·
          refine ⟨5632498152524842905089167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30039990146799162160475557 5632498152524842905089167)
          ·
            refine ⟨8448747228787264357633751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5632498152524842905089167 8448747228787264357633751)
            ·
              refine ⟨12673120843180896536450627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8448747228787264357633751 12673120843180896536450627)
              ·
                refine ⟨19009681264771344804675941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12673120843180896536450627 19009681264771344804675941)
                ·
                  refine ⟨3564315237144627150876739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19009681264771344804675941 3564315237144627150876739)
                  ·
                    refine ⟨5346472855716940726315109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3564315237144627150876739 5346472855716940726315109)
                    ·
                      refine ⟨1002463660446926386184083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5346472855716940726315109 1002463660446926386184083)
                      ·
                        rfl

theorem cell23_1952291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_1952291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952291 prefixEnd_1952291 := by exact prefixLift 1952291
  have htrace : WordTrace (prefixWord ++ tailWord_1952291) baseStart_1952291 baseEnd_1952291 := by
    simpa [prefixWord, tailWord_1952291, baseEnd_1952291] using wordTrace_append hprefix tailTrace_1952291
  have hstable : (prefixWord ++ tailWord_1952291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952291).length < 2 ^ (prefixWord ++ tailWord_1952291).sum := by decide
  have hdescent : baseEnd_1952291 < baseStart_1952291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952292 : List Nat := [2, 3, 1, 5, 1, 1, 3, 2, 5]
def baseStart_1952292 : Nat := 118140960795 + 1952292 * 2 ^ 59
def prefixEnd_1952292 : Nat := 4983230072969 + 3 ^ 40 * 1952292 * 2
def baseEnd_1952292 : Nat := 111384908214175653585731

theorem tailTrace_1952292 : CollatzResearch.WordTrace tailWord_1952292 prefixEnd_1952292 111384908214175653585731 := by
  unfold tailWord_1952292
  simp only [CollatzResearch.WordTrace]
  refine ⟨35602969521593491886697565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47470626028791322515596753 35602969521593491886697565)
  ·
    refine ⟨13351113570597559457511587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35602969521593491886697565 13351113570597559457511587)
    ·
      refine ⟨20026670355896339186267381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13351113570597559457511587 20026670355896339186267381)
      ·
        refine ⟨1877500345865281798712567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20026670355896339186267381 1877500345865281798712567)
        ·
          refine ⟨2816250518797922698068851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1877500345865281798712567 2816250518797922698068851)
          ·
            refine ⟨4224375778196884047103277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816250518797922698068851 4224375778196884047103277)
            ·
              refine ⟨1584140916823831517663729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4224375778196884047103277 1584140916823831517663729)
              ·
                refine ⟨1188105687617873638247797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584140916823831517663729 1188105687617873638247797)
                ·
                  refine ⟨111384908214175653585731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188105687617873638247797 111384908214175653585731)
                  ·
                    rfl

theorem cell23_1952292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_1952292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952292 prefixEnd_1952292 := by exact prefixLift 1952292
  have htrace : WordTrace (prefixWord ++ tailWord_1952292) baseStart_1952292 baseEnd_1952292 := by
    simpa [prefixWord, tailWord_1952292, baseEnd_1952292] using wordTrace_append hprefix tailTrace_1952292
  have hstable : (prefixWord ++ tailWord_1952292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952292).length < 2 ^ (prefixWord ++ tailWord_1952292).sum := by decide
  have hdescent : baseEnd_1952292 < baseStart_1952292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952304 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_1952304 : Nat := 118140960795 + 1952304 * 2 ^ 59
def prefixEnd_1952304 : Nat := 4983230072969 + 3 ^ 40 * 1952304 * 2
def baseEnd_1952304 : Nat := 1002470335695434835321523

theorem tailTrace_1952304 : CollatzResearch.WordTrace tailWord_1952304 prefixEnd_1952304 1002470335695434835321523 := by
  unfold tailWord_1952304
  simp only [CollatzResearch.WordTrace]
  refine ⟨35603188359571754911415983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47470917812762339881887977 35603188359571754911415983)
  ·
    refine ⟨53404782539357632367123975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35603188359571754911415983 53404782539357632367123975)
    ·
      refine ⟨80107173809036448550685963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53404782539357632367123975 80107173809036448550685963)
      ·
        refine ⟨120160760713554672826028945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80107173809036448550685963 120160760713554672826028945)
        ·
          refine ⟨90120570535166004619521709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120160760713554672826028945 90120570535166004619521709)
          ·
            refine ⟨33795213950687251732320641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90120570535166004619521709 33795213950687251732320641)
            ·
              refine ⟨25346410463015438799240481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33795213950687251732320641 25346410463015438799240481)
              ·
                refine ⟨19009807847261579099430361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25346410463015438799240481 19009807847261579099430361)
                ·
                  refine ⟨14257355885446184324572771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19009807847261579099430361 14257355885446184324572771)
                  ·
                    refine ⟨21386033828169276486859157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14257355885446184324572771 21386033828169276486859157)
                    ·
                      refine ⟨1002470335695434835321523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21386033828169276486859157 1002470335695434835321523)
                      ·
                        rfl

theorem cell23_1952304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_1952304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952304 prefixEnd_1952304 := by exact prefixLift 1952304
  have htrace : WordTrace (prefixWord ++ tailWord_1952304) baseStart_1952304 baseEnd_1952304 := by
    simpa [prefixWord, tailWord_1952304, baseEnd_1952304] using wordTrace_append hprefix tailTrace_1952304
  have hstable : (prefixWord ++ tailWord_1952304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952304).length < 2 ^ (prefixWord ++ tailWord_1952304).sum := by decide
  have hdescent : baseEnd_1952304 < baseStart_1952304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952311 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 3]
def baseStart_1952311 : Nat := 118140960795 + 1952311 * 2 ^ 59
def prefixEnd_1952311 : Nat := 4983230072969 + 3 ^ 40 * 1952311 * 2
def baseEnd_1952311 : Nat := 1002473930060016307933991

theorem tailTrace_1952311 : CollatzResearch.WordTrace tailWord_1952311 prefixEnd_1952311 1002473930060016307933991 := by
  unfold tailWord_1952311
  simp only [CollatzResearch.WordTrace]
  refine ⟨71206632030118150018336787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47471088020078766678891191 71206632030118150018336787)
  ·
    refine ⟨106809948045177225027505181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71206632030118150018336787 106809948045177225027505181)
    ·
      refine ⟨40053730516941459385314443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106809948045177225027505181 40053730516941459385314443)
      ·
        refine ⟨60080595775412189077971665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40053730516941459385314443 60080595775412189077971665)
        ·
          refine ⟨45060446831559141808478749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60080595775412189077971665 45060446831559141808478749)
          ·
            refine ⟨16897667561834678178179531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45060446831559141808478749 16897667561834678178179531)
            ·
              refine ⟨25346501342752017267269297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16897667561834678178179531 25346501342752017267269297)
              ·
                refine ⟨19009876007064012950451973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25346501342752017267269297 19009876007064012950451973)
                ·
                  refine ⟨3564351751324502428209745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19009876007064012950451973 3564351751324502428209745)
                  ·
                    refine ⟨2673263813493376821157309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3564351751324502428209745 2673263813493376821157309)
                    ·
                      refine ⟨1002473930060016307933991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2673263813493376821157309 1002473930060016307933991)
                      ·
                        rfl

theorem cell23_1952311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_1952311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952311 prefixEnd_1952311 := by exact prefixLift 1952311
  have htrace : WordTrace (prefixWord ++ tailWord_1952311) baseStart_1952311 baseEnd_1952311 := by
    simpa [prefixWord, tailWord_1952311, baseEnd_1952311] using wordTrace_append hprefix tailTrace_1952311
  have hstable : (prefixWord ++ tailWord_1952311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952311).length < 2 ^ (prefixWord ++ tailWord_1952311).sum := by decide
  have hdescent : baseEnd_1952311 < baseStart_1952311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952391 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 1, 6]
def baseStart_1952391 : Nat := 118140960795 + 1952391 * 2 ^ 59
def prefixEnd_1952391 : Nat := 4983230072969 + 3 ^ 40 * 1952391 * 2
def baseEnd_1952391 : Nat := 334171669504125331644541

theorem tailTrace_1952391 : CollatzResearch.WordTrace tailWord_1952391 prefixEnd_1952391 334171669504125331644541 := by
  unfold tailWord_1952391
  simp only [CollatzResearch.WordTrace]
  refine ⟨71209549869828323681249027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47473033246552215787499351 71209549869828323681249027)
  ·
    refine ⟨106814324804742485521873541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71209549869828323681249027 106814324804742485521873541)
    ·
      refine ⟨20027685900889216035351289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106814324804742485521873541 20027685900889216035351289)
      ·
        refine ⟨15020764425666912026513467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20027685900889216035351289 15020764425666912026513467)
        ·
          refine ⟨22531146638500368039770201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15020764425666912026513467 22531146638500368039770201)
          ·
            refine ⟨16898359978875276029827651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22531146638500368039770201 16898359978875276029827651)
            ·
              refine ⟨25347539968312914044741477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16898359978875276029827651 25347539968312914044741477)
              ·
                refine ⟨4752663744058671383389027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25347539968312914044741477 4752663744058671383389027)
                ·
                  refine ⟨7128995616088007075083541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4752663744058671383389027 7128995616088007075083541)
                  ·
                    refine ⟨334171669504125331644541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7128995616088007075083541 334171669504125331644541)
                    ·
                      rfl

theorem cell23_1952391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_1952391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952391 prefixEnd_1952391 := by exact prefixLift 1952391
  have htrace : WordTrace (prefixWord ++ tailWord_1952391) baseStart_1952391 baseEnd_1952391 := by
    simpa [prefixWord, tailWord_1952391, baseEnd_1952391] using wordTrace_append hprefix tailTrace_1952391
  have hstable : (prefixWord ++ tailWord_1952391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952391).length < 2 ^ (prefixWord ++ tailWord_1952391).sum := by decide
  have hdescent : baseEnd_1952391 < baseStart_1952391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952408 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 4, 4]
def baseStart_1952408 : Nat := 118140960795 + 1952408 * 2 ^ 59
def prefixEnd_1952408 : Nat := 4983230072969 + 3 ^ 40 * 1952408 * 2
def baseEnd_1952408 : Nat := 334174579227834142807015

theorem tailTrace_1952408 : CollatzResearch.WordTrace tailWord_1952408 prefixEnd_1952408 334174579227834142807015 := by
  unfold tailWord_1952408
  simp only [CollatzResearch.WordTrace]
  refine ⟨35605084955383367792308939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47473446607177823723078585 35605084955383367792308939)
  ·
    refine ⟨53407627433075051688463409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35605084955383367792308939 53407627433075051688463409)
    ·
      refine ⟨40055720574806288766347557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53407627433075051688463409 40055720574806288766347557)
      ·
        refine ⟨7510447607776179143690167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40055720574806288766347557 7510447607776179143690167)
        ·
          refine ⟨11265671411664268715535251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7510447607776179143690167 11265671411664268715535251)
          ·
            refine ⟨16898507117496403073302877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11265671411664268715535251 16898507117496403073302877)
            ·
              refine ⟨6336940169061151152488579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16898507117496403073302877 6336940169061151152488579)
              ·
                refine ⟨9505410253591726728732869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6336940169061151152488579 9505410253591726728732869)
                ·
                  refine ⟨1782264422548448761637413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9505410253591726728732869 1782264422548448761637413)
                  ·
                    refine ⟨334174579227834142807015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1782264422548448761637413 334174579227834142807015)
                    ·
                      rfl

theorem cell23_1952408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_1952408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952408 prefixEnd_1952408 := by exact prefixLift 1952408
  have htrace : WordTrace (prefixWord ++ tailWord_1952408) baseStart_1952408 baseEnd_1952408 := by
    simpa [prefixWord, tailWord_1952408, baseEnd_1952408] using wordTrace_append hprefix tailTrace_1952408
  have hstable : (prefixWord ++ tailWord_1952408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952408).length < 2 ^ (prefixWord ++ tailWord_1952408).sum := by decide
  have hdescent : baseEnd_1952408 < baseStart_1952408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952435 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 1, 2, 3]
def baseStart_1952435 : Nat := 118140960795 + 1952435 * 2 ^ 59
def prefixEnd_1952435 : Nat := 4983230072969 + 3 ^ 40 * 1952435 * 2
def baseEnd_1952435 : Nat := 1002537601661173822783421

theorem tailTrace_1952435 : CollatzResearch.WordTrace tailWord_1952435 prefixEnd_1952435 1002537601661173822783421 := by
  unfold tailWord_1952435
  simp only [CollatzResearch.WordTrace]
  refine ⟨71211154681668919195850759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47474103121112612797233839 71211154681668919195850759)
  ·
    refine ⟨106816732022503378793776139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71211154681668919195850759 106816732022503378793776139)
    ·
      refine ⟨160225098033755068190664209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106816732022503378793776139 160225098033755068190664209)
      ·
        refine ⟨120168823525316301142998157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160225098033755068190664209 120168823525316301142998157)
        ·
          refine ⟨45063308821993612928624309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120168823525316301142998157 45063308821993612928624309)
          ·
            refine ⟨4224685202061901212058529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45063308821993612928624309 4224685202061901212058529)
            ·
              refine ⟨3168513901546425909043897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4224685202061901212058529 3168513901546425909043897)
              ·
                refine ⟨2376385426159819431782923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168513901546425909043897 2376385426159819431782923)
                ·
                  refine ⟨3564578139239729147674385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376385426159819431782923 3564578139239729147674385)
                  ·
                    refine ⟨2673433604429796860755789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3564578139239729147674385 2673433604429796860755789)
                    ·
                      refine ⟨1002537601661173822783421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2673433604429796860755789 1002537601661173822783421)
                      ·
                        rfl

theorem cell23_1952435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 2, 3].length) (baseStart_1952435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952435 prefixEnd_1952435 := by exact prefixLift 1952435
  have htrace : WordTrace (prefixWord ++ tailWord_1952435) baseStart_1952435 baseEnd_1952435 := by
    simpa [prefixWord, tailWord_1952435, baseEnd_1952435] using wordTrace_append hprefix tailTrace_1952435
  have hstable : (prefixWord ++ tailWord_1952435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952435).length < 2 ^ (prefixWord ++ tailWord_1952435).sum := by decide
  have hdescent : baseEnd_1952435 < baseStart_1952435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952465 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 2, 1, 3]
def baseStart_1952465 : Nat := 118140960795 + 1952465 * 2 ^ 59
def prefixEnd_1952465 : Nat := 4983230072969 + 3 ^ 40 * 1952465 * 2
def baseEnd_1952465 : Nat := 1002553006080808705408283

theorem tailTrace_1952465 : CollatzResearch.WordTrace tailWord_1952465 prefixEnd_1952465 1002553006080808705408283 := by
  unfold tailWord_1952465
  simp only [CollatzResearch.WordTrace]
  refine ⟨71212248871560234319442849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47474832581040156212961899 71212248871560234319442849)
  ·
    refine ⟨53409186653670175739582137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71212248871560234319442849 53409186653670175739582137)
    ·
      refine ⟨40056889990252631804686603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53409186653670175739582137 40056889990252631804686603)
      ·
        refine ⟨60085334985378947707029905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40056889990252631804686603 60085334985378947707029905)
        ·
          refine ⟨45064001239034210780272429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60085334985378947707029905 45064001239034210780272429)
          ·
            refine ⟨16899000464637829042602161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45064001239034210780272429 16899000464637829042602161)
            ·
              refine ⟨12674250348478371781951621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16899000464637829042602161 12674250348478371781951621)
              ·
                refine ⟨2376421940339694709115929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12674250348478371781951621 2376421940339694709115929)
                ·
                  refine ⟨1782316455254771031836947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2376421940339694709115929 1782316455254771031836947)
                  ·
                    refine ⟨2673474682882156547755421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1782316455254771031836947 2673474682882156547755421)
                    ·
                      refine ⟨1002553006080808705408283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2673474682882156547755421 1002553006080808705408283)
                      ·
                        rfl

theorem cell23_1952465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_1952465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952465 prefixEnd_1952465 := by exact prefixLift 1952465
  have htrace : WordTrace (prefixWord ++ tailWord_1952465) baseStart_1952465 baseEnd_1952465 := by
    simpa [prefixWord, tailWord_1952465, baseEnd_1952465] using wordTrace_append hprefix tailTrace_1952465
  have hstable : (prefixWord ++ tailWord_1952465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952465).length < 2 ^ (prefixWord ++ tailWord_1952465).sum := by decide
  have hdescent : baseEnd_1952465 < baseStart_1952465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952466 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 3, 2, 2]
def baseStart_1952466 : Nat := 118140960795 + 1952466 * 2 ^ 59
def prefixEnd_1952466 : Nat := 4983230072969 + 3 ^ 40 * 1952466 * 2
def baseEnd_1952466 : Nat := 1002553519561463201495779

theorem tailTrace_1952466 : CollatzResearch.WordTrace tailWord_1952466 prefixEnd_1952466 1002553519561463201495779 := by
  unfold tailWord_1952466
  simp only [CollatzResearch.WordTrace]
  refine ⟨17803071336139152872557313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47474856896371074326819501 17803071336139152872557313)
  ·
    refine ⟨13352303502104364654417985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17803071336139152872557313 13352303502104364654417985)
    ·
      refine ⟨10014227626578273490813489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13352303502104364654417985 10014227626578273490813489)
      ·
        refine ⟨7510670719933705118110117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10014227626578273490813489 7510670719933705118110117)
        ·
          refine ⟨1408250759987569709645647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7510670719933705118110117 1408250759987569709645647)
          ·
            refine ⟨2112376139981354564468471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408250759987569709645647 2112376139981354564468471)
            ·
              refine ⟨3168564209972031846702707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112376139981354564468471 3168564209972031846702707)
              ·
                refine ⟨4752846314958047770054061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168564209972031846702707 4752846314958047770054061)
                ·
                  refine ⟨1782317368109267913770273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4752846314958047770054061 1782317368109267913770273)
                  ·
                    refine ⟨1336738026081950935327705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1782317368109267913770273 1336738026081950935327705)
                    ·
                      refine ⟨1002553519561463201495779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336738026081950935327705 1002553519561463201495779)
                      ·
                        rfl

theorem cell23_1952466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_1952466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952466 prefixEnd_1952466 := by exact prefixLift 1952466
  have htrace : WordTrace (prefixWord ++ tailWord_1952466) baseStart_1952466 baseEnd_1952466 := by
    simpa [prefixWord, tailWord_1952466, baseEnd_1952466] using wordTrace_append hprefix tailTrace_1952466
  have hstable : (prefixWord ++ tailWord_1952466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952466).length < 2 ^ (prefixWord ++ tailWord_1952466).sum := by decide
  have hdescent : baseEnd_1952466 < baseStart_1952466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952505 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 6, 2, 2]
def baseStart_1952505 : Nat := 118140960795 + 1952505 * 2 ^ 59
def prefixEnd_1952505 : Nat := 4983230072969 + 3 ^ 40 * 1952505 * 2
def baseEnd_1952505 : Nat := 1002573545306988548908099

theorem tailTrace_1952505 : CollatzResearch.WordTrace tailWord_1952505 prefixEnd_1952505 1002573545306988548908099 := by
  unfold tailWord_1952505
  simp only [CollatzResearch.WordTrace]
  refine ⟨71213707791415321150898969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47475805194276880767265979 71213707791415321150898969)
  ·
    refine ⟨53410280843561490863174227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71213707791415321150898969 53410280843561490863174227)
    ·
      refine ⟨80115421265342236294761341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53410280843561490863174227 80115421265342236294761341)
      ·
        refine ⟨30043282974503338610535503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80115421265342236294761341 30043282974503338610535503)
        ·
          refine ⟨45064924461755007915803255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30043282974503338610535503 45064924461755007915803255)
          ·
            refine ⟨67597386692632511873704883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45064924461755007915803255 67597386692632511873704883)
            ·
              refine ⟨101396080038948767810557325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67597386692632511873704883 101396080038948767810557325)
              ·
                refine ⟨38023530014605787928958997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101396080038948767810557325 38023530014605787928958997)
                ·
                  refine ⟨1782352969434646309169953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 38023530014605787928958997 1782352969434646309169953)
                  ·
                    refine ⟨1336764727075984731877465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1782352969434646309169953 1336764727075984731877465)
                    ·
                      refine ⟨1002573545306988548908099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336764727075984731877465 1002573545306988548908099)
                      ·
                        rfl

theorem cell23_1952505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_1952505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952505 prefixEnd_1952505 := by exact prefixLift 1952505
  have htrace : WordTrace (prefixWord ++ tailWord_1952505) baseStart_1952505 baseEnd_1952505 := by
    simpa [prefixWord, tailWord_1952505, baseEnd_1952505] using wordTrace_append hprefix tailTrace_1952505
  have hstable : (prefixWord ++ tailWord_1952505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952505).length < 2 ^ (prefixWord ++ tailWord_1952505).sum := by decide
  have hdescent : baseEnd_1952505 < baseStart_1952505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952508 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_1952508 : Nat := 118140960795 + 1952508 * 2 ^ 59
def prefixEnd_1952508 : Nat := 4983230072969 + 3 ^ 40 * 1952508 * 2
def baseEnd_1952508 : Nat := 1002575085748952037170585

theorem tailTrace_1952508 : CollatzResearch.WordTrace tailWord_1952508 prefixEnd_1952508 1002575085748952037170585 := by
  unfold tailWord_1952508
  simp only [CollatzResearch.WordTrace]
  refine ⟨35606908605202226331629089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47475878140269635108838785 35606908605202226331629089)
  ·
    refine ⟨26705181453901669748721817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35606908605202226331629089 26705181453901669748721817)
    ·
      refine ⟨20028886090426252311541363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26705181453901669748721817 20028886090426252311541363)
      ·
        refine ⟨30043329135639378467312045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20028886090426252311541363 30043329135639378467312045)
        ·
          refine ⟨11266248425864766925242017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30043329135639378467312045 11266248425864766925242017)
          ·
            refine ⟨8449686319398575193931513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11266248425864766925242017 8449686319398575193931513)
            ·
              refine ⟨6337264739548931395448635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8449686319398575193931513 6337264739548931395448635)
              ·
                refine ⟨9505897109323397093172953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337264739548931395448635 9505897109323397093172953)
                ·
                  refine ⟨7129422831992547819879715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9505897109323397093172953 7129422831992547819879715)
                  ·
                    refine ⟨10694134247988821729819573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7129422831992547819879715 10694134247988821729819573)
                    ·
                      refine ⟨1002575085748952037170585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10694134247988821729819573 1002575085748952037170585)
                      ·
                        rfl

theorem cell23_1952508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_1952508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952508 prefixEnd_1952508 := by exact prefixLift 1952508
  have htrace : WordTrace (prefixWord ++ tailWord_1952508) baseStart_1952508 baseEnd_1952508 := by
    simpa [prefixWord, tailWord_1952508, baseEnd_1952508] using wordTrace_append hprefix tailTrace_1952508
  have hstable : (prefixWord ++ tailWord_1952508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952508).length < 2 ^ (prefixWord ++ tailWord_1952508).sum := by decide
  have hdescent : baseEnd_1952508 < baseStart_1952508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952521 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_1952521 : Nat := 118140960795 + 1952521 * 2 ^ 59
def prefixEnd_1952521 : Nat := 4983230072969 + 3 ^ 40 * 1952521 * 2
def baseEnd_1952521 : Nat := 1002581760997460486308025

theorem tailTrace_1952521 : CollatzResearch.WordTrace tailWord_1952521 prefixEnd_1952521 1002581760997460486308025 := by
  unfold tailWord_1952521
  simp only [CollatzResearch.WordTrace]
  refine ⟨71214291359357355883481417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47476194239571570588987611 71214291359357355883481417)
  ·
    refine ⟨53410718519518016912611063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71214291359357355883481417 53410718519518016912611063)
    ·
      refine ⟨80116077779277025368916595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53410718519518016912611063 80116077779277025368916595)
      ·
        refine ⟨120174116668915538053374893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80116077779277025368916595 120174116668915538053374893)
        ·
          refine ⟨45065293750843326770015585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120174116668915538053374893 45065293750843326770015585)
          ·
            refine ⟨33798970313132495077511689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45065293750843326770015585 33798970313132495077511689)
            ·
              refine ⟨25349227734849371308133767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33798970313132495077511689 25349227734849371308133767)
              ·
                refine ⟨38023841602274056962200651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25349227734849371308133767 38023841602274056962200651)
                ·
                  refine ⟨57035762403411085443300977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38023841602274056962200651 57035762403411085443300977)
                  ·
                    refine ⟨42776821802558314082475733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57035762403411085443300977 42776821802558314082475733)
                    ·
                      refine ⟨1002581760997460486308025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42776821802558314082475733 1002581760997460486308025)
                      ·
                        rfl

theorem cell23_1952521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_1952521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952521 prefixEnd_1952521 := by exact prefixLift 1952521
  have htrace : WordTrace (prefixWord ++ tailWord_1952521) baseStart_1952521 baseEnd_1952521 := by
    simpa [prefixWord, tailWord_1952521, baseEnd_1952521] using wordTrace_append hprefix tailTrace_1952521
  have hstable : (prefixWord ++ tailWord_1952521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952521).length < 2 ^ (prefixWord ++ tailWord_1952521).sum := by decide
  have hdescent : baseEnd_1952521 < baseStart_1952521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952535 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1952535 : Nat := 118140960795 + 1952535 * 2 ^ 59
def prefixEnd_1952535 : Nat := 4983230072969 + 3 ^ 40 * 1952535 * 2
def baseEnd_1952535 : Nat := 1002588949726623431532961

theorem tailTrace_1952535 : CollatzResearch.WordTrace tailWord_1952535 prefixEnd_1952535 1002588949726623431532961 := by
  unfold tailWord_1952535
  simp only [CollatzResearch.WordTrace]
  refine ⟨71214801981306636274491059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47476534654204424182994039 71214801981306636274491059)
  ·
    refine ⟨106822202971959954411736589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71214801981306636274491059 106822202971959954411736589)
    ·
      refine ⟨40058326114484982904401221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106822202971959954411736589 40058326114484982904401221)
      ·
        refine ⟨7510936146465934294575229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40058326114484982904401221 7510936146465934294575229)
        ·
          refine ⟨2816601054924725360465711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7510936146465934294575229 2816601054924725360465711)
          ·
            refine ⟨4224901582387088040698567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816601054924725360465711 4224901582387088040698567)
            ·
              refine ⟨6337352373580632061047851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4224901582387088040698567 6337352373580632061047851)
              ·
                refine ⟨9506028560370948091571777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337352373580632061047851 9506028560370948091571777)
                ·
                  refine ⟨7129521420278211068678833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9506028560370948091571777 7129521420278211068678833)
                  ·
                    refine ⟨5347141065208658301509125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7129521420278211068678833 5347141065208658301509125)
                    ·
                      refine ⟨1002588949726623431532961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5347141065208658301509125 1002588949726623431532961)
                      ·
                        rfl

theorem cell23_1952535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1952535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952535 prefixEnd_1952535 := by exact prefixLift 1952535
  have htrace : WordTrace (prefixWord ++ tailWord_1952535) baseStart_1952535 baseEnd_1952535 := by
    simpa [prefixWord, tailWord_1952535, baseEnd_1952535] using wordTrace_append hprefix tailTrace_1952535
  have hstable : (prefixWord ++ tailWord_1952535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952535).length < 2 ^ (prefixWord ++ tailWord_1952535).sum := by decide
  have hdescent : baseEnd_1952535 < baseStart_1952535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952573 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 2, 2, 2]
def baseStart_1952573 : Nat := 118140960795 + 1952573 * 2 ^ 59
def prefixEnd_1952573 : Nat := 4983230072969 + 3 ^ 40 * 1952573 * 2
def baseEnd_1952573 : Nat := 1002608461991494282857787

theorem tailTrace_1952573 : CollatzResearch.WordTrace tailWord_1952573 prefixEnd_1952573 1002608461991494282857787 := by
  unfold tailWord_1952573
  simp only [CollatzResearch.WordTrace]
  refine ⟨71216187955168968764374373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47477458636779312509582915 71216187955168968764374373)
  ·
    refine ⟨13353035241594181643320195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71216187955168968764374373 13353035241594181643320195)
    ·
      refine ⟨20029552862391272464980293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13353035241594181643320195 20029552862391272464980293)
      ·
        refine ⟨3755541161698363587183805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20029552862391272464980293 3755541161698363587183805)
        ·
          refine ⟨1408327935636886345193927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3755541161698363587183805 1408327935636886345193927)
          ·
            refine ⟨2112491903455329517790891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408327935636886345193927 2112491903455329517790891)
            ·
              refine ⟨3168737855182994276686337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112491903455329517790891 3168737855182994276686337)
              ·
                refine ⟨2376553391387245707514753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3168737855182994276686337 2376553391387245707514753)
                ·
                  refine ⟨1782415043540434280636065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2376553391387245707514753 1782415043540434280636065)
                  ·
                    refine ⟨1336811282655325710477049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1782415043540434280636065 1336811282655325710477049)
                    ·
                      refine ⟨1002608461991494282857787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336811282655325710477049 1002608461991494282857787)
                      ·
                        rfl

theorem cell23_1952573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_1952573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952573 prefixEnd_1952573 := by exact prefixLift 1952573
  have htrace : WordTrace (prefixWord ++ tailWord_1952573) baseStart_1952573 baseEnd_1952573 := by
    simpa [prefixWord, tailWord_1952573, baseEnd_1952573] using wordTrace_append hprefix tailTrace_1952573
  have hstable : (prefixWord ++ tailWord_1952573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952573).length < 2 ^ (prefixWord ++ tailWord_1952573).sum := by decide
  have hdescent : baseEnd_1952573 < baseStart_1952573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952608 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_1952608 : Nat := 118140960795 + 1952608 * 2 ^ 59
def prefixEnd_1952608 : Nat := 4983230072969 + 3 ^ 40 * 1952608 * 2
def baseEnd_1952608 : Nat := 1002626433814401645920125

theorem tailTrace_1952608 : CollatzResearch.WordTrace tailWord_1952608 prefixEnd_1952608 1002626433814401645920125 := by
  unfold tailWord_1952608
  simp only [CollatzResearch.WordTrace]
  refine ⟨35608732255021084870949239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47478309673361446494598985 35608732255021084870949239)
  ·
    refine ⟨53413098382531627306423859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35608732255021084870949239 53413098382531627306423859)
    ·
      refine ⟨80119647573797440959635789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53413098382531627306423859 80119647573797440959635789)
      ·
        refine ⟨30044867840174040359863421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80119647573797440959635789 30044867840174040359863421)
        ·
          refine ⟨11266825440065265134948783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30044867840174040359863421 11266825440065265134948783)
          ·
            refine ⟨16900238160097897702423175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11266825440065265134948783 16900238160097897702423175)
            ·
              refine ⟨25350357240146846553634763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16900238160097897702423175 25350357240146846553634763)
              ·
                refine ⟨38025535860220269830452145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25350357240146846553634763 38025535860220269830452145)
                ·
                  refine ⟨28519151895165202372839109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38025535860220269830452145 28519151895165202372839109)
                  ·
                    refine ⟨5347340980343475444907333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28519151895165202372839109 5347340980343475444907333)
                    ·
                      refine ⟨1002626433814401645920125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5347340980343475444907333 1002626433814401645920125)
                      ·
                        rfl

theorem cell23_1952608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_1952608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952608 prefixEnd_1952608 := by exact prefixLift 1952608
  have htrace : WordTrace (prefixWord ++ tailWord_1952608) baseStart_1952608 baseEnd_1952608 := by
    simpa [prefixWord, tailWord_1952608, baseEnd_1952608] using wordTrace_append hprefix tailTrace_1952608
  have hstable : (prefixWord ++ tailWord_1952608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952608).length < 2 ^ (prefixWord ++ tailWord_1952608).sum := by decide
  have hdescent : baseEnd_1952608 < baseStart_1952608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952615 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1952615 : Nat := 118140960795 + 1952615 * 2 ^ 59
def prefixEnd_1952615 : Nat := 4983230072969 + 3 ^ 40 * 1952615 * 2
def baseEnd_1952615 : Nat := 1002630028178983118532593

theorem tailTrace_1952615 : CollatzResearch.WordTrace tailWord_1952615 prefixEnd_1952615 1002630028178983118532593 := by
  unfold tailWord_1952615
  simp only [CollatzResearch.WordTrace]
  refine ⟨71217719821016809937403299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47478479880677873291602199 71217719821016809937403299)
  ·
    refine ⟨106826579731525214906104949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71217719821016809937403299 106826579731525214906104949)
    ·
      refine ⟨10014991849830488897447339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106826579731525214906104949 10014991849830488897447339)
      ·
        refine ⟨15022487774745733346171009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10014991849830488897447339 15022487774745733346171009)
        ·
          refine ⟨11266865831059300009628257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15022487774745733346171009 11266865831059300009628257)
          ·
            refine ⟨8450149373294475007221193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11266865831059300009628257 8450149373294475007221193)
            ·
              refine ⟨6337612029970856255415895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8450149373294475007221193 6337612029970856255415895)
              ·
                refine ⟨9506418044956284383123843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6337612029970856255415895 9506418044956284383123843)
                ·
                  refine ⟨14259627067434426574685765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9506418044956284383123843 14259627067434426574685765)
                  ·
                    refine ⟨2673680075143954982753581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14259627067434426574685765 2673680075143954982753581)
                    ·
                      refine ⟨1002630028178983118532593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2673680075143954982753581 1002630028178983118532593)
                      ·
                        rfl

theorem cell23_1952615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1952615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952615 prefixEnd_1952615 := by exact prefixLift 1952615
  have htrace : WordTrace (prefixWord ++ tailWord_1952615) baseStart_1952615 baseEnd_1952615 := by
    simpa [prefixWord, tailWord_1952615, baseEnd_1952615] using wordTrace_append hprefix tailTrace_1952615
  have hstable : (prefixWord ++ tailWord_1952615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952615).length < 2 ^ (prefixWord ++ tailWord_1952615).sum := by decide
  have hdescent : baseEnd_1952615 < baseStart_1952615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952672 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 2, 3, 2]
def baseStart_1952672 : Nat := 118140960795 + 1952672 * 2 ^ 59
def prefixEnd_1952672 : Nat := 4983230072969 + 3 ^ 40 * 1952672 * 2
def baseEnd_1952672 : Nat := 1002659296576289395519831

theorem tailTrace_1952672 : CollatzResearch.WordTrace tailWord_1952672 prefixEnd_1952672 1002659296576289395519831 := by
  unfold tailWord_1952672
  simp only [CollatzResearch.WordTrace]
  refine ⟨35609899390905154336114135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47479865854540205781485513 35609899390905154336114135)
  ·
    refine ⟨53414849086357731504171203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35609899390905154336114135 53414849086357731504171203)
    ·
      refine ⟨80122273629536597256256805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53414849086357731504171203 80122273629536597256256805)
      ·
        refine ⟨15022926305538111985548151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80122273629536597256256805 15022926305538111985548151)
        ·
          refine ⟨22534389458307167978322227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15022926305538111985548151 22534389458307167978322227)
          ·
            refine ⟨33801584187460751967483341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22534389458307167978322227 33801584187460751967483341)
            ·
              refine ⟨12675594070297781987806253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33801584187460751967483341 12675594070297781987806253)
              ·
                refine ⟨4753347776361668245427345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12675594070297781987806253 4753347776361668245427345)
                ·
                  refine ⟨3565010832271251184070509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4753347776361668245427345 3565010832271251184070509)
                  ·
                    refine ⟨1336879062101719194026441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565010832271251184070509 1336879062101719194026441)
                    ·
                      refine ⟨1002659296576289395519831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336879062101719194026441 1002659296576289395519831)
                      ·
                        rfl

theorem cell23_1952672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_1952672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952672 prefixEnd_1952672 := by exact prefixLift 1952672
  have htrace : WordTrace (prefixWord ++ tailWord_1952672) baseStart_1952672 baseEnd_1952672 := by
    simpa [prefixWord, tailWord_1952672, baseEnd_1952672] using wordTrace_append hprefix tailTrace_1952672
  have hstable : (prefixWord ++ tailWord_1952672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952672).length < 2 ^ (prefixWord ++ tailWord_1952672).sum := by decide
  have hdescent : baseEnd_1952672 < baseStart_1952672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952695 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 4, 4]
def baseStart_1952695 : Nat := 118140960795 + 1952695 * 2 ^ 59
def prefixEnd_1952695 : Nat := 4983230072969 + 3 ^ 40 * 1952695 * 2
def baseEnd_1952695 : Nat := 334223702210447601844075

theorem tailTrace_1952695 : CollatzResearch.WordTrace tailWord_1952695 prefixEnd_1952695 334223702210447601844075 := by
  unfold tailWord_1952695
  simp only [CollatzResearch.WordTrace]
  refine ⟨71220637660726983600315539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47480425107151322400210359 71220637660726983600315539)
  ·
    refine ⟨106830956491090475400473309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71220637660726983600315539 106830956491090475400473309)
    ·
      refine ⟨40061608684158928275177491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106830956491090475400473309 40061608684158928275177491)
      ·
        refine ⟨60092413026238392412766237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40061608684158928275177491 60092413026238392412766237)
        ·
          refine ⟨22534654884839397154787339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60092413026238392412766237 22534654884839397154787339)
          ·
            refine ⟨33801982327259095732181009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22534654884839397154787339 33801982327259095732181009)
            ·
              refine ⟨25351486745444321799135757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33801982327259095732181009 25351486745444321799135757)
              ·
                refine ⟨9506807529541620674675909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25351486745444321799135757 9506807529541620674675909)
                ·
                  refine ⟨1782526411789053876501733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9506807529541620674675909 1782526411789053876501733)
                  ·
                    refine ⟨334223702210447601844075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1782526411789053876501733 334223702210447601844075)
                    ·
                      rfl

theorem cell23_1952695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_1952695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952695 prefixEnd_1952695 := by exact prefixLift 1952695
  have htrace : WordTrace (prefixWord ++ tailWord_1952695) baseStart_1952695 baseEnd_1952695 := by
    simpa [prefixWord, tailWord_1952695, baseEnd_1952695] using wordTrace_append hprefix tailTrace_1952695
  have hstable : (prefixWord ++ tailWord_1952695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952695).length < 2 ^ (prefixWord ++ tailWord_1952695).sum := by decide
  have hdescent : baseEnd_1952695 < baseStart_1952695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952696 : List Nat := [2, 1, 2, 1, 2, 4, 4, 2, 1, 1, 3]
def baseStart_1952696 : Nat := 118140960795 + 1952696 * 2 ^ 59
def prefixEnd_1952696 : Nat := 4983230072969 + 3 ^ 40 * 1952696 * 2
def baseEnd_1952696 : Nat := 1002671620111997301619721

theorem tailTrace_1952696 : CollatzResearch.WordTrace tailWord_1952696 prefixEnd_1952696 1002671620111997301619721 := by
  unfold tailWord_1952696
  simp only [CollatzResearch.WordTrace]
  refine ⟨35610337066861680385550971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47480449422482240514067961 35610337066861680385550971)
  ·
    refine ⟨53415505600292520578326457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35610337066861680385550971 53415505600292520578326457)
    ·
      refine ⟨40061629200219390433744843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53415505600292520578326457 40061629200219390433744843)
      ·
        refine ⟨60092443800329085650617265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40061629200219390433744843 60092443800329085650617265)
        ·
          refine ⟨45069332850246814237962949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60092443800329085650617265 45069332850246814237962949)
          ·
            refine ⟨8450499909421277669618053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45069332850246814237962949 8450499909421277669618053)
            ·
              refine ⟨1584468733016489563053385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8450499909421277669618053 1584468733016489563053385)
              ·
                refine ⟨1188351549762367172290039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1584468733016489563053385 1188351549762367172290039)
                ·
                  refine ⟨1782527324643550758435059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188351549762367172290039 1782527324643550758435059)
                  ·
                    refine ⟨2673790986965326137652589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1782527324643550758435059 2673790986965326137652589)
                    ·
                      refine ⟨1002671620111997301619721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2673790986965326137652589 1002671620111997301619721)
                      ·
                        rfl

theorem cell23_1952696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 1, 1, 3].length) (baseStart_1952696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952696 prefixEnd_1952696 := by exact prefixLift 1952696
  have htrace : WordTrace (prefixWord ++ tailWord_1952696) baseStart_1952696 baseEnd_1952696 := by
    simpa [prefixWord, tailWord_1952696, baseEnd_1952696] using wordTrace_append hprefix tailTrace_1952696
  have hstable : (prefixWord ++ tailWord_1952696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952696).length < 2 ^ (prefixWord ++ tailWord_1952696).sum := by decide
  have hdescent : baseEnd_1952696 < baseStart_1952696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952712 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 1, 6]
def baseStart_1952712 : Nat := 118140960795 + 1952712 * 2 ^ 59
def prefixEnd_1952712 : Nat := 4983230072969 + 3 ^ 40 * 1952712 * 2
def baseEnd_1952712 : Nat := 334226611934156413006549

theorem tailTrace_1952712 : CollatzResearch.WordTrace tailWord_1952712 prefixEnd_1952712 334226611934156413006549 := by
  unfold tailWord_1952712
  simp only [CollatzResearch.WordTrace]
  refine ⟨35610628850832697751842195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47480838467776930335789593 35610628850832697751842195)
  ·
    refine ⟨53415943276249046627763293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35610628850832697751842195 53415943276249046627763293)
    ·
      refine ⟨20030978728593392485411235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53415943276249046627763293 20030978728593392485411235)
      ·
        refine ⟨30046468092890088728116853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20030978728593392485411235 30046468092890088728116853)
        ·
          refine ⟨2816856383708445818260955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30046468092890088728116853 2816856383708445818260955)
          ·
            refine ⟨4225284575562668727391433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2816856383708445818260955 4225284575562668727391433)
            ·
              refine ⟨3168963431672001545543575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4225284575562668727391433 3168963431672001545543575)
              ·
                refine ⟨4753445147508002318315363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3168963431672001545543575 4753445147508002318315363)
                ·
                  refine ⟨7130167721262003477473045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753445147508002318315363 7130167721262003477473045)
                  ·
                    refine ⟨334226611934156413006549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7130167721262003477473045 334226611934156413006549)
                    ·
                      rfl

theorem cell23_1952712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_1952712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952712 prefixEnd_1952712 := by exact prefixLift 1952712
  have htrace : WordTrace (prefixWord ++ tailWord_1952712) baseStart_1952712 baseEnd_1952712 := by
    simpa [prefixWord, tailWord_1952712, baseEnd_1952712] using wordTrace_append hprefix tailTrace_1952712
  have hstable : (prefixWord ++ tailWord_1952712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952712).length < 2 ^ (prefixWord ++ tailWord_1952712).sum := by decide
  have hdescent : baseEnd_1952712 < baseStart_1952712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952715 : List Nat := [1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 4]
def baseStart_1952715 : Nat := 118140960795 + 1952715 * 2 ^ 59
def prefixEnd_1952715 : Nat := 4983230072969 + 3 ^ 40 * 1952715 * 2
def baseEnd_1952715 : Nat := 1002681376244432727282133

theorem tailTrace_1952715 : CollatzResearch.WordTrace tailWord_1952715 prefixEnd_1952715 1002681376244432727282133 := by
  unfold tailWord_1952715
  simp only [CollatzResearch.WordTrace]
  refine ⟨71221367120654527016043599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47480911413769684677362399 71221367120654527016043599)
  ·
    refine ⟨106832050680981790524065399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71221367120654527016043599 106832050680981790524065399)
    ·
      refine ⟨160248076021472685786098099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106832050680981790524065399 160248076021472685786098099)
      ·
        refine ⟨240372114032209028679147149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160248076021472685786098099 240372114032209028679147149)
        ·
          refine ⟨90139542762078385754680181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240372114032209028679147149 90139542762078385754680181)
          ·
            refine ⟨8450582133944848664501267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90139542762078385754680181 8450582133944848664501267)
            ·
              refine ⟨12675873200917272996751901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8450582133944848664501267 12675873200917272996751901)
              ·
                refine ⟨4753452450343977373781963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12675873200917272996751901 4753452450343977373781963)
                ·
                  refine ⟨7130178675515966060672945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753452450343977373781963 7130178675515966060672945)
                  ·
                    refine ⟨5347634006636974545504709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7130178675515966060672945 5347634006636974545504709)
                    ·
                      refine ⟨1002681376244432727282133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5347634006636974545504709 1002681376244432727282133)
                      ·
                        rfl

theorem cell23_1952715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 4].length) (baseStart_1952715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952715 prefixEnd_1952715 := by exact prefixLift 1952715
  have htrace : WordTrace (prefixWord ++ tailWord_1952715) baseStart_1952715 baseEnd_1952715 := by
    simpa [prefixWord, tailWord_1952715, baseEnd_1952715] using wordTrace_append hprefix tailTrace_1952715
  have hstable : (prefixWord ++ tailWord_1952715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952715).length < 2 ^ (prefixWord ++ tailWord_1952715).sum := by decide
  have hdescent : baseEnd_1952715 < baseStart_1952715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952719 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 3, 2, 2]
def baseStart_1952719 : Nat := 118140960795 + 1952719 * 2 ^ 59
def prefixEnd_1952719 : Nat := 4983230072969 + 3 ^ 40 * 1952719 * 2
def baseEnd_1952719 : Nat := 1002683430167050711632115

theorem tailTrace_1952719 : CollatzResearch.WordTrace tailWord_1952719 prefixEnd_1952719 1002683430167050711632115 := by
  unfold tailWord_1952719
  simp only [CollatzResearch.WordTrace]
  refine ⟨71221513012640035699189211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47481008675093357132792807 71221513012640035699189211)
  ·
    refine ⟨106832269518960053548783817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71221513012640035699189211 106832269518960053548783817)
    ·
      refine ⟨80124202139220040161587863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106832269518960053548783817 80124202139220040161587863)
      ·
        refine ⟨120186303208830060242381795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80124202139220040161587863 120186303208830060242381795)
        ·
          refine ⟨180279454813245090363572693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120186303208830060242381795 180279454813245090363572693)
          ·
            refine ⟨4225299722185431805396235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 180279454813245090363572693 4225299722185431805396235)
            ·
              refine ⟨6337949583278147708094353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225299722185431805396235 6337949583278147708094353)
              ·
                refine ⟨4753462187458610781070765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6337949583278147708094353 4753462187458610781070765)
                ·
                  refine ⟨1782548320296979042901537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4753462187458610781070765 1782548320296979042901537)
                  ·
                    refine ⟨1336911240222734282176153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1782548320296979042901537 1336911240222734282176153)
                    ·
                      refine ⟨1002683430167050711632115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336911240222734282176153 1002683430167050711632115)
                      ·
                        rfl

theorem cell23_1952719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 2, 2].length) (baseStart_1952719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952719 prefixEnd_1952719 := by exact prefixLift 1952719
  have htrace : WordTrace (prefixWord ++ tailWord_1952719) baseStart_1952719 baseEnd_1952719 := by
    simpa [prefixWord, tailWord_1952719, baseEnd_1952719] using wordTrace_append hprefix tailTrace_1952719
  have hstable : (prefixWord ++ tailWord_1952719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952719).length < 2 ^ (prefixWord ++ tailWord_1952719).sum := by decide
  have hdescent : baseEnd_1952719 < baseStart_1952719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952762 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2]
def baseStart_1952762 : Nat := 118140960795 + 1952762 * 2 ^ 59
def prefixEnd_1952762 : Nat := 4983230072969 + 3 ^ 40 * 1952762 * 2
def baseEnd_1952762 : Nat := 1002705509835194043394417

theorem tailTrace_1952762 : CollatzResearch.WordTrace tailWord_1952762 prefixEnd_1952762 1002705509835194043394417 := by
  unfold tailWord_1952762
  simp only [CollatzResearch.WordTrace]
  refine ⟨17805770337871063510751135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47482054234322836028669693 17805770337871063510751135)
  ·
    refine ⟨26708655506806595266126703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17805770337871063510751135 26708655506806595266126703)
    ·
      refine ⟨40062983260209892899190055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26708655506806595266126703 40062983260209892899190055)
      ·
        refine ⟨60094474890314839348785083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40062983260209892899190055 60094474890314839348785083)
        ·
          refine ⟨90141712335472259023177625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60094474890314839348785083 90141712335472259023177625)
          ·
            refine ⟨67606284251604194267383219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90141712335472259023177625 67606284251604194267383219)
            ·
              refine ⟨101409426377406291401074829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67606284251604194267383219 101409426377406291401074829)
              ·
                refine ⟨38028534891527359275403061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101409426377406291401074829 38028534891527359275403061)
                ·
                  refine ⟨3565175146080689932069037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38028534891527359275403061 3565175146080689932069037)
                  ·
                    refine ⟨1336940679780258724525889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565175146080689932069037 1336940679780258724525889)
                    ·
                      refine ⟨1002705509835194043394417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336940679780258724525889 1002705509835194043394417)
                      ·
                        rfl

theorem cell23_1952762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_1952762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952762 prefixEnd_1952762 := by exact prefixLift 1952762
  have htrace : WordTrace (prefixWord ++ tailWord_1952762) baseStart_1952762 baseEnd_1952762 := by
    simpa [prefixWord, tailWord_1952762, baseEnd_1952762] using wordTrace_append hprefix tailTrace_1952762
  have hstable : (prefixWord ++ tailWord_1952762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952762).length < 2 ^ (prefixWord ++ tailWord_1952762).sum := by decide
  have hdescent : baseEnd_1952762 < baseStart_1952762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952766 : List Nat := [4, 2, 2, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1952766 : Nat := 118140960795 + 1952766 * 2 ^ 59
def prefixEnd_1952766 : Nat := 4983230072969 + 3 ^ 40 * 1952766 * 2
def baseEnd_1952766 : Nat := 1002707563757812027744399

theorem tailTrace_1952766 : CollatzResearch.WordTrace tailWord_1952766 prefixEnd_1952766 1002707563757812027744399 := by
  unfold tailWord_1952766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8902903405433720340768769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47482151495646508484100101 8902903405433720340768769)
  ·
    refine ⟨6677177554075290255576577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8902903405433720340768769 6677177554075290255576577)
    ·
      refine ⟨5007883165556467691682433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6677177554075290255576577 5007883165556467691682433)
      ·
        refine ⟨3755912374167350768761825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5007883165556467691682433 3755912374167350768761825)
        ·
          refine ⟨2816934280625513076571369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3755912374167350768761825 2816934280625513076571369)
          ·
            refine ⟨2112700710469134807428527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2816934280625513076571369 2112700710469134807428527)
            ·
              refine ⟨3169051065703702211142791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112700710469134807428527 3169051065703702211142791)
              ·
                refine ⟨4753576598555553316714187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169051065703702211142791 4753576598555553316714187)
                ·
                  refine ⟨7130364897833329975071281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753576598555553316714187 7130364897833329975071281)
                  ·
                    refine ⟨5347773673374997481303461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7130364897833329975071281 5347773673374997481303461)
                    ·
                      refine ⟨1002707563757812027744399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5347773673374997481303461 1002707563757812027744399)
                      ·
                        rfl

theorem cell23_1952766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1952766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952766 prefixEnd_1952766 := by exact prefixLift 1952766
  have htrace : WordTrace (prefixWord ++ tailWord_1952766) baseStart_1952766 baseEnd_1952766 := by
    simpa [prefixWord, tailWord_1952766, baseEnd_1952766] using wordTrace_append hprefix tailTrace_1952766
  have hstable : (prefixWord ++ tailWord_1952766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952766).length < 2 ^ (prefixWord ++ tailWord_1952766).sum := by decide
  have hdescent : baseEnd_1952766 < baseStart_1952766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952769 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_1952769 : Nat := 118140960795 + 1952769 * 2 ^ 59
def prefixEnd_1952769 : Nat := 4983230072969 + 3 ^ 40 * 1952769 * 2
def baseEnd_1952769 : Nat := 1002709104199775516006885

theorem tailTrace_1952769 : CollatzResearch.WordTrace tailWord_1952769 prefixEnd_1952769 1002709104199775516006885 := by
  unfold tailWord_1952769
  simp only [CollatzResearch.WordTrace]
  refine ⟨71223336662458894238509361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47482224441639262825672907 71223336662458894238509361)
  ·
    refine ⟨53417502496844170678882021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71223336662458894238509361 53417502496844170678882021)
    ·
      refine ⟨10015781718158282002290379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53417502496844170678882021 10015781718158282002290379)
      ·
        refine ⟨15023672577237423003435569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10015781718158282002290379 15023672577237423003435569)
        ·
          refine ⟨11267754432928067252576677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15023672577237423003435569 11267754432928067252576677)
          ·
            refine ⟨2112703956174012609858127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11267754432928067252576677 2112703956174012609858127)
            ·
              refine ⟨3169055934261018914787191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112703956174012609858127 3169055934261018914787191)
              ·
                refine ⟨4753583901391528372180787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169055934261018914787191 4753583901391528372180787)
                ·
                  refine ⟨7130375852087292558271181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4753583901391528372180787 7130375852087292558271181)
                  ·
                    refine ⟨2673890944532734709351693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7130375852087292558271181 2673890944532734709351693)
                    ·
                      refine ⟨1002709104199775516006885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2673890944532734709351693 1002709104199775516006885)
                      ·
                        rfl

theorem cell23_1952769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_1952769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952769 prefixEnd_1952769 := by exact prefixLift 1952769
  have htrace : WordTrace (prefixWord ++ tailWord_1952769) baseStart_1952769 baseEnd_1952769 := by
    simpa [prefixWord, tailWord_1952769, baseEnd_1952769] using wordTrace_append hprefix tailTrace_1952769
  have hstable : (prefixWord ++ tailWord_1952769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952769).length < 2 ^ (prefixWord ++ tailWord_1952769).sum := by decide
  have hdescent : baseEnd_1952769 < baseStart_1952769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952779 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 1, 3, 2]
def baseStart_1952779 : Nat := 118140960795 + 1952779 * 2 ^ 59
def prefixEnd_1952779 : Nat := 4983230072969 + 3 ^ 40 * 1952779 * 2
def baseEnd_1952779 : Nat := 1002714239006320476881839

theorem tailTrace_1952779 : CollatzResearch.WordTrace tailWord_1952779 prefixEnd_1952779 1002714239006320476881839 := by
  unfold tailWord_1952779
  simp only [CollatzResearch.WordTrace]
  refine ⟨71223701392422665946373391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47482467594948443964248927 71223701392422665946373391)
  ·
    refine ⟨106835552088633998919560087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71223701392422665946373391 106835552088633998919560087)
    ·
      refine ⟨160253328132950998379340131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106835552088633998919560087 160253328132950998379340131)
      ·
        refine ⟨240379992199426497569010197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160253328132950998379340131 240379992199426497569010197)
        ·
          refine ⟨11267812134348117073547353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 240379992199426497569010197 11267812134348117073547353)
          ·
            refine ⟨8450859100761087805160515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11267812134348117073547353 8450859100761087805160515)
            ·
              refine ⟨12676288651141631707740773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8450859100761087805160515 12676288651141631707740773)
              ·
                refine ⟨2376804122089055945201395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12676288651141631707740773 2376804122089055945201395)
                ·
                  refine ⟨3565206183133583917802093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2376804122089055945201395 3565206183133583917802093)
                  ·
                    refine ⟨1336952318675093969175785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3565206183133583917802093 1336952318675093969175785)
                    ·
                      refine ⟨1002714239006320476881839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1336952318675093969175785 1002714239006320476881839)
                      ·
                        rfl

theorem cell23_1952779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 3, 2].length) (baseStart_1952779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952779 prefixEnd_1952779 := by exact prefixLift 1952779
  have htrace : WordTrace (prefixWord ++ tailWord_1952779) baseStart_1952779 baseEnd_1952779 := by
    simpa [prefixWord, tailWord_1952779, baseEnd_1952779] using wordTrace_append hprefix tailTrace_1952779
  have hstable : (prefixWord ++ tailWord_1952779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952779).length < 2 ^ (prefixWord ++ tailWord_1952779).sum := by decide
  have hdescent : baseEnd_1952779 < baseStart_1952779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952820 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 2, 1, 3]
def baseStart_1952820 : Nat := 118140960795 + 1952820 * 2 ^ 59
def prefixEnd_1952820 : Nat := 4983230072969 + 3 ^ 40 * 1952820 * 2
def baseEnd_1952820 : Nat := 1002735291713154816469151

theorem tailTrace_1952820 : CollatzResearch.WordTrace tailWord_1952820 prefixEnd_1952820 1002735291713154816469151 := by
  unfold tailWord_1952820
  simp only [CollatzResearch.WordTrace]
  refine ⟨35612598392637064974307957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47483464523516086632410609 35612598392637064974307957)
  ·
    refine ⟨3338681099309724841341371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35612598392637064974307957 3338681099309724841341371)
    ·
      refine ⟨5008021648964587262012057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3338681099309724841341371 5008021648964587262012057)
      ·
        refine ⟨3756016236723440446509043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5008021648964587262012057 3756016236723440446509043)
        ·
          refine ⟨5634024355085160669763565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756016236723440446509043 5634024355085160669763565)
          ·
            refine ⟨2112759133156935251161337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5634024355085160669763565 2112759133156935251161337)
            ·
              refine ⟨1584569349867701438371003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2112759133156935251161337 1584569349867701438371003)
              ·
                refine ⟨2376854024801552157556505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584569349867701438371003 2376854024801552157556505)
                ·
                  refine ⟨1782640518601164118167379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2376854024801552157556505 1782640518601164118167379)
                  ·
                    refine ⟨2673960777901746177251069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1782640518601164118167379 2673960777901746177251069)
                    ·
                      refine ⟨1002735291713154816469151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2673960777901746177251069 1002735291713154816469151)
                      ·
                        rfl

theorem cell23_1952820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_1952820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952820 prefixEnd_1952820 := by exact prefixLift 1952820
  have htrace : WordTrace (prefixWord ++ tailWord_1952820) baseStart_1952820 baseEnd_1952820 := by
    simpa [prefixWord, tailWord_1952820, baseEnd_1952820] using wordTrace_append hprefix tailTrace_1952820
  have hstable : (prefixWord ++ tailWord_1952820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952820).length < 2 ^ (prefixWord ++ tailWord_1952820).sum := by decide
  have hdescent : baseEnd_1952820 < baseStart_1952820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952866 : List Nat := [3, 3, 2, 2, 1, 2, 1, 4, 5]
def baseStart_1952866 : Nat := 118140960795 + 1952866 * 2 ^ 59
def prefixEnd_1952866 : Nat := 4983230072969 + 3 ^ 40 * 1952866 * 2
def baseEnd_1952866 : Nat := 111417656869251292943771

theorem tailTrace_1952866 : CollatzResearch.WordTrace tailWord_1952866 prefixEnd_1952866 111417656869251292943771 := by
  unfold tailWord_1952866
  simp only [CollatzResearch.WordTrace]
  refine ⟨17806718635776869951197613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47484583028738319869860301 17806718635776869951197613)
  ·
    refine ⟨6677519488416326231699105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17806718635776869951197613 6677519488416326231699105)
    ·
      refine ⟨5008139616312244673774329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6677519488416326231699105 5008139616312244673774329)
      ·
        refine ⟨3756104712234183505330747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5008139616312244673774329 3756104712234183505330747)
        ·
          refine ⟨5634157068351275257996121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756104712234183505330747 5634157068351275257996121)
          ·
            refine ⟨4225617801263456443497091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5634157068351275257996121 4225617801263456443497091)
            ·
              refine ⟨6338426701895184665245637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4225617801263456443497091 6338426701895184665245637)
              ·
                refine ⟨1188455006605347124733557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6338426701895184665245637 1188455006605347124733557)
                ·
                  refine ⟨111417656869251292943771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188455006605347124733557 111417656869251292943771)
                  ·
                    rfl

theorem cell23_1952866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_1952866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952866 prefixEnd_1952866 := by exact prefixLift 1952866
  have htrace : WordTrace (prefixWord ++ tailWord_1952866) baseStart_1952866 baseEnd_1952866 := by
    simpa [prefixWord, tailWord_1952866, baseEnd_1952866] using wordTrace_append hprefix tailTrace_1952866
  have hstable : (prefixWord ++ tailWord_1952866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952866).length < 2 ^ (prefixWord ++ tailWord_1952866).sum := by decide
  have hdescent : baseEnd_1952866 < baseStart_1952866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952882 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1952882 : Nat := 118140960795 + 1952882 * 2 ^ 59
def prefixEnd_1952882 : Nat := 4983230072969 + 3 ^ 40 * 1952882 * 2
def baseEnd_1952882 : Nat := 1002767127513733573893865

theorem tailTrace_1952882 : CollatzResearch.WordTrace tailWord_1952882 prefixEnd_1952882 1002767127513733573893865 := by
  unfold tailWord_1952882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17806864527762378634343225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47484972074033009691581933 17806864527762378634343225)
  ·
    refine ⟨13355148395821783975757419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17806864527762378634343225 13355148395821783975757419)
    ·
      refine ⟨20032722593732675963636129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13355148395821783975757419 20032722593732675963636129)
      ·
        refine ⟨15024541945299506972727097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20032722593732675963636129 15024541945299506972727097)
        ·
          refine ⟨11268406458974630229545323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15024541945299506972727097 11268406458974630229545323)
          ·
            refine ⟨16902609688461945344317985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11268406458974630229545323 16902609688461945344317985)
            ·
              refine ⟨12676957266346459008238489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16902609688461945344317985 12676957266346459008238489)
              ·
                refine ⟨9507717949759844256178867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12676957266346459008238489 9507717949759844256178867)
                ·
                  refine ⟨14261576924639766384268301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9507717949759844256178867 14261576924639766384268301)
                  ·
                    refine ⟨5348091346739912394100613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14261576924639766384268301 5348091346739912394100613)
                    ·
                      refine ⟨1002767127513733573893865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5348091346739912394100613 1002767127513733573893865)
                      ·
                        rfl

theorem cell23_1952882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1952882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952882 prefixEnd_1952882 := by exact prefixLift 1952882
  have htrace : WordTrace (prefixWord ++ tailWord_1952882) baseStart_1952882 baseEnd_1952882 := by
    simpa [prefixWord, tailWord_1952882, baseEnd_1952882] using wordTrace_append hprefix tailTrace_1952882
  have hstable : (prefixWord ++ tailWord_1952882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952882).length < 2 ^ (prefixWord ++ tailWord_1952882).sum := by decide
  have hdescent : baseEnd_1952882 < baseStart_1952882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952895 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 6]
def baseStart_1952895 : Nat := 118140960795 + 1952895 * 2 ^ 59
def prefixEnd_1952895 : Nat := 4983230072969 + 3 ^ 40 * 1952895 * 2
def baseEnd_1952895 : Nat := 1002773802762242023031305

theorem tailTrace_1952895 : CollatzResearch.WordTrace tailWord_1952895 prefixEnd_1952895 1002773802762242023031305 := by
  unfold tailWord_1952895
  simp only [CollatzResearch.WordTrace]
  refine ⟨71227932260002417757596139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47485288173334945171730759 71227932260002417757596139)
  ·
    refine ⟨106841898390003626636394209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71227932260002417757596139 106841898390003626636394209)
    ·
      refine ⟨80131423792502719977295657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106841898390003626636394209 80131423792502719977295657)
      ·
        refine ⟨60098567844377039982971743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80131423792502719977295657 60098567844377039982971743)
        ·
          refine ⟨90147851766565559974457615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60098567844377039982971743 90147851766565559974457615)
          ·
            refine ⟨135221777649848339961686423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90147851766565559974457615 135221777649848339961686423)
            ·
              refine ⟨202832666474772509942529635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135221777649848339961686423 202832666474772509942529635)
              ·
                refine ⟨304248999712158764913794453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202832666474772509942529635 304248999712158764913794453)
                ·
                  refine ⟨14261671861507442105334115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 304248999712158764913794453 14261671861507442105334115)
                  ·
                    refine ⟨21392507792261163158001173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14261671861507442105334115 21392507792261163158001173)
                    ·
                      refine ⟨1002773802762242023031305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21392507792261163158001173 1002773802762242023031305)
                      ·
                        rfl

theorem cell23_1952895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_1952895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952895 prefixEnd_1952895 := by exact prefixLift 1952895
  have htrace : WordTrace (prefixWord ++ tailWord_1952895) baseStart_1952895 baseEnd_1952895 := by
    simpa [prefixWord, tailWord_1952895, baseEnd_1952895] using wordTrace_append hprefix tailTrace_1952895
  have hstable : (prefixWord ++ tailWord_1952895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952895).length < 2 ^ (prefixWord ++ tailWord_1952895).sum := by decide
  have hdescent : baseEnd_1952895 < baseStart_1952895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952926 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_1952926 : Nat := 118140960795 + 1952926 * 2 ^ 59
def prefixEnd_1952926 : Nat := 4983230072969 + 3 ^ 40 * 1952926 * 2
def baseEnd_1952926 : Nat := 334263240220843800581221

theorem tailTrace_1952926 : CollatzResearch.WordTrace tailWord_1952926 prefixEnd_1952926 334263240220843800581221 := by
  unfold tailWord_1952926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903632865361263756496829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47486041948593406701316421 8903632865361263756496829)
  ·
    refine ⟨3338862324510473908686311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8903632865361263756496829 3338862324510473908686311)
    ·
      refine ⟨5008293486765710863029467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3338862324510473908686311 5008293486765710863029467)
      ·
        refine ⟨7512440230148566294544201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5008293486765710863029467 7512440230148566294544201)
        ·
          refine ⟨5634330172611424720908151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7512440230148566294544201 5634330172611424720908151)
          ·
            refine ⟨8451495258917137081362227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5634330172611424720908151 8451495258917137081362227)
            ·
              refine ⟨12677242888375705622043341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8451495258917137081362227 12677242888375705622043341)
              ·
                refine ⟨4753966083140889608266253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12677242888375705622043341 4753966083140889608266253)
                ·
                  refine ⟨1782737281177833603099845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4753966083140889608266253 1782737281177833603099845)
                  ·
                    refine ⟨334263240220843800581221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1782737281177833603099845 334263240220843800581221)
                    ·
                      rfl

theorem cell23_1952926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_1952926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952926 prefixEnd_1952926 := by exact prefixLift 1952926
  have htrace : WordTrace (prefixWord ++ tailWord_1952926) baseStart_1952926 baseEnd_1952926 := by
    simpa [prefixWord, tailWord_1952926, baseEnd_1952926] using wordTrace_append hprefix tailTrace_1952926
  have hstable : (prefixWord ++ tailWord_1952926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952926).length < 2 ^ (prefixWord ++ tailWord_1952926).sum := by decide
  have hdescent : baseEnd_1952926 < baseStart_1952926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952959 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 1, 5, 2]
def baseStart_1952959 : Nat := 118140960795 + 1952959 * 2 ^ 59
def prefixEnd_1952959 : Nat := 4983230072969 + 3 ^ 40 * 1952959 * 2
def baseEnd_1952959 : Nat := 1002806665524129772631011

theorem tailTrace_1952959 : CollatzResearch.WordTrace tailWord_1952959 prefixEnd_1952959 1002806665524129772631011 := by
  unfold tailWord_1952959
  simp only [CollatzResearch.WordTrace]
  refine ⟨71230266531770556687925931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47486844354513704458617287 71230266531770556687925931)
  ·
    refine ⟨106845399797655835031888897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71230266531770556687925931 106845399797655835031888897)
    ·
      refine ⟨80134049848241876273916673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106845399797655835031888897 80134049848241876273916673)
      ·
        refine ⟨60100537386181407205437505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80134049848241876273916673 60100537386181407205437505)
        ·
          refine ⟨45075403039636055404078129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60100537386181407205437505 45075403039636055404078129)
          ·
            refine ⟨33806552279727041553058597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45075403039636055404078129 33806552279727041553058597)
            ·
              refine ⟨6338728552448820291198487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33806552279727041553058597 6338728552448820291198487)
              ·
                refine ⟨9508092828673230436797731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6338728552448820291198487 9508092828673230436797731)
                ·
                  refine ⟨14262139243009845655196597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9508092828673230436797731 14262139243009845655196597)
                  ·
                    refine ⟨1337075554032173030174681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14262139243009845655196597 1337075554032173030174681)
                    ·
                      refine ⟨1002806665524129772631011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337075554032173030174681 1002806665524129772631011)
                      ·
                        rfl

theorem cell23_1952959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_1952959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952959 prefixEnd_1952959 := by exact prefixLift 1952959
  have htrace : WordTrace (prefixWord ++ tailWord_1952959) baseStart_1952959 baseEnd_1952959 := by
    simpa [prefixWord, tailWord_1952959, baseEnd_1952959] using wordTrace_append hprefix tailTrace_1952959
  have hstable : (prefixWord ++ tailWord_1952959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952959).length < 2 ^ (prefixWord ++ tailWord_1952959).sum := by decide
  have hdescent : baseEnd_1952959 < baseStart_1952959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1952960 : List Nat := [2, 1, 1, 2, 7, 1, 1, 3, 1, 4]
def baseStart_1952960 : Nat := 118140960795 + 1952960 * 2 ^ 59
def prefixEnd_1952960 : Nat := 4983230072969 + 3 ^ 40 * 1952960 * 2
def baseEnd_1952960 : Nat := 334269059668261422906169

theorem tailTrace_1952960 : CollatzResearch.WordTrace tailWord_1952960 prefixEnd_1952960 334269059668261422906169 := by
  unfold tailWord_1952960
  simp only [CollatzResearch.WordTrace]
  refine ⟨35615151502383466929356167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47486868669844622572474889 35615151502383466929356167)
  ·
    refine ⟨53422727253575200394034251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35615151502383466929356167 53422727253575200394034251)
    ·
      refine ⟨80134090880362800591051377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53422727253575200394034251 80134090880362800591051377)
      ·
        refine ⟨60100568160272100443288533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80134090880362800591051377 60100568160272100443288533)
        ·
          refine ⟨1408607066256377354139575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 60100568160272100443288533 1408607066256377354139575)
          ·
            refine ⟨2112910599384566031209363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1408607066256377354139575 2112910599384566031209363)
            ·
              refine ⟨3169365899076849046814045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2112910599384566031209363 3169365899076849046814045)
              ·
                refine ⟨1188512212153818392555267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3169365899076849046814045 1188512212153818392555267)
                ·
                  refine ⟨1782768318230727588832901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188512212153818392555267 1782768318230727588832901)
                  ·
                    refine ⟨334269059668261422906169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1782768318230727588832901 334269059668261422906169)
                    ·
                      rfl

theorem cell23_1952960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 1, 4].length) (baseStart_1952960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1952960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1952960 prefixEnd_1952960 := by exact prefixLift 1952960
  have htrace : WordTrace (prefixWord ++ tailWord_1952960) baseStart_1952960 baseEnd_1952960 := by
    simpa [prefixWord, tailWord_1952960, baseEnd_1952960] using wordTrace_append hprefix tailTrace_1952960
  have hstable : (prefixWord ++ tailWord_1952960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1952960).length < 2 ^ (prefixWord ++ tailWord_1952960).sum := by decide
  have hdescent : baseEnd_1952960 < baseStart_1952960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1952960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953006 : List Nat := [4, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4]
def baseStart_1953006 : Nat := 118140960795 + 1953006 * 2 ^ 59
def prefixEnd_1953006 : Nat := 4983230072969 + 3 ^ 40 * 1953006 * 2
def baseEnd_1953006 : Nat := 1002830799114891088743295

theorem tailTrace_1953006 : CollatzResearch.WordTrace tailWord_1953006 prefixEnd_1953006 1002830799114891088743295 := by
  unfold tailWord_1953006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8903997595325035464360859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47487987175066855809924581 8903997595325035464360859)
  ·
    refine ⟨13355996392987553196541289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8903997595325035464360859 13355996392987553196541289)
    ·
      refine ⟨10016997294740664897405967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13355996392987553196541289 10016997294740664897405967)
      ·
        refine ⟨15025495942110997346108951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10016997294740664897405967 15025495942110997346108951)
        ·
          refine ⟨22538243913166496019163427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15025495942110997346108951 22538243913166496019163427)
          ·
            refine ⟨33807365869749744028745141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22538243913166496019163427 33807365869749744028745141)
            ·
              refine ⟨3169440550289038502694857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33807365869749744028745141 3169440550289038502694857)
              ·
                refine ⟨2377080412716778877021143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3169440550289038502694857 2377080412716778877021143)
                ·
                  refine ⟨3565620619075168315531715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377080412716778877021143 3565620619075168315531715)
                  ·
                    refine ⟨5348430928612752473297573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3565620619075168315531715 5348430928612752473297573)
                    ·
                      refine ⟨1002830799114891088743295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5348430928612752473297573 1002830799114891088743295)
                      ·
                        rfl

theorem cell23_1953006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_1953006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953006 prefixEnd_1953006 := by exact prefixLift 1953006
  have htrace : WordTrace (prefixWord ++ tailWord_1953006) baseStart_1953006 baseEnd_1953006 := by
    simpa [prefixWord, tailWord_1953006, baseEnd_1953006] using wordTrace_append hprefix tailTrace_1953006
  have hstable : (prefixWord ++ tailWord_1953006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953006).length < 2 ^ (prefixWord ++ tailWord_1953006).sum := by decide
  have hdescent : baseEnd_1953006 < baseStart_1953006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953072 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 1, 8]
def baseStart_1953072 : Nat := 118140960795 + 1953072 * 2 ^ 59
def prefixEnd_1953072 : Nat := 4983230072969 + 3 ^ 40 * 1953072 * 2
def baseEnd_1953072 : Nat := 334288229612695943505997

theorem tailTrace_1953072 : CollatzResearch.WordTrace tailWord_1953072 prefixEnd_1953072 334288229612695943505997 := by
  unfold tailWord_1953072
  simp only [CollatzResearch.WordTrace]
  refine ⟨35617193990180588493394735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47489591986907451324526313 35617193990180588493394735)
  ·
    refine ⟨53425790985270882740092103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35617193990180588493394735 53425790985270882740092103)
    ·
      refine ⟨80138686477906324110138155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53425790985270882740092103 80138686477906324110138155)
      ·
        refine ⟨120208029716859486165207233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80138686477906324110138155 120208029716859486165207233)
        ·
          refine ⟨90156022287644614623905425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120208029716859486165207233 90156022287644614623905425)
          ·
            refine ⟨67617016715733460967929069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90156022287644614623905425 67617016715733460967929069)
            ·
              refine ⟨25356381268400047862973401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67617016715733460967929069 25356381268400047862973401)
              ·
                refine ⟨19017285951300035897230051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25356381268400047862973401 19017285951300035897230051)
                ·
                  refine ⟨28525928926950053845845077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19017285951300035897230051 28525928926950053845845077)
                  ·
                    refine ⟨334288229612695943505997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28525928926950053845845077 334288229612695943505997)
                    ·
                      rfl

theorem cell23_1953072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_1953072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953072 prefixEnd_1953072 := by exact prefixLift 1953072
  have htrace : WordTrace (prefixWord ++ tailWord_1953072) baseStart_1953072 baseEnd_1953072 := by
    simpa [prefixWord, tailWord_1953072, baseEnd_1953072] using wordTrace_append hprefix tailTrace_1953072
  have hstable : (prefixWord ++ tailWord_1953072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953072).length < 2 ^ (prefixWord ++ tailWord_1953072).sum := by decide
  have hdescent : baseEnd_1953072 < baseStart_1953072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953113 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 2, 2, 2]
def baseStart_1953113 : Nat := 118140960795 + 1953113 * 2 ^ 59
def prefixEnd_1953113 : Nat := 4983230072969 + 3 ^ 40 * 1953113 * 2
def baseEnd_1953113 : Nat := 1002885741544922170105303

theorem tailTrace_1953113 : CollatzResearch.WordTrace tailWord_1953113 prefixEnd_1953113 1002885741544922170105303 := by
  unfold tailWord_1953113
  simp only [CollatzResearch.WordTrace]
  refine ⟨71235883373212640989031993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47490588915475093992687995 71235883373212640989031993)
  ·
    refine ⟨53426912529909480741773995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71235883373212640989031993 53426912529909480741773995)
    ·
      refine ⟨80140368794864221112660993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53426912529909480741773995 80140368794864221112660993)
      ·
        refine ⟨60105276596148165834495745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80140368794864221112660993 60105276596148165834495745)
        ·
          refine ⟨45078957447111124375871809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60105276596148165834495745 45078957447111124375871809)
          ·
            refine ⟨33809218085333343281903857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45078957447111124375871809 33809218085333343281903857)
            ·
              refine ⟨25356913564000007461427893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33809218085333343281903857 25356913564000007461427893)
              ·
                refine ⟨2377210646625000699508865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25356913564000007461427893 2377210646625000699508865)
                ·
                  refine ⟨1782907984968750524631649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2377210646625000699508865 1782907984968750524631649)
                  ·
                    refine ⟨1337180988726562893473737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1782907984968750524631649 1337180988726562893473737)
                    ·
                      refine ⟨1002885741544922170105303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337180988726562893473737 1002885741544922170105303)
                      ·
                        rfl

theorem cell23_1953113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_1953113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953113 prefixEnd_1953113 := by exact prefixLift 1953113
  have htrace : WordTrace (prefixWord ++ tailWord_1953113) baseStart_1953113 baseEnd_1953113 := by
    simpa [prefixWord, tailWord_1953113, baseEnd_1953113] using wordTrace_append hprefix tailTrace_1953113
  have hstable : (prefixWord ++ tailWord_1953113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953113).length < 2 ^ (prefixWord ++ tailWord_1953113).sum := by decide
  have hdescent : baseEnd_1953113 < baseStart_1953113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953129 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 4, 3, 3]
def baseStart_1953129 : Nat := 118140960795 + 1953129 * 2 ^ 59
def prefixEnd_1953129 : Nat := 4983230072969 + 3 ^ 40 * 1953129 * 2
def baseEnd_1953129 : Nat := 1002893957235394107505229

theorem tailTrace_1953129 : CollatzResearch.WordTrace tailWord_1953129 prefixEnd_1953129 1002893957235394107505229 := by
  unfold tailWord_1953129
  simp only [CollatzResearch.WordTrace]
  refine ⟨71236466941154675721614441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47490977960769783814409627 71236466941154675721614441)
  ·
    refine ⟨53427350205866006791210831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71236466941154675721614441 53427350205866006791210831)
    ·
      refine ⟨80141025308799010186816247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53427350205866006791210831 80141025308799010186816247)
      ·
        refine ⟨120211537963198515280224371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80141025308799010186816247 120211537963198515280224371)
        ·
          refine ⟨180317306944797772920336557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120211537963198515280224371 180317306944797772920336557)
          ·
            refine ⟨67618990104299164845126209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180317306944797772920336557 67618990104299164845126209)
            ·
              refine ⟨50714242578224373633844657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67618990104299164845126209 50714242578224373633844657)
              ·
                refine ⟨38035681933668280225383493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50714242578224373633844657 38035681933668280225383493)
                ·
                  refine ⟨7131690362562802542259405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38035681933668280225383493 7131690362562802542259405)
                  ·
                    refine ⟨2674383885961050953347277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7131690362562802542259405 2674383885961050953347277)
                    ·
                      refine ⟨1002893957235394107505229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2674383885961050953347277 1002893957235394107505229)
                      ·
                        rfl

theorem cell23_1953129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 3, 3].length) (baseStart_1953129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953129 prefixEnd_1953129 := by exact prefixLift 1953129
  have htrace : WordTrace (prefixWord ++ tailWord_1953129) baseStart_1953129 baseEnd_1953129 := by
    simpa [prefixWord, tailWord_1953129, baseEnd_1953129] using wordTrace_append hprefix tailTrace_1953129
  have hstable : (prefixWord ++ tailWord_1953129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953129).length < 2 ^ (prefixWord ++ tailWord_1953129).sum := by decide
  have hdescent : baseEnd_1953129 < baseStart_1953129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953153 : List Nat := [1, 2, 4, 3, 2, 2, 1, 1, 7]
def baseStart_1953153 : Nat := 118140960795 + 1953153 * 2 ^ 59
def prefixEnd_1953153 : Nat := 4983230072969 + 3 ^ 40 * 1953153 * 2
def baseEnd_1953153 : Nat := 111434031196789112622791

theorem tailTrace_1953153 : CollatzResearch.WordTrace tailWord_1953153 prefixEnd_1953153 111434031196789112622791 := by
  unfold tailWord_1953153
  simp only [CollatzResearch.WordTrace]
  refine ⟨71237342293067727820488113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47491561528711818546992075 71237342293067727820488113)
  ·
    refine ⟨53428006719800795865366085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71237342293067727820488113 53428006719800795865366085)
    ·
      refine ⟨10017751259962649224756141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53428006719800795865366085 10017751259962649224756141)
      ·
        refine ⟨3756656722485993459283553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10017751259962649224756141 3756656722485993459283553)
        ·
          refine ⟨2817492541864495094462665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3756656722485993459283553 2817492541864495094462665)
          ·
            refine ⟨2113119406398371320846999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2817492541864495094462665 2113119406398371320846999)
            ·
              refine ⟨3169679109597556981270499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113119406398371320846999 3169679109597556981270499)
              ·
                refine ⟨4754518664396335471905749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169679109597556981270499 4754518664396335471905749)
                ·
                  refine ⟨111434031196789112622791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4754518664396335471905749 111434031196789112622791)
                  ·
                    rfl

theorem cell23_1953153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 1, 7].length) (baseStart_1953153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953153 prefixEnd_1953153 := by exact prefixLift 1953153
  have htrace : WordTrace (prefixWord ++ tailWord_1953153) baseStart_1953153 baseEnd_1953153 := by
    simpa [prefixWord, tailWord_1953153, baseEnd_1953153] using wordTrace_append hprefix tailTrace_1953153
  have hstable : (prefixWord ++ tailWord_1953153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953153).length < 2 ^ (prefixWord ++ tailWord_1953153).sum := by decide
  have hdescent : baseEnd_1953153 < baseStart_1953153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953159 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1953159 : Nat := 118140960795 + 1953159 * 2 ^ 59
def prefixEnd_1953159 : Nat := 4983230072969 + 3 ^ 40 * 1953159 * 2
def baseEnd_1953159 : Nat := 1002909361655028990130091

theorem tailTrace_1953159 : CollatzResearch.WordTrace tailWord_1953159 prefixEnd_1953159 1002909361655028990130091 := by
  unfold tailWord_1953159
  simp only [CollatzResearch.WordTrace]
  refine ⟨71237561131045990845206531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47491707420697327230137687 71237561131045990845206531)
  ·
    refine ⟨106856341696568986267809797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71237561131045990845206531 106856341696568986267809797)
    ·
      refine ⟨20035564068106684925214337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106856341696568986267809797 20035564068106684925214337)
      ·
        refine ⟨15026673051080013693910753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20035564068106684925214337 15026673051080013693910753)
        ·
          refine ⟨11270004788310010270433065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15026673051080013693910753 11270004788310010270433065)
          ·
            refine ⟨8452503591232507702824799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11270004788310010270433065 8452503591232507702824799)
            ·
              refine ⟨12678755386848761554237199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452503591232507702824799 12678755386848761554237199)
              ·
                refine ⟨19018133080273142331355799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12678755386848761554237199 19018133080273142331355799)
                ·
                  refine ⟨28527199620409713497033699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19018133080273142331355799 28527199620409713497033699)
                  ·
                    refine ⟨42790799430614570245550549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28527199620409713497033699 42790799430614570245550549)
                    ·
                      refine ⟨1002909361655028990130091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42790799430614570245550549 1002909361655028990130091)
                      ·
                        rfl

theorem cell23_1953159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1953159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953159 prefixEnd_1953159 := by exact prefixLift 1953159
  have htrace : WordTrace (prefixWord ++ tailWord_1953159) baseStart_1953159 baseEnd_1953159 := by
    simpa [prefixWord, tailWord_1953159, baseEnd_1953159] using wordTrace_append hprefix tailTrace_1953159
  have hstable : (prefixWord ++ tailWord_1953159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953159).length < 2 ^ (prefixWord ++ tailWord_1953159).sum := by decide
  have hdescent : baseEnd_1953159 < baseStart_1953159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953220 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 2, 4, 2]
def baseStart_1953220 : Nat := 118140960795 + 1953220 * 2 ^ 59
def prefixEnd_1953220 : Nat := 4983230072969 + 3 ^ 40 * 1953220 * 2
def baseEnd_1953220 : Nat := 1002940683974953251467311

theorem tailTrace_1953220 : CollatzResearch.WordTrace tailWord_1953220 prefixEnd_1953220 1002940683974953251467311 := by
  unfold tailWord_1953220
  simp only [CollatzResearch.WordTrace]
  refine ⟨35619892991912499131588557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47493190655883332175451409 35619892991912499131588557)
  ·
    refine ⟨13357459871967187174345709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35619892991912499131588557 13357459871967187174345709)
    ·
      refine ⟨5009047451987695190379641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13357459871967187174345709 5009047451987695190379641)
      ·
        refine ⟨3756785588990771392784731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5009047451987695190379641 3756785588990771392784731)
        ·
          refine ⟨5635178383486157089177097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3756785588990771392784731 5635178383486157089177097)
          ·
            refine ⟨4226383787614617816882823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5635178383486157089177097 4226383787614617816882823)
            ·
              refine ⟨6339575681421926725324235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4226383787614617816882823 6339575681421926725324235)
              ·
                refine ⟨9509363522132890087986353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6339575681421926725324235 9509363522132890087986353)
                ·
                  refine ⟨7132022641599667565989765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9509363522132890087986353 7132022641599667565989765)
                  ·
                    refine ⟨1337254245299937668623081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7132022641599667565989765 1337254245299937668623081)
                    ·
                      refine ⟨1002940683974953251467311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337254245299937668623081 1002940683974953251467311)
                      ·
                        rfl

theorem cell23_1953220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_1953220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953220 prefixEnd_1953220 := by exact prefixLift 1953220
  have htrace : WordTrace (prefixWord ++ tailWord_1953220) baseStart_1953220 baseEnd_1953220 := by
    simpa [prefixWord, tailWord_1953220, baseEnd_1953220] using wordTrace_append hprefix tailTrace_1953220
  have hstable : (prefixWord ++ tailWord_1953220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953220).length < 2 ^ (prefixWord ++ tailWord_1953220).sum := by decide
  have hdescent : baseEnd_1953220 < baseStart_1953220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953226 : List Nat := [3, 1, 2, 1, 2, 3, 2, 3, 6]
def baseStart_1953226 : Nat := 118140960795 + 1953226 * 2 ^ 59
def prefixEnd_1953226 : Nat := 4983230072969 + 3 ^ 40 * 1953226 * 2
def baseEnd_1953226 : Nat := 111438196095431136443587

theorem tailTrace_1953226 : CollatzResearch.WordTrace tailWord_1953226 prefixEnd_1953226 111438196095431136443587 := by
  unfold tailWord_1953226
  simp only [CollatzResearch.WordTrace]
  refine ⟨17810001205450815321973883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47493336547868840858597021 17810001205450815321973883)
  ·
    refine ⟨26715001808176222982960825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17810001205450815321973883 26715001808176222982960825)
    ·
      refine ⟨20036251356132167237220619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26715001808176222982960825 20036251356132167237220619)
      ·
        refine ⟨30054377034198250855830929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20036251356132167237220619 30054377034198250855830929)
        ·
          refine ⟨22540782775648688141873197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30054377034198250855830929 22540782775648688141873197)
          ·
            refine ⟨8452793540868258053202449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22540782775648688141873197 8452793540868258053202449)
            ·
              refine ⟨6339595155651193539901837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8452793540868258053202449 6339595155651193539901837)
              ·
                refine ⟨2377348183369197577463189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6339595155651193539901837 2377348183369197577463189)
                ·
                  refine ⟨111438196095431136443587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2377348183369197577463189 111438196095431136443587)
                  ·
                    rfl

theorem cell23_1953226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_1953226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953226 prefixEnd_1953226 := by exact prefixLift 1953226
  have htrace : WordTrace (prefixWord ++ tailWord_1953226) baseStart_1953226 baseEnd_1953226 := by
    simpa [prefixWord, tailWord_1953226, baseEnd_1953226] using wordTrace_append hprefix tailTrace_1953226
  have hstable : (prefixWord ++ tailWord_1953226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953226).length < 2 ^ (prefixWord ++ tailWord_1953226).sum := by decide
  have hdescent : baseEnd_1953226 < baseStart_1953226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953263 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 2, 3, 2]
def baseStart_1953263 : Nat := 118140960795 + 1953263 * 2 ^ 59
def prefixEnd_1953263 : Nat := 4983230072969 + 3 ^ 40 * 1953263 * 2
def baseEnd_1953263 : Nat := 1002962763643096583229613

theorem tailTrace_1953263 : CollatzResearch.WordTrace tailWord_1953263 prefixEnd_1953263 1002962763643096583229613 := by
  unfold tailWord_1953263
  simp only [CollatzResearch.WordTrace]
  refine ⟨71241354322669216606992443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47494236215112811071328295 71241354322669216606992443)
  ·
    refine ⟨106862031484003824910488665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71241354322669216606992443 106862031484003824910488665)
    ·
      refine ⟨80146523613002868682866499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106862031484003824910488665 80146523613002868682866499)
      ·
        refine ⟨120219785419504303024299749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80146523613002868682866499 120219785419504303024299749)
        ·
          refine ⟨22541209766157056817056203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120219785419504303024299749 22541209766157056817056203)
          ·
            refine ⟨33811814649235585225584305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22541209766157056817056203 33811814649235585225584305)
            ·
              refine ⟨25358860986926688919188229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33811814649235585225584305 25358860986926688919188229)
              ·
                refine ⟨4754786435048754172347793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25358860986926688919188229 4754786435048754172347793)
                ·
                  refine ⟨3566089826286565629260845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4754786435048754172347793 3566089826286565629260845)
                  ·
                    refine ⟨1337283684857462110972817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3566089826286565629260845 1337283684857462110972817)
                    ·
                      refine ⟨1002962763643096583229613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337283684857462110972817 1002962763643096583229613)
                      ·
                        rfl

theorem cell23_1953263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 3, 2].length) (baseStart_1953263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953263 prefixEnd_1953263 := by exact prefixLift 1953263
  have htrace : WordTrace (prefixWord ++ tailWord_1953263) baseStart_1953263 baseEnd_1953263 := by
    simpa [prefixWord, tailWord_1953263, baseEnd_1953263] using wordTrace_append hprefix tailTrace_1953263
  have hstable : (prefixWord ++ tailWord_1953263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953263).length < 2 ^ (prefixWord ++ tailWord_1953263).sum := by decide
  have hdescent : baseEnd_1953263 < baseStart_1953263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953270 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1953270 : Nat := 118140960795 + 1953270 * 2 ^ 59
def prefixEnd_1953270 : Nat := 4983230072969 + 3 ^ 40 * 1953270 * 2
def baseEnd_1953270 : Nat := 1002966358007678055842081

theorem tailTrace_1953270 : CollatzResearch.WordTrace tailWord_1953270 prefixEnd_1953270 1002966358007678055842081 := by
  unfold tailWord_1953270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4452600602102741050156079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47494406422429237868331509 4452600602102741050156079)
  ·
    refine ⟨6678900903154111575234119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4452600602102741050156079 6678900903154111575234119)
    ·
      refine ⟨10018351354731167362851179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6678900903154111575234119 10018351354731167362851179)
      ·
        refine ⟨15027527032096751044276769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10018351354731167362851179 15027527032096751044276769)
        ·
          refine ⟨11270645274072563283207577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15027527032096751044276769 11270645274072563283207577)
          ·
            refine ⟨8452983955554422462405683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11270645274072563283207577 8452983955554422462405683)
            ·
              refine ⟨12679475933331633693608525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8452983955554422462405683 12679475933331633693608525)
              ·
                refine ⟨4754803474999362635103197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12679475933331633693608525 4754803474999362635103197)
                ·
                  refine ⟨1783051303124760988163699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4754803474999362635103197 1783051303124760988163699)
                  ·
                    refine ⟨2674576954687141482245549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1783051303124760988163699 2674576954687141482245549)
                    ·
                      refine ⟨1002966358007678055842081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2674576954687141482245549 1002966358007678055842081)
                      ·
                        rfl

theorem cell23_1953270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1953270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953270 prefixEnd_1953270 := by exact prefixLift 1953270
  have htrace : WordTrace (prefixWord ++ tailWord_1953270) baseStart_1953270 baseEnd_1953270 := by
    simpa [prefixWord, tailWord_1953270, baseEnd_1953270] using wordTrace_append hprefix tailTrace_1953270
  have hstable : (prefixWord ++ tailWord_1953270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953270).length < 2 ^ (prefixWord ++ tailWord_1953270).sum := by decide
  have hdescent : baseEnd_1953270 < baseStart_1953270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953276 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_1953276 : Nat := 118140960795 + 1953276 * 2 ^ 59
def prefixEnd_1953276 : Nat := 4983230072969 + 3 ^ 40 * 1953276 * 2
def baseEnd_1953276 : Nat := 1002969438891605032367053

theorem tailTrace_1953276 : CollatzResearch.WordTrace tailWord_1953276 prefixEnd_1953276 1002969438891605032367053 := by
  unfold tailWord_1953276
  simp only [CollatzResearch.WordTrace]
  refine ⟨35620914235811059913607841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47494552314414746551477121 35620914235811059913607841)
  ·
    refine ⟨26715685676858294935205881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35620914235811059913607841 26715685676858294935205881)
    ·
      refine ⟨20036764257643721201404411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26715685676858294935205881 20036764257643721201404411)
      ·
        refine ⟨30055146386465581802106617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20036764257643721201404411 30055146386465581802106617)
        ·
          refine ⟨22541359789849186351579963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30055146386465581802106617 22541359789849186351579963)
          ·
            refine ⟨33812039684773779527369945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22541359789849186351579963 33812039684773779527369945)
            ·
              refine ⟨25359029763580334645527459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33812039684773779527369945 25359029763580334645527459)
              ·
                refine ⟨38038544645370501968291189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25359029763580334645527459 38038544645370501968291189)
                ·
                  refine ⟨3566113560503484559527299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38038544645370501968291189 3566113560503484559527299)
                  ·
                    refine ⟨5349170340755226839290949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3566113560503484559527299 5349170340755226839290949)
                    ·
                      refine ⟨1002969438891605032367053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5349170340755226839290949 1002969438891605032367053)
                      ·
                        rfl

theorem cell23_1953276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_1953276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953276 prefixEnd_1953276 := by exact prefixLift 1953276
  have htrace : WordTrace (prefixWord ++ tailWord_1953276) baseStart_1953276 baseEnd_1953276 := by
    simpa [prefixWord, tailWord_1953276, baseEnd_1953276] using wordTrace_append hprefix tailTrace_1953276
  have hstable : (prefixWord ++ tailWord_1953276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953276).length < 2 ^ (prefixWord ++ tailWord_1953276).sum := by decide
  have hdescent : baseEnd_1953276 < baseStart_1953276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953304 : List Nat := [2, 1, 2, 3, 4, 2, 1, 3, 1, 1, 3]
def baseStart_1953304 : Nat := 118140960795 + 1953304 * 2 ^ 59
def prefixEnd_1953304 : Nat := 4983230072969 + 3 ^ 40 * 1953304 * 2
def baseEnd_1953304 : Nat := 1002983816349930922816925

theorem tailTrace_1953304 : CollatzResearch.WordTrace tailWord_1953304 prefixEnd_1953304 1002983816349930922816925 := by
  unfold tailWord_1953304
  simp only [CollatzResearch.WordTrace]
  refine ⟨35621424857760340304617483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47495233143680453739489977 35621424857760340304617483)
  ·
    refine ⟨53432137286640510456926225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35621424857760340304617483 53432137286640510456926225)
    ·
      refine ⟨40074102964980382842694669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53432137286640510456926225 40074102964980382842694669)
      ·
        refine ⟨15027788611867643566010501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40074102964980382842694669 15027788611867643566010501)
        ·
          refine ⟨2817710364725183168626969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15027788611867643566010501 2817710364725183168626969)
          ·
            refine ⟨2113282773543887376470227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2817710364725183168626969 2113282773543887376470227)
            ·
              refine ⟨3169924160315831064705341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113282773543887376470227 3169924160315831064705341)
              ·
                refine ⟨1188721560118436649264503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3169924160315831064705341 1188721560118436649264503)
                ·
                  refine ⟨1783082340177654973896755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1188721560118436649264503 1783082340177654973896755)
                  ·
                    refine ⟨2674623510266482460845133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1783082340177654973896755 2674623510266482460845133)
                    ·
                      refine ⟨1002983816349930922816925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2674623510266482460845133 1002983816349930922816925)
                      ·
                        rfl

theorem cell23_1953304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_1953304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953304 prefixEnd_1953304 := by exact prefixLift 1953304
  have htrace : WordTrace (prefixWord ++ tailWord_1953304) baseStart_1953304 baseEnd_1953304 := by
    simpa [prefixWord, tailWord_1953304, baseEnd_1953304] using wordTrace_append hprefix tailTrace_1953304
  have hstable : (prefixWord ++ tailWord_1953304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953304).length < 2 ^ (prefixWord ++ tailWord_1953304).sum := by decide
  have hdescent : baseEnd_1953304 < baseStart_1953304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953306 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1953306 : Nat := 118140960795 + 1953306 * 2 ^ 59
def prefixEnd_1953306 : Nat := 4983230072969 + 3 ^ 40 * 1953306 * 2
def baseEnd_1953306 : Nat := 1002984843311239914991915

theorem tailTrace_1953306 : CollatzResearch.WordTrace tailWord_1953306 prefixEnd_1953306 1002984843311239914991915 := by
  unfold tailWord_1953306
  simp only [CollatzResearch.WordTrace]
  refine ⟨17810730665378358737701943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47495281774342289967205181 17810730665378358737701943)
  ·
    refine ⟨26716095998067538106552915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17810730665378358737701943 26716095998067538106552915)
    ·
      refine ⟨40074143997101307159829373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26716095998067538106552915 40074143997101307159829373)
      ·
        refine ⟨15027803998912990184936015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40074143997101307159829373 15027803998912990184936015)
        ·
          refine ⟨22541705998369485277404023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15027803998912990184936015 22541705998369485277404023)
          ·
            refine ⟨33812558997554227916106035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22541705998369485277404023 33812558997554227916106035)
            ·
              refine ⟨50718838496331341874159053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33812558997554227916106035 50718838496331341874159053)
              ·
                refine ⟨19019564436124253202809645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50718838496331341874159053 19019564436124253202809645)
                ·
                  refine ⟨7132336663546594951053617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19019564436124253202809645 7132336663546594951053617)
                  ·
                    refine ⟨5349252497659946213290213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7132336663546594951053617 5349252497659946213290213)
                    ·
                      refine ⟨1002984843311239914991915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5349252497659946213290213 1002984843311239914991915)
                      ·
                        rfl

theorem cell23_1953306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1953306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953306 prefixEnd_1953306 := by exact prefixLift 1953306
  have htrace : WordTrace (prefixWord ++ tailWord_1953306) baseStart_1953306 baseEnd_1953306 := by
    simpa [prefixWord, tailWord_1953306, baseEnd_1953306] using wordTrace_append hprefix tailTrace_1953306
  have hstable : (prefixWord ++ tailWord_1953306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953306).length < 2 ^ (prefixWord ++ tailWord_1953306).sum := by decide
  have hdescent : baseEnd_1953306 < baseStart_1953306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953313 : List Nat := [1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1953313 : Nat := 118140960795 + 1953313 * 2 ^ 59
def prefixEnd_1953313 : Nat := 4983230072969 + 3 ^ 40 * 1953313 * 2
def baseEnd_1953313 : Nat := 1002988437675821387604383

theorem tailTrace_1953313 : CollatzResearch.WordTrace tailWord_1953313 prefixEnd_1953313 1002988437675821387604383 := by
  unfold tailWord_1953313
  simp only [CollatzResearch.WordTrace]
  refine ⟨71243177972488075146312593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47495451981658716764208395 71243177972488075146312593)
  ·
    refine ⟨53432383479366056359734445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71243177972488075146312593 53432383479366056359734445)
    ·
      refine ⟨20037143804762271134900417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53432383479366056359734445 20037143804762271134900417)
      ·
        refine ⟨15027857853571703351175313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20037143804762271134900417 15027857853571703351175313)
        ·
          refine ⟨11270893390178777513381485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15027857853571703351175313 11270893390178777513381485)
          ·
            refine ⟨4226585021317041567518057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11270893390178777513381485 4226585021317041567518057)
            ·
              refine ⟨3169938765987781175638543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4226585021317041567518057 3169938765987781175638543)
              ·
                refine ⟨4754908148981671763457815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3169938765987781175638543 4754908148981671763457815)
                ·
                  refine ⟨7132362223472507645186723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4754908148981671763457815 7132362223472507645186723)
                  ·
                    refine ⟨10698543335208761467780085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7132362223472507645186723 10698543335208761467780085)
                    ·
                      refine ⟨1002988437675821387604383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10698543335208761467780085 1002988437675821387604383)
                      ·
                        rfl

theorem cell23_1953313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1953313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953313 prefixEnd_1953313 := by exact prefixLift 1953313
  have htrace : WordTrace (prefixWord ++ tailWord_1953313) baseStart_1953313 baseEnd_1953313 := by
    simpa [prefixWord, tailWord_1953313, baseEnd_1953313] using wordTrace_append hprefix tailTrace_1953313
  have hstable : (prefixWord ++ tailWord_1953313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953313).length < 2 ^ (prefixWord ++ tailWord_1953313).sum := by decide
  have hdescent : baseEnd_1953313 < baseStart_1953313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953337 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 2, 4]
def baseStart_1953337 : Nat := 118140960795 + 1953337 * 2 ^ 59
def prefixEnd_1953337 : Nat := 4983230072969 + 3 ^ 40 * 1953337 * 2
def baseEnd_1953337 : Nat := 334333587070509764568091

theorem tailTrace_1953337 : CollatzResearch.WordTrace tailWord_1953337 prefixEnd_1953337 334333587070509764568091 := by
  unfold tailWord_1953337
  simp only [CollatzResearch.WordTrace]
  refine ⟨71244053324401127245186265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47496035549600751496790843 71244053324401127245186265)
  ·
    refine ⟨53433039993300845433889699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71244053324401127245186265 53433039993300845433889699)
    ·
      refine ⟨80149559989951268150834549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53433039993300845433889699 80149559989951268150834549)
      ·
        refine ⟨7514021249057931389140739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80149559989951268150834549 7514021249057931389140739)
        ·
          refine ⟨11271031873586897083711109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7514021249057931389140739 11271031873586897083711109)
          ·
            refine ⟨2113318476297543203195833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11271031873586897083711109 2113318476297543203195833)
            ·
              refine ⟨1584988857223157402396875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2113318476297543203195833 1584988857223157402396875)
              ·
                refine ⟨2377483285834736103595313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1584988857223157402396875 2377483285834736103595313)
                ·
                  refine ⟨1783112464376052077696485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2377483285834736103595313 1783112464376052077696485)
                  ·
                    refine ⟨334333587070509764568091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1783112464376052077696485 334333587070509764568091)
                    ·
                      rfl

theorem cell23_1953337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 2, 4].length) (baseStart_1953337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953337 prefixEnd_1953337 := by exact prefixLift 1953337
  have htrace : WordTrace (prefixWord ++ tailWord_1953337) baseStart_1953337 baseEnd_1953337 := by
    simpa [prefixWord, tailWord_1953337, baseEnd_1953337] using wordTrace_append hprefix tailTrace_1953337
  have hstable : (prefixWord ++ tailWord_1953337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953337).length < 2 ^ (prefixWord ++ tailWord_1953337).sum := by decide
  have hdescent : baseEnd_1953337 < baseStart_1953337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953370 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2]
def baseStart_1953370 : Nat := 118140960795 + 1953370 * 2 ^ 59
def prefixEnd_1953370 : Nat := 4983230072969 + 3 ^ 40 * 1953370 * 2
def baseEnd_1953370 : Nat := 1003017706073127664591621

theorem tailTrace_1953370 : CollatzResearch.WordTrace tailWord_1953370 prefixEnd_1953370 1003017706073127664591621 := by
  unfold tailWord_1953370
  simp only [CollatzResearch.WordTrace]
  refine ⟨17811314233320393470284391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47496837955521049254091709 17811314233320393470284391)
  ·
    refine ⟨26716971349980590205426587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17811314233320393470284391 26716971349980590205426587)
    ·
      refine ⟨40075457024970885308139881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26716971349980590205426587 40075457024970885308139881)
      ·
        refine ⟨30056592768728163981104911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40075457024970885308139881 30056592768728163981104911)
        ·
          refine ⟨45084889153092245971657367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30056592768728163981104911 45084889153092245971657367)
          ·
            refine ⟨67627333729638368957486051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45084889153092245971657367 67627333729638368957486051)
            ·
              refine ⟨101441000594457553436229077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67627333729638368957486051 101441000594457553436229077)
              ·
                refine ⟨2377523451432598908661619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101441000594457553436229077 2377523451432598908661619)
                ·
                  refine ⟨3566285177148898362992429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377523451432598908661619 3566285177148898362992429)
                  ·
                    refine ⟨1337356941430836886122161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3566285177148898362992429 1337356941430836886122161)
                    ·
                      refine ⟨1003017706073127664591621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337356941430836886122161 1003017706073127664591621)
                      ·
                        rfl

theorem cell23_1953370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_1953370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953370 prefixEnd_1953370 := by exact prefixLift 1953370
  have htrace : WordTrace (prefixWord ++ tailWord_1953370) baseStart_1953370 baseEnd_1953370 := by
    simpa [prefixWord, tailWord_1953370, baseEnd_1953370] using wordTrace_append hprefix tailTrace_1953370
  have hstable : (prefixWord ++ tailWord_1953370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953370).length < 2 ^ (prefixWord ++ tailWord_1953370).sum := by decide
  have hdescent : baseEnd_1953370 < baseStart_1953370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953376 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 2, 6]
def baseStart_1953376 : Nat := 118140960795 + 1953376 * 2 ^ 59
def prefixEnd_1953376 : Nat := 4983230072969 + 3 ^ 40 * 1953376 * 2
def baseEnd_1953376 : Nat := 334340262319018213705531

theorem tailTrace_1953376 : CollatzResearch.WordTrace tailWord_1953376 prefixEnd_1953376 334340262319018213705531 := by
  unfold tailWord_1953376
  simp only [CollatzResearch.WordTrace]
  refine ⟨35622737885629918452927991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47496983847506557937237321 35622737885629918452927991)
  ·
    refine ⟨53434106828444877679391987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35622737885629918452927991 53434106828444877679391987)
    ·
      refine ⟨80151160242667316519087981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53434106828444877679391987 80151160242667316519087981)
      ·
        refine ⟨30056685091000243694657993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80151160242667316519087981 30056685091000243694657993)
        ·
          refine ⟨22542513818250182770993495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30056685091000243694657993 22542513818250182770993495)
          ·
            refine ⟨33813770727375274156490243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22542513818250182770993495 33813770727375274156490243)
            ·
              refine ⟨50720656091062911234735365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33813770727375274156490243 50720656091062911234735365)
              ·
                refine ⟨9510123017074295856512881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50720656091062911234735365 9510123017074295856512881)
                ·
                  refine ⟨7132592262805721892384661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9510123017074295856512881 7132592262805721892384661)
                  ·
                    refine ⟨334340262319018213705531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7132592262805721892384661 334340262319018213705531)
                    ·
                      rfl

theorem cell23_1953376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_1953376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953376 prefixEnd_1953376 := by exact prefixLift 1953376
  have htrace : WordTrace (prefixWord ++ tailWord_1953376) baseStart_1953376 baseEnd_1953376 := by
    simpa [prefixWord, tailWord_1953376, baseEnd_1953376] using wordTrace_append hprefix tailTrace_1953376
  have hstable : (prefixWord ++ tailWord_1953376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953376).length < 2 ^ (prefixWord ++ tailWord_1953376).sum := by decide
  have hdescent : baseEnd_1953376 < baseStart_1953376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953440 : List Nat := [2, 1, 1, 4, 3, 1, 2, 4, 5]
def baseStart_1953440 : Nat := 118140960795 + 1953440 * 2 ^ 59
def prefixEnd_1953440 : Nat := 4983230072969 + 3 ^ 40 * 1953440 * 2
def baseEnd_1953440 : Nat := 111450405524326932301811

theorem tailTrace_1953440 : CollatzResearch.WordTrace tailWord_1953440 prefixEnd_1953440 111450405524326932301811 := by
  unfold tailWord_1953440
  simp only [CollatzResearch.WordTrace]
  refine ⟨35623905021513987918092887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47498540028685317224123849 35623905021513987918092887)
  ·
    refine ⟨53435857532270981877139331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35623905021513987918092887 53435857532270981877139331)
    ·
      refine ⟨80153786298406472815708997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53435857532270981877139331 80153786298406472815708997)
      ·
        refine ⟨15028834930951213652945437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80153786298406472815708997 15028834930951213652945437)
        ·
          refine ⟨5635813099106705119854539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15028834930951213652945437 5635813099106705119854539)
          ·
            refine ⟨8453719648660057679781809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635813099106705119854539 8453719648660057679781809)
            ·
              refine ⟨6340289736495043259836357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8453719648660057679781809 6340289736495043259836357)
              ·
                refine ⟨1188804325592820611219317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6340289736495043259836357 1188804325592820611219317)
                ·
                  refine ⟨111450405524326932301811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188804325592820611219317 111450405524326932301811)
                  ·
                    rfl

theorem cell23_1953440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 4, 5].length) (baseStart_1953440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953440 prefixEnd_1953440 := by exact prefixLift 1953440
  have htrace : WordTrace (prefixWord ++ tailWord_1953440) baseStart_1953440 baseEnd_1953440 := by
    simpa [prefixWord, tailWord_1953440, baseEnd_1953440] using wordTrace_append hprefix tailTrace_1953440
  have hstable : (prefixWord ++ tailWord_1953440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953440).length < 2 ^ (prefixWord ++ tailWord_1953440).sum := by decide
  have hdescent : baseEnd_1953440 < baseStart_1953440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953453 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1953453 : Nat := 118140960795 + 1953453 * 2 ^ 59
def prefixEnd_1953453 : Nat := 4983230072969 + 3 ^ 40 * 1953453 * 2
def baseEnd_1953453 : Nat := 334353441655816946617913

theorem tailTrace_1953453 : CollatzResearch.WordTrace tailWord_1953453 prefixEnd_1953453 334353441655816946617913 := by
  unfold tailWord_1953453
  simp only [CollatzResearch.WordTrace]
  refine ⟨71248284191980879056409013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47498856127987252704272675 71248284191980879056409013)
  ·
    refine ⟨6679526642998207411538345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71248284191980879056409013 6679526642998207411538345)
    ·
      refine ⟨5009644982248655558653759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6679526642998207411538345 5009644982248655558653759)
      ·
        refine ⟨7514467473372983337980639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5009644982248655558653759 7514467473372983337980639)
        ·
          refine ⟨11271701210059475006970959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7514467473372983337980639 11271701210059475006970959)
          ·
            refine ⟨16907551815089212510456439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11271701210059475006970959 16907551815089212510456439)
            ·
              refine ⟨25361327722633818765684659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16907551815089212510456439 25361327722633818765684659)
              ·
                refine ⟨38041991583950728148526989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25361327722633818765684659 38041991583950728148526989)
                ·
                  refine ⟨14265746843981523055697621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38041991583950728148526989 14265746843981523055697621)
                  ·
                    refine ⟨334353441655816946617913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14265746843981523055697621 334353441655816946617913)
                    ·
                      rfl

theorem cell23_1953453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1953453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953453 prefixEnd_1953453 := by exact prefixLift 1953453
  have htrace : WordTrace (prefixWord ++ tailWord_1953453) baseStart_1953453 baseEnd_1953453 := by
    simpa [prefixWord, tailWord_1953453, baseEnd_1953453] using wordTrace_append hprefix tailTrace_1953453
  have hstable : (prefixWord ++ tailWord_1953453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953453).length < 2 ^ (prefixWord ++ tailWord_1953453).sum := by decide
  have hdescent : baseEnd_1953453 < baseStart_1953453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953483 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 5, 4]
def baseStart_1953483 : Nat := 118140960795 + 1953483 * 2 ^ 59
def prefixEnd_1953483 : Nat := 4983230072969 + 3 ^ 40 * 1953483 * 2
def baseEnd_1953483 : Nat := 334358576462361907492867

theorem tailTrace_1953483 : CollatzResearch.WordTrace tailWord_1953483 prefixEnd_1953483 334358576462361907492867 := by
  unfold tailWord_1953483
  simp only [CollatzResearch.WordTrace]
  refine ⟨71249378381872194180001103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47499585587914796120000735 71249378381872194180001103)
  ·
    refine ⟨106874067572808291270001655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71249378381872194180001103 106874067572808291270001655)
    ·
      refine ⟨160311101359212436905002483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106874067572808291270001655 160311101359212436905002483)
      ·
        refine ⟨240466652038818655357503725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160311101359212436905002483 240466652038818655357503725)
        ·
          refine ⟨90174994514556995759063897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240466652038818655357503725 90174994514556995759063897)
          ·
            refine ⟨67631245885917746819297923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90174994514556995759063897 67631245885917746819297923)
            ·
              refine ⟨101446868828876620228946885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67631245885917746819297923 101446868828876620228946885)
              ·
                refine ⟨19021287905414366292927541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101446868828876620228946885 19021287905414366292927541)
                ·
                  refine ⟨1783245741132596839961957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19021287905414366292927541 1783245741132596839961957)
                  ·
                    refine ⟨334358576462361907492867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1783245741132596839961957 334358576462361907492867)
                    ·
                      rfl

theorem cell23_1953483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 4].length) (baseStart_1953483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953483 prefixEnd_1953483 := by exact prefixLift 1953483
  have htrace : WordTrace (prefixWord ++ tailWord_1953483) baseStart_1953483 baseEnd_1953483 := by
    simpa [prefixWord, tailWord_1953483, baseEnd_1953483] using wordTrace_append hprefix tailTrace_1953483
  have hstable : (prefixWord ++ tailWord_1953483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953483).length < 2 ^ (prefixWord ++ tailWord_1953483).sum := by decide
  have hdescent : baseEnd_1953483 < baseStart_1953483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953490 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_1953490 : Nat := 118140960795 + 1953490 * 2 ^ 59
def prefixEnd_1953490 : Nat := 4983230072969 + 3 ^ 40 * 1953490 * 2
def baseEnd_1953490 : Nat := 1003079323751667195091069

theorem tailTrace_1953490 : CollatzResearch.WordTrace tailWord_1953490 prefixEnd_1953490 1003079323751667195091069 := by
  unfold tailWord_1953490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17812408423211708593876481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47499755795231222917003949 17812408423211708593876481)
  ·
    refine ⟨13359306317408781445407361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17812408423211708593876481 13359306317408781445407361)
    ·
      refine ⟨10019479738056586084055521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13359306317408781445407361 10019479738056586084055521)
      ·
        refine ⟨7514609803542439563041641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10019479738056586084055521 7514609803542439563041641)
        ·
          refine ⟨5635957352656829672281231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7514609803542439563041641 5635957352656829672281231)
          ·
            refine ⟨8453936028985244508421847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5635957352656829672281231 8453936028985244508421847)
            ·
              refine ⟨12680904043477866762632771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8453936028985244508421847 12680904043477866762632771)
              ·
                refine ⟨19021356065216800143949157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12680904043477866762632771 19021356065216800143949157)
                ·
                  refine ⟨3566504262228150026990467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19021356065216800143949157 3566504262228150026990467)
                  ·
                    refine ⟨5349756393342225040485701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3566504262228150026990467 5349756393342225040485701)
                    ·
                      refine ⟨1003079323751667195091069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5349756393342225040485701 1003079323751667195091069)
                      ·
                        rfl

theorem cell23_1953490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_1953490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953490 prefixEnd_1953490 := by exact prefixLift 1953490
  have htrace : WordTrace (prefixWord ++ tailWord_1953490) baseStart_1953490 baseEnd_1953490 := by
    simpa [prefixWord, tailWord_1953490, baseEnd_1953490] using wordTrace_append hprefix tailTrace_1953490
  have hstable : (prefixWord ++ tailWord_1953490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953490).length < 2 ^ (prefixWord ++ tailWord_1953490).sum := by decide
  have hdescent : baseEnd_1953490 < baseStart_1953490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953523 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 3]
def baseStart_1953523 : Nat := 118140960795 + 1953523 * 2 ^ 59
def prefixEnd_1953523 : Nat := 4983230072969 + 3 ^ 40 * 1953523 * 2
def baseEnd_1953523 : Nat := 1003096268613265565978417

theorem tailTrace_1953523 : CollatzResearch.WordTrace tailWord_1953523 prefixEnd_1953523 1003096268613265565978417 := by
  unfold tailWord_1953523
  simp only [CollatzResearch.WordTrace]
  refine ⟨71250837301727281011457223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47500558201151520674304815 71250837301727281011457223)
  ·
    refine ⟨106876255952590921517185835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71250837301727281011457223 106876255952590921517185835)
    ·
      refine ⟨160314383928886382275778753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106876255952590921517185835 160314383928886382275778753)
      ·
        refine ⟨120235787946664786706834065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160314383928886382275778753 120235787946664786706834065)
        ·
          refine ⟨90176840959998590030125549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120235787946664786706834065 90176840959998590030125549)
          ·
            refine ⟨33816315359999471261297081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90176840959998590030125549 33816315359999471261297081)
            ·
              refine ⟨25362236519999603445972811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33816315359999471261297081 25362236519999603445972811)
              ·
                refine ⟨38043354779999405168959217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25362236519999603445972811 38043354779999405168959217)
                ·
                  refine ⟨28532516084999553876719413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38043354779999405168959217 28532516084999553876719413)
                  ·
                    refine ⟨2674923382968708175942445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28532516084999553876719413 2674923382968708175942445)
                    ·
                      refine ⟨1003096268613265565978417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2674923382968708175942445 1003096268613265565978417)
                      ·
                        rfl

theorem cell23_1953523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 3].length) (baseStart_1953523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953523 prefixEnd_1953523 := by exact prefixLift 1953523
  have htrace : WordTrace (prefixWord ++ tailWord_1953523) baseStart_1953523 baseEnd_1953523 := by
    simpa [prefixWord, tailWord_1953523, baseEnd_1953523] using wordTrace_append hprefix tailTrace_1953523
  have hstable : (prefixWord ++ tailWord_1953523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953523).length < 2 ^ (prefixWord ++ tailWord_1953523).sum := by decide
  have hdescent : baseEnd_1953523 < baseStart_1953523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953524 : List Nat := [2, 6, 1, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1953524 : Nat := 118140960795 + 1953524 * 2 ^ 59
def prefixEnd_1953524 : Nat := 4983230072969 + 3 ^ 40 * 1953524 * 2
def baseEnd_1953524 : Nat := 1003096782093920062065913

theorem tailTrace_1953524 : CollatzResearch.WordTrace tailWord_1953524 prefixEnd_1953524 1003096782093920062065913 := by
  unfold tailWord_1953524
  simp only [CollatzResearch.WordTrace]
  refine ⟨35625436887361829091121813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47500582516482438788162417 35625436887361829091121813)
  ·
    refine ⟨1669942354095085738646335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 35625436887361829091121813 1669942354095085738646335)
    ·
      refine ⟨2504913531142628607969503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1669942354095085738646335 2504913531142628607969503)
      ·
        refine ⟨3757370296713942911954255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2504913531142628607969503 3757370296713942911954255)
        ·
          refine ⟨5636055445070914367931383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3757370296713942911954255 5636055445070914367931383)
          ·
            refine ⟨8454083167606371551897075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636055445070914367931383 8454083167606371551897075)
            ·
              refine ⟨12681124751409557327845613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454083167606371551897075 12681124751409557327845613)
              ·
                refine ⟨4755421781778583997942105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12681124751409557327845613 4755421781778583997942105)
                ·
                  refine ⟨3566566336333937998456579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4755421781778583997942105 3566566336333937998456579)
                  ·
                    refine ⟨5349849504500906997684869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3566566336333937998456579 5349849504500906997684869)
                    ·
                      refine ⟨1003096782093920062065913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5349849504500906997684869 1003096782093920062065913)
                      ·
                        rfl

theorem cell23_1953524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1953524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953524 prefixEnd_1953524 := by exact prefixLift 1953524
  have htrace : WordTrace (prefixWord ++ tailWord_1953524) baseStart_1953524 baseEnd_1953524 := by
    simpa [prefixWord, tailWord_1953524, baseEnd_1953524] using wordTrace_append hprefix tailTrace_1953524
  have hstable : (prefixWord ++ tailWord_1953524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953524).length < 2 ^ (prefixWord ++ tailWord_1953524).sum := by decide
  have hdescent : baseEnd_1953524 < baseStart_1953524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953542 : List Nat := [6, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1953542 : Nat := 118140960795 + 1953542 * 2 ^ 59
def prefixEnd_1953542 : Nat := 4983230072969 + 3 ^ 40 * 1953542 * 2
def baseEnd_1953542 : Nat := 111456224971744554626759

theorem tailTrace_1953542 : CollatzResearch.WordTrace tailWord_1953542 prefixEnd_1953542 111456224971744554626759 := by
  unfold tailWord_1953542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2226610321520576476762465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 47501020192438964837599253 2226610321520576476762465)
  ·
    refine ⟨1669957741140432357571849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2226610321520576476762465 1669957741140432357571849)
    ·
      refine ⟨1252468305855324268178887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1669957741140432357571849 1252468305855324268178887)
      ·
        refine ⟨1878702458782986402268331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1252468305855324268178887 1878702458782986402268331)
        ·
          refine ⟨2818053688174479603402497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1878702458782986402268331 2818053688174479603402497)
          ·
            refine ⟨2113540266130859702551873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2818053688174479603402497 2113540266130859702551873)
            ·
              refine ⟨1585155199598144776913905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2113540266130859702551873 1585155199598144776913905)
              ·
                refine ⟨1188866399698608582685429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1585155199598144776913905 1188866399698608582685429)
                ·
                  refine ⟨111456224971744554626759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188866399698608582685429 111456224971744554626759)
                  ·
                    rfl

theorem cell23_1953542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1953542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953542 prefixEnd_1953542 := by exact prefixLift 1953542
  have htrace : WordTrace (prefixWord ++ tailWord_1953542) baseStart_1953542 baseEnd_1953542 := by
    simpa [prefixWord, tailWord_1953542, baseEnd_1953542] using wordTrace_append hprefix tailTrace_1953542
  have hstable : (prefixWord ++ tailWord_1953542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953542).length < 2 ^ (prefixWord ++ tailWord_1953542).sum := by decide
  have hdescent : baseEnd_1953542 < baseStart_1953542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953580 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_1953580 : Nat := 118140960795 + 1953580 * 2 ^ 59
def prefixEnd_1953580 : Nat := 4983230072969 + 3 ^ 40 * 1953580 * 2
def baseEnd_1953580 : Nat := 1003125537010571842965655

theorem tailTrace_1953580 : CollatzResearch.WordTrace tailWord_1953580 prefixEnd_1953580 1003125537010571842965655 := by
  unfold tailWord_1953580
  simp only [CollatzResearch.WordTrace]
  refine ⟨35626458131260389873141097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47501944175013853164188129 35626458131260389873141097)
  ·
    refine ⟨26719843598445292404855823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35626458131260389873141097 26719843598445292404855823)
    ·
      refine ⟨40079765397667938607283735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26719843598445292404855823 40079765397667938607283735)
      ·
        refine ⟨60119648096501907910925603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40079765397667938607283735 60119648096501907910925603)
        ·
          refine ⟨90179472144752861866388405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60119648096501907910925603 90179472144752861866388405)
          ·
            refine ⟨8454325513570580799973913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90179472144752861866388405 8454325513570580799973913)
            ·
              refine ⟨6340744135177935599980435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8454325513570580799973913 6340744135177935599980435)
              ·
                refine ⟨9511116202766903399970653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6340744135177935599980435 9511116202766903399970653)
                ·
                  refine ⟨3566668576037588774988995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9511116202766903399970653 3566668576037588774988995)
                  ·
                    refine ⟨5350002864056383162483493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3566668576037588774988995 5350002864056383162483493)
                    ·
                      refine ⟨1003125537010571842965655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5350002864056383162483493 1003125537010571842965655)
                      ·
                        rfl

theorem cell23_1953580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_1953580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953580 prefixEnd_1953580 := by exact prefixLift 1953580
  have htrace : WordTrace (prefixWord ++ tailWord_1953580) baseStart_1953580 baseEnd_1953580 := by
    simpa [prefixWord, tailWord_1953580, baseEnd_1953580] using wordTrace_append hprefix tailTrace_1953580
  have hstable : (prefixWord ++ tailWord_1953580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953580).length < 2 ^ (prefixWord ++ tailWord_1953580).sum := by decide
  have hdescent : baseEnd_1953580 < baseStart_1953580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953583 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 5]
def baseStart_1953583 : Nat := 118140960795 + 1953583 * 2 ^ 59
def prefixEnd_1953583 : Nat := 4983230072969 + 3 ^ 40 * 1953583 * 2
def baseEnd_1953583 : Nat := 1003127077452535331228141

theorem tailTrace_1953583 : CollatzResearch.WordTrace tailWord_1953583 prefixEnd_1953583 1003127077452535331228141 := by
  unfold tailWord_1953583
  simp only [CollatzResearch.WordTrace]
  refine ⟨71253025681509911258641403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47502017121006607505760935 71253025681509911258641403)
  ·
    refine ⟨106879538522264866887962105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71253025681509911258641403 106879538522264866887962105)
    ·
      refine ⟨80159653891698650165971579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106879538522264866887962105 80159653891698650165971579)
      ·
        refine ⟨120239480837547975248957369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80159653891698650165971579 120239480837547975248957369)
        ·
          refine ⟨90179610628160981436718027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120239480837547975248957369 90179610628160981436718027)
          ·
            refine ⟨135269415942241472155077041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90179610628160981436718027 135269415942241472155077041)
            ·
              refine ⟨101452061956681104116307781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135269415942241472155077041 101452061956681104116307781)
              ·
                refine ⟨19022261616877707021807709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101452061956681104116307781 19022261616877707021807709)
                ·
                  refine ⟨7133348106329140133177891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19022261616877707021807709 7133348106329140133177891)
                  ·
                    refine ⟨10700022159493710199766837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7133348106329140133177891 10700022159493710199766837)
                    ·
                      refine ⟨1003127077452535331228141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10700022159493710199766837 1003127077452535331228141)
                      ·
                        rfl

theorem cell23_1953583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_1953583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953583 prefixEnd_1953583 := by exact prefixLift 1953583
  have htrace : WordTrace (prefixWord ++ tailWord_1953583) baseStart_1953583 baseEnd_1953583 := by
    simpa [prefixWord, tailWord_1953583, baseEnd_1953583] using wordTrace_append hprefix tailTrace_1953583
  have hstable : (prefixWord ++ tailWord_1953583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953583).length < 2 ^ (prefixWord ++ tailWord_1953583).sum := by decide
  have hdescent : baseEnd_1953583 < baseStart_1953583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953594 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 1, 5]
def baseStart_1953594 : Nat := 118140960795 + 1953594 * 2 ^ 59
def prefixEnd_1953594 : Nat := 4983230072969 + 3 ^ 40 * 1953594 * 2
def baseEnd_1953594 : Nat := 334377575246578262730197

theorem tailTrace_1953594 : CollatzResearch.WordTrace tailWord_1953594 prefixEnd_1953594 334377575246578262730197 := by
  unfold tailWord_1953594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17813356721117515034322959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47502284589646706758194557 17813356721117515034322959)
  ·
    refine ⟨26720035081676272551484439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17813356721117515034322959 26720035081676272551484439)
    ·
      refine ⟨40080052622514408827226659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26720035081676272551484439 40080052622514408827226659)
      ·
        refine ⟨60120078933771613240839989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40080052622514408827226659 60120078933771613240839989)
        ·
          refine ⟨5636257400041088741328749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60120078933771613240839989 5636257400041088741328749)
          ·
            refine ⟨2113596525015408277998281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5636257400041088741328749 2113596525015408277998281)
            ·
              refine ⟨1585197393761556208498711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2113596525015408277998281 1585197393761556208498711)
              ·
                refine ⟨2377796090642334312748067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585197393761556208498711 2377796090642334312748067)
                ·
                  refine ⟨3566694135963501469122101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377796090642334312748067 3566694135963501469122101)
                  ·
                    refine ⟨334377575246578262730197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3566694135963501469122101 334377575246578262730197)
                    ·
                      rfl

theorem cell23_1953594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_1953594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953594 prefixEnd_1953594 := by exact prefixLift 1953594
  have htrace : WordTrace (prefixWord ++ tailWord_1953594) baseStart_1953594 baseEnd_1953594 := by
    simpa [prefixWord, tailWord_1953594, baseEnd_1953594] using wordTrace_append hprefix tailTrace_1953594
  have hstable : (prefixWord ++ tailWord_1953594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953594).length < 2 ^ (prefixWord ++ tailWord_1953594).sum := by decide
  have hdescent : baseEnd_1953594 < baseStart_1953594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953603 : List Nat := [1, 1, 1, 3, 1, 6, 10]
def baseStart_1953603 : Nat := 118140960795 + 1953603 * 2 ^ 59
def prefixEnd_1953603 : Nat := 4983230072969 + 3 ^ 40 * 1953603 * 2
def baseEnd_1953603 : Nat := 12384411692168212999729

theorem tailTrace_1953603 : CollatzResearch.WordTrace tailWord_1953603 prefixEnd_1953603 12384411692168212999729 := by
  unfold tailWord_1953603
  simp only [CollatzResearch.WordTrace]
  refine ⟨71253755141437454674369463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47502503427624969782912975 71253755141437454674369463)
  ·
    refine ⟨106880632712156182011554195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71253755141437454674369463 106880632712156182011554195)
    ·
      refine ⟨160320949068234273017331293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106880632712156182011554195 160320949068234273017331293)
      ·
        refine ⟨60120355900587852381499235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160320949068234273017331293 60120355900587852381499235)
        ·
          refine ⟨90180533850881778572248853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60120355900587852381499235 90180533850881778572248853)
          ·
            refine ⟨4227212524260083370574165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 90180533850881778572248853 4227212524260083370574165)
            ·
              refine ⟨12384411692168212999729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4227212524260083370574165 12384411692168212999729)
              ·
                rfl

theorem cell23_1953603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 10].length) (baseStart_1953603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953603 prefixEnd_1953603 := by exact prefixLift 1953603
  have htrace : WordTrace (prefixWord ++ tailWord_1953603) baseStart_1953603 baseEnd_1953603 := by
    simpa [prefixWord, tailWord_1953603, baseEnd_1953603] using wordTrace_append hprefix tailTrace_1953603
  have hstable : (prefixWord ++ tailWord_1953603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953603).length < 2 ^ (prefixWord ++ tailWord_1953603).sum := by decide
  have hdescent : baseEnd_1953603 < baseStart_1953603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953607 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 2, 4]
def baseStart_1953607 : Nat := 118140960795 + 1953607 * 2 ^ 59
def prefixEnd_1953607 : Nat := 4983230072969 + 3 ^ 40 * 1953607 * 2
def baseEnd_1953607 : Nat := 334379800329414412442677

theorem tailTrace_1953607 : CollatzResearch.WordTrace tailWord_1953607 prefixEnd_1953607 334379800329414412442677 := by
  unfold tailWord_1953607
  simp only [CollatzResearch.WordTrace]
  refine ⟨71253901033422963357515075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47502600688948642238343383 71253901033422963357515075)
  ·
    refine ⟨106880851550134445036272613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71253901033422963357515075 106880851550134445036272613)
    ·
      refine ⟨20040159665650208444301115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106880851550134445036272613 20040159665650208444301115)
      ·
        refine ⟨30060239498475312666451673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20040159665650208444301115 30060239498475312666451673)
        ·
          refine ⟨22545179623856484499838755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30060239498475312666451673 22545179623856484499838755)
          ·
            refine ⟨33817769435784726749758133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22545179623856484499838755 33817769435784726749758133)
            ·
              refine ⟨3170415884604818132789825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33817769435784726749758133 3170415884604818132789825)
              ·
                refine ⟨2377811913453613599592369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3170415884604818132789825 2377811913453613599592369)
                ·
                  refine ⟨1783358935090210199694277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2377811913453613599592369 1783358935090210199694277)
                  ·
                    refine ⟨334379800329414412442677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1783358935090210199694277 334379800329414412442677)
                    ·
                      rfl

theorem cell23_1953607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_1953607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953607 prefixEnd_1953607 := by exact prefixLift 1953607
  have htrace : WordTrace (prefixWord ++ tailWord_1953607) baseStart_1953607 baseEnd_1953607 := by
    simpa [prefixWord, tailWord_1953607, baseEnd_1953607] using wordTrace_append hprefix tailTrace_1953607
  have hstable : (prefixWord ++ tailWord_1953607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953607).length < 2 ^ (prefixWord ++ tailWord_1953607).sum := by decide
  have hdescent : baseEnd_1953607 < baseStart_1953607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953634 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_1953634 : Nat := 118140960795 + 1953634 * 2 ^ 59
def prefixEnd_1953634 : Nat := 4983230072969 + 3 ^ 40 * 1953634 * 2
def baseEnd_1953634 : Nat := 1003153264965914631690407

theorem tailTrace_1953634 : CollatzResearch.WordTrace tailWord_1953634 prefixEnd_1953634 1003153264965914631690407 := by
  unfold tailWord_1953634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17813721451081286742186989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47503257202883431312498637 17813721451081286742186989)
  ·
    refine ⟨6680145544155482528320121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17813721451081286742186989 6680145544155482528320121)
    ·
      refine ⟨5010109158116611896240091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6680145544155482528320121 5010109158116611896240091)
      ·
        refine ⟨7515163737174917844360137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5010109158116611896240091 7515163737174917844360137)
        ·
          refine ⟨5636372802881188383270103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7515163737174917844360137 5636372802881188383270103)
          ·
            refine ⟨8454559204321782574905155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5636372802881188383270103 8454559204321782574905155)
            ·
              refine ⟨12681838806482673862357733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8454559204321782574905155 12681838806482673862357733)
              ·
                refine ⟨2377844776215501349192075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12681838806482673862357733 2377844776215501349192075)
                ·
                  refine ⟨3566767164323252023788113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2377844776215501349192075 3566767164323252023788113)
                  ·
                    refine ⟨2675075373242439017841085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3566767164323252023788113 2675075373242439017841085)
                    ·
                      refine ⟨1003153264965914631690407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2675075373242439017841085 1003153264965914631690407)
                      ·
                        rfl

theorem cell23_1953634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_1953634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953634 prefixEnd_1953634 := by exact prefixLift 1953634
  have htrace : WordTrace (prefixWord ++ tailWord_1953634) baseStart_1953634 baseEnd_1953634 := by
    simpa [prefixWord, tailWord_1953634, baseEnd_1953634] using wordTrace_append hprefix tailTrace_1953634
  have hstable : (prefixWord ++ tailWord_1953634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953634).length < 2 ^ (prefixWord ++ tailWord_1953634).sum := by decide
  have hdescent : baseEnd_1953634 < baseStart_1953634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953654 : List Nat := [5, 1, 1, 3, 3, 1, 9]
def baseStart_1953654 : Nat := 118140960795 + 1953654 * 2 ^ 59
def prefixEnd_1953654 : Nat := 4983230072969 + 3 ^ 40 * 1953654 * 2
def baseEnd_1953654 : Nat := 12384734994802525351115

theorem tailTrace_1953654 : CollatzResearch.WordTrace tailWord_1953654 prefixEnd_1953654 12384734994802525351115 := by
  unfold tailWord_1953654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4453475954015793149029751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47503743509501793589650677 4453475954015793149029751)
  ·
    refine ⟨6680213931023689723544627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4453475954015793149029751 6680213931023689723544627)
    ·
      refine ⟨10020320896535534585316941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6680213931023689723544627 10020320896535534585316941)
      ·
        refine ⟨3757620336200825469493853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10020320896535534585316941 3757620336200825469493853)
        ·
          refine ⟨1409107626075309551060195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3757620336200825469493853 1409107626075309551060195)
          ·
            refine ⟨2113661439112964326590293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409107626075309551060195 2113661439112964326590293)
            ·
              refine ⟨12384734994802525351115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2113661439112964326590293 12384734994802525351115)
              ·
                rfl

theorem cell23_1953654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 9].length) (baseStart_1953654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953654 prefixEnd_1953654 := by exact prefixLift 1953654
  have htrace : WordTrace (prefixWord ++ tailWord_1953654) baseStart_1953654 baseEnd_1953654 := by
    simpa [prefixWord, tailWord_1953654, baseEnd_1953654] using wordTrace_append hprefix tailTrace_1953654
  have hstable : (prefixWord ++ tailWord_1953654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953654).length < 2 ^ (prefixWord ++ tailWord_1953654).sum := by decide
  have hdescent : baseEnd_1953654 < baseStart_1953654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953665 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1953665 : Nat := 118140960795 + 1953665 * 2 ^ 59
def prefixEnd_1953665 : Nat := 4983230072969 + 3 ^ 40 * 1953665 * 2
def baseEnd_1953665 : Nat := 1003169182866204010402765

theorem tailTrace_1953665 : CollatzResearch.WordTrace tailWord_1953665 prefixEnd_1953665 1003169182866204010402765 := by
  unfold tailWord_1953665
  simp only [CollatzResearch.WordTrace]
  refine ⟨71256016467212839263126449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47504010978141892842084299 71256016467212839263126449)
  ·
    refine ⟨53442012350409629447344837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71256016467212839263126449 53442012350409629447344837)
    ·
      refine ⟨10020377315701805521377157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53442012350409629447344837 10020377315701805521377157)
      ·
        refine ⟨1878820746694088535258217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10020377315701805521377157 1878820746694088535258217)
        ·
          refine ⟨1409115560020566401443663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1878820746694088535258217 1409115560020566401443663)
          ·
            refine ⟨2113673340030849602165495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409115560020566401443663 2113673340030849602165495)
            ·
              refine ⟨3170510010046274403248243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2113673340030849602165495 3170510010046274403248243)
              ·
                refine ⟨4755765015069411604872365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3170510010046274403248243 4755765015069411604872365)
                ·
                  refine ⟨1783411880651029351827137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4755765015069411604872365 1783411880651029351827137)
                  ·
                    refine ⟨1337558910488272013870353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1783411880651029351827137 1337558910488272013870353)
                    ·
                      refine ⟨1003169182866204010402765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337558910488272013870353 1003169182866204010402765)
                      ·
                        rfl

theorem cell23_1953665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1953665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953665 prefixEnd_1953665 := by exact prefixLift 1953665
  have htrace : WordTrace (prefixWord ++ tailWord_1953665) baseStart_1953665 baseEnd_1953665 := by
    simpa [prefixWord, tailWord_1953665, baseEnd_1953665] using wordTrace_append hprefix tailTrace_1953665
  have hstable : (prefixWord ++ tailWord_1953665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953665).length < 2 ^ (prefixWord ++ tailWord_1953665).sum := by decide
  have hdescent : baseEnd_1953665 < baseStart_1953665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953721 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 2, 2, 2]
def baseStart_1953721 : Nat := 118140960795 + 1953721 * 2 ^ 59
def prefixEnd_1953721 : Nat := 4983230072969 + 3 ^ 40 * 1953721 * 2
def baseEnd_1953721 : Nat := 1003197937782855791302507

theorem tailTrace_1953721 : CollatzResearch.WordTrace tailWord_1953721 prefixEnd_1953721 1003197937782855791302507 := by
  unfold tailWord_1953721
  simp only [CollatzResearch.WordTrace]
  refine ⟨71258058955009960827165017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47505372636673307218110011 71258058955009960827165017)
  ·
    refine ⟨53443544216257470620373763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71258058955009960827165017 53443544216257470620373763)
    ·
      refine ⟨80165316324386205930560645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53443544216257470620373763 80165316324386205930560645)
      ·
        refine ⟨15030996810822413611980121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80165316324386205930560645 15030996810822413611980121)
        ·
          refine ⟨11273247608116810208985091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15030996810822413611980121 11273247608116810208985091)
          ·
            refine ⟨16909871412175215313477637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11273247608116810208985091 16909871412175215313477637)
            ·
              refine ⟨3170600889782852871277057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16909871412175215313477637 3170600889782852871277057)
              ·
                refine ⟨2377950667337139653457793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3170600889782852871277057 2377950667337139653457793)
                ·
                  refine ⟨1783463000502854740093345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2377950667337139653457793 1783463000502854740093345)
                  ·
                    refine ⟨1337597250377141055070009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1783463000502854740093345 1337597250377141055070009)
                    ·
                      refine ⟨1003197937782855791302507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337597250377141055070009 1003197937782855791302507)
                      ·
                        rfl

theorem cell23_1953721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_1953721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953721 prefixEnd_1953721 := by exact prefixLift 1953721
  have htrace : WordTrace (prefixWord ++ tailWord_1953721) baseStart_1953721 baseEnd_1953721 := by
    simpa [prefixWord, tailWord_1953721, baseEnd_1953721] using wordTrace_append hprefix tailTrace_1953721
  have hstable : (prefixWord ++ tailWord_1953721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953721).length < 2 ^ (prefixWord ++ tailWord_1953721).sum := by decide
  have hdescent : baseEnd_1953721 < baseStart_1953721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953727 : List Nat := [1, 1, 2, 2, 2, 1, 5, 4, 5]
def baseStart_1953727 : Nat := 118140960795 + 1953727 * 2 ^ 59
def prefixEnd_1953727 : Nat := 4983230072969 + 3 ^ 40 * 1953727 * 2
def baseEnd_1953727 : Nat := 111466779851864751980831

theorem tailTrace_1953727 : CollatzResearch.WordTrace tailWord_1953727 prefixEnd_1953727 111466779851864751980831 := by
  unfold tailWord_1953727
  simp only [CollatzResearch.WordTrace]
  refine ⟨71258277792988223851883435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47505518528658815901255623 71258277792988223851883435)
  ·
    refine ⟨106887416689482335777825153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71258277792988223851883435 106887416689482335777825153)
    ·
      refine ⟨80165562517111751833368865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106887416689482335777825153 80165562517111751833368865)
      ·
        refine ⟨60124171887833813875026649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80165562517111751833368865 60124171887833813875026649)
        ·
          refine ⟨45093128915875360406269987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60124171887833813875026649 45093128915875360406269987)
          ·
            refine ⟨67639693373813040609404981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45093128915875360406269987 67639693373813040609404981)
            ·
              refine ⟨6341221253794972557131717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67639693373813040609404981 6341221253794972557131717)
              ·
                refine ⟨1188978985086557354462197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6341221253794972557131717 1188978985086557354462197)
                ·
                  refine ⟨111466779851864751980831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1188978985086557354462197 111466779851864751980831)
                  ·
                    rfl

theorem cell23_1953727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4, 5].length) (baseStart_1953727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953727 prefixEnd_1953727 := by exact prefixLift 1953727
  have htrace : WordTrace (prefixWord ++ tailWord_1953727) baseStart_1953727 baseEnd_1953727 := by
    simpa [prefixWord, tailWord_1953727, baseEnd_1953727] using wordTrace_append hprefix tailTrace_1953727
  have hstable : (prefixWord ++ tailWord_1953727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953727).length < 2 ^ (prefixWord ++ tailWord_1953727).sum := by decide
  have hdescent : baseEnd_1953727 < baseStart_1953727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953787 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 3, 4]
def baseStart_1953787 : Nat := 118140960795 + 1953787 * 2 ^ 59
def prefixEnd_1953787 : Nat := 4983230072969 + 3 ^ 40 * 1953787 * 2
def baseEnd_1953787 : Nat := 334410609168684177692401

theorem tailTrace_1953787 : CollatzResearch.WordTrace tailWord_1953787 prefixEnd_1953787 334410609168684177692401 := by
  unfold tailWord_1953787
  simp only [CollatzResearch.WordTrace]
  refine ⟨71260466172770854099067615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47506977448513902732711743 71260466172770854099067615)
  ·
    refine ⟨106890699259156281148601423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71260466172770854099067615 106890699259156281148601423)
    ·
      refine ⟨160336048888734421722902135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106890699259156281148601423 160336048888734421722902135)
      ·
        refine ⟨240504073333101632584353203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160336048888734421722902135 240504073333101632584353203)
        ·
          refine ⟨360756109999652448876529805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240504073333101632584353203 360756109999652448876529805)
          ·
            refine ⟨135283541249869668328698677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360756109999652448876529805 135283541249869668328698677)
            ·
              refine ⟨12682831992175281405815501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135283541249869668328698677 12682831992175281405815501)
              ·
                refine ⟨4756061997065730527180813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12682831992175281405815501 4756061997065730527180813)
                ·
                  refine ⟨1783523248899648947692805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4756061997065730527180813 1783523248899648947692805)
                  ·
                    refine ⟨334410609168684177692401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1783523248899648947692805 334410609168684177692401)
                    ·
                      rfl

theorem cell23_1953787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 4].length) (baseStart_1953787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953787 prefixEnd_1953787 := by exact prefixLift 1953787
  have htrace : WordTrace (prefixWord ++ tailWord_1953787) baseStart_1953787 baseEnd_1953787 := by
    simpa [prefixWord, tailWord_1953787, baseEnd_1953787] using wordTrace_append hprefix tailTrace_1953787
  have hstable : (prefixWord ++ tailWord_1953787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953787).length < 2 ^ (prefixWord ++ tailWord_1953787).sum := by decide
  have hdescent : baseEnd_1953787 < baseStart_1953787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953797 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 1, 4, 3]
def baseStart_1953797 : Nat := 118140960795 + 1953797 * 2 ^ 59
def prefixEnd_1953797 : Nat := 4983230072969 + 3 ^ 40 * 1953797 * 2
def baseEnd_1953797 : Nat := 1003236962312597493952157

theorem tailTrace_1953797 : CollatzResearch.WordTrace tailWord_1953797 prefixEnd_1953797 1003236962312597493952157 := by
  unfold tailWord_1953797
  simp only [CollatzResearch.WordTrace]
  refine ⟨71260830902734625806931645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47507220601823083871287763 71260830902734625806931645)
  ·
    refine ⟨26722811588525484677599367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71260830902734625806931645 26722811588525484677599367)
    ·
      refine ⟨40084217382788227016399051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26722811588525484677599367 40084217382788227016399051)
      ·
        refine ⟨60126326074182340524598577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40084217382788227016399051 60126326074182340524598577)
        ·
          refine ⟨45094744555636755393448933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60126326074182340524598577 45094744555636755393448933)
          ·
            refine ⟨8455264604181891636271675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45094744555636755393448933 8455264604181891636271675)
            ·
              refine ⟨12682896906272837454407513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8455264604181891636271675 12682896906272837454407513)
              ·
                refine ⟨9512172679704628090805635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12682896906272837454407513 9512172679704628090805635)
                ·
                  refine ⟨14268259019556942136208453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9512172679704628090805635 14268259019556942136208453)
                  ·
                    refine ⟨2675298566166926650539085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14268259019556942136208453 2675298566166926650539085)
                    ·
                      refine ⟨1003236962312597493952157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2675298566166926650539085 1003236962312597493952157)
                      ·
                        rfl

theorem cell23_1953797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_1953797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953797 prefixEnd_1953797 := by exact prefixLift 1953797
  have htrace : WordTrace (prefixWord ++ tailWord_1953797) baseStart_1953797 baseEnd_1953797 := by
    simpa [prefixWord, tailWord_1953797, baseEnd_1953797] using wordTrace_append hprefix tailTrace_1953797
  have hstable : (prefixWord ++ tailWord_1953797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953797).length < 2 ^ (prefixWord ++ tailWord_1953797).sum := by decide
  have hdescent : baseEnd_1953797 < baseStart_1953797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953867 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 4]
def baseStart_1953867 : Nat := 118140960795 + 1953867 * 2 ^ 59
def prefixEnd_1953867 : Nat := 4983230072969 + 3 ^ 40 * 1953867 * 2
def baseEnd_1953867 : Nat := 1003272905958412220076835

theorem tailTrace_1953867 : CollatzResearch.WordTrace tailWord_1953867 prefixEnd_1953867 1003272905958412220076835 := by
  unfold tailWord_1953867
  simp only [CollatzResearch.WordTrace]
  refine ⟨71263384012481027761979855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47508922674987351841319903 71263384012481027761979855)
  ·
    refine ⟨106895076018721541642969783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71263384012481027761979855 106895076018721541642969783)
    ·
      refine ⟨160342614028082312464454675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106895076018721541642969783 160342614028082312464454675)
      ·
        refine ⟨240513921042123468696682013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160342614028082312464454675 240513921042123468696682013)
        ·
          refine ⟨90192720390796300761255755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240513921042123468696682013 90192720390796300761255755)
          ·
            refine ⟨135289080586194451141883633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90192720390796300761255755 135289080586194451141883633)
            ·
              refine ⟨101466810439645838356412725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135289080586194451141883633 101466810439645838356412725)
              ·
                refine ⟨9512513478716797345913693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101466810439645838356412725 9512513478716797345913693)
                ·
                  refine ⟨3567192554518799004717635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9512513478716797345913693 3567192554518799004717635)
                  ·
                    refine ⟨5350788831778198507076453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3567192554518799004717635 5350788831778198507076453)
                    ·
                      refine ⟨1003272905958412220076835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5350788831778198507076453 1003272905958412220076835)
                      ·
                        rfl

theorem cell23_1953867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 4].length) (baseStart_1953867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953867 prefixEnd_1953867 := by exact prefixLift 1953867
  have htrace : WordTrace (prefixWord ++ tailWord_1953867) baseStart_1953867 baseEnd_1953867 := by
    simpa [prefixWord, tailWord_1953867, baseEnd_1953867] using wordTrace_append hprefix tailTrace_1953867
  have hstable : (prefixWord ++ tailWord_1953867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953867).length < 2 ^ (prefixWord ++ tailWord_1953867).sum := by decide
  have hdescent : baseEnd_1953867 < baseStart_1953867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953877 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_1953877 : Nat := 118140960795 + 1953877 * 2 ^ 59
def prefixEnd_1953877 : Nat := 4983230072969 + 3 ^ 40 * 1953877 * 2
def baseEnd_1953877 : Nat := 334426013588319060317263

theorem tailTrace_1953877 : CollatzResearch.WordTrace tailWord_1953877 prefixEnd_1953877 334426013588319060317263 := by
  unfold tailWord_1953877
  simp only [CollatzResearch.WordTrace]
  refine ⟨71263748742444799469843885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47509165828296532979895923 71263748742444799469843885)
  ·
    refine ⟨26723905778416799801191457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71263748742444799469843885 26723905778416799801191457)
    ·
      refine ⟨20042929333812599850893593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26723905778416799801191457 20042929333812599850893593)
      ·
        refine ⟨15032197000359449888170195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20042929333812599850893593 15032197000359449888170195)
        ·
          refine ⟨22548295500539174832255293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15032197000359449888170195 22548295500539174832255293)
          ·
            refine ⟨8455610812702190562095735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22548295500539174832255293 8455610812702190562095735)
            ·
              refine ⟨12683416219053285843143603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8455610812702190562095735 12683416219053285843143603)
              ·
                refine ⟨19025124328579928764715405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12683416219053285843143603 19025124328579928764715405)
                ·
                  refine ⟨7134421623217473286768277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19025124328579928764715405 7134421623217473286768277)
                  ·
                    refine ⟨334426013588319060317263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7134421623217473286768277 334426013588319060317263)
                    ·
                      rfl

theorem cell23_1953877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_1953877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953877 prefixEnd_1953877 := by exact prefixLift 1953877
  have htrace : WordTrace (prefixWord ++ tailWord_1953877) baseStart_1953877 baseEnd_1953877 := by
    simpa [prefixWord, tailWord_1953877, baseEnd_1953877] using wordTrace_append hprefix tailTrace_1953877
  have hstable : (prefixWord ++ tailWord_1953877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953877).length < 2 ^ (prefixWord ++ tailWord_1953877).sum := by decide
  have hdescent : baseEnd_1953877 < baseStart_1953877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953887 : List Nat := [1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 5]
def baseStart_1953887 : Nat := 118140960795 + 1953887 * 2 ^ 59
def prefixEnd_1953887 : Nat := 4983230072969 + 3 ^ 40 * 1953887 * 2
def baseEnd_1953887 : Nat := 1003283175571502141826743

theorem tailTrace_1953887 : CollatzResearch.WordTrace tailWord_1953887 prefixEnd_1953887 1003283175571502141826743 := by
  unfold tailWord_1953887
  simp only [CollatzResearch.WordTrace]
  refine ⟨71264113472408571177707915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47509408981605714118471943 71264113472408571177707915)
  ·
    refine ⟨106896170208612856766561873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71264113472408571177707915 106896170208612856766561873)
    ·
      refine ⟨80172127656459642574921405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106896170208612856766561873 80172127656459642574921405)
      ·
        refine ⟨30064547871172365965595527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80172127656459642574921405 30064547871172365965595527)
        ·
          refine ⟨45096821806758548948393291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30064547871172365965595527 45096821806758548948393291)
          ·
            refine ⟨67645232710137823422589937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45096821806758548948393291 67645232710137823422589937)
            ·
              refine ⟨50733924532603367566942453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67645232710137823422589937 50733924532603367566942453)
              ·
                refine ⟨4756305424931565709400855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50733924532603367566942453 4756305424931565709400855)
                ·
                  refine ⟨7134458137397348564101283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756305424931565709400855 7134458137397348564101283)
                  ·
                    refine ⟨10701687206096022846151925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7134458137397348564101283 10701687206096022846151925)
                    ·
                      refine ⟨1003283175571502141826743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10701687206096022846151925 1003283175571502141826743)
                      ·
                        rfl

theorem cell23_1953887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_1953887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953887 prefixEnd_1953887 := by exact prefixLift 1953887
  have htrace : WordTrace (prefixWord ++ tailWord_1953887) baseStart_1953887 baseEnd_1953887 := by
    simpa [prefixWord, tailWord_1953887, baseEnd_1953887] using wordTrace_append hprefix tailTrace_1953887
  have hstable : (prefixWord ++ tailWord_1953887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953887).length < 2 ^ (prefixWord ++ tailWord_1953887).sum := by decide
  have hdescent : baseEnd_1953887 < baseStart_1953887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953897 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_1953897 : Nat := 118140960795 + 1953897 * 2 ^ 59
def prefixEnd_1953897 : Nat := 4983230072969 + 3 ^ 40 * 1953897 * 2
def baseEnd_1953897 : Nat := 1003288310378047102701697

theorem tailTrace_1953897 : CollatzResearch.WordTrace tailWord_1953897 prefixEnd_1953897 1003288310378047102701697 := by
  unfold tailWord_1953897
  simp only [CollatzResearch.WordTrace]
  refine ⟨71264478202372342885571945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47509652134914895257047963 71264478202372342885571945)
  ·
    refine ⟨53448358651779257164178959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71264478202372342885571945 53448358651779257164178959)
    ·
      refine ⟨80172537977668885746268439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53448358651779257164178959 80172537977668885746268439)
      ·
        refine ⟨120258806966503328619402659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80172537977668885746268439 120258806966503328619402659)
        ·
          refine ⟨180388210449754992929103989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120258806966503328619402659 180388210449754992929103989)
          ·
            refine ⟨16911394729664530587103499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180388210449754992929103989 16911394729664530587103499)
            ·
              refine ⟨25367092094496795880655249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16911394729664530587103499 25367092094496795880655249)
              ·
                refine ⟨19025319070872596910491437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25367092094496795880655249 19025319070872596910491437)
                ·
                  refine ⟨7134494651577223841434289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19025319070872596910491437 7134494651577223841434289)
                  ·
                    refine ⟨5350870988682917881075717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7134494651577223841434289 5350870988682917881075717)
                    ·
                      refine ⟨1003288310378047102701697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5350870988682917881075717 1003288310378047102701697)
                      ·
                        rfl

theorem cell23_1953897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_1953897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953897 prefixEnd_1953897 := by exact prefixLift 1953897
  have htrace : WordTrace (prefixWord ++ tailWord_1953897) baseStart_1953897 baseEnd_1953897 := by
    simpa [prefixWord, tailWord_1953897, baseEnd_1953897] using wordTrace_append hprefix tailTrace_1953897
  have hstable : (prefixWord ++ tailWord_1953897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953897).length < 2 ^ (prefixWord ++ tailWord_1953897).sum := by decide
  have hdescent : baseEnd_1953897 < baseStart_1953897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953904 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 3]
def baseStart_1953904 : Nat := 118140960795 + 1953904 * 2 ^ 59
def prefixEnd_1953904 : Nat := 4983230072969 + 3 ^ 40 * 1953904 * 2
def baseEnd_1953904 : Nat := 1003291904742628575314165

theorem tailTrace_1953904 : CollatzResearch.WordTrace tailWord_1953904 prefixEnd_1953904 1003291904742628575314165 := by
  unfold tailWord_1953904
  simp only [CollatzResearch.WordTrace]
  refine ⟨35632366756673491540538383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47509822342231322054051177 35632366756673491540538383)
  ·
    refine ⟨53448550135010237310807575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35632366756673491540538383 53448550135010237310807575)
    ·
      refine ⟨80172825202515355966211363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53448550135010237310807575 80172825202515355966211363)
      ·
        refine ⟨120259237803773033949317045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80172825202515355966211363 120259237803773033949317045)
        ·
          refine ⟨11274303544103721932748473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120259237803773033949317045 11274303544103721932748473)
          ·
            refine ⟨8455727658077791449561355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11274303544103721932748473 8455727658077791449561355)
            ·
              refine ⟨12683591487116687174342033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8455727658077791449561355 12683591487116687174342033)
              ·
                refine ⟨9512693615337515380756525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12683591487116687174342033 9512693615337515380756525)
                ·
                  refine ⟨3567260105751568267783697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9512693615337515380756525 3567260105751568267783697)
                  ·
                    refine ⟨2675445079313676200837773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3567260105751568267783697 2675445079313676200837773)
                    ·
                      refine ⟨1003291904742628575314165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2675445079313676200837773 1003291904742628575314165)
                      ·
                        rfl

theorem cell23_1953904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 3].length) (baseStart_1953904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953904 prefixEnd_1953904 := by exact prefixLift 1953904
  have htrace : WordTrace (prefixWord ++ tailWord_1953904) baseStart_1953904 baseEnd_1953904 := by
    simpa [prefixWord, tailWord_1953904, baseEnd_1953904] using wordTrace_append hprefix tailTrace_1953904
  have hstable : (prefixWord ++ tailWord_1953904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953904).length < 2 ^ (prefixWord ++ tailWord_1953904).sum := by decide
  have hdescent : baseEnd_1953904 < baseStart_1953904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953924 : List Nat := [2, 3, 2, 1, 2, 1, 5, 7]
def baseStart_1953924 : Nat := 118140960795 + 1953924 * 2 ^ 59
def prefixEnd_1953924 : Nat := 4983230072969 + 3 ^ 40 * 1953924 * 2
def baseEnd_1953924 : Nat := 37159339790952536928299

theorem tailTrace_1953924 : CollatzResearch.WordTrace tailWord_1953924 prefixEnd_1953924 37159339790952536928299 := by
  unfold tailWord_1953924
  simp only [CollatzResearch.WordTrace]
  refine ⟨35632731486637263248402413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47510308648849684331203217 35632731486637263248402413)
  ·
    refine ⟨13362274307488973718150905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35632731486637263248402413 13362274307488973718150905)
    ·
      refine ⟨10021705730616730288613179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13362274307488973718150905 10021705730616730288613179)
      ·
        refine ⟨15032558595925095432919769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10021705730616730288613179 15032558595925095432919769)
        ·
          refine ⟨11274418946943821574689827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15032558595925095432919769 11274418946943821574689827)
          ·
            refine ⟨16911628420415732362034741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274418946943821574689827 16911628420415732362034741)
            ·
              refine ⟨1585465164413974908940757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16911628420415732362034741 1585465164413974908940757)
              ·
                refine ⟨37159339790952536928299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1585465164413974908940757 37159339790952536928299)
                ·
                  rfl

theorem cell23_1953924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 7].length) (baseStart_1953924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953924 prefixEnd_1953924 := by exact prefixLift 1953924
  have htrace : WordTrace (prefixWord ++ tailWord_1953924) baseStart_1953924 baseEnd_1953924 := by
    simpa [prefixWord, tailWord_1953924, baseEnd_1953924] using wordTrace_append hprefix tailTrace_1953924
  have hstable : (prefixWord ++ tailWord_1953924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953924).length < 2 ^ (prefixWord ++ tailWord_1953924).sum := by decide
  have hdescent : baseEnd_1953924 < baseStart_1953924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953986 : List Nat := [3, 5, 1, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_1953986 : Nat := 118140960795 + 1953986 * 2 ^ 59
def prefixEnd_1953986 : Nat := 4983230072969 + 3 ^ 40 * 1953986 * 2
def baseEnd_1953986 : Nat := 1003334010156297254488789

theorem tailTrace_1953986 : CollatzResearch.WordTrace tailWord_1953986 prefixEnd_1953986 1003334010156297254488789 := by
  unfold tailWord_1953986
  simp only [CollatzResearch.WordTrace]
  refine ⟨17816931074762477771390453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47511816199366607390374541 17816931074762477771390453)
  ·
    refine ⟨1670337288258982291067855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17816931074762477771390453 1670337288258982291067855)
    ·
      refine ⟨2505505932388473436601783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1670337288258982291067855 2505505932388473436601783)
      ·
        refine ⟨3758258898582710154902675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505505932388473436601783 3758258898582710154902675)
        ·
          refine ⟨5637388347874065232354013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758258898582710154902675 5637388347874065232354013)
          ·
            refine ⟨2114020630452774462132755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5637388347874065232354013 2114020630452774462132755)
            ·
              refine ⟨3171030945679161693199133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114020630452774462132755 3171030945679161693199133)
              ·
                refine ⟨1189136604629685634949675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3171030945679161693199133 1189136604629685634949675)
                ·
                  refine ⟨1783704906944528452424513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189136604629685634949675 1783704906944528452424513)
                  ·
                    refine ⟨1337778680208396339318385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1783704906944528452424513 1337778680208396339318385)
                    ·
                      refine ⟨1003334010156297254488789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337778680208396339318385 1003334010156297254488789)
                      ·
                        rfl

theorem cell23_1953986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_1953986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953986 prefixEnd_1953986 := by exact prefixLift 1953986
  have htrace : WordTrace (prefixWord ++ tailWord_1953986) baseStart_1953986 baseEnd_1953986 := by
    simpa [prefixWord, tailWord_1953986, baseEnd_1953986] using wordTrace_append hprefix tailTrace_1953986
  have hstable : (prefixWord ++ tailWord_1953986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953986).length < 2 ^ (prefixWord ++ tailWord_1953986).sum := by decide
  have hdescent : baseEnd_1953986 < baseStart_1953986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1953994 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_1953994 : Nat := 118140960795 + 1953994 * 2 ^ 59
def prefixEnd_1953994 : Nat := 4983230072969 + 3 ^ 40 * 1953994 * 2
def baseEnd_1953994 : Nat := 1003338118001533223188751

theorem tailTrace_1953994 : CollatzResearch.WordTrace tailWord_1953994 prefixEnd_1953994 1003338118001533223188751 := by
  unfold tailWord_1953994
  simp only [CollatzResearch.WordTrace]
  refine ⟨17817004020755232112963259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47512010722013952301235357 17817004020755232112963259)
  ·
    refine ⟨26725506031132848169444889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17817004020755232112963259 26725506031132848169444889)
    ·
      refine ⟨20044129523349636127083667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26725506031132848169444889 20044129523349636127083667)
      ·
        refine ⟨30066194285024454190625501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20044129523349636127083667 30066194285024454190625501)
        ·
          refine ⟨11274822856884170321484563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30066194285024454190625501 11274822856884170321484563)
          ·
            refine ⟨16912234285326255482226845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274822856884170321484563 16912234285326255482226845)
            ·
              refine ⟨6342087856997345805835067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16912234285326255482226845 6342087856997345805835067)
              ·
                refine ⟨9513131785496018708752601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6342087856997345805835067 9513131785496018708752601)
                ·
                  refine ⟨7134848839122014031564451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9513131785496018708752601 7134848839122014031564451)
                  ·
                    refine ⟨10702273258683021047346677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7134848839122014031564451 10702273258683021047346677)
                    ·
                      refine ⟨1003338118001533223188751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10702273258683021047346677 1003338118001533223188751)
                      ·
                        rfl

theorem cell23_1953994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_1953994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1953994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1953994 prefixEnd_1953994 := by exact prefixLift 1953994
  have htrace : WordTrace (prefixWord ++ tailWord_1953994) baseStart_1953994 baseEnd_1953994 := by
    simpa [prefixWord, tailWord_1953994, baseEnd_1953994] using wordTrace_append hprefix tailTrace_1953994
  have hstable : (prefixWord ++ tailWord_1953994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1953994).length < 2 ^ (prefixWord ++ tailWord_1953994).sum := by decide
  have hdescent : baseEnd_1953994 < baseStart_1953994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1953994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954007 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_1954007 : Nat := 118140960795 + 1954007 * 2 ^ 59
def prefixEnd_1954007 : Nat := 4983230072969 + 3 ^ 40 * 1954007 * 2
def baseEnd_1954007 : Nat := 1003344793250041672326191

theorem tailTrace_1954007 : CollatzResearch.WordTrace tailWord_1954007 prefixEnd_1954007 1003344793250041672326191 := by
  unfold tailWord_1954007
  simp only [CollatzResearch.WordTrace]
  refine ⟨71268490231973831672076275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47512326821315887781384183 71268490231973831672076275)
  ·
    refine ⟨106902735347960747508114413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71268490231973831672076275 106902735347960747508114413)
    ·
      refine ⟨40088525755485280315542905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106902735347960747508114413 40088525755485280315542905)
      ·
        refine ⟨30066394316613960236657179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40088525755485280315542905 30066394316613960236657179)
        ·
          refine ⟨45099591474920940354985769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30066394316613960236657179 45099591474920940354985769)
          ·
            refine ⟨33824693606190705266239327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45099591474920940354985769 33824693606190705266239327)
            ·
              refine ⟨50737040409286057899358991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33824693606190705266239327 50737040409286057899358991)
              ·
                refine ⟨76105560613929086849038487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50737040409286057899358991 76105560613929086849038487)
                ·
                  refine ⟨114158340920893630273557731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76105560613929086849038487 114158340920893630273557731)
                  ·
                    refine ⟨171237511381340445410336597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114158340920893630273557731 171237511381340445410336597)
                    ·
                      refine ⟨1003344793250041672326191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 171237511381340445410336597 1003344793250041672326191)
                      ·
                        rfl

theorem cell23_1954007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_1954007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954007 prefixEnd_1954007 := by exact prefixLift 1954007
  have htrace : WordTrace (prefixWord ++ tailWord_1954007) baseStart_1954007 baseEnd_1954007 := by
    simpa [prefixWord, tailWord_1954007, baseEnd_1954007] using wordTrace_append hprefix tailTrace_1954007
  have hstable : (prefixWord ++ tailWord_1954007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954007).length < 2 ^ (prefixWord ++ tailWord_1954007).sum := by decide
  have hdescent : baseEnd_1954007 < baseStart_1954007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954008 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 4, 2, 2]
def baseStart_1954008 : Nat := 118140960795 + 1954008 * 2 ^ 59
def prefixEnd_1954008 : Nat := 4983230072969 + 3 ^ 40 * 1954008 * 2
def baseEnd_1954008 : Nat := 1003345306730696168413687

theorem tailTrace_1954008 : CollatzResearch.WordTrace tailWord_1954008 prefixEnd_1954008 1003345306730696168413687 := by
  unfold tailWord_1954008
  simp only [CollatzResearch.WordTrace]
  refine ⟨35634263352485104421431339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47512351136646805895241785 35634263352485104421431339)
  ·
    refine ⟨53451395028727656632147009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35634263352485104421431339 53451395028727656632147009)
    ·
      refine ⟨40088546271545742474110257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53451395028727656632147009 40088546271545742474110257)
      ·
        refine ⟨30066409703659306855582693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40088546271545742474110257 30066409703659306855582693)
        ·
          refine ⟨5637451819436120035421755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30066409703659306855582693 5637451819436120035421755)
          ·
            refine ⟨8456177729154180053132633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637451819436120035421755 8456177729154180053132633)
            ·
              refine ⟨6342133296865635039849475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8456177729154180053132633 6342133296865635039849475)
              ·
                refine ⟨9513199945298452559774213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6342133296865635039849475 9513199945298452559774213)
                ·
                  refine ⟨1783724989743459854957665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9513199945298452559774213 1783724989743459854957665)
                  ·
                    refine ⟨1337793742307594891218249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1783724989743459854957665 1337793742307594891218249)
                    ·
                      refine ⟨1003345306730696168413687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337793742307594891218249 1003345306730696168413687)
                      ·
                        rfl

theorem cell23_1954008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_1954008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954008 prefixEnd_1954008 := by exact prefixLift 1954008
  have htrace : WordTrace (prefixWord ++ tailWord_1954008) baseStart_1954008 baseEnd_1954008 := by
    simpa [prefixWord, tailWord_1954008, baseEnd_1954008] using wordTrace_append hprefix tailTrace_1954008
  have hstable : (prefixWord ++ tailWord_1954008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954008).length < 2 ^ (prefixWord ++ tailWord_1954008).sum := by decide
  have hdescent : baseEnd_1954008 < baseStart_1954008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954019 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1954019 : Nat := 118140960795 + 1954019 * 2 ^ 59
def prefixEnd_1954019 : Nat := 4983230072969 + 3 ^ 40 * 1954019 * 2
def baseEnd_1954019 : Nat := 1003350955017895625376137

theorem tailTrace_1954019 : CollatzResearch.WordTrace tailWord_1954019 prefixEnd_1954019 1003350955017895625376137 := by
  unfold tailWord_1954019
  simp only [CollatzResearch.WordTrace]
  refine ⟨71268927907930357721513111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47512618605286905147675407 71268927907930357721513111)
  ·
    refine ⟨106903391861895536582269667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71268927907930357721513111 106903391861895536582269667)
    ·
      refine ⟨160355087792843304873404501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106903391861895536582269667 160355087792843304873404501)
      ·
        refine ⟨1879161185072382478985209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 160355087792843304873404501 1879161185072382478985209)
        ·
          refine ⟨1409370888804286859238907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1879161185072382478985209 1409370888804286859238907)
          ·
            refine ⟨2114056333206430288858361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1409370888804286859238907 2114056333206430288858361)
            ·
              refine ⟨1585542249904822716643771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2114056333206430288858361 1585542249904822716643771)
              ·
                refine ⟨2378313374857234074965657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585542249904822716643771 2378313374857234074965657)
                ·
                  refine ⟨1783735031142925556224243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2378313374857234074965657 1783735031142925556224243)
                  ·
                    refine ⟨2675602546714388334336365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1783735031142925556224243 2675602546714388334336365)
                    ·
                      refine ⟨1003350955017895625376137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2675602546714388334336365 1003350955017895625376137)
                      ·
                        rfl

theorem cell23_1954019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1954019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954019 prefixEnd_1954019 := by exact prefixLift 1954019
  have htrace : WordTrace (prefixWord ++ tailWord_1954019) baseStart_1954019 baseEnd_1954019 := by
    simpa [prefixWord, tailWord_1954019, baseEnd_1954019] using wordTrace_append hprefix tailTrace_1954019
  have hstable : (prefixWord ++ tailWord_1954019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954019).length < 2 ^ (prefixWord ++ tailWord_1954019).sum := by decide
  have hdescent : baseEnd_1954019 < baseStart_1954019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954081 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 1, 6, 2]
def baseStart_1954081 : Nat := 118140960795 + 1954081 * 2 ^ 59
def prefixEnd_1954081 : Nat := 4983230072969 + 3 ^ 40 * 1954081 * 2
def baseEnd_1954081 : Nat := 1003382790818474382800851

theorem tailTrace_1954081 : CollatzResearch.WordTrace tailWord_1954081 prefixEnd_1954081 1003382790818474382800851 := by
  unfold tailWord_1954081
  simp only [CollatzResearch.WordTrace]
  refine ⟨71271189233705742310270097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47514126155803828206846731 71271189233705742310270097)
  ·
    refine ⟨53453391925279306732702573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71271189233705742310270097 53453391925279306732702573)
    ·
      refine ⟨20045021971979740024763465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53453391925279306732702573 20045021971979740024763465)
      ·
        refine ⟨15033766478984805018572599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20045021971979740024763465 15033766478984805018572599)
        ·
          refine ⟨22550649718477207527858899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15033766478984805018572599 22550649718477207527858899)
          ·
            refine ⟨33825974577715811291788349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22550649718477207527858899 33825974577715811291788349)
            ·
              refine ⟨12684740466643429234420631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33825974577715811291788349 12684740466643429234420631)
              ·
                refine ⟨19027110699965143851630947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12684740466643429234420631 19027110699965143851630947)
                ·
                  refine ⟨28540666049947715777446421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19027110699965143851630947 28540666049947715777446421)
                  ·
                    refine ⟨1337843721091299177067801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28540666049947715777446421 1337843721091299177067801)
                    ·
                      refine ⟨1003382790818474382800851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337843721091299177067801 1003382790818474382800851)
                      ·
                        rfl

theorem cell23_1954081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_1954081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954081 prefixEnd_1954081 := by exact prefixLift 1954081
  have htrace : WordTrace (prefixWord ++ tailWord_1954081) baseStart_1954081 baseEnd_1954081 := by
    simpa [prefixWord, tailWord_1954081, baseEnd_1954081] using wordTrace_append hprefix tailTrace_1954081
  have hstable : (prefixWord ++ tailWord_1954081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954081).length < 2 ^ (prefixWord ++ tailWord_1954081).sum := by decide
  have hdescent : baseEnd_1954081 < baseStart_1954081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954101 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_1954101 : Nat := 118140960795 + 1954101 * 2 ^ 59
def prefixEnd_1954101 : Nat := 4983230072969 + 3 ^ 40 * 1954101 * 2
def baseEnd_1954101 : Nat := 1003393060431564304550759

theorem tailTrace_1954101 : CollatzResearch.WordTrace tailWord_1954101 prefixEnd_1954101 1003393060431564304550759 := by
  unfold tailWord_1954101
  simp only [CollatzResearch.WordTrace]
  refine ⟨71271918693633285725998157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47514612462422190483998771 71271918693633285725998157)
  ·
    refine ⟨26726969510112482147249309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71271918693633285725998157 26726969510112482147249309)
    ·
      refine ⟨10022613566292180805218491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26726969510112482147249309 10022613566292180805218491)
      ·
        refine ⟨15033920349438271207827737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10022613566292180805218491 15033920349438271207827737)
        ·
          refine ⟨11275440262078703405870803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15033920349438271207827737 11275440262078703405870803)
          ·
            refine ⟨16913160393118055108806205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11275440262078703405870803 16913160393118055108806205)
            ·
              refine ⟨6342435147419270665802327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16913160393118055108806205 6342435147419270665802327)
              ·
                refine ⟨9513652721128905998703491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6342435147419270665802327 9513652721128905998703491)
                ·
                  refine ⟨14270479081693358998055237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9513652721128905998703491 14270479081693358998055237)
                  ·
                    refine ⟨2675714827817504812135357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14270479081693358998055237 2675714827817504812135357)
                    ·
                      refine ⟨1003393060431564304550759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2675714827817504812135357 1003393060431564304550759)
                      ·
                        rfl

theorem cell23_1954101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_1954101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954101 prefixEnd_1954101 := by exact prefixLift 1954101
  have htrace : WordTrace (prefixWord ++ tailWord_1954101) baseStart_1954101 baseEnd_1954101 := by
    simpa [prefixWord, tailWord_1954101, baseEnd_1954101] using wordTrace_append hprefix tailTrace_1954101
  have hstable : (prefixWord ++ tailWord_1954101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954101).length < 2 ^ (prefixWord ++ tailWord_1954101).sum := by decide
  have hdescent : baseEnd_1954101 < baseStart_1954101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954124 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1954124 : Nat := 118140960795 + 1954124 * 2 ^ 59
def prefixEnd_1954124 : Nat := 4983230072969 + 3 ^ 40 * 1954124 * 2
def baseEnd_1954124 : Nat := 1003404870486617714563153

theorem tailTrace_1954124 : CollatzResearch.WordTrace tailWord_1954124 prefixEnd_1954124 1003404870486617714563153 := by
  unfold tailWord_1954124
  simp only [CollatzResearch.WordTrace]
  refine ⟨35636378786274980327042713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47515171715033307102723617 35636378786274980327042713)
  ·
    refine ⟨26727284089706235245282035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35636378786274980327042713 26727284089706235245282035)
    ·
      refine ⟨40090926134559352867923053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26727284089706235245282035 40090926134559352867923053)
      ·
        refine ⟨15034097300459757325471145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40090926134559352867923053 15034097300459757325471145)
        ·
          refine ⟨11275572975344817994103359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15034097300459757325471145 11275572975344817994103359)
          ·
            refine ⟨16913359463017226991155039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11275572975344817994103359 16913359463017226991155039)
            ·
              refine ⟨25370039194525840486732559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16913359463017226991155039 25370039194525840486732559)
              ·
                refine ⟨38055058791788760730098839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25370039194525840486732559 38055058791788760730098839)
                ·
                  refine ⟨57082588187683141095148259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38055058791788760730098839 57082588187683141095148259)
                  ·
                    refine ⟨85623882281524711642722389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57082588187683141095148259 85623882281524711642722389)
                    ·
                      refine ⟨1003404870486617714563153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 85623882281524711642722389 1003404870486617714563153)
                      ·
                        rfl

theorem cell23_1954124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1954124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954124 prefixEnd_1954124 := by exact prefixLift 1954124
  have htrace : WordTrace (prefixWord ++ tailWord_1954124) baseStart_1954124 baseEnd_1954124 := by
    simpa [prefixWord, tailWord_1954124, baseEnd_1954124] using wordTrace_append hprefix tailTrace_1954124
  have hstable : (prefixWord ++ tailWord_1954124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954124).length < 2 ^ (prefixWord ++ tailWord_1954124).sum := by decide
  have hdescent : baseEnd_1954124 < baseStart_1954124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954148 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_1954148 : Nat := 118140960795 + 1954148 * 2 ^ 59
def prefixEnd_1954148 : Nat := 4983230072969 + 3 ^ 40 * 1954148 * 2
def baseEnd_1954148 : Nat := 1003417194022325620663043

theorem tailTrace_1954148 : CollatzResearch.WordTrace tailWord_1954148 prefixEnd_1954148 1003417194022325620663043 := by
  unfold tailWord_1954148
  simp only [CollatzResearch.WordTrace]
  refine ⟨35636816462231506376479549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47515755282975341835306065 35636816462231506376479549)
  ·
    refine ⟨13363806173336814891179831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35636816462231506376479549 13363806173336814891179831)
    ·
      refine ⟨20045709260005222336769747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13363806173336814891179831 20045709260005222336769747)
      ·
        refine ⟨30068563890007833505154621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20045709260005222336769747 30068563890007833505154621)
        ·
          refine ⟨11275711458752937564432983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30068563890007833505154621 11275711458752937564432983)
          ·
            refine ⟨16913567188129406346649475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11275711458752937564432983 16913567188129406346649475)
            ·
              refine ⟨25370350782194109519974213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16913567188129406346649475 25370350782194109519974213)
              ·
                refine ⟨4756940771661395534995165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25370350782194109519974213 4756940771661395534995165)
                ·
                  refine ⟨1783852789373023325623187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4756940771661395534995165 1783852789373023325623187)
                  ·
                    refine ⟨2675779184059534988434781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1783852789373023325623187 2675779184059534988434781)
                    ·
                      refine ⟨1003417194022325620663043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2675779184059534988434781 1003417194022325620663043)
                      ·
                        rfl

theorem cell23_1954148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_1954148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954148 prefixEnd_1954148 := by exact prefixLift 1954148
  have htrace : WordTrace (prefixWord ++ tailWord_1954148) baseStart_1954148 baseEnd_1954148 := by
    simpa [prefixWord, tailWord_1954148, baseEnd_1954148] using wordTrace_append hprefix tailTrace_1954148
  have hstable : (prefixWord ++ tailWord_1954148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954148).length < 2 ^ (prefixWord ++ tailWord_1954148).sum := by decide
  have hdescent : baseEnd_1954148 < baseStart_1954148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954201 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 4]
def baseStart_1954201 : Nat := 118140960795 + 1954201 * 2 ^ 59
def prefixEnd_1954201 : Nat := 4983230072969 + 3 ^ 40 * 1954201 * 2
def baseEnd_1954201 : Nat := 1003444408497013913300299

theorem tailTrace_1954201 : CollatzResearch.WordTrace tailWord_1954201 prefixEnd_1954201 1003444408497013913300299 := by
  unfold tailWord_1954201
  simp only [CollatzResearch.WordTrace]
  refine ⟨71275565993271002804638457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47517043995514001869758971 71275565993271002804638457)
  ·
    refine ⟨53456674494953252103478843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71275565993271002804638457 53456674494953252103478843)
    ·
      refine ⟨80185011742429878155218265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53456674494953252103478843 80185011742429878155218265)
      ·
        refine ⟨60138758806822408616413699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80185011742429878155218265 60138758806822408616413699)
        ·
          refine ⟨90208138210233612924620549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60138758806822408616413699 90208138210233612924620549)
          ·
            refine ⟨16914025914418802423366353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90208138210233612924620549 16914025914418802423366353)
            ·
              refine ⟨12685519435814101817524765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16914025914418802423366353 12685519435814101817524765)
              ·
                refine ⟨4757069788430288181571787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12685519435814101817524765 4757069788430288181571787)
                ·
                  refine ⟨7135604682645432272357681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757069788430288181571787 7135604682645432272357681)
                  ·
                    refine ⟨5351703511984074204268261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7135604682645432272357681 5351703511984074204268261)
                    ·
                      refine ⟨1003444408497013913300299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5351703511984074204268261 1003444408497013913300299)
                      ·
                        rfl

theorem cell23_1954201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_1954201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954201 prefixEnd_1954201 := by exact prefixLift 1954201
  have htrace : WordTrace (prefixWord ++ tailWord_1954201) baseStart_1954201 baseEnd_1954201 := by
    simpa [prefixWord, tailWord_1954201, baseEnd_1954201] using wordTrace_append hprefix tailTrace_1954201
  have hstable : (prefixWord ++ tailWord_1954201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954201).length < 2 ^ (prefixWord ++ tailWord_1954201).sum := by decide
  have hdescent : baseEnd_1954201 < baseStart_1954201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954208 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 3]
def baseStart_1954208 : Nat := 118140960795 + 1954208 * 2 ^ 59
def prefixEnd_1954208 : Nat := 4983230072969 + 3 ^ 40 * 1954208 * 2
def baseEnd_1954208 : Nat := 1003448002861595385912767

theorem tailTrace_1954208 : CollatzResearch.WordTrace tailWord_1954208 prefixEnd_1954208 1003448002861595385912767 := by
  unfold tailWord_1954208
  simp only [CollatzResearch.WordTrace]
  refine ⟨35637910652122821500071639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47517214202830428666762185 35637910652122821500071639)
  ·
    refine ⟨53456865978184232250107459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35637910652122821500071639 53456865978184232250107459)
    ·
      refine ⟨80185298967276348375161189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53456865978184232250107459 80185298967276348375161189)
      ·
        refine ⟨15034743556364315320342723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80185298967276348375161189 15034743556364315320342723)
        ·
          refine ⟨22552115334546472980514085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15034743556364315320342723 22552115334546472980514085)
          ·
            refine ⟨4228521625227463683846391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22552115334546472980514085 4228521625227463683846391)
            ·
              refine ⟨6342782437841195525769587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4228521625227463683846391 6342782437841195525769587)
              ·
                refine ⟨9514173656761793288654381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6342782437841195525769587 9514173656761793288654381)
                ·
                  refine ⟨3567815121285672483245393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9514173656761793288654381 3567815121285672483245393)
                  ·
                    refine ⟨2675861340964254362434045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3567815121285672483245393 2675861340964254362434045)
                    ·
                      refine ⟨1003448002861595385912767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2675861340964254362434045 1003448002861595385912767)
                      ·
                        rfl

theorem cell23_1954208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_1954208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954208 prefixEnd_1954208 := by exact prefixLift 1954208
  have htrace : WordTrace (prefixWord ++ tailWord_1954208) baseStart_1954208 baseEnd_1954208 := by
    simpa [prefixWord, tailWord_1954208, baseEnd_1954208] using wordTrace_append hprefix tailTrace_1954208
  have hstable : (prefixWord ++ tailWord_1954208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954208).length < 2 ^ (prefixWord ++ tailWord_1954208).sum := by decide
  have hdescent : baseEnd_1954208 < baseStart_1954208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954228 : List Nat := [2, 5, 2, 2, 12]
def baseStart_1954228 : Nat := 118140960795 + 1954228 * 2 ^ 59
def prefixEnd_1954228 : Nat := 4983230072969 + 3 ^ 40 * 1954228 * 2
def baseEnd_1954228 : Nat := 1376485970472819352075

theorem tailTrace_1954228 : CollatzResearch.WordTrace tailWord_1954228 prefixEnd_1954228 1376485970472819352075 := by
  unfold tailWord_1954228
  simp only [CollatzResearch.WordTrace]
  refine ⟨35638275382086593207935669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47517700509448790943914225 35638275382086593207935669)
  ·
    refine ⟨3341088317070618113243969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35638275382086593207935669 3341088317070618113243969)
    ·
      refine ⟨2505816237802963584932977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3341088317070618113243969 2505816237802963584932977)
      ·
        refine ⟨1879362178352222688699733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2505816237802963584932977 1879362178352222688699733)
        ·
          refine ⟨1376485970472819352075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1879362178352222688699733 1376485970472819352075)
          ·
            rfl

theorem cell23_1954228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 12].length) (baseStart_1954228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954228 prefixEnd_1954228 := by exact prefixLift 1954228
  have htrace : WordTrace (prefixWord ++ tailWord_1954228) baseStart_1954228 baseEnd_1954228 := by
    simpa [prefixWord, tailWord_1954228, baseEnd_1954228] using wordTrace_append hprefix tailTrace_1954228
  have hstable : (prefixWord ++ tailWord_1954228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954228).length < 2 ^ (prefixWord ++ tailWord_1954228).sum := by decide
  have hdescent : baseEnd_1954228 < baseStart_1954228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954265 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 1, 3, 2]
def baseStart_1954265 : Nat := 118140960795 + 1954265 * 2 ^ 59
def prefixEnd_1954265 : Nat := 4983230072969 + 3 ^ 40 * 1954265 * 2
def baseEnd_1954265 : Nat := 1003477271258901662900005

theorem tailTrace_1954265 : CollatzResearch.WordTrace tailWord_1954265 prefixEnd_1954265 1003477271258901662900005 := by
  unfold tailWord_1954265
  simp only [CollatzResearch.WordTrace]
  refine ⟨71277900265039141734968249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47518600176692761156645499 71277900265039141734968249)
  ·
    refine ⟨53458425198779356301226187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71277900265039141734968249 53458425198779356301226187)
    ·
      refine ⟨80187637798169034451839281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53458425198779356301226187 80187637798169034451839281)
      ·
        refine ⟨60140728348626775838879461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80187637798169034451839281 60140728348626775838879461)
        ·
          refine ⟨11276386565367520469789899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60140728348626775838879461 11276386565367520469789899)
          ·
            refine ⟨16914579848051280704684849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11276386565367520469789899 16914579848051280704684849)
            ·
              refine ⟨12685934886038460528513637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16914579848051280704684849 12685934886038460528513637)
              ·
                refine ⟨2378612791132211349096307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12685934886038460528513637 2378612791132211349096307)
                ·
                  refine ⟨3567919186698317023644461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378612791132211349096307 3567919186698317023644461)
                  ·
                    refine ⟨1337969695011868883866673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3567919186698317023644461 1337969695011868883866673)
                    ·
                      refine ⟨1003477271258901662900005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337969695011868883866673 1003477271258901662900005)
                      ·
                        rfl

theorem cell23_1954265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_1954265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954265 prefixEnd_1954265 := by exact prefixLift 1954265
  have htrace : WordTrace (prefixWord ++ tailWord_1954265) baseStart_1954265 baseEnd_1954265 := by
    simpa [prefixWord, tailWord_1954265, baseEnd_1954265] using wordTrace_append hprefix tailTrace_1954265
  have hstable : (prefixWord ++ tailWord_1954265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954265).length < 2 ^ (prefixWord ++ tailWord_1954265).sum := by decide
  have hdescent : baseEnd_1954265 < baseStart_1954265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954281 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 1, 6, 3]
def baseStart_1954281 : Nat := 118140960795 + 1954281 * 2 ^ 59
def prefixEnd_1954281 : Nat := 4983230072969 + 3 ^ 40 * 1954281 * 2
def baseEnd_1954281 : Nat := 1003485486949373600299931

theorem tailTrace_1954281 : CollatzResearch.WordTrace tailWord_1954281 prefixEnd_1954281 1003485486949373600299931 := by
  unfold tailWord_1954281
  simp only [CollatzResearch.WordTrace]
  refine ⟨71278483832981176467550697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47518989221987450978367131 71278483832981176467550697)
  ·
    refine ⟨53458862874735882350663023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71278483832981176467550697 53458862874735882350663023)
    ·
      refine ⟨80188294312103823525994535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53458862874735882350663023 80188294312103823525994535)
      ·
        refine ⟨120282441468155735288991803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80188294312103823525994535 120282441468155735288991803)
        ·
          refine ⟨180423662202233602933487705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120282441468155735288991803 180423662202233602933487705)
          ·
            refine ⟨135317746651675202200115779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180423662202233602933487705 135317746651675202200115779)
            ·
              refine ⟨202976619977512803300173669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135317746651675202200115779 202976619977512803300173669)
              ·
                refine ⟨38058116245783650618782563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202976619977512803300173669 38058116245783650618782563)
                ·
                  refine ⟨57087174368675475928173845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38058116245783650618782563 57087174368675475928173845)
                  ·
                    refine ⟨2675961298531662934133149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57087174368675475928173845 2675961298531662934133149)
                    ·
                      refine ⟨1003485486949373600299931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2675961298531662934133149 1003485486949373600299931)
                      ·
                        rfl

theorem cell23_1954281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 6, 3].length) (baseStart_1954281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954281 prefixEnd_1954281 := by exact prefixLift 1954281
  have htrace : WordTrace (prefixWord ++ tailWord_1954281) baseStart_1954281 baseEnd_1954281 := by
    simpa [prefixWord, tailWord_1954281, baseEnd_1954281] using wordTrace_append hprefix tailTrace_1954281
  have hstable : (prefixWord ++ tailWord_1954281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954281).length < 2 ^ (prefixWord ++ tailWord_1954281).sum := by decide
  have hdescent : baseEnd_1954281 < baseStart_1954281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954282 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_1954282 : Nat := 118140960795 + 1954282 * 2 ^ 59
def prefixEnd_1954282 : Nat := 4983230072969 + 3 ^ 40 * 1954282 * 2
def baseEnd_1954282 : Nat := 1003486000430028096387427

theorem tailTrace_1954282 : CollatzResearch.WordTrace tailWord_1954282 prefixEnd_1954282 1003486000430028096387427 := by
  unfold tailWord_1954282
  simp only [CollatzResearch.WordTrace]
  refine ⟨17819630076494388409584275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47519013537318369092224733 17819630076494388409584275)
  ·
    refine ⟨26729445114741582614376413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17819630076494388409584275 26729445114741582614376413)
    ·
      refine ⟨10023541918028093480391155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26729445114741582614376413 10023541918028093480391155)
      ·
        refine ⟨15035312877042140220586733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10023541918028093480391155 15035312877042140220586733)
        ·
          refine ⟨5638242328890802582720025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15035312877042140220586733 5638242328890802582720025)
          ·
            refine ⟨4228681746668101937040019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5638242328890802582720025 4228681746668101937040019)
            ·
              refine ⟨6343022620002152905560029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4228681746668101937040019 6343022620002152905560029)
              ·
                refine ⟨2378633482500807339585011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6343022620002152905560029 2378633482500807339585011)
                ·
                  refine ⟨3567950223751211009377517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378633482500807339585011 3567950223751211009377517)
                  ·
                    refine ⟨1337981333906704128516569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3567950223751211009377517 1337981333906704128516569)
                    ·
                      refine ⟨1003486000430028096387427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1337981333906704128516569 1003486000430028096387427)
                      ·
                        rfl

theorem cell23_1954282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_1954282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954282 prefixEnd_1954282 := by exact prefixLift 1954282
  have htrace : WordTrace (prefixWord ++ tailWord_1954282) baseStart_1954282 baseEnd_1954282 := by
    simpa [prefixWord, tailWord_1954282, baseEnd_1954282] using wordTrace_append hprefix tailTrace_1954282
  have hstable : (prefixWord ++ tailWord_1954282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954282).length < 2 ^ (prefixWord ++ tailWord_1954282).sum := by decide
  have hdescent : baseEnd_1954282 < baseStart_1954282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954291 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 4]
def baseStart_1954291 : Nat := 118140960795 + 1954291 * 2 ^ 59
def prefixEnd_1954291 : Nat := 4983230072969 + 3 ^ 40 * 1954291 * 2
def baseEnd_1954291 : Nat := 1003490621755918561174885

theorem tailTrace_1954291 : CollatzResearch.WordTrace tailWord_1954291 prefixEnd_1954291 1003490621755918561174885 := by
  unfold tailWord_1954291
  simp only [CollatzResearch.WordTrace]
  refine ⟨71278848562944948175414727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47519232375296632116943151 71278848562944948175414727)
  ·
    refine ⟨106918272844417422263122091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71278848562944948175414727 106918272844417422263122091)
    ·
      refine ⟨160377409266626133394683137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106918272844417422263122091 160377409266626133394683137)
      ·
        refine ⟨120283056949969600046012353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160377409266626133394683137 120283056949969600046012353)
        ·
          refine ⟨90212292712477200034509265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120283056949969600046012353 90212292712477200034509265)
          ·
            refine ⟨67659219534357900025881949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90212292712477200034509265 67659219534357900025881949)
            ·
              refine ⟨25372207325384212509705731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67659219534357900025881949 25372207325384212509705731)
              ·
                refine ⟨38058310988076318764558597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25372207325384212509705731 38058310988076318764558597)
                ·
                  refine ⟨7135933310264309768354737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38058310988076318764558597 7135933310264309768354737)
                  ·
                    refine ⟨5351949982698232326266053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7135933310264309768354737 5351949982698232326266053)
                    ·
                      refine ⟨1003490621755918561174885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5351949982698232326266053 1003490621755918561174885)
                      ·
                        rfl

theorem cell23_1954291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_1954291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954291 prefixEnd_1954291 := by exact prefixLift 1954291
  have htrace : WordTrace (prefixWord ++ tailWord_1954291) baseStart_1954291 baseEnd_1954291 := by
    simpa [prefixWord, tailWord_1954291, baseEnd_1954291] using wordTrace_append hprefix tailTrace_1954291
  have hstable : (prefixWord ++ tailWord_1954291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954291).length < 2 ^ (prefixWord ++ tailWord_1954291).sum := by decide
  have hdescent : baseEnd_1954291 < baseStart_1954291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954306 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_1954306 : Nat := 118140960795 + 1954306 * 2 ^ 59
def prefixEnd_1954306 : Nat := 4983230072969 + 3 ^ 40 * 1954306 * 2
def baseEnd_1954306 : Nat := 1003498323965736002487317

theorem tailTrace_1954306 : CollatzResearch.WordTrace tailWord_1954306 prefixEnd_1954306 1003498323965736002487317 := by
  unfold tailWord_1954306
  simp only [CollatzResearch.WordTrace]
  refine ⟨17819848914472651434302693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47519597105260403824807181 17819848914472651434302693)
  ·
    refine ⟨3341221671463622143931755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17819848914472651434302693 3341221671463622143931755)
    ·
      refine ⟨5011832507195433215897633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3341221671463622143931755 5011832507195433215897633)
      ·
        refine ⟨3758874380396574911923225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5011832507195433215897633 3758874380396574911923225)
        ·
          refine ⟨2819155785297431183942419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3758874380396574911923225 2819155785297431183942419)
          ·
            refine ⟨4228733677946146775913629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819155785297431183942419 4228733677946146775913629)
            ·
              refine ⟨1585775129229805040967611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4228733677946146775913629 1585775129229805040967611)
              ·
                refine ⟨2378662693844707561451417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585775129229805040967611 2378662693844707561451417)
                ·
                  refine ⟨1783997020383530671088563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2378662693844707561451417 1783997020383530671088563)
                  ·
                    refine ⟨2675995530575296006632845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1783997020383530671088563 2675995530575296006632845)
                    ·
                      refine ⟨1003498323965736002487317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2675995530575296006632845 1003498323965736002487317)
                      ·
                        rfl

theorem cell23_1954306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_1954306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954306 prefixEnd_1954306 := by exact prefixLift 1954306
  have htrace : WordTrace (prefixWord ++ tailWord_1954306) baseStart_1954306 baseEnd_1954306 := by
    simpa [prefixWord, tailWord_1954306, baseEnd_1954306] using wordTrace_append hprefix tailTrace_1954306
  have hstable : (prefixWord ++ tailWord_1954306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954306).length < 2 ^ (prefixWord ++ tailWord_1954306).sum := by decide
  have hdescent : baseEnd_1954306 < baseStart_1954306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954318 : List Nat := [4, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_1954318 : Nat := 118140960795 + 1954318 * 2 ^ 59
def prefixEnd_1954318 : Nat := 4983230072969 + 3 ^ 40 * 1954318 * 2
def baseEnd_1954318 : Nat := 111500498414843328393029

theorem tailTrace_1954318 : CollatzResearch.WordTrace tailWord_1954318 prefixEnd_1954318 111500498414843328393029 := by
  unfold tailWord_1954318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8909979166730891473330951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47519888889231421191098405 8909979166730891473330951)
  ·
    refine ⟨13364968750096337209996427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8909979166730891473330951 13364968750096337209996427)
    ·
      refine ⟨20047453125144505814994641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13364968750096337209996427 20047453125144505814994641)
      ·
        refine ⟨15035589843858379361245981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20047453125144505814994641 15035589843858379361245981)
        ·
          refine ⟨5638346191446892260467243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15035589843858379361245981 5638346191446892260467243)
          ·
            refine ⟨8457519287170338390700865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638346191446892260467243 8457519287170338390700865)
            ·
              refine ⟨6343139465377753793025649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8457519287170338390700865 6343139465377753793025649)
              ·
                refine ⟨4757354599033315344769237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6343139465377753793025649 4757354599033315344769237)
                ·
                  refine ⟨111500498414843328393029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4757354599033315344769237 111500498414843328393029)
                  ·
                    rfl

theorem cell23_1954318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_1954318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954318 prefixEnd_1954318 := by exact prefixLift 1954318
  have htrace : WordTrace (prefixWord ++ tailWord_1954318) baseStart_1954318 baseEnd_1954318 := by
    simpa [prefixWord, tailWord_1954318, baseEnd_1954318] using wordTrace_append hprefix tailTrace_1954318
  have hstable : (prefixWord ++ tailWord_1954318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954318).length < 2 ^ (prefixWord ++ tailWord_1954318).sum := by decide
  have hdescent : baseEnd_1954318 < baseStart_1954318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954331 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 8, 5]
def baseStart_1954331 : Nat := 118140960795 + 1954331 * 2 ^ 59
def prefixEnd_1954331 : Nat := 4983230072969 + 3 ^ 40 * 1954331 * 2
def baseEnd_1954331 : Nat := 334503720327366134891567

theorem tailTrace_1954331 : CollatzResearch.WordTrace tailWord_1954331 prefixEnd_1954331 334503720327366134891567 := by
  unfold tailWord_1954331
  simp only [CollatzResearch.WordTrace]
  refine ⟨71280307482800035006870847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47520204988533356671247231 71280307482800035006870847)
  ·
    refine ⟨106920461224200052510306271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71280307482800035006870847 106920461224200052510306271)
    ·
      refine ⟨160380691836300078765459407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106920461224200052510306271 160380691836300078765459407)
      ·
        refine ⟨240571037754450118148189111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160380691836300078765459407 240571037754450118148189111)
        ·
          refine ⟨360856556631675177222283667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240571037754450118148189111 360856556631675177222283667)
          ·
            refine ⟨541284834947512765833425501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360856556631675177222283667 541284834947512765833425501)
            ·
              refine ⟨202981813105317287187534563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541284834947512765833425501 202981813105317287187534563)
              ·
                refine ⟨304472719657975930781301845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202981813105317287187534563 304472719657975930781301845)
                ·
                  refine ⟨3568039683491905438843381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 304472719657975930781301845 3568039683491905438843381)
                  ·
                    refine ⟨334503720327366134891567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3568039683491905438843381 334503720327366134891567)
                    ·
                      rfl

theorem cell23_1954331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 5].length) (baseStart_1954331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954331 prefixEnd_1954331 := by exact prefixLift 1954331
  have htrace : WordTrace (prefixWord ++ tailWord_1954331) baseStart_1954331 baseEnd_1954331 := by
    simpa [prefixWord, tailWord_1954331, baseEnd_1954331] using wordTrace_append hprefix tailTrace_1954331
  have hstable : (prefixWord ++ tailWord_1954331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954331).length < 2 ^ (prefixWord ++ tailWord_1954331).sum := by decide
  have hdescent : baseEnd_1954331 < baseStart_1954331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954351 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 4]
def baseStart_1954351 : Nat := 118140960795 + 1954351 * 2 ^ 59
def prefixEnd_1954351 : Nat := 4983230072969 + 3 ^ 40 * 1954351 * 2
def baseEnd_1954351 : Nat := 1003521430595188326424609

theorem tailTrace_1954351 : CollatzResearch.WordTrace tailWord_1954351 prefixEnd_1954351 1003521430595188326424609 := by
  unfold tailWord_1954351
  simp only [CollatzResearch.WordTrace]
  refine ⟨71281036942727578422598907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47520691295151718948399271 71281036942727578422598907)
  ·
    refine ⟨106921555414091367633898361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71281036942727578422598907 106921555414091367633898361)
    ·
      refine ⟨80191166560568525725423771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106921555414091367633898361 80191166560568525725423771)
      ·
        refine ⟨120286749840852788588135657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80191166560568525725423771 120286749840852788588135657)
        ·
          refine ⟨90215062380639591441101743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120286749840852788588135657 90215062380639591441101743)
          ·
            refine ⟨135322593570959387161652615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90215062380639591441101743 135322593570959387161652615)
            ·
              refine ⟨202983890356439080742478923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135322593570959387161652615 202983890356439080742478923)
              ·
                refine ⟨304475835534658621113718385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202983890356439080742478923 304475835534658621113718385)
                ·
                  refine ⟨228356876650993965835288789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 304475835534658621113718385 228356876650993965835288789)
                  ·
                    refine ⟨5352114296507671074264581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 228356876650993965835288789 5352114296507671074264581)
                    ·
                      refine ⟨1003521430595188326424609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5352114296507671074264581 1003521430595188326424609)
                      ·
                        rfl

theorem cell23_1954351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_1954351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954351 prefixEnd_1954351 := by exact prefixLift 1954351
  have htrace : WordTrace (prefixWord ++ tailWord_1954351) baseStart_1954351 baseEnd_1954351 := by
    simpa [prefixWord, tailWord_1954351, baseEnd_1954351] using wordTrace_append hprefix tailTrace_1954351
  have hstable : (prefixWord ++ tailWord_1954351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954351).length < 2 ^ (prefixWord ++ tailWord_1954351).sum := by decide
  have hdescent : baseEnd_1954351 < baseStart_1954351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954371 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 5]
def baseStart_1954371 : Nat := 118140960795 + 1954371 * 2 ^ 59
def prefixEnd_1954371 : Nat := 4983230072969 + 3 ^ 40 * 1954371 * 2
def baseEnd_1954371 : Nat := 1003531700208278248174517

theorem tailTrace_1954371 : CollatzResearch.WordTrace tailWord_1954371 prefixEnd_1954371 1003531700208278248174517 := by
  unfold tailWord_1954371
  simp only [CollatzResearch.WordTrace]
  refine ⟨71281766402655121838326967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47521177601770081225551311 71281766402655121838326967)
  ·
    refine ⟨106922649603982682757490451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71281766402655121838326967 106922649603982682757490451)
    ·
      refine ⟨160383974405974024136235677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106922649603982682757490451 160383974405974024136235677)
      ·
        refine ⟨60143990402240259051088379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160383974405974024136235677 60143990402240259051088379)
        ·
          refine ⟨90215985603360388576632569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60143990402240259051088379 90215985603360388576632569)
          ·
            refine ⟨67661989202520291432474427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90215985603360388576632569 67661989202520291432474427)
            ·
              refine ⟨101492983803780437148711641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67661989202520291432474427 101492983803780437148711641)
              ·
                refine ⟨76119737852835327861533731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101492983803780437148711641 76119737852835327861533731)
                ·
                  refine ⟨114179606779252991792300597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76119737852835327861533731 114179606779252991792300597)
                  ·
                    refine ⟨10704338135554967980528181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114179606779252991792300597 10704338135554967980528181)
                    ·
                      refine ⟨1003531700208278248174517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10704338135554967980528181 1003531700208278248174517)
                      ·
                        rfl

theorem cell23_1954371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_1954371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954371 prefixEnd_1954371 := by exact prefixLift 1954371
  have htrace : WordTrace (prefixWord ++ tailWord_1954371) baseStart_1954371 baseEnd_1954371 := by
    simpa [prefixWord, tailWord_1954371, baseEnd_1954371] using wordTrace_append hprefix tailTrace_1954371
  have hstable : (prefixWord ++ tailWord_1954371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954371).length < 2 ^ (prefixWord ++ tailWord_1954371).sum := by decide
  have hdescent : baseEnd_1954371 < baseStart_1954371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954385 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 4]
def baseStart_1954385 : Nat := 118140960795 + 1954385 * 2 ^ 59
def prefixEnd_1954385 : Nat := 4983230072969 + 3 ^ 40 * 1954385 * 2
def baseEnd_1954385 : Nat := 1003538888937441193399453

theorem tailTrace_1954385 : CollatzResearch.WordTrace tailWord_1954385 prefixEnd_1954385 1003538888937441193399453 := by
  unfold tailWord_1954385
  simp only [CollatzResearch.WordTrace]
  refine ⟨71282277024604402229336609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47521518016402934819557739 71282277024604402229336609)
  ·
    refine ⟨53461707768453301672002457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71282277024604402229336609 53461707768453301672002457)
    ·
      refine ⟨40096280826339976254001843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53461707768453301672002457 40096280826339976254001843)
      ·
        refine ⟨60144421239509964381002765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40096280826339976254001843 60144421239509964381002765)
        ·
          refine ⟨22554157964816236642876037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60144421239509964381002765 22554157964816236642876037)
          ·
            refine ⟨4228904618403044370539257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22554157964816236642876037 4228904618403044370539257)
            ·
              refine ⟨3171678463802283277904443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4228904618403044370539257 3171678463802283277904443)
              ·
                refine ⟨4757517695703424916856665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171678463802283277904443 4757517695703424916856665)
                ·
                  refine ⟨3568138271777568687642499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4757517695703424916856665 3568138271777568687642499)
                  ·
                    refine ⟨5352207407666353031463749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3568138271777568687642499 5352207407666353031463749)
                    ·
                      refine ⟨1003538888937441193399453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5352207407666353031463749 1003538888937441193399453)
                      ·
                        rfl

theorem cell23_1954385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_1954385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954385 prefixEnd_1954385 := by exact prefixLift 1954385
  have htrace : WordTrace (prefixWord ++ tailWord_1954385) baseStart_1954385 baseEnd_1954385 := by
    simpa [prefixWord, tailWord_1954385, baseEnd_1954385] using wordTrace_append hprefix tailTrace_1954385
  have hstable : (prefixWord ++ tailWord_1954385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954385).length < 2 ^ (prefixWord ++ tailWord_1954385).sum := by decide
  have hdescent : baseEnd_1954385 < baseStart_1954385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954435 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 5, 1, 3]
def baseStart_1954435 : Nat := 118140960795 + 1954435 * 2 ^ 59
def prefixEnd_1954435 : Nat := 4983230072969 + 3 ^ 40 * 1954435 * 2
def baseEnd_1954435 : Nat := 1003564562970165997774223

theorem tailTrace_1954435 : CollatzResearch.WordTrace tailWord_1954435 prefixEnd_1954435 1003564562970165997774223 := by
  unfold tailWord_1954435
  simp only [CollatzResearch.WordTrace]
  refine ⟨71284100674423260768656759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47522733782948840512437839 71284100674423260768656759)
  ·
    refine ⟨106926151011634891152985139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71284100674423260768656759 106926151011634891152985139)
    ·
      refine ⟨160389226517452336729477709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106926151011634891152985139 160389226517452336729477709)
      ·
        refine ⟨60145959944044626273554141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160389226517452336729477709 60145959944044626273554141)
        ·
          refine ⟨22554734979016734852582803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60145959944044626273554141 22554734979016734852582803)
          ·
            refine ⟨33832102468525102278874205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22554734979016734852582803 33832102468525102278874205)
            ·
              refine ⟨12687038425696913354577827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33832102468525102278874205 12687038425696913354577827)
              ·
                refine ⟨19030557638545370031866741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12687038425696913354577827 19030557638545370031866741)
                ·
                  refine ⟨1784114778613628440487507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19030557638545370031866741 1784114778613628440487507)
                  ·
                    refine ⟨2676172167920442660731261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1784114778613628440487507 2676172167920442660731261)
                    ·
                      refine ⟨1003564562970165997774223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2676172167920442660731261 1003564562970165997774223)
                      ·
                        rfl

theorem cell23_1954435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_1954435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954435 prefixEnd_1954435 := by exact prefixLift 1954435
  have htrace : WordTrace (prefixWord ++ tailWord_1954435) baseStart_1954435 baseEnd_1954435 := by
    simpa [prefixWord, tailWord_1954435, baseEnd_1954435] using wordTrace_append hprefix tailTrace_1954435
  have hstable : (prefixWord ++ tailWord_1954435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954435).length < 2 ^ (prefixWord ++ tailWord_1954435).sum := by decide
  have hdescent : baseEnd_1954435 < baseStart_1954435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954455 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 1, 5]
def baseStart_1954455 : Nat := 118140960795 + 1954455 * 2 ^ 59
def prefixEnd_1954455 : Nat := 4983230072969 + 3 ^ 40 * 1954455 * 2
def baseEnd_1954455 : Nat := 334524944194418639841377

theorem tailTrace_1954455 : CollatzResearch.WordTrace tailWord_1954455 prefixEnd_1954455 334524944194418639841377 := by
  unfold tailWord_1954455
  simp only [CollatzResearch.WordTrace]
  refine ⟨71284830134350804184384819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47523220089567202789589879 71284830134350804184384819)
  ·
    refine ⟨106927245201526206276577229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71284830134350804184384819 106927245201526206276577229)
    ·
      refine ⟨40097716950572327353716461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106927245201526206276577229 40097716950572327353716461)
      ·
        refine ⟨15036643856464622757643673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40097716950572327353716461 15036643856464622757643673)
        ·
          refine ⟨11277482892348467068232755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15036643856464622757643673 11277482892348467068232755)
          ·
            refine ⟨16916224338522700602349133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11277482892348467068232755 16916224338522700602349133)
            ·
              refine ⟨6343584126946012725880925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16916224338522700602349133 6343584126946012725880925)
              ·
                refine ⟨2378844047604754772205347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6343584126946012725880925 2378844047604754772205347)
                ·
                  refine ⟨3568266071407132158308021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378844047604754772205347 3568266071407132158308021)
                  ·
                    refine ⟨334524944194418639841377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3568266071407132158308021 334524944194418639841377)
                    ·
                      rfl

theorem cell23_1954455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_1954455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954455 prefixEnd_1954455 := by exact prefixLift 1954455
  have htrace : WordTrace (prefixWord ++ tailWord_1954455) baseStart_1954455 baseEnd_1954455 := by
    simpa [prefixWord, tailWord_1954455, baseEnd_1954455] using wordTrace_append hprefix tailTrace_1954455
  have hstable : (prefixWord ++ tailWord_1954455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954455).length < 2 ^ (prefixWord ++ tailWord_1954455).sum := by decide
  have hdescent : baseEnd_1954455 < baseStart_1954455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954492 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_1954492 : Nat := 118140960795 + 1954492 * 2 ^ 59
def prefixEnd_1954492 : Nat := 4983230072969 + 3 ^ 40 * 1954492 * 2
def baseEnd_1954492 : Nat := 1003593831367472274761461

theorem tailTrace_1954492 : CollatzResearch.WordTrace tailWord_1954492 prefixEnd_1954492 1003593831367472274761461 := by
  unfold tailWord_1954492
  simp only [CollatzResearch.WordTrace]
  refine ⟨35643089817608379751740865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47524119756811173002321153 35643089817608379751740865)
  ·
    refine ⟨26732317363206284813805649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35643089817608379751740865 26732317363206284813805649)
    ·
      refine ⟨20049238022404713610354237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26732317363206284813805649 20049238022404713610354237)
      ·
        refine ⟨7518464258401767603882839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20049238022404713610354237 7518464258401767603882839)
        ·
          refine ⟨11277696387602651405824259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7518464258401767603882839 11277696387602651405824259)
          ·
            refine ⟨16916544581403977108736389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11277696387602651405824259 16916544581403977108736389)
            ·
              refine ⟨3171852109013245707888073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16916544581403977108736389 3171852109013245707888073)
              ·
                refine ⟨2378889081759934280916055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3171852109013245707888073 2378889081759934280916055)
                ·
                  refine ⟨3568333622639901421374083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378889081759934280916055 3568333622639901421374083)
                  ·
                    refine ⟨5352500433959852132061125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3568333622639901421374083 5352500433959852132061125)
                    ·
                      refine ⟨1003593831367472274761461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5352500433959852132061125 1003593831367472274761461)
                      ·
                        rfl

theorem cell23_1954492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_1954492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954492 prefixEnd_1954492 := by exact prefixLift 1954492
  have htrace : WordTrace (prefixWord ++ tailWord_1954492) baseStart_1954492 baseEnd_1954492 := by
    simpa [prefixWord, tailWord_1954492, baseEnd_1954492] using wordTrace_append hprefix tailTrace_1954492
  have hstable : (prefixWord ++ tailWord_1954492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954492).length < 2 ^ (prefixWord ++ tailWord_1954492).sum := by decide
  have hdescent : baseEnd_1954492 < baseStart_1954492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954528 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 2, 7]
def baseStart_1954528 : Nat := 118140960795 + 1954528 * 2 ^ 59
def prefixEnd_1954528 : Nat := 4983230072969 + 3 ^ 40 * 1954528 * 2
def baseEnd_1954528 : Nat := 334537438890344711303765

theorem tailTrace_1954528 : CollatzResearch.WordTrace tailWord_1954528 prefixEnd_1954528 334537438890344711303765 := by
  unfold tailWord_1954528
  simp only [CollatzResearch.WordTrace]
  refine ⟨35643746331543168825896119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47524995108724225101194825 35643746331543168825896119)
  ·
    refine ⟨53465619497314753238844179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35643746331543168825896119 53465619497314753238844179)
    ·
      refine ⟨80198429245972129858266269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53465619497314753238844179 80198429245972129858266269)
      ·
        refine ⟨30074410967239548696849851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80198429245972129858266269 30074410967239548696849851)
        ·
          refine ⟨45111616450859323045274777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30074410967239548696849851 45111616450859323045274777)
          ·
            refine ⟨33833712338144492283956083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45111616450859323045274777 33833712338144492283956083)
            ·
              refine ⟨50750568507216738425934125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33833712338144492283956083 50750568507216738425934125)
              ·
                refine ⟨19031463190206276909725297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50750568507216738425934125 19031463190206276909725297)
                ·
                  refine ⟨14273597392654707682293973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19031463190206276909725297 14273597392654707682293973)
                  ·
                    refine ⟨334537438890344711303765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14273597392654707682293973 334537438890344711303765)
                    ·
                      rfl

theorem cell23_1954528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_1954528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954528 prefixEnd_1954528 := by exact prefixLift 1954528
  have htrace : WordTrace (prefixWord ++ tailWord_1954528) baseStart_1954528 baseEnd_1954528 := by
    simpa [prefixWord, tailWord_1954528, baseEnd_1954528] using wordTrace_append hprefix tailTrace_1954528
  have hstable : (prefixWord ++ tailWord_1954528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954528).length < 2 ^ (prefixWord ++ tailWord_1954528).sum := by decide
  have hdescent : baseEnd_1954528 < baseStart_1954528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954536 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 2, 4]
def baseStart_1954536 : Nat := 118140960795 + 1954536 * 2 ^ 59
def prefixEnd_1954536 : Nat := 4983230072969 + 3 ^ 40 * 1954536 * 2
def baseEnd_1954536 : Nat := 334538808172090034203753

theorem tailTrace_1954536 : CollatzResearch.WordTrace tailWord_1954536 prefixEnd_1954536 334538808172090034203753 := by
  unfold tailWord_1954536
  simp only [CollatzResearch.WordTrace]
  refine ⟨35643892223528677509041731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47525189631371570012055641 35643892223528677509041731)
  ·
    refine ⟨53465838335293016263562597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35643892223528677509041731 53465838335293016263562597)
    ·
      refine ⟨10024844687867440549417987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53465838335293016263562597 10024844687867440549417987)
      ·
        refine ⟨15037267031801160824126981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10024844687867440549417987 15037267031801160824126981)
        ·
          refine ⟨2819487568462717654523809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15037267031801160824126981 2819487568462717654523809)
          ·
            refine ⟨2114615676347038240892857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2819487568462717654523809 2114615676347038240892857)
            ·
              refine ⟨1585961757260278680669643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2114615676347038240892857 1585961757260278680669643)
              ·
                refine ⟨2378942635890418021004465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1585961757260278680669643 2378942635890418021004465)
                ·
                  refine ⟨1784206976917813515753349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2378942635890418021004465 1784206976917813515753349)
                  ·
                    refine ⟨334538808172090034203753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1784206976917813515753349 334538808172090034203753)
                    ·
                      rfl

theorem cell23_1954536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_1954536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954536 prefixEnd_1954536 := by exact prefixLift 1954536
  have htrace : WordTrace (prefixWord ++ tailWord_1954536) baseStart_1954536 baseEnd_1954536 := by
    simpa [prefixWord, tailWord_1954536, baseEnd_1954536] using wordTrace_append hprefix tailTrace_1954536
  have hstable : (prefixWord ++ tailWord_1954536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954536).length < 2 ^ (prefixWord ++ tailWord_1954536).sum := by decide
  have hdescent : baseEnd_1954536 < baseStart_1954536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954552 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 3, 3, 2]
def baseStart_1954552 : Nat := 118140960795 + 1954552 * 2 ^ 59
def prefixEnd_1954552 : Nat := 4983230072969 + 3 ^ 40 * 1954552 * 2
def baseEnd_1954552 : Nat := 1003624640206742040011185

theorem tailTrace_1954552 : CollatzResearch.WordTrace tailWord_1954552 prefixEnd_1954552 1003624640206742040011185 := by
  unfold tailWord_1954552
  simp only [CollatzResearch.WordTrace]
  refine ⟨35644184007499694875332955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47525578676666259833777273 35644184007499694875332955)
  ·
    refine ⟨53466276011249542312999433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35644184007499694875332955 53466276011249542312999433)
    ·
      refine ⟨40099707008437156734749575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53466276011249542312999433 40099707008437156734749575)
      ·
        refine ⟨60149560512655735102124363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40099707008437156734749575 60149560512655735102124363)
        ·
          refine ⟨90224340768983602653186545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60149560512655735102124363 90224340768983602653186545)
          ·
            refine ⟨67668255576737701989889909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90224340768983602653186545 67668255576737701989889909)
            ·
              refine ⟨6343898960319159561552179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67668255576737701989889909 6343898960319159561552179)
              ·
                refine ⟨9515848440478739342328269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6343898960319159561552179 9515848440478739342328269)
                ·
                  refine ⟨3568443165179527253373101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9515848440478739342328269 3568443165179527253373101)
                  ·
                    refine ⟨1338166186942322720014913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3568443165179527253373101 1338166186942322720014913)
                    ·
                      refine ⟨1003624640206742040011185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338166186942322720014913 1003624640206742040011185)
                      ·
                        rfl

theorem cell23_1954552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_1954552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954552 prefixEnd_1954552 := by exact prefixLift 1954552
  have htrace : WordTrace (prefixWord ++ tailWord_1954552) baseStart_1954552 baseEnd_1954552 := by
    simpa [prefixWord, tailWord_1954552, baseEnd_1954552] using wordTrace_append hprefix tailTrace_1954552
  have hstable : (prefixWord ++ tailWord_1954552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954552).length < 2 ^ (prefixWord ++ tailWord_1954552).sum := by decide
  have hdescent : baseEnd_1954552 < baseStart_1954552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954615 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 3]
def baseStart_1954615 : Nat := 118140960795 + 1954615 * 2 ^ 59
def prefixEnd_1954615 : Nat := 4983230072969 + 3 ^ 40 * 1954615 * 2
def baseEnd_1954615 : Nat := 1003656989487975293523395

theorem tailTrace_1954615 : CollatzResearch.WordTrace tailWord_1954615 prefixEnd_1954615 1003656989487975293523395 := by
  unfold tailWord_1954615
  simp only [CollatzResearch.WordTrace]
  refine ⟨71290665813771151510209299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47527110542514101006806199 71290665813771151510209299)
  ·
    refine ⟨106935998720656727265313949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71290665813771151510209299 106935998720656727265313949)
    ·
      refine ⟨40100999520246272724492731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106935998720656727265313949 40100999520246272724492731)
      ·
        refine ⟨60151499280369409086739097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40100999520246272724492731 60151499280369409086739097)
        ·
          refine ⟨45113624460277056815054323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60151499280369409086739097 45113624460277056815054323)
          ·
            refine ⟨67670436690415585222581485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45113624460277056815054323 67670436690415585222581485)
            ·
              refine ⟨25376413758905844458468057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67670436690415585222581485 25376413758905844458468057)
              ·
                refine ⟨19032310319179383343851043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25376413758905844458468057 19032310319179383343851043)
                ·
                  refine ⟨28548465478769075015776565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19032310319179383343851043 28548465478769075015776565)
                  ·
                    refine ⟨2676418638634600782729053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28548465478769075015776565 2676418638634600782729053)
                    ·
                      refine ⟨1003656989487975293523395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2676418638634600782729053 1003656989487975293523395)
                      ·
                        rfl

theorem cell23_1954615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_1954615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954615 prefixEnd_1954615 := by exact prefixLift 1954615
  have htrace : WordTrace (prefixWord ++ tailWord_1954615) baseStart_1954615 baseEnd_1954615 := by
    simpa [prefixWord, tailWord_1954615, baseEnd_1954615] using wordTrace_append hprefix tailTrace_1954615
  have hstable : (prefixWord ++ tailWord_1954615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954615).length < 2 ^ (prefixWord ++ tailWord_1954615).sum := by decide
  have hdescent : baseEnd_1954615 < baseStart_1954615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954645 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_1954645 : Nat := 118140960795 + 1954645 * 2 ^ 59
def prefixEnd_1954645 : Nat := 4983230072969 + 3 ^ 40 * 1954645 * 2
def baseEnd_1954645 : Nat := 1003672393907610176148257

theorem tailTrace_1954645 : CollatzResearch.WordTrace tailWord_1954645 prefixEnd_1954645 1003672393907610176148257 := by
  unfold tailWord_1954645
  simp only [CollatzResearch.WordTrace]
  refine ⟨71291760003662466633801389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47527840002441644422534259 71291760003662466633801389)
  ·
    refine ⟨26734410001373424987675521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71291760003662466633801389 26734410001373424987675521)
    ·
      refine ⟨20050807501030068740756641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26734410001373424987675521 20050807501030068740756641)
      ·
        refine ⟨15038105625772551555567481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20050807501030068740756641 15038105625772551555567481)
        ·
          refine ⟨11278579219329413666675611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15038105625772551555567481 11278579219329413666675611)
          ·
            refine ⟨16917868828994120500013417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11278579219329413666675611 16917868828994120500013417)
            ·
              refine ⟨12688401621745590375010063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16917868828994120500013417 12688401621745590375010063)
              ·
                refine ⟨19032602432618385562515095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12688401621745590375010063 19032602432618385562515095)
                ·
                  refine ⟨28548903648927578343772643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19032602432618385562515095 28548903648927578343772643)
                  ·
                    refine ⟨42823355473391367515658965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28548903648927578343772643 42823355473391367515658965)
                    ·
                      refine ⟨1003672393907610176148257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42823355473391367515658965 1003672393907610176148257)
                      ·
                        rfl

theorem cell23_1954645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_1954645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954645 prefixEnd_1954645 := by exact prefixLift 1954645
  have htrace : WordTrace (prefixWord ++ tailWord_1954645) baseStart_1954645 baseEnd_1954645 := by
    simpa [prefixWord, tailWord_1954645, baseEnd_1954645] using wordTrace_append hprefix tailTrace_1954645
  have hstable : (prefixWord ++ tailWord_1954645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954645).length < 2 ^ (prefixWord ++ tailWord_1954645).sum := by decide
  have hdescent : baseEnd_1954645 < baseStart_1954645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954652 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1954652 : Nat := 118140960795 + 1954652 * 2 ^ 59
def prefixEnd_1954652 : Nat := 4983230072969 + 3 ^ 40 * 1954652 * 2
def baseEnd_1954652 : Nat := 334558662757397216253575

theorem tailTrace_1954652 : CollatzResearch.WordTrace tailWord_1954652 prefixEnd_1954652 334558662757397216253575 := by
  unfold tailWord_1954652
  simp only [CollatzResearch.WordTrace]
  refine ⟨35646007657318553414653105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47528010209758071219537473 35646007657318553414653105)
  ·
    refine ⟨26734505742988915060989829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35646007657318553414653105 26734505742988915060989829)
    ·
      refine ⟨5012719826810421573935593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26734505742988915060989829 5012719826810421573935593)
      ·
        refine ⟨3759539870107816180451695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5012719826810421573935593 3759539870107816180451695)
        ·
          refine ⟨5639309805161724270677543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3759539870107816180451695 5639309805161724270677543)
          ·
            refine ⟨8458964707742586406016315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639309805161724270677543 8458964707742586406016315)
            ·
              refine ⟨12688447061613879609024473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458964707742586406016315 12688447061613879609024473)
              ·
                refine ⟨9516335296210409706768355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12688447061613879609024473 9516335296210409706768355)
                ·
                  refine ⟨14274502944315614560152533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9516335296210409706768355 14274502944315614560152533)
                  ·
                    refine ⟨334558662757397216253575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14274502944315614560152533 334558662757397216253575)
                    ·
                      rfl

theorem cell23_1954652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1954652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954652 prefixEnd_1954652 := by exact prefixLift 1954652
  have htrace : WordTrace (prefixWord ++ tailWord_1954652) baseStart_1954652 baseEnd_1954652 := by
    simpa [prefixWord, tailWord_1954652, baseEnd_1954652] using wordTrace_append hprefix tailTrace_1954652
  have hstable : (prefixWord ++ tailWord_1954652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954652).length < 2 ^ (prefixWord ++ tailWord_1954652).sum := by decide
  have hdescent : baseEnd_1954652 < baseStart_1954652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954655 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 4]
def baseStart_1954655 : Nat := 118140960795 + 1954655 * 2 ^ 59
def prefixEnd_1954655 : Nat := 4983230072969 + 3 ^ 40 * 1954655 * 2
def baseEnd_1954655 : Nat := 1003677528714155137023211

theorem tailTrace_1954655 : CollatzResearch.WordTrace tailWord_1954655 prefixEnd_1954655 1003677528714155137023211 := by
  unfold tailWord_1954655
  simp only [CollatzResearch.WordTrace]
  refine ⟨71292124733626238341665419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47528083155750825561110279 71292124733626238341665419)
  ·
    refine ⟨106938187100439357512498129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71292124733626238341665419 106938187100439357512498129)
    ·
      refine ⟨80203640325329518134373597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106938187100439357512498129 80203640325329518134373597)
      ·
        refine ⟨30076365121998569300390099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80203640325329518134373597 30076365121998569300390099)
        ·
          refine ⟨45114547682997853950585149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30076365121998569300390099 45114547682997853950585149)
          ·
            refine ⟨16917955381124195231469431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45114547682997853950585149 16917955381124195231469431)
            ·
              refine ⟨25376933071686292847204147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16917955381124195231469431 25376933071686292847204147)
              ·
                refine ⟨38065399607529439270806221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25376933071686292847204147 38065399607529439270806221)
                ·
                  refine ⟨14274524852823539726552333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38065399607529439270806221 14274524852823539726552333)
                  ·
                    refine ⟨5352946819808827397457125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14274524852823539726552333 5352946819808827397457125)
                    ·
                      refine ⟨1003677528714155137023211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5352946819808827397457125 1003677528714155137023211)
                      ·
                        rfl

theorem cell23_1954655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_1954655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954655 prefixEnd_1954655 := by exact prefixLift 1954655
  have htrace : WordTrace (prefixWord ++ tailWord_1954655) baseStart_1954655 baseEnd_1954655 := by
    simpa [prefixWord, tailWord_1954655, baseEnd_1954655] using wordTrace_append hprefix tailTrace_1954655
  have hstable : (prefixWord ++ tailWord_1954655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954655).length < 2 ^ (prefixWord ++ tailWord_1954655).sum := by decide
  have hdescent : baseEnd_1954655 < baseStart_1954655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954672 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 1, 6, 2]
def baseStart_1954672 : Nat := 118140960795 + 1954672 * 2 ^ 59
def prefixEnd_1954672 : Nat := 4983230072969 + 3 ^ 40 * 1954672 * 2
def baseEnd_1954672 : Nat := 1003686257885281570510633

theorem tailTrace_1954672 : CollatzResearch.WordTrace tailWord_1954672 prefixEnd_1954672 1003686257885281570510633 := by
  unfold tailWord_1954672
  simp only [CollatzResearch.WordTrace]
  refine ⟨35646372387282325122517135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47528496516376433496689513 35646372387282325122517135)
  ·
    refine ⟨53469558580923487683775703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35646372387282325122517135 53469558580923487683775703)
    ·
      refine ⟨80204337871385231525663555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53469558580923487683775703 80204337871385231525663555)
      ·
        refine ⟨120306506807077847288495333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80204337871385231525663555 120306506807077847288495333)
        ·
          refine ⟨22557470026327096366592875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120306506807077847288495333 22557470026327096366592875)
          ·
            refine ⟨33836205039490644549889313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22557470026327096366592875 33836205039490644549889313)
            ·
              refine ⟨25377153779617983412416985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33836205039490644549889313 25377153779617983412416985)
              ·
                refine ⟨19032865334713487559312739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25377153779617983412416985 19032865334713487559312739)
                ·
                  refine ⟨28549298002070231338969109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19032865334713487559312739 28549298002070231338969109)
                  ·
                    refine ⟨1338248343847042094014177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28549298002070231338969109 1338248343847042094014177)
                    ·
                      refine ⟨1003686257885281570510633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338248343847042094014177 1003686257885281570510633)
                      ·
                        rfl

theorem cell23_1954672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 6, 2].length) (baseStart_1954672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954672 prefixEnd_1954672 := by exact prefixLift 1954672
  have htrace : WordTrace (prefixWord ++ tailWord_1954672) baseStart_1954672 baseEnd_1954672 := by
    simpa [prefixWord, tailWord_1954672, baseEnd_1954672] using wordTrace_append hprefix tailTrace_1954672
  have hstable : (prefixWord ++ tailWord_1954672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954672).length < 2 ^ (prefixWord ++ tailWord_1954672).sum := by decide
  have hdescent : baseEnd_1954672 < baseStart_1954672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954685 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_1954685 : Nat := 118140960795 + 1954685 * 2 ^ 59
def prefixEnd_1954685 : Nat := 4983230072969 + 3 ^ 40 * 1954685 * 2
def baseEnd_1954685 : Nat := 1003692933133790019648073

theorem tailTrace_1954685 : CollatzResearch.WordTrace tailWord_1954685 prefixEnd_1954685 1003692933133790019648073 := by
  unfold tailWord_1954685
  simp only [CollatzResearch.WordTrace]
  refine ⟨71293218923517553465257509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47528812615678368976838339 71293218923517553465257509)
  ·
    refine ⟨13367478548159541274735783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71293218923517553465257509 13367478548159541274735783)
    ·
      refine ⟨20051217822239311912103675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13367478548159541274735783 20051217822239311912103675)
      ·
        refine ⟨30076826733358967868155513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20051217822239311912103675 30076826733358967868155513)
        ·
          refine ⟨22557620050019225901116635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30076826733358967868155513 22557620050019225901116635)
          ·
            refine ⟨33836430075028838851674953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22557620050019225901116635 33836430075028838851674953)
            ·
              refine ⟨25377322556271629138756215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33836430075028838851674953 25377322556271629138756215)
              ·
                refine ⟨38065983834407443708134323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25377322556271629138756215 38065983834407443708134323)
                ·
                  refine ⟨57098975751611165562201485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38065983834407443708134323 57098975751611165562201485)
                  ·
                    refine ⟨21412115906854187085825557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57098975751611165562201485 21412115906854187085825557)
                    ·
                      refine ⟨1003692933133790019648073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21412115906854187085825557 1003692933133790019648073)
                      ·
                        rfl

theorem cell23_1954685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_1954685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954685 prefixEnd_1954685 := by exact prefixLift 1954685
  have htrace : WordTrace (prefixWord ++ tailWord_1954685) baseStart_1954685 baseEnd_1954685 := by
    simpa [prefixWord, tailWord_1954685, baseEnd_1954685] using wordTrace_append hprefix tailTrace_1954685
  have hstable : (prefixWord ++ tailWord_1954685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954685).length < 2 ^ (prefixWord ++ tailWord_1954685).sum := by decide
  have hdescent : baseEnd_1954685 < baseStart_1954685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954686 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1954686 : Nat := 118140960795 + 1954686 * 2 ^ 59
def prefixEnd_1954686 : Nat := 4983230072969 + 3 ^ 40 * 1954686 * 2
def baseEnd_1954686 : Nat := 334564482204814838578523

theorem tailTrace_1954686 : CollatzResearch.WordTrace tailWord_1954686 prefixEnd_1954686 334564482204814838578523 := by
  unfold tailWord_1954686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911656924564241329505489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47528836931009287090695941 8911656924564241329505489)
  ·
    refine ⟨6683742693423180997129117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8911656924564241329505489 6683742693423180997129117)
    ·
      refine ⟨2506403510033692873923419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6683742693423180997129117 2506403510033692873923419)
      ·
        refine ⟨3759605265050539310885129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2506403510033692873923419 3759605265050539310885129)
        ·
          refine ⟨2819703948787904483163847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3759605265050539310885129 2819703948787904483163847)
          ·
            refine ⟨4229555923181856724745771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819703948787904483163847 4229555923181856724745771)
            ·
              refine ⟨6344333884772785087118657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4229555923181856724745771 6344333884772785087118657)
              ·
                refine ⟨4758250413579588815338993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6344333884772785087118657 4758250413579588815338993)
                ·
                  refine ⟨3568687810184691611504245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4758250413579588815338993 3568687810184691611504245)
                  ·
                    refine ⟨334564482204814838578523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3568687810184691611504245 334564482204814838578523)
                    ·
                      rfl

theorem cell23_1954686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1954686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954686 prefixEnd_1954686 := by exact prefixLift 1954686
  have htrace : WordTrace (prefixWord ++ tailWord_1954686) baseStart_1954686 baseEnd_1954686 := by
    simpa [prefixWord, tailWord_1954686, baseEnd_1954686] using wordTrace_append hprefix tailTrace_1954686
  have hstable : (prefixWord ++ tailWord_1954686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954686).length < 2 ^ (prefixWord ++ tailWord_1954686).sum := by decide
  have hdescent : baseEnd_1954686 < baseStart_1954686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954690 : List Nat := [3, 4, 2, 2, 1, 1, 3, 2, 5]
def baseStart_1954690 : Nat := 118140960795 + 1954690 * 2 ^ 59
def prefixEnd_1954690 : Nat := 4983230072969 + 3 ^ 40 * 1954690 * 2
def baseEnd_1954690 : Nat := 111521722281895833342839

theorem tailTrace_1954690 : CollatzResearch.WordTrace tailWord_1954690 prefixEnd_1954690 111521722281895833342839 := by
  unfold tailWord_1954690
  simp only [CollatzResearch.WordTrace]
  refine ⟨17823350322124859829797381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47528934192332959546126349 17823350322124859829797381)
  ·
    refine ⟨3341878185398411218087009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17823350322124859829797381 3341878185398411218087009)
    ·
      refine ⟨2506408639048808413565257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3341878185398411218087009 2506408639048808413565257)
      ·
        refine ⟨1879806479286606310173943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2506408639048808413565257 1879806479286606310173943)
        ·
          refine ⟨2819709718929909465260915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1879806479286606310173943 2819709718929909465260915)
          ·
            refine ⟨4229564578394864197891373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819709718929909465260915 4229564578394864197891373)
            ·
              refine ⟨1586086716898074074209265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4229564578394864197891373 1586086716898074074209265)
              ·
                refine ⟨1189565037673555555656949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586086716898074074209265 1189565037673555555656949)
                ·
                  refine ⟨111521722281895833342839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1189565037673555555656949 111521722281895833342839)
                  ·
                    rfl

theorem cell23_1954690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_1954690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954690 prefixEnd_1954690 := by exact prefixLift 1954690
  have htrace : WordTrace (prefixWord ++ tailWord_1954690) baseStart_1954690 baseEnd_1954690 := by
    simpa [prefixWord, tailWord_1954690, baseEnd_1954690] using wordTrace_append hprefix tailTrace_1954690
  have hstable : (prefixWord ++ tailWord_1954690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954690).length < 2 ^ (prefixWord ++ tailWord_1954690).sum := by decide
  have hdescent : baseEnd_1954690 < baseStart_1954690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954699 : List Nat := [1, 1, 1, 1, 4, 2, 2, 6, 1, 4]
def baseStart_1954699 : Nat := 118140960795 + 1954699 * 2 ^ 59
def prefixEnd_1954699 : Nat := 4983230072969 + 3 ^ 40 * 1954699 * 2
def baseEnd_1954699 : Nat := 334566707287650988291003

theorem tailTrace_1954699 : CollatzResearch.WordTrace tailWord_1954699 prefixEnd_1954699 334566707287650988291003 := by
  unfold tailWord_1954699
  simp only [CollatzResearch.WordTrace]
  refine ⟨71293729545466833856267151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47529153030311222570844767 71293729545466833856267151)
  ·
    refine ⟨106940594318200250784400727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71293729545466833856267151 106940594318200250784400727)
    ·
      refine ⟨160410891477300376176601091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106940594318200250784400727 160410891477300376176601091)
      ·
        refine ⟨240616337215950564264901637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160410891477300376176601091 240616337215950564264901637)
        ·
          refine ⟨45115563227990730799669057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240616337215950564264901637 45115563227990730799669057)
          ·
            refine ⟨33836672420993048099751793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45115563227990730799669057 33836672420993048099751793)
            ·
              refine ⟨25377504315744786074813845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33836672420993048099751793 25377504315744786074813845)
              ·
                refine ⟨1189570514800536847256899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25377504315744786074813845 1189570514800536847256899)
                ·
                  refine ⟨1784355772200805270885349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189570514800536847256899 1784355772200805270885349)
                  ·
                    refine ⟨334566707287650988291003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1784355772200805270885349 334566707287650988291003)
                    ·
                      rfl

theorem cell23_1954699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 1, 4].length) (baseStart_1954699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954699 prefixEnd_1954699 := by exact prefixLift 1954699
  have htrace : WordTrace (prefixWord ++ tailWord_1954699) baseStart_1954699 baseEnd_1954699 := by
    simpa [prefixWord, tailWord_1954699, baseEnd_1954699] using wordTrace_append hprefix tailTrace_1954699
  have hstable : (prefixWord ++ tailWord_1954699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954699).length < 2 ^ (prefixWord ++ tailWord_1954699).sum := by decide
  have hdescent : baseEnd_1954699 < baseStart_1954699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954735 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 5]
def baseStart_1954735 : Nat := 118140960795 + 1954735 * 2 ^ 59
def prefixEnd_1954735 : Nat := 4983230072969 + 3 ^ 40 * 1954735 * 2
def baseEnd_1954735 : Nat := 1003718607166514824022843

theorem tailTrace_1954735 : CollatzResearch.WordTrace tailWord_1954735 prefixEnd_1954735 1003718607166514824022843 := by
  unfold tailWord_1954735
  simp only [CollatzResearch.WordTrace]
  refine ⟨71295042573336412004577659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47530028382224274669718439 71295042573336412004577659)
  ·
    refine ⟨106942563860004618006866489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71295042573336412004577659 106942563860004618006866489)
    ·
      refine ⟨80206922895003463505149867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106942563860004618006866489 80206922895003463505149867)
      ·
        refine ⟨120310384342505195257724801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80206922895003463505149867 120310384342505195257724801)
        ·
          refine ⟨90232788256878896443293601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120310384342505195257724801 90232788256878896443293601)
          ·
            refine ⟨67674591192659172332470201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90232788256878896443293601 67674591192659172332470201)
            ·
              refine ⟨50755943394494379249352651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67674591192659172332470201 50755943394494379249352651)
              ·
                refine ⟨76133915091741568874028977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50755943394494379249352651 76133915091741568874028977)
                ·
                  refine ⟨57100436318806176655521733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76133915091741568874028977 57100436318806176655521733)
                  ·
                    refine ⟨10706331809776158122910325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57100436318806176655521733 10706331809776158122910325)
                    ·
                      refine ⟨1003718607166514824022843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10706331809776158122910325 1003718607166514824022843)
                      ·
                        rfl

theorem cell23_1954735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 5].length) (baseStart_1954735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954735 prefixEnd_1954735 := by exact prefixLift 1954735
  have htrace : WordTrace (prefixWord ++ tailWord_1954735) baseStart_1954735 baseEnd_1954735 := by
    simpa [prefixWord, tailWord_1954735, baseEnd_1954735] using wordTrace_append hprefix tailTrace_1954735
  have hstable : (prefixWord ++ tailWord_1954735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954735).length < 2 ^ (prefixWord ++ tailWord_1954735).sum := by decide
  have hdescent : baseEnd_1954735 < baseStart_1954735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954783 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 2, 3, 2]
def baseStart_1954783 : Nat := 118140960795 + 1954783 * 2 ^ 59
def prefixEnd_1954783 : Nat := 4983230072969 + 3 ^ 40 * 1954783 * 2
def baseEnd_1954783 : Nat := 1003743254237930636222623

theorem tailTrace_1954783 : CollatzResearch.WordTrace tailWord_1954783 prefixEnd_1954783 1003743254237930636222623 := by
  unfold tailWord_1954783
  simp only [CollatzResearch.WordTrace]
  refine ⟨71296793277162516202325003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47531195518108344134883335 71296793277162516202325003)
  ·
    refine ⟨106945189915743774303487505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71296793277162516202325003 106945189915743774303487505)
    ·
      refine ⟨80208892436807830727615629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106945189915743774303487505 80208892436807830727615629)
      ·
        refine ⟨30078334663802936522855861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80208892436807830727615629 30078334663802936522855861)
        ·
          refine ⟨2819843874731525299017737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30078334663802936522855861 2819843874731525299017737)
          ·
            refine ⟨2114882906048643974263303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2819843874731525299017737 2114882906048643974263303)
            ·
              refine ⟨3172324359072965961394955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114882906048643974263303 3172324359072965961394955)
              ·
                refine ⟨4758486538609448942092433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172324359072965961394955 4758486538609448942092433)
                ·
                  refine ⟨3568864903957086706569325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4758486538609448942092433 3568864903957086706569325)
                  ·
                    refine ⟨1338324338983907514963497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3568864903957086706569325 1338324338983907514963497)
                    ·
                      refine ⟨1003743254237930636222623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338324338983907514963497 1003743254237930636222623)
                      ·
                        rfl

theorem cell23_1954783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_1954783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954783 prefixEnd_1954783 := by exact prefixLift 1954783
  have htrace : WordTrace (prefixWord ++ tailWord_1954783) baseStart_1954783 baseEnd_1954783 := by
    simpa [prefixWord, tailWord_1954783, baseEnd_1954783] using wordTrace_append hprefix tailTrace_1954783
  have hstable : (prefixWord ++ tailWord_1954783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954783).length < 2 ^ (prefixWord ++ tailWord_1954783).sum := by decide
  have hdescent : baseEnd_1954783 < baseStart_1954783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954806 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_1954806 : Nat := 118140960795 + 1954806 * 2 ^ 59
def prefixEnd_1954806 : Nat := 4983230072969 + 3 ^ 40 * 1954806 * 2
def baseEnd_1954806 : Nat := 334585021430994682078339

theorem tailTrace_1954806 : CollatzResearch.WordTrace tailWord_1954806 prefixEnd_1954806 334585021430994682078339 := by
  unfold tailWord_1954806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4456102009754949445650767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47531754770719460753608181 4456102009754949445650767)
  ·
    refine ⟨6684153014632424168476151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4456102009754949445650767 6684153014632424168476151)
    ·
      refine ⟨10026229521948636252714227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6684153014632424168476151 10026229521948636252714227)
      ·
        refine ⟨15039344282922954379071341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10026229521948636252714227 15039344282922954379071341)
        ·
          refine ⟨5639754106096107892151753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15039344282922954379071341 5639754106096107892151753)
          ·
            refine ⟨4229815579572080919113815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5639754106096107892151753 4229815579572080919113815)
            ·
              refine ⟨6344723369358121378670723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4229815579572080919113815 6344723369358121378670723)
              ·
                refine ⟨9517085054037182068006085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6344723369358121378670723 9517085054037182068006085)
                ·
                  refine ⟨1784453447631971637751141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9517085054037182068006085 1784453447631971637751141)
                  ·
                    refine ⟨334585021430994682078339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1784453447631971637751141 334585021430994682078339)
                    ·
                      rfl

theorem cell23_1954806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_1954806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954806 prefixEnd_1954806 := by exact prefixLift 1954806
  have htrace : WordTrace (prefixWord ++ tailWord_1954806) baseStart_1954806 baseEnd_1954806 := by
    simpa [prefixWord, tailWord_1954806, baseEnd_1954806] using wordTrace_append hprefix tailTrace_1954806
  have hstable : (prefixWord ++ tailWord_1954806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954806).length < 2 ^ (prefixWord ++ tailWord_1954806).sum := by decide
  have hdescent : baseEnd_1954806 < baseStart_1954806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954826 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_1954826 : Nat := 118140960795 + 1954826 * 2 ^ 59
def prefixEnd_1954826 : Nat := 4983230072969 + 3 ^ 40 * 1954826 * 2
def baseEnd_1954826 : Nat := 1003765333906073967984925

theorem tailTrace_1954826 : CollatzResearch.WordTrace tailWord_1954826 prefixEnd_1954826 1003765333906073967984925 := by
  unfold tailWord_1954826
  simp only [CollatzResearch.WordTrace]
  refine ⟨17824590404001683636535083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47532241077337823030760221 17824590404001683636535083)
  ·
    refine ⟨26736885606002525454802625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17824590404001683636535083 26736885606002525454802625)
    ·
      refine ⟨20052664204501894091101969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26736885606002525454802625 20052664204501894091101969)
      ·
        refine ⟨15039498153376420568326477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20052664204501894091101969 15039498153376420568326477)
        ·
          refine ⟨5639811807516157713122429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15039498153376420568326477 5639811807516157713122429)
          ·
            refine ⟨2114929427818559142420911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5639811807516157713122429 2114929427818559142420911)
            ·
              refine ⟨3172394141727838713631367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2114929427818559142420911 3172394141727838713631367)
              ·
                refine ⟨4758591212591758070447051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172394141727838713631367 4758591212591758070447051)
                ·
                  refine ⟨7137886818887637105670577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758591212591758070447051 7137886818887637105670577)
                  ·
                    refine ⟨5353415114165727829252933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7137886818887637105670577 5353415114165727829252933)
                    ·
                      refine ⟨1003765333906073967984925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5353415114165727829252933 1003765333906073967984925)
                      ·
                        rfl

theorem cell23_1954826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_1954826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954826 prefixEnd_1954826 := by exact prefixLift 1954826
  have htrace : WordTrace (prefixWord ++ tailWord_1954826) baseStart_1954826 baseEnd_1954826 := by
    simpa [prefixWord, tailWord_1954826, baseEnd_1954826] using wordTrace_append hprefix tailTrace_1954826
  have hstable : (prefixWord ++ tailWord_1954826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954826).length < 2 ^ (prefixWord ++ tailWord_1954826).sum := by decide
  have hdescent : baseEnd_1954826 < baseStart_1954826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954842 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_1954842 : Nat := 118140960795 + 1954842 * 2 ^ 59
def prefixEnd_1954842 : Nat := 4983230072969 + 3 ^ 40 * 1954842 * 2
def baseEnd_1954842 : Nat := 1003773549596545905384851

theorem tailTrace_1954842 : CollatzResearch.WordTrace tailWord_1954842 prefixEnd_1954842 1003773549596545905384851 := by
  unfold tailWord_1954842
  simp only [CollatzResearch.WordTrace]
  refine ⟨17824736295987192319680695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47532630122632512852481853 17824736295987192319680695)
  ·
    refine ⟨26737104443980788479521043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17824736295987192319680695 26737104443980788479521043)
    ·
      refine ⟨40105656665971182719281565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26737104443980788479521043 40105656665971182719281565)
      ·
        refine ⟨15039621249739193519730587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40105656665971182719281565 15039621249739193519730587)
        ·
          refine ⟨22559431874608790279595881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15039621249739193519730587 22559431874608790279595881)
          ·
            refine ⟨16919573905956592709696911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22559431874608790279595881 16919573905956592709696911)
            ·
              refine ⟨25379360858934889064545367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16919573905956592709696911 25379360858934889064545367)
              ·
                refine ⟨38069041288402333596818051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25379360858934889064545367 38069041288402333596818051)
                ·
                  refine ⟨57103561932603500395227077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38069041288402333596818051 57103561932603500395227077)
                  ·
                    refine ⟨10706917862363156324105077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57103561932603500395227077 10706917862363156324105077)
                    ·
                      refine ⟨1003773549596545905384851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10706917862363156324105077 1003773549596545905384851)
                      ·
                        rfl

theorem cell23_1954842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_1954842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954842 prefixEnd_1954842 := by exact prefixLift 1954842
  have htrace : WordTrace (prefixWord ++ tailWord_1954842) baseStart_1954842 baseEnd_1954842 := by
    simpa [prefixWord, tailWord_1954842, baseEnd_1954842] using wordTrace_append hprefix tailTrace_1954842
  have hstable : (prefixWord ++ tailWord_1954842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954842).length < 2 ^ (prefixWord ++ tailWord_1954842).sum := by decide
  have hdescent : baseEnd_1954842 < baseStart_1954842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954892 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 9]
def baseStart_1954892 : Nat := 118140960795 + 1954892 * 2 ^ 59
def prefixEnd_1954892 : Nat := 4983230072969 + 3 ^ 40 * 1954892 * 2
def baseEnd_1954892 : Nat := 111533247069918967751069

theorem tailTrace_1954892 : CollatzResearch.WordTrace tailWord_1954892 prefixEnd_1954892 111533247069918967751069 := by
  unfold tailWord_1954892
  simp only [CollatzResearch.WordTrace]
  refine ⟨35650384416883813909021465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47533845889178418545361953 35650384416883813909021465)
  ·
    refine ⟨26737788312662860431766099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35650384416883813909021465 26737788312662860431766099)
    ·
      refine ⟨40106682468994290647649149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26737788312662860431766099 40106682468994290647649149)
      ·
        refine ⟨15040005925872858992868431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40106682468994290647649149 15040005925872858992868431)
        ·
          refine ⟨22560008888809288489302647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15040005925872858992868431 22560008888809288489302647)
          ·
            refine ⟨33840013333213932733953971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22560008888809288489302647 33840013333213932733953971)
            ·
              refine ⟨50760019999820899100930957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33840013333213932733953971 50760019999820899100930957)
              ·
                refine ⟨19035007499932837162849109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50760019999820899100930957 19035007499932837162849109)
                ·
                  refine ⟨111533247069918967751069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19035007499932837162849109 111533247069918967751069)
                  ·
                    rfl

theorem cell23_1954892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_1954892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954892 prefixEnd_1954892 := by exact prefixLift 1954892
  have htrace : WordTrace (prefixWord ++ tailWord_1954892) baseStart_1954892 baseEnd_1954892 := by
    simpa [prefixWord, tailWord_1954892, baseEnd_1954892] using wordTrace_append hprefix tailTrace_1954892
  have hstable : (prefixWord ++ tailWord_1954892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954892).length < 2 ^ (prefixWord ++ tailWord_1954892).sum := by decide
  have hdescent : baseEnd_1954892 < baseStart_1954892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954933 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1954933 : Nat := 118140960795 + 1954933 * 2 ^ 59
def prefixEnd_1954933 : Nat := 4983230072969 + 3 ^ 40 * 1954933 * 2
def baseEnd_1954933 : Nat := 1003820276336105049346933

theorem tailTrace_1954933 : CollatzResearch.WordTrace tailWord_1954933 prefixEnd_1954933 1003820276336105049346933 := by
  unfold tailWord_1954933
  simp only [CollatzResearch.WordTrace]
  refine ⟨71302264226619091820285453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47534842817746061213523635 71302264226619091820285453)
  ·
    refine ⟨26738349084982159432607045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71302264226619091820285453 26738349084982159432607045)
    ·
      refine ⟨5013440453434154893613821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26738349084982159432607045 5013440453434154893613821)
      ·
        refine ⟨1880040170037808085105183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5013440453434154893613821 1880040170037808085105183)
        ·
          refine ⟨2820060255056712127657775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1880040170037808085105183 2820060255056712127657775)
          ·
            refine ⟨4230090382585068191486663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820060255056712127657775 4230090382585068191486663)
            ·
              refine ⟨6345135573877602287229995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4230090382585068191486663 6345135573877602287229995)
              ·
                refine ⟨9517703360816403430844993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345135573877602287229995 9517703360816403430844993)
                ·
                  refine ⟨7138277520612302573133745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9517703360816403430844993 7138277520612302573133745)
                  ·
                    refine ⟨5353708140459226929850309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7138277520612302573133745 5353708140459226929850309)
                    ·
                      refine ⟨1003820276336105049346933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5353708140459226929850309 1003820276336105049346933)
                      ·
                        rfl

theorem cell23_1954933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1954933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954933 prefixEnd_1954933 := by exact prefixLift 1954933
  have htrace : WordTrace (prefixWord ++ tailWord_1954933) baseStart_1954933 baseEnd_1954933 := by
    simpa [prefixWord, tailWord_1954933, baseEnd_1954933] using wordTrace_append hprefix tailTrace_1954933
  have hstable : (prefixWord ++ tailWord_1954933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954933).length < 2 ^ (prefixWord ++ tailWord_1954933).sum := by decide
  have hdescent : baseEnd_1954933 < baseStart_1954933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954976 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 4, 4, 2]
def baseStart_1954976 : Nat := 118140960795 + 1954976 * 2 ^ 59
def prefixEnd_1954976 : Nat := 4983230072969 + 3 ^ 40 * 1954976 * 2
def baseEnd_1954976 : Nat := 1003842356004248381109235

theorem tailTrace_1954976 : CollatzResearch.WordTrace tailWord_1954976 prefixEnd_1954976 1003842356004248381109235 := by
  unfold tailWord_1954976
  simp only [CollatzResearch.WordTrace]
  refine ⟨35651916282731655082050391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47535888376975540109400521 35651916282731655082050391)
  ·
    refine ⟨53477874424097482623075587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35651916282731655082050391 53477874424097482623075587)
    ·
      refine ⟨80216811636146223934613381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53477874424097482623075587 80216811636146223934613381)
      ·
        refine ⟨15040652181777416987740009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80216811636146223934613381 15040652181777416987740009)
        ·
          refine ⟨11280489136333062740805007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15040652181777416987740009 11280489136333062740805007)
          ·
            refine ⟨16920733704499594111207511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11280489136333062740805007 16920733704499594111207511)
            ·
              refine ⟨25381100556749391166811267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16920733704499594111207511 25381100556749391166811267)
              ·
                refine ⟨38071650835124086750216901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25381100556749391166811267 38071650835124086750216901)
                ·
                  refine ⟨7138434531585766265665669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38071650835124086750216901 7138434531585766265665669)
                  ·
                    refine ⟨1338456474672331174812313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7138434531585766265665669 1338456474672331174812313)
                    ·
                      refine ⟨1003842356004248381109235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338456474672331174812313 1003842356004248381109235)
                      ·
                        rfl

theorem cell23_1954976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_1954976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954976 prefixEnd_1954976 := by exact prefixLift 1954976
  have htrace : WordTrace (prefixWord ++ tailWord_1954976) baseStart_1954976 baseEnd_1954976 := by
    simpa [prefixWord, tailWord_1954976, baseEnd_1954976] using wordTrace_append hprefix tailTrace_1954976
  have hstable : (prefixWord ++ tailWord_1954976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954976).length < 2 ^ (prefixWord ++ tailWord_1954976).sum := by decide
  have hdescent : baseEnd_1954976 < baseStart_1954976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1954993 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 2, 4, 2]
def baseStart_1954993 : Nat := 118140960795 + 1954993 * 2 ^ 59
def prefixEnd_1954993 : Nat := 4983230072969 + 3 ^ 40 * 1954993 * 2
def baseEnd_1954993 : Nat := 1003851085175374814596657

theorem tailTrace_1954993 : CollatzResearch.WordTrace tailWord_1954993 prefixEnd_1954993 1003851085175374814596657 := by
  unfold tailWord_1954993
  simp only [CollatzResearch.WordTrace]
  refine ⟨71304452606401722067469633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47536301737601148044979755 71304452606401722067469633)
  ·
    refine ⟨53478339454801291550602225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71304452606401722067469633 53478339454801291550602225)
    ·
      refine ⟨40108754591100968662951669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53478339454801291550602225 40108754591100968662951669)
      ·
        refine ⟨3760195742915715812151719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40108754591100968662951669 3760195742915715812151719)
        ·
          refine ⟨5640293614373573718227579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760195742915715812151719 5640293614373573718227579)
          ·
            refine ⟨8460440421560360577341369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640293614373573718227579 8460440421560360577341369)
            ·
              refine ⟨6345330316170270433006027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8460440421560360577341369 6345330316170270433006027)
              ·
                refine ⟨9517995474255405649509041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345330316170270433006027 9517995474255405649509041)
                ·
                  refine ⟨7138496605691554237131781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9517995474255405649509041 7138496605691554237131781)
                  ·
                    refine ⟨1338468113567166419462209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7138496605691554237131781 1338468113567166419462209)
                    ·
                      refine ⟨1003851085175374814596657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338468113567166419462209 1003851085175374814596657)
                      ·
                        rfl

theorem cell23_1954993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_1954993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1954993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1954993 prefixEnd_1954993 := by exact prefixLift 1954993
  have htrace : WordTrace (prefixWord ++ tailWord_1954993) baseStart_1954993 baseEnd_1954993 := by
    simpa [prefixWord, tailWord_1954993, baseEnd_1954993] using wordTrace_append hprefix tailTrace_1954993
  have hstable : (prefixWord ++ tailWord_1954993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1954993).length < 2 ^ (prefixWord ++ tailWord_1954993).sum := by decide
  have hdescent : baseEnd_1954993 < baseStart_1954993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1954993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955037 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1955037 : Nat := 118140960795 + 1955037 * 2 ^ 59
def prefixEnd_1955037 : Nat := 4983230072969 + 3 ^ 40 * 1955037 * 2
def baseEnd_1955037 : Nat := 334624559441390880815485

theorem tailTrace_1955037 : CollatzResearch.WordTrace tailWord_1955037 prefixEnd_1955037 334624559441390880815485 := by
  unfold tailWord_1955037
  simp only [CollatzResearch.WordTrace]
  refine ⟨71306057418242317582071365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47537371612161545054714243 71306057418242317582071365)
  ·
    refine ⟨13369885765920434546638381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71306057418242317582071365 13369885765920434546638381)
    ·
      refine ⟨5013707162220162954989393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13369885765920434546638381 5013707162220162954989393)
      ·
        refine ⟨3760280371665122216242045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5013707162220162954989393 3760280371665122216242045)
        ·
          refine ⟨1410105139374420831090767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3760280371665122216242045 1410105139374420831090767)
          ·
            refine ⟨2115157709061631246636151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410105139374420831090767 2115157709061631246636151)
            ·
              refine ⟨3172736563592446869954227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115157709061631246636151 3172736563592446869954227)
              ·
                refine ⟨4759104845388670304931341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172736563592446869954227 4759104845388670304931341)
                ·
                  refine ⟨1784664317020751364349253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4759104845388670304931341 1784664317020751364349253)
                  ·
                    refine ⟨334624559441390880815485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1784664317020751364349253 334624559441390880815485)
                    ·
                      rfl

theorem cell23_1955037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1955037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955037 prefixEnd_1955037 := by exact prefixLift 1955037
  have htrace : WordTrace (prefixWord ++ tailWord_1955037) baseStart_1955037 baseEnd_1955037 := by
    simpa [prefixWord, tailWord_1955037, baseEnd_1955037] using wordTrace_append hprefix tailTrace_1955037
  have hstable : (prefixWord ++ tailWord_1955037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955037).length < 2 ^ (prefixWord ++ tailWord_1955037).sum := by decide
  have hdescent : baseEnd_1955037 < baseStart_1955037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955066 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_1955066 : Nat := 118140960795 + 1955066 * 2 ^ 59
def prefixEnd_1955066 : Nat := 4983230072969 + 3 ^ 40 * 1955066 * 2
def baseEnd_1955066 : Nat := 1003888569263153028983821

theorem tailTrace_1955066 : CollatzResearch.WordTrace tailWord_1955066 prefixEnd_1955066 1003888569263153028983821 := by
  unfold tailWord_1955066
  simp only [CollatzResearch.WordTrace]
  refine ⟨17826778783784313883719263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47538076756758170356584701 17826778783784313883719263)
  ·
    refine ⟨26740168175676470825578895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17826778783784313883719263 26740168175676470825578895)
    ·
      refine ⟨40110252263514706238368343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26740168175676470825578895 40110252263514706238368343)
      ·
        refine ⟨60165378395272059357552515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40110252263514706238368343 60165378395272059357552515)
        ·
          refine ⟨90248067592908089036328773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60165378395272059357552515 90248067592908089036328773)
          ·
            refine ⟨16921512673670266694311645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90248067592908089036328773 16921512673670266694311645)
            ·
              refine ⟨6345567252626350010366867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16921512673670266694311645 6345567252626350010366867)
              ·
                refine ⟨9518350878939525015550301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345567252626350010366867 9518350878939525015550301)
                ·
                  refine ⟨3569381579602321880831363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9518350878939525015550301 3569381579602321880831363)
                  ·
                    refine ⟨5354072369403482821247045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3569381579602321880831363 5354072369403482821247045)
                    ·
                      refine ⟨1003888569263153028983821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5354072369403482821247045 1003888569263153028983821)
                      ·
                        rfl

theorem cell23_1955066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_1955066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955066 prefixEnd_1955066 := by exact prefixLift 1955066
  have htrace : WordTrace (prefixWord ++ tailWord_1955066) baseStart_1955066 baseEnd_1955066 := by
    simpa [prefixWord, tailWord_1955066, baseEnd_1955066] using wordTrace_append hprefix tailTrace_1955066
  have hstable : (prefixWord ++ tailWord_1955066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955066).length < 2 ^ (prefixWord ++ tailWord_1955066).sum := by decide
  have hdescent : baseEnd_1955066 < baseStart_1955066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955069 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_1955069 : Nat := 118140960795 + 1955069 * 2 ^ 59
def prefixEnd_1955069 : Nat := 4983230072969 + 3 ^ 40 * 1955069 * 2
def baseEnd_1955069 : Nat := 1003890109705116517246307

theorem tailTrace_1955069 : CollatzResearch.WordTrace tailWord_1955069 prefixEnd_1955069 1003890109705116517246307 := by
  unfold tailWord_1955069
  simp only [CollatzResearch.WordTrace]
  refine ⟨71307224554126387047236261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47538149702750924698157507 71307224554126387047236261)
  ·
    refine ⟨13370104603898697571356799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71307224554126387047236261 13370104603898697571356799)
    ·
      refine ⟨20055156905848046357035199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13370104603898697571356799 20055156905848046357035199)
      ·
        refine ⟨30082735358772069535552799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20055156905848046357035199 30082735358772069535552799)
        ·
          refine ⟨45124103038158104303329199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30082735358772069535552799 45124103038158104303329199)
          ·
            refine ⟨67686154557237156454993799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45124103038158104303329199 67686154557237156454993799)
            ·
              refine ⟨101529231835855734682490699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67686154557237156454993799 101529231835855734682490699)
              ·
                refine ⟨152293847753783602023736049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101529231835855734682490699 152293847753783602023736049)
                ·
                  refine ⟨114220385815337701517802037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152293847753783602023736049 114220385815337701517802037)
                  ·
                    refine ⟨10708161170187909517293941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114220385815337701517802037 10708161170187909517293941)
                    ·
                      refine ⟨1003890109705116517246307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10708161170187909517293941 1003890109705116517246307)
                      ·
                        rfl

theorem cell23_1955069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_1955069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955069 prefixEnd_1955069 := by exact prefixLift 1955069
  have htrace : WordTrace (prefixWord ++ tailWord_1955069) baseStart_1955069 baseEnd_1955069 := by
    simpa [prefixWord, tailWord_1955069, baseEnd_1955069] using wordTrace_append hprefix tailTrace_1955069
  have hstable : (prefixWord ++ tailWord_1955069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955069).length < 2 ^ (prefixWord ++ tailWord_1955069).sum := by decide
  have hdescent : baseEnd_1955069 < baseStart_1955069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955070 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_1955070 : Nat := 118140960795 + 1955070 * 2 ^ 59
def prefixEnd_1955070 : Nat := 4983230072969 + 3 ^ 40 * 1955070 * 2
def baseEnd_1955070 : Nat := 1003890623185771013333803

theorem tailTrace_1955070 : CollatzResearch.WordTrace tailWord_1955070 prefixEnd_1955070 1003890623185771013333803 := by
  unfold tailWord_1955070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913407628390345527252833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47538174018081842812015109 8913407628390345527252833)
  ·
    refine ⟨6685055721292759145439625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8913407628390345527252833 6685055721292759145439625)
    ·
      refine ⟨5013791790969569359079719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6685055721292759145439625 5013791790969569359079719)
      ·
        refine ⟨7520687686454354038619579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5013791790969569359079719 7520687686454354038619579)
        ·
          refine ⟨11281031529681531057929369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520687686454354038619579 11281031529681531057929369)
          ·
            refine ⟨8460773647261148293447027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11281031529681531057929369 8460773647261148293447027)
            ·
              refine ⟨12691160470891722440170541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460773647261148293447027 12691160470891722440170541)
              ·
                refine ⟨4759185176584395915063953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12691160470891722440170541 4759185176584395915063953)
                ·
                  refine ⟨3569388882438296936297965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4759185176584395915063953 3569388882438296936297965)
                  ·
                    refine ⟨1338520830914361351111737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3569388882438296936297965 1338520830914361351111737)
                    ·
                      refine ⟨1003890623185771013333803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338520830914361351111737 1003890623185771013333803)
                      ·
                        rfl

theorem cell23_1955070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_1955070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955070 prefixEnd_1955070 := by exact prefixLift 1955070
  have htrace : WordTrace (prefixWord ++ tailWord_1955070) baseStart_1955070 baseEnd_1955070 := by
    simpa [prefixWord, tailWord_1955070, baseEnd_1955070] using wordTrace_append hprefix tailTrace_1955070
  have hstable : (prefixWord ++ tailWord_1955070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955070).length < 2 ^ (prefixWord ++ tailWord_1955070).sum := by decide
  have hdescent : baseEnd_1955070 < baseStart_1955070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955076 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1955076 : Nat := 118140960795 + 1955076 * 2 ^ 59
def prefixEnd_1955076 : Nat := 4983230072969 + 3 ^ 40 * 1955076 * 2
def baseEnd_1955076 : Nat := 334631234689899329952925

theorem tailTrace_1955076 : CollatzResearch.WordTrace tailWord_1955076 prefixEnd_1955076 334631234689899329952925 := by
  unfold tailWord_1955076
  simp only [CollatzResearch.WordTrace]
  refine ⟨35653739932550513621370541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47538319910067351495160721 35653739932550513621370541)
  ·
    refine ⟨13370152474706442608013953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35653739932550513621370541 13370152474706442608013953)
    ·
      refine ⟨10027614356029831956010465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13370152474706442608013953 10027614356029831956010465)
      ·
        refine ⟨7520710767022373967007849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10027614356029831956010465 7520710767022373967007849)
        ·
          refine ⟨5640533075266780475255887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7520710767022373967007849 5640533075266780475255887)
          ·
            refine ⟨8460799612900170712883831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640533075266780475255887 8460799612900170712883831)
            ·
              refine ⟨12691199419350256069325747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460799612900170712883831 12691199419350256069325747)
              ·
                refine ⟨19036799129025384103988621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12691199419350256069325747 19036799129025384103988621)
                ·
                  refine ⟨7138799673384519038995733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19036799129025384103988621 7138799673384519038995733)
                  ·
                    refine ⟨334631234689899329952925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7138799673384519038995733 334631234689899329952925)
                    ·
                      rfl

theorem cell23_1955076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1955076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955076 prefixEnd_1955076 := by exact prefixLift 1955076
  have htrace : WordTrace (prefixWord ++ tailWord_1955076) baseStart_1955076 baseEnd_1955076 := by
    simpa [prefixWord, tailWord_1955076, baseEnd_1955076] using wordTrace_append hprefix tailTrace_1955076
  have hstable : (prefixWord ++ tailWord_1955076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955076).length < 2 ^ (prefixWord ++ tailWord_1955076).sum := by decide
  have hdescent : baseEnd_1955076 < baseStart_1955076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955080 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 1, 5]
def baseStart_1955080 : Nat := 118140960795 + 1955080 * 2 ^ 59
def prefixEnd_1955080 : Nat := 4983230072969 + 3 ^ 40 * 1955080 * 2
def baseEnd_1955080 : Nat := 334631919330771991402919

theorem tailTrace_1955080 : CollatzResearch.WordTrace tailWord_1955080 prefixEnd_1955080 334631919330771991402919 := by
  unfold tailWord_1955080
  simp only [CollatzResearch.WordTrace]
  refine ⟨35653812878543267962943347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47538417171391023950591129 35653812878543267962943347)
  ·
    refine ⟨53480719317814901944415021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35653812878543267962943347 53480719317814901944415021)
    ·
      refine ⟨20055269744180588229155633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53480719317814901944415021 20055269744180588229155633)
      ·
        refine ⟨15041452308135441171866725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20055269744180588229155633 15041452308135441171866725)
        ·
          refine ⟨2820272307775395219725011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15041452308135441171866725 2820272307775395219725011)
          ·
            refine ⟨4230408461663092829587517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820272307775395219725011 4230408461663092829587517)
            ·
              refine ⟨1586403173123659811095319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4230408461663092829587517 1586403173123659811095319)
              ·
                refine ⟨2379604759685489716642979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586403173123659811095319 2379604759685489716642979)
                ·
                  refine ⟨3569407139528234574964469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379604759685489716642979 3569407139528234574964469)
                  ·
                    refine ⟨334631919330771991402919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3569407139528234574964469 334631919330771991402919)
                    ·
                      rfl

theorem cell23_1955080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_1955080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955080 prefixEnd_1955080 := by exact prefixLift 1955080
  have htrace : WordTrace (prefixWord ++ tailWord_1955080) baseStart_1955080 baseEnd_1955080 := by
    simpa [prefixWord, tailWord_1955080, baseEnd_1955080] using wordTrace_append hprefix tailTrace_1955080
  have hstable : (prefixWord ++ tailWord_1955080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955080).length < 2 ^ (prefixWord ++ tailWord_1955080).sum := by decide
  have hdescent : baseEnd_1955080 < baseStart_1955080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955117 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_1955117 : Nat := 118140960795 + 1955117 * 2 ^ 59
def prefixEnd_1955117 : Nat := 4983230072969 + 3 ^ 40 * 1955117 * 2
def baseEnd_1955117 : Nat := 1003914756776532329446087

theorem tailTrace_1955117 : CollatzResearch.WordTrace tailWord_1955117 prefixEnd_1955117 1003914756776532329446087 := by
  unfold tailWord_1955117
  simp only [CollatzResearch.WordTrace]
  refine ⟨71308975257952491244983605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47539316838634994163322403 71308975257952491244983605)
  ·
    refine ⟨6685216430433046054217213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71308975257952491244983605 6685216430433046054217213)
    ·
      refine ⟨2506956161412392270331455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6685216430433046054217213 2506956161412392270331455)
      ·
        refine ⟨3760434242118588405497183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2506956161412392270331455 3760434242118588405497183)
        ·
          refine ⟨5640651363177882608245775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760434242118588405497183 5640651363177882608245775)
          ·
            refine ⟨8460977044766823912368663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640651363177882608245775 8460977044766823912368663)
            ·
              refine ⟨12691465567150235868552995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8460977044766823912368663 12691465567150235868552995)
              ·
                refine ⟨19037198350725353802829493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12691465567150235868552995 19037198350725353802829493)
                ·
                  refine ⟨1784737345380501919015265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19037198350725353802829493 1784737345380501919015265)
                  ·
                    refine ⟨1338553009035376439261449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1784737345380501919015265 1338553009035376439261449)
                    ·
                      refine ⟨1003914756776532329446087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338553009035376439261449 1003914756776532329446087)
                      ·
                        rfl

theorem cell23_1955117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_1955117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955117 prefixEnd_1955117 := by exact prefixLift 1955117
  have htrace : WordTrace (prefixWord ++ tailWord_1955117) baseStart_1955117 baseEnd_1955117 := by
    simpa [prefixWord, tailWord_1955117, baseEnd_1955117] using wordTrace_append hprefix tailTrace_1955117
  have hstable : (prefixWord ++ tailWord_1955117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955117).length < 2 ^ (prefixWord ++ tailWord_1955117).sum := by decide
  have hdescent : baseEnd_1955117 < baseStart_1955117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955119 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 4, 7]
def baseStart_1955119 : Nat := 118140960795 + 1955119 * 2 ^ 59
def prefixEnd_1955119 : Nat := 4983230072969 + 3 ^ 40 * 1955119 * 2
def baseEnd_1955119 : Nat := 334638594579280440540359

theorem tailTrace_1955119 : CollatzResearch.WordTrace tailWord_1955119 prefixEnd_1955119 334638594579280440540359 := by
  unfold tailWord_1955119
  simp only [CollatzResearch.WordTrace]
  refine ⟨71309048203945245586556411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47539365469296830391037607 71309048203945245586556411)
  ·
    refine ⟨106963572305917868379834617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71309048203945245586556411 106963572305917868379834617)
    ·
      refine ⟨80222679229438401284875963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106963572305917868379834617 80222679229438401284875963)
      ·
        refine ⟨120334018844157601927313945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80222679229438401284875963 120334018844157601927313945)
        ·
          refine ⟨90250514133118201445485459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120334018844157601927313945 90250514133118201445485459)
          ·
            refine ⟨135375771199677302168228189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90250514133118201445485459 135375771199677302168228189)
            ·
              refine ⟨50765914199878988313085571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135375771199677302168228189 50765914199878988313085571)
              ·
                refine ⟨76148871299818482469628357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50765914199878988313085571 76148871299818482469628357)
                ·
                  refine ⟨14277913368715965463055317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76148871299818482469628357 14277913368715965463055317)
                  ·
                    refine ⟨334638594579280440540359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14277913368715965463055317 334638594579280440540359)
                    ·
                      rfl

theorem cell23_1955119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_1955119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955119 prefixEnd_1955119 := by exact prefixLift 1955119
  have htrace : WordTrace (prefixWord ++ tailWord_1955119) baseStart_1955119 baseEnd_1955119 := by
    simpa [prefixWord, tailWord_1955119, baseEnd_1955119] using wordTrace_append hprefix tailTrace_1955119
  have hstable : (prefixWord ++ tailWord_1955119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955119).length < 2 ^ (prefixWord ++ tailWord_1955119).sum := by decide
  have hdescent : baseEnd_1955119 < baseStart_1955119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955134 : List Nat := [4, 2, 1, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_1955134 : Nat := 118140960795 + 1955134 * 2 ^ 59
def prefixEnd_1955134 : Nat := 4983230072969 + 3 ^ 40 * 1955134 * 2
def baseEnd_1955134 : Nat := 1003923485947658762933509

theorem tailTrace_1955134 : CollatzResearch.WordTrace tailWord_1955134 prefixEnd_1955134 1003923485947658762933509 := by
  unfold tailWord_1955134
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913699412361362893544057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47539730199260602098901637 8913699412361362893544057)
  ·
    refine ⟨6685274559271022170158043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8913699412361362893544057 6685274559271022170158043)
    ·
      refine ⟨10027911838906533255237065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6685274559271022170158043 10027911838906533255237065)
      ·
        refine ⟨7520933879179899941427799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10027911838906533255237065 7520933879179899941427799)
        ·
          refine ⟨11281400818769849912141699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520933879179899941427799 11281400818769849912141699)
          ·
            refine ⟨16922101228154774868212549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11281400818769849912141699 16922101228154774868212549)
            ·
              refine ⟨3172893980279020287789853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16922101228154774868212549 3172893980279020287789853)
              ·
                refine ⟨1189835242604632607921195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3172893980279020287789853 1189835242604632607921195)
                ·
                  refine ⟨1784752863906948911881793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189835242604632607921195 1784752863906948911881793)
                  ·
                    refine ⟨1338564647930211683911345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1784752863906948911881793 1338564647930211683911345)
                    ·
                      refine ⟨1003923485947658762933509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338564647930211683911345 1003923485947658762933509)
                      ·
                        rfl

theorem cell23_1955134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_1955134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955134 prefixEnd_1955134 := by exact prefixLift 1955134
  have htrace : WordTrace (prefixWord ++ tailWord_1955134) baseStart_1955134 baseEnd_1955134 := by
    simpa [prefixWord, tailWord_1955134, baseEnd_1955134] using wordTrace_append hprefix tailTrace_1955134
  have hstable : (prefixWord ++ tailWord_1955134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955134).length < 2 ^ (prefixWord ++ tailWord_1955134).sum := by decide
  have hdescent : baseEnd_1955134 < baseStart_1955134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955137 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_1955137 : Nat := 118140960795 + 1955137 * 2 ^ 59
def prefixEnd_1955137 : Nat := 4983230072969 + 3 ^ 40 * 1955137 * 2
def baseEnd_1955137 : Nat := 1003925026389622251195995

theorem tailTrace_1955137 : CollatzResearch.WordTrace tailWord_1955137 prefixEnd_1955137 1003925026389622251195995 := by
  unfold tailWord_1955137
  simp only [CollatzResearch.WordTrace]
  refine ⟨71309704717880034660711665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47539803145253356440474443 71309704717880034660711665)
  ·
    refine ⟨53482278538410025995533749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71309704717880034660711665 53482278538410025995533749)
    ·
      refine ⟨5013963612975939937081289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53482278538410025995533749 5013963612975939937081289)
      ·
        refine ⟨3760472709731954952810967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5013963612975939937081289 3760472709731954952810967)
        ·
          refine ⟨5640709064597932429216451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760472709731954952810967 5640709064597932429216451)
          ·
            refine ⟨8461063596896898643824677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640709064597932429216451 8461063596896898643824677)
            ·
              refine ⟨1586449424418168495717127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8461063596896898643824677 1586449424418168495717127)
              ·
                refine ⟨2379674136627252743575691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586449424418168495717127 2379674136627252743575691)
                ·
                  refine ⟨3569511204940879115363537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379674136627252743575691 3569511204940879115363537)
                  ·
                    refine ⟨2677133403705659336522653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3569511204940879115363537 2677133403705659336522653)
                    ·
                      refine ⟨1003925026389622251195995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2677133403705659336522653 1003925026389622251195995)
                      ·
                        rfl

theorem cell23_1955137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_1955137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955137 prefixEnd_1955137 := by exact prefixLift 1955137
  have htrace : WordTrace (prefixWord ++ tailWord_1955137) baseStart_1955137 baseEnd_1955137 := by
    simpa [prefixWord, tailWord_1955137, baseEnd_1955137] using wordTrace_append hprefix tailTrace_1955137
  have hstable : (prefixWord ++ tailWord_1955137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955137).length < 2 ^ (prefixWord ++ tailWord_1955137).sum := by decide
  have hdescent : baseEnd_1955137 < baseStart_1955137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955218 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 2, 1, 3]
def baseStart_1955218 : Nat := 118140960795 + 1955218 * 2 ^ 59
def prefixEnd_1955218 : Nat := 4983230072969 + 3 ^ 40 * 1955218 * 2
def baseEnd_1955218 : Nat := 1003966618322636434283123

theorem tailTrace_1955218 : CollatzResearch.WordTrace tailWord_1955218 prefixEnd_1955218 1003966618322636434283123 := by
  unfold tailWord_1955218
  simp only [CollatzResearch.WordTrace]
  refine ⟨17828164757646646373602577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47541772687057723662940205 17828164757646646373602577)
  ·
    refine ⟨13371123568234984780201933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17828164757646646373602577 13371123568234984780201933)
    ·
      refine ⟨5014171338088119292575725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13371123568234984780201933 5014171338088119292575725)
      ·
        refine ⟨1880314251783044734715897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5014171338088119292575725 1880314251783044734715897)
        ·
          refine ⟨1410235688837283551036923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1880314251783044734715897 1410235688837283551036923)
          ·
            refine ⟨2115353533255925326555385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410235688837283551036923 2115353533255925326555385)
            ·
              refine ⟨1586515149941943994916539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2115353533255925326555385 1586515149941943994916539)
              ·
                refine ⟨2379772724912915992374809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586515149941943994916539 2379772724912915992374809)
                ·
                  refine ⟨1784829543684686994281107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2379772724912915992374809 1784829543684686994281107)
                  ·
                    refine ⟨2677244315527030491421661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1784829543684686994281107 2677244315527030491421661)
                    ·
                      refine ⟨1003966618322636434283123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2677244315527030491421661 1003966618322636434283123)
                      ·
                        rfl

theorem cell23_1955218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_1955218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955218 prefixEnd_1955218 := by exact prefixLift 1955218
  have htrace : WordTrace (prefixWord ++ tailWord_1955218) baseStart_1955218 baseEnd_1955218 := by
    simpa [prefixWord, tailWord_1955218, baseEnd_1955218] using wordTrace_append hprefix tailTrace_1955218
  have hstable : (prefixWord ++ tailWord_1955218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955218).length < 2 ^ (prefixWord ++ tailWord_1955218).sum := by decide
  have hdescent : baseEnd_1955218 < baseStart_1955218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955224 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 2, 2, 2]
def baseStart_1955224 : Nat := 118140960795 + 1955224 * 2 ^ 59
def prefixEnd_1955224 : Nat := 4983230072969 + 3 ^ 40 * 1955224 * 2
def baseEnd_1955224 : Nat := 1003969699206563410808095

theorem tailTrace_1955224 : CollatzResearch.WordTrace tailWord_1955224 prefixEnd_1955224 1003969699206563410808095 := by
  unfold tailWord_1955224
  simp only [CollatzResearch.WordTrace]
  refine ⟨35656438934282424259564363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47541918579043232346085817 35656438934282424259564363)
  ·
    refine ⟨53484658401423636389346545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35656438934282424259564363 53484658401423636389346545)
    ·
      refine ⟨40113493801067727292009909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53484658401423636389346545 40113493801067727292009909)
      ·
        refine ⟨3760640043850099433625929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40113493801067727292009909 3760640043850099433625929)
        ·
          refine ⟨2820480032887574575219447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3760640043850099433625929 2820480032887574575219447)
          ·
            refine ⟨4230720049331361862829171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820480032887574575219447 4230720049331361862829171)
            ·
              refine ⟨6346080073997042794243757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4230720049331361862829171 6346080073997042794243757)
              ·
                refine ⟨2379780027748891047841409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6346080073997042794243757 2379780027748891047841409)
                ·
                  refine ⟨1784835020811668285881057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2379780027748891047841409 1784835020811668285881057)
                  ·
                    refine ⟨1338626265608751214410793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1784835020811668285881057 1338626265608751214410793)
                    ·
                      refine ⟨1003969699206563410808095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338626265608751214410793 1003969699206563410808095)
                      ·
                        rfl

theorem cell23_1955224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_1955224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955224 prefixEnd_1955224 := by exact prefixLift 1955224
  have htrace : WordTrace (prefixWord ++ tailWord_1955224) baseStart_1955224 baseEnd_1955224 := by
    simpa [prefixWord, tailWord_1955224, baseEnd_1955224] using wordTrace_append hprefix tailTrace_1955224
  have hstable : (prefixWord ++ tailWord_1955224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955224).length < 2 ^ (prefixWord ++ tailWord_1955224).sum := by decide
  have hdescent : baseEnd_1955224 < baseStart_1955224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955236 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1955236 : Nat := 118140960795 + 1955236 * 2 ^ 59
def prefixEnd_1955236 : Nat := 4983230072969 + 3 ^ 40 * 1955236 * 2
def baseEnd_1955236 : Nat := 1003975860974417363858039

theorem tailTrace_1955236 : CollatzResearch.WordTrace tailWord_1955236 prefixEnd_1955236 1003975860974417363858039 := by
  unfold tailWord_1955236
  simp only [CollatzResearch.WordTrace]
  refine ⟨35656657772260687284282781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47542210363014249712377041 35656657772260687284282781)
  ·
    refine ⟨13371246664597757731606043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35656657772260687284282781 13371246664597757731606043)
    ·
      refine ⟨20056869996896636597409065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13371246664597757731606043 20056869996896636597409065)
      ·
        refine ⟨15042652497672477448056799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20056869996896636597409065 15042652497672477448056799)
        ·
          refine ⟨22563978746508716172085199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15042652497672477448056799 22563978746508716172085199)
          ·
            refine ⟨33845968119763074258127799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22563978746508716172085199 33845968119763074258127799)
            ·
              refine ⟨50768952179644611387191699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33845968119763074258127799 50768952179644611387191699)
              ·
                refine ⟨76153428269466917080787549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50768952179644611387191699 76153428269466917080787549)
                ·
                  refine ⟨28557535601050093905295331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76153428269466917080787549 28557535601050093905295331)
                  ·
                    refine ⟨42836303401575140857942997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28557535601050093905295331 42836303401575140857942997)
                    ·
                      refine ⟨1003975860974417363858039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42836303401575140857942997 1003975860974417363858039)
                      ·
                        rfl

theorem cell23_1955236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1955236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955236 prefixEnd_1955236 := by exact prefixLift 1955236
  have htrace : WordTrace (prefixWord ++ tailWord_1955236) baseStart_1955236 baseEnd_1955236 := by
    simpa [prefixWord, tailWord_1955236, baseEnd_1955236] using wordTrace_append hprefix tailTrace_1955236
  have hstable : (prefixWord ++ tailWord_1955236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955236).length < 2 ^ (prefixWord ++ tailWord_1955236).sum := by decide
  have hdescent : baseEnd_1955236 < baseStart_1955236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955253 : List Nat := [1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1955253 : Nat := 118140960795 + 1955253 * 2 ^ 59
def prefixEnd_1955253 : Nat := 4983230072969 + 3 ^ 40 * 1955253 * 2
def baseEnd_1955253 : Nat := 1003984590145543797345461

theorem tailTrace_1955253 : CollatzResearch.WordTrace tailWord_1955253 prefixEnd_1955253 1003984590145543797345461 := by
  unfold tailWord_1955253
  simp only [CollatzResearch.WordTrace]
  refine ⟨71313935585459786471934413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47542623723639857647956275 71313935585459786471934413)
  ·
    refine ⟨26742725844547419926975405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71313935585459786471934413 26742725844547419926975405)
    ·
      refine ⟨10028522191705282472615777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26742725844547419926975405 10028522191705282472615777)
      ·
        refine ⟨7521391643778961854461833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10028522191705282472615777 7521391643778961854461833)
        ·
          refine ⟨5641043732834221390846375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7521391643778961854461833 5641043732834221390846375)
          ·
            refine ⟨8461565599251332086269563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5641043732834221390846375 8461565599251332086269563)
            ·
              refine ⟨12692348398876998129404345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8461565599251332086269563 12692348398876998129404345)
              ·
                refine ⟨9519261299157748597053259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12692348398876998129404345 9519261299157748597053259)
                ·
                  refine ⟨14278891948736622895579889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9519261299157748597053259 14278891948736622895579889)
                  ·
                    refine ⟨10709168961552467171684917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14278891948736622895579889 10709168961552467171684917)
                    ·
                      refine ⟨1003984590145543797345461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10709168961552467171684917 1003984590145543797345461)
                      ·
                        rfl

theorem cell23_1955253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1955253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955253 prefixEnd_1955253 := by exact prefixLift 1955253
  have htrace : WordTrace (prefixWord ++ tailWord_1955253) baseStart_1955253 baseEnd_1955253 := by
    simpa [prefixWord, tailWord_1955253, baseEnd_1955253] using wordTrace_append hprefix tailTrace_1955253
  have hstable : (prefixWord ++ tailWord_1955253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955253).length < 2 ^ (prefixWord ++ tailWord_1955253).sum := by decide
  have hdescent : baseEnd_1955253 < baseStart_1955253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955263 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 3, 6, 2]
def baseStart_1955263 : Nat := 118140960795 + 1955263 * 2 ^ 59
def prefixEnd_1955263 : Nat := 4983230072969 + 3 ^ 40 * 1955263 * 2
def baseEnd_1955263 : Nat := 1003989724952088758220415

theorem tailTrace_1955263 : CollatzResearch.WordTrace tailWord_1955263 prefixEnd_1955263 1003989724952088758220415 := by
  unfold tailWord_1955263
  simp only [CollatzResearch.WordTrace]
  refine ⟨71314300315423558179798443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47542866876949038786532295 71314300315423558179798443)
  ·
    refine ⟨106971450473135337269697665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71314300315423558179798443 106971450473135337269697665)
    ·
      refine ⟨80228587854851502952273249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106971450473135337269697665 80228587854851502952273249)
      ·
        refine ⟨60171440891138627214204937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80228587854851502952273249 60171440891138627214204937)
        ·
          refine ⟨45128580668353970410653703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60171440891138627214204937 45128580668353970410653703)
          ·
            refine ⟨67692871002530955615980555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45128580668353970410653703 67692871002530955615980555)
            ·
              refine ⟨101539306503796433423970833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67692871002530955615980555 101539306503796433423970833)
              ·
                refine ⟨76154479877847325067978125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101539306503796433423970833 76154479877847325067978125)
                ·
                  refine ⟨28557929954192746900491797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76154479877847325067978125 28557929954192746900491797)
                  ·
                    refine ⟨1338652966602785010960553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28557929954192746900491797 1338652966602785010960553)
                    ·
                      refine ⟨1003989724952088758220415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338652966602785010960553 1003989724952088758220415)
                      ·
                        rfl

theorem cell23_1955263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 6, 2].length) (baseStart_1955263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955263 prefixEnd_1955263 := by exact prefixLift 1955263
  have htrace : WordTrace (prefixWord ++ tailWord_1955263) baseStart_1955263 baseEnd_1955263 := by
    simpa [prefixWord, tailWord_1955263, baseEnd_1955263] using wordTrace_append hprefix tailTrace_1955263
  have hstable : (prefixWord ++ tailWord_1955263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955263).length < 2 ^ (prefixWord ++ tailWord_1955263).sum := by decide
  have hdescent : baseEnd_1955263 < baseStart_1955263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955273 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 3, 4]
def baseStart_1955273 : Nat := 118140960795 + 1955273 * 2 ^ 59
def prefixEnd_1955273 : Nat := 4983230072969 + 3 ^ 40 * 1955273 * 2
def baseEnd_1955273 : Nat := 334664953252877906365123

theorem tailTrace_1955273 : CollatzResearch.WordTrace tailWord_1955273 prefixEnd_1955273 334664953252877906365123 := by
  unfold tailWord_1955273
  simp only [CollatzResearch.WordTrace]
  refine ⟨71314665045387329887662473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47543110030258219925108315 71314665045387329887662473)
  ·
    refine ⟨53485998784040497415746855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71314665045387329887662473 53485998784040497415746855)
    ·
      refine ⟨80228998176060746123620283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53485998784040497415746855 80228998176060746123620283)
      ·
        refine ⟨120343497264091119185430425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80228998176060746123620283 120343497264091119185430425)
        ·
          refine ⟨90257622948068339389072819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120343497264091119185430425 90257622948068339389072819)
          ·
            refine ⟨135386434422102509083609229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90257622948068339389072819 135386434422102509083609229)
            ·
              refine ⟨50769912908288440906353461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135386434422102509083609229 50769912908288440906353461)
              ·
                refine ⟨4759679335152041334970637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50769912908288440906353461 4759679335152041334970637)
                ·
                  refine ⟨1784879750682015500613989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4759679335152041334970637 1784879750682015500613989)
                  ·
                    refine ⟨334664953252877906365123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1784879750682015500613989 334664953252877906365123)
                    ·
                      rfl

theorem cell23_1955273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 4].length) (baseStart_1955273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955273 prefixEnd_1955273 := by exact prefixLift 1955273
  have htrace : WordTrace (prefixWord ++ tailWord_1955273) baseStart_1955273 baseEnd_1955273 := by
    simpa [prefixWord, tailWord_1955273, baseEnd_1955273] using wordTrace_append hprefix tailTrace_1955273
  have hstable : (prefixWord ++ tailWord_1955273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955273).length < 2 ^ (prefixWord ++ tailWord_1955273).sum := by decide
  have hdescent : baseEnd_1955273 < baseStart_1955273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955290 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 3, 4]
def baseStart_1955290 : Nat := 118140960795 + 1955290 * 2 ^ 59
def prefixEnd_1955290 : Nat := 4983230072969 + 3 ^ 40 * 1955290 * 2
def baseEnd_1955290 : Nat := 334667862976586717527597

theorem tailTrace_1955290 : CollatzResearch.WordTrace tailWord_1955290 prefixEnd_1955290 334667862976586717527597 := by
  unfold tailWord_1955290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17828821271581435447757831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47543523390883827860687549 17828821271581435447757831)
  ·
    refine ⟨26743231907372153171636747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17828821271581435447757831 26743231907372153171636747)
    ·
      refine ⟨40114847861058229757455121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26743231907372153171636747 40114847861058229757455121)
      ·
        refine ⟨30086135895793672318091341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40114847861058229757455121 30086135895793672318091341)
        ·
          refine ⟨11282300960922627119284253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30086135895793672318091341 11282300960922627119284253)
          ·
            refine ⟨4230862860345985169731595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11282300960922627119284253 4230862860345985169731595)
            ·
              refine ⟨6346294290518977754597393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4230862860345985169731595 6346294290518977754597393)
              ·
                refine ⟨4759720717889233315948045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6346294290518977754597393 4759720717889233315948045)
                ·
                  refine ⟨1784895269208462493480517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4759720717889233315948045 1784895269208462493480517)
                  ·
                    refine ⟨334667862976586717527597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1784895269208462493480517 334667862976586717527597)
                    ·
                      rfl

theorem cell23_1955290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_1955290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955290 prefixEnd_1955290 := by exact prefixLift 1955290
  have htrace : WordTrace (prefixWord ++ tailWord_1955290) baseStart_1955290 baseEnd_1955290 := by
    simpa [prefixWord, tailWord_1955290, baseEnd_1955290] using wordTrace_append hprefix tailTrace_1955290
  have hstable : (prefixWord ++ tailWord_1955290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955290).length < 2 ^ (prefixWord ++ tailWord_1955290).sum := by decide
  have hdescent : baseEnd_1955290 < baseStart_1955290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955320 : List Nat := [2, 1, 2, 1, 1, 7, 1, 2, 6]
def baseStart_1955320 : Nat := 118140960795 + 1955320 * 2 ^ 59
def prefixEnd_1955320 : Nat := 4983230072969 + 3 ^ 40 * 1955320 * 2
def baseEnd_1955320 : Nat := 111557665927710559467517

theorem tailTrace_1955320 : CollatzResearch.WordTrace tailWord_1955320 prefixEnd_1955320 111557665927710559467517 := by
  unfold tailWord_1955320
  simp only [CollatzResearch.WordTrace]
  refine ⟨35658189638108528457311707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47544252850811371276415609 35658189638108528457311707)
  ·
    refine ⟨53487284457162792685967561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35658189638108528457311707 53487284457162792685967561)
    ·
      refine ⟨40115463342872094514475671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53487284457162792685967561 40115463342872094514475671)
      ·
        refine ⟨60173195014308141771713507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40115463342872094514475671 60173195014308141771713507)
        ·
          refine ⟨90259792521462212657570261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60173195014308141771713507 90259792521462212657570261)
          ·
            refine ⟨2115463887221770609161803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 90259792521462212657570261 2115463887221770609161803)
            ·
              refine ⟨3173195830832655913742705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115463887221770609161803 3173195830832655913742705)
              ·
                refine ⟨2379896873124491935307029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3173195830832655913742705 2379896873124491935307029)
                ·
                  refine ⟨111557665927710559467517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2379896873124491935307029 111557665927710559467517)
                  ·
                    rfl

theorem cell23_1955320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 2, 6].length) (baseStart_1955320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955320 prefixEnd_1955320 := by exact prefixLift 1955320
  have htrace : WordTrace (prefixWord ++ tailWord_1955320) baseStart_1955320 baseEnd_1955320 := by
    simpa [prefixWord, tailWord_1955320, baseEnd_1955320] using wordTrace_append hprefix tailTrace_1955320
  have hstable : (prefixWord ++ tailWord_1955320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955320).length < 2 ^ (prefixWord ++ tailWord_1955320).sum := by decide
  have hdescent : baseEnd_1955320 < baseStart_1955320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955357 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_1955357 : Nat := 118140960795 + 1955357 * 2 ^ 59
def prefixEnd_1955357 : Nat := 4983230072969 + 3 ^ 40 * 1955357 * 2
def baseEnd_1955357 : Nat := 1004037992133611390444983

theorem tailTrace_1955357 : CollatzResearch.WordTrace tailWord_1955357 prefixEnd_1955357 1004037992133611390444983 := by
  unfold tailWord_1955357
  simp only [CollatzResearch.WordTrace]
  refine ⟨71317728777083012233720325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47545152518055341489146883 71317728777083012233720325)
  ·
    refine ⟨13372074145703064793822561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71317728777083012233720325 13372074145703064793822561)
    ·
      refine ⟨10029055609277298595366921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13372074145703064793822561 10029055609277298595366921)
      ·
        refine ⟨7521791706957973946525191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10029055609277298595366921 7521791706957973946525191)
        ·
          refine ⟨11282687560436960919787787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7521791706957973946525191 11282687560436960919787787)
          ·
            refine ⟨16924031340655441379681681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11282687560436960919787787 16924031340655441379681681)
            ·
              refine ⟨12693023505491581034761261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16924031340655441379681681 12693023505491581034761261)
              ·
                refine ⟨4759883814559342888035473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12693023505491581034761261 4759883814559342888035473)
                ·
                  refine ⟨3569912860919507166026605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4759883814559342888035473 3569912860919507166026605)
                  ·
                    refine ⟨1338717322844815187259977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3569912860919507166026605 1338717322844815187259977)
                    ·
                      refine ⟨1004037992133611390444983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338717322844815187259977 1004037992133611390444983)
                      ·
                        rfl

theorem cell23_1955357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_1955357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955357 prefixEnd_1955357 := by exact prefixLift 1955357
  have htrace : WordTrace (prefixWord ++ tailWord_1955357) baseStart_1955357 baseEnd_1955357 := by
    simpa [prefixWord, tailWord_1955357, baseEnd_1955357] using wordTrace_append hprefix tailTrace_1955357
  have hstable : (prefixWord ++ tailWord_1955357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955357).length < 2 ^ (prefixWord ++ tailWord_1955357).sum := by decide
  have hdescent : baseEnd_1955357 < baseStart_1955357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955374 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_1955374 : Nat := 118140960795 + 1955374 * 2 ^ 59
def prefixEnd_1955374 : Nat := 4983230072969 + 3 ^ 40 * 1955374 * 2
def baseEnd_1955374 : Nat := 1004046721304737823932405

theorem tailTrace_1955374 : CollatzResearch.WordTrace tailWord_1955374 prefixEnd_1955374 1004046721304737823932405 := by
  unfold tailWord_1955374
  simp only [CollatzResearch.WordTrace]
  refine ⟨8914793602252678017136147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47545565878680949424726117 8914793602252678017136147)
  ·
    refine ⟨13372190403379017025704221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8914793602252678017136147 13372190403379017025704221)
    ·
      refine ⟨5014571401267131384639083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13372190403379017025704221 5014571401267131384639083)
      ·
        refine ⟨7521857101900697076958625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5014571401267131384639083 7521857101900697076958625)
        ·
          refine ⟨5641392826425522807718969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7521857101900697076958625 5641392826425522807718969)
          ·
            refine ⟨4231044619819142105789227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5641392826425522807718969 4231044619819142105789227)
            ·
              refine ⟨6346566929728713158683841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231044619819142105789227 6346566929728713158683841)
              ·
                refine ⟨4759925197296534869012881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6346566929728713158683841 4759925197296534869012881)
                ·
                  refine ⟨3569943897972401151759661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4759925197296534869012881 3569943897972401151759661)
                  ·
                    refine ⟨1338728961739650431909873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3569943897972401151759661 1338728961739650431909873)
                    ·
                      refine ⟨1004046721304737823932405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338728961739650431909873 1004046721304737823932405)
                      ·
                        rfl

theorem cell23_1955374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_1955374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955374 prefixEnd_1955374 := by exact prefixLift 1955374
  have htrace : WordTrace (prefixWord ++ tailWord_1955374) baseStart_1955374 baseEnd_1955374 := by
    simpa [prefixWord, tailWord_1955374, baseEnd_1955374] using wordTrace_append hprefix tailTrace_1955374
  have hstable : (prefixWord ++ tailWord_1955374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955374).length < 2 ^ (prefixWord ++ tailWord_1955374).sum := by decide
  have hdescent : baseEnd_1955374 < baseStart_1955374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955381 : List Nat := [1, 3, 3, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_1955381 : Nat := 118140960795 + 1955381 * 2 ^ 59
def prefixEnd_1955381 : Nat := 4983230072969 + 3 ^ 40 * 1955381 * 2
def baseEnd_1955381 : Nat := 1004050315669319296544873

theorem tailTrace_1955381 : CollatzResearch.WordTrace tailWord_1955381 prefixEnd_1955381 1004050315669319296544873 := by
  unfold tailWord_1955381
  simp only [CollatzResearch.WordTrace]
  refine ⟨71318604128996064332593997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47545736085997376221729331 71318604128996064332593997)
  ·
    refine ⟨26744476548373524124722749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71318604128996064332593997 26744476548373524124722749)
    ·
      refine ⟨10029178705640071546771031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26744476548373524124722749 10029178705640071546771031)
      ·
        refine ⟨15043768058460107320156547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10029178705640071546771031 15043768058460107320156547)
        ·
          refine ⟨22565652087690160980234821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15043768058460107320156547 22565652087690160980234821)
          ·
            refine ⟨4231059766441905183794029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22565652087690160980234821 4231059766441905183794029)
            ·
              refine ⟨1586647412415714443922761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4231059766441905183794029 1586647412415714443922761)
              ·
                refine ⟨1189985559311785832942071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1586647412415714443922761 1189985559311785832942071)
                ·
                  refine ⟨1784978338967678749413107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1189985559311785832942071 1784978338967678749413107)
                  ·
                    refine ⟨2677467508451518124119661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1784978338967678749413107 2677467508451518124119661)
                    ·
                      refine ⟨1004050315669319296544873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2677467508451518124119661 1004050315669319296544873)
                      ·
                        rfl

theorem cell23_1955381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_1955381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955381 prefixEnd_1955381 := by exact prefixLift 1955381
  have htrace : WordTrace (prefixWord ++ tailWord_1955381) baseStart_1955381 baseEnd_1955381 := by
    simpa [prefixWord, tailWord_1955381, baseEnd_1955381] using wordTrace_append hprefix tailTrace_1955381
  have hstable : (prefixWord ++ tailWord_1955381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955381).length < 2 ^ (prefixWord ++ tailWord_1955381).sum := by decide
  have hdescent : baseEnd_1955381 < baseStart_1955381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955383 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_1955383 : Nat := 118140960795 + 1955383 * 2 ^ 59
def prefixEnd_1955383 : Nat := 4983230072969 + 3 ^ 40 * 1955383 * 2
def baseEnd_1955383 : Nat := 1004051342630628288719863

theorem tailTrace_1955383 : CollatzResearch.WordTrace tailWord_1955383 prefixEnd_1955383 1004051342630628288719863 := by
  unfold tailWord_1955383
  simp only [CollatzResearch.WordTrace]
  refine ⟨71318677074988818674166803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47545784716659212449444535 71318677074988818674166803)
  ·
    refine ⟨106978015612483228011250205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71318677074988818674166803 106978015612483228011250205)
    ·
      refine ⟨40116755854681210504218827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106978015612483228011250205 40116755854681210504218827)
      ·
        refine ⟨60175133782021815756328241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40116755854681210504218827 60175133782021815756328241)
        ·
          refine ⟨45131350336516361817246181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60175133782021815756328241 45131350336516361817246181)
          ·
            refine ⟨8462128188096817840733659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45131350336516361817246181 8462128188096817840733659)
            ·
              refine ⟨12693192282145226761100489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8462128188096817840733659 12693192282145226761100489)
              ·
                refine ⟨9519894211608920070825367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12693192282145226761100489 9519894211608920070825367)
                ·
                  refine ⟨14279841317413380106238051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9519894211608920070825367 14279841317413380106238051)
                  ·
                    refine ⟨21419761976120070159357077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14279841317413380106238051 21419761976120070159357077)
                    ·
                      refine ⟨1004051342630628288719863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21419761976120070159357077 1004051342630628288719863)
                      ·
                        rfl

theorem cell23_1955383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_1955383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955383 prefixEnd_1955383 := by exact prefixLift 1955383
  have htrace : WordTrace (prefixWord ++ tailWord_1955383) baseStart_1955383 baseEnd_1955383 := by
    simpa [prefixWord, tailWord_1955383, baseEnd_1955383] using wordTrace_append hprefix tailTrace_1955383
  have hstable : (prefixWord ++ tailWord_1955383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955383).length < 2 ^ (prefixWord ++ tailWord_1955383).sum := by decide
  have hdescent : baseEnd_1955383 < baseStart_1955383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955433 : List Nat := [1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_1955433 : Nat := 118140960795 + 1955433 * 2 ^ 59
def prefixEnd_1955433 : Nat := 4983230072969 + 3 ^ 40 * 1955433 * 2
def baseEnd_1955433 : Nat := 1004077016663353093094633

theorem tailTrace_1955433 : CollatzResearch.WordTrace tailWord_1955433 prefixEnd_1955433 1004077016663353093094633 := by
  unfold tailWord_1955433
  simp only [CollatzResearch.WordTrace]
  refine ⟨71320500724807677213486953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47547000483205118142324635 71320500724807677213486953)
  ·
    refine ⟨53490375543605757910115215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71320500724807677213486953 53490375543605757910115215)
    ·
      refine ⟨80235563315408636865172823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53490375543605757910115215 80235563315408636865172823)
      ·
        refine ⟨120353344973112955297759235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80235563315408636865172823 120353344973112955297759235)
        ·
          refine ⟨180530017459669432946638853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120353344973112955297759235 180530017459669432946638853)
          ·
            refine ⟨33849378273688018677494785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180530017459669432946638853 33849378273688018677494785)
            ·
              refine ⟨25387033705266014008121089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33849378273688018677494785 25387033705266014008121089)
              ·
                refine ⟨19040275278949510506090817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25387033705266014008121089 19040275278949510506090817)
                ·
                  refine ⟨14280206459212132879568113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19040275278949510506090817 14280206459212132879568113)
                  ·
                    refine ⟨10710154844409099659676085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14280206459212132879568113 10710154844409099659676085)
                    ·
                      refine ⟨1004077016663353093094633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10710154844409099659676085 1004077016663353093094633)
                      ·
                        rfl

theorem cell23_1955433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_1955433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955433 prefixEnd_1955433 := by exact prefixLift 1955433
  have htrace : WordTrace (prefixWord ++ tailWord_1955433) baseStart_1955433 baseEnd_1955433 := by
    simpa [prefixWord, tailWord_1955433, baseEnd_1955433] using wordTrace_append hprefix tailTrace_1955433
  have hstable : (prefixWord ++ tailWord_1955433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955433).length < 2 ^ (prefixWord ++ tailWord_1955433).sum := by decide
  have hdescent : baseEnd_1955433 < baseStart_1955433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955438 : List Nat := [4, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_1955438 : Nat := 118140960795 + 1955438 * 2 ^ 59
def prefixEnd_1955438 : Nat := 4983230072969 + 3 ^ 40 * 1955438 * 2
def baseEnd_1955438 : Nat := 1004079584066625573532111

theorem tailTrace_1955438 : CollatzResearch.WordTrace tailWord_1955438 prefixEnd_1955438 1004079584066625573532111 := by
  unfold tailWord_1955438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915085386223695383427371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47547122059859708711612645 8915085386223695383427371)
  ·
    refine ⟨13372628079335543075141057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8915085386223695383427371 13372628079335543075141057)
    ·
      refine ⟨10029471059501657306355793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13372628079335543075141057 10029471059501657306355793)
      ·
        refine ⟨7522103294626242979766845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10029471059501657306355793 7522103294626242979766845)
        ·
          refine ⟨2820788735484841117412567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7522103294626242979766845 2820788735484841117412567)
          ·
            refine ⟨4231183103227261676118851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820788735484841117412567 4231183103227261676118851)
            ·
              refine ⟨6346774654840892514178277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231183103227261676118851 6346774654840892514178277)
              ·
                refine ⟨1190020247782667346408427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6346774654840892514178277 1190020247782667346408427)
                ·
                  refine ⟨1785030371674001019612641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190020247782667346408427 1785030371674001019612641)
                  ·
                    refine ⟨1338772778755500764709481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1785030371674001019612641 1338772778755500764709481)
                    ·
                      refine ⟨1004079584066625573532111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338772778755500764709481 1004079584066625573532111)
                      ·
                        rfl

theorem cell23_1955438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_1955438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955438 prefixEnd_1955438 := by exact prefixLift 1955438
  have htrace : WordTrace (prefixWord ++ tailWord_1955438) baseStart_1955438 baseEnd_1955438 := by
    simpa [prefixWord, tailWord_1955438, baseEnd_1955438] using wordTrace_append hprefix tailTrace_1955438
  have hstable : (prefixWord ++ tailWord_1955438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955438).length < 2 ^ (prefixWord ++ tailWord_1955438).sum := by decide
  have hdescent : baseEnd_1955438 < baseStart_1955438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955567 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 1, 6, 2]
def baseStart_1955567 : Nat := 118140960795 + 1955567 * 2 ^ 59
def prefixEnd_1955567 : Nat := 4983230072969 + 3 ^ 40 * 1955567 * 2
def baseEnd_1955567 : Nat := 1004145823071055568819017

theorem tailTrace_1955567 : CollatzResearch.WordTrace tailWord_1955567 prefixEnd_1955567 1004145823071055568819017 := by
  unfold tailWord_1955567
  simp only [CollatzResearch.WordTrace]
  refine ⟨71325388106322218098864955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47550258737548145399243303 71325388106322218098864955)
  ·
    refine ⟨106988082159483327148297433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71325388106322218098864955 106988082159483327148297433)
    ·
      refine ⟨80241061619612495361223075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106988082159483327148297433 80241061619612495361223075)
      ·
        refine ⟨120361592429418743041834613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80241061619612495361223075 120361592429418743041834613)
        ·
          refine ⟨11283899290258007160171995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120361592429418743041834613 11283899290258007160171995)
          ·
            refine ⟨16925848935387010740257993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11283899290258007160171995 16925848935387010740257993)
            ·
              refine ⟨12694386701540258055193495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16925848935387010740257993 12694386701540258055193495)
              ·
                refine ⟨19041580052310387082790243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12694386701540258055193495 19041580052310387082790243)
                ·
                  refine ⟨28562370078465580624185365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19041580052310387082790243 28562370078465580624185365)
                  ·
                    refine ⟨1338861097428074091758689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28562370078465580624185365 1338861097428074091758689)
                    ·
                      refine ⟨1004145823071055568819017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338861097428074091758689 1004145823071055568819017)
                      ·
                        rfl

theorem cell23_1955567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 6, 2].length) (baseStart_1955567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955567 prefixEnd_1955567 := by exact prefixLift 1955567
  have htrace : WordTrace (prefixWord ++ tailWord_1955567) baseStart_1955567 baseEnd_1955567 := by
    simpa [prefixWord, tailWord_1955567, baseEnd_1955567] using wordTrace_append hprefix tailTrace_1955567
  have hstable : (prefixWord ++ tailWord_1955567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955567).length < 2 ^ (prefixWord ++ tailWord_1955567).sum := by decide
  have hdescent : baseEnd_1955567 < baseStart_1955567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955587 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 3]
def baseStart_1955587 : Nat := 118140960795 + 1955587 * 2 ^ 59
def prefixEnd_1955587 : Nat := 4983230072969 + 3 ^ 40 * 1955587 * 2
def baseEnd_1955587 : Nat := 1004156092684145490568925

theorem tailTrace_1955587 : CollatzResearch.WordTrace tailWord_1955587 prefixEnd_1955587 1004156092684145490568925 := by
  unfold tailWord_1955587
  simp only [CollatzResearch.WordTrace]
  refine ⟨71326117566249761514593015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47550745044166507676395343 71326117566249761514593015)
  ·
    refine ⟨106989176349374642271889523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71326117566249761514593015 106989176349374642271889523)
    ·
      refine ⟨160483764524061963407834285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106989176349374642271889523 160483764524061963407834285)
      ·
        refine ⟨60181411696523236277937857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160483764524061963407834285 60181411696523236277937857)
        ·
          refine ⟨45136058772392427208453393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60181411696523236277937857 45136058772392427208453393)
          ·
            refine ⟨33852044079294320406340045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45136058772392427208453393 33852044079294320406340045)
            ·
              refine ⟨12694516529735370152377517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33852044079294320406340045 12694516529735370152377517)
              ·
                refine ⟨4760443698650763807141569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12694516529735370152377517 4760443698650763807141569)
                ·
                  refine ⟨3570332773988072855356177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4760443698650763807141569 3570332773988072855356177)
                  ·
                    refine ⟨2677749580491054641517133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3570332773988072855356177 2677749580491054641517133)
                    ·
                      refine ⟨1004156092684145490568925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2677749580491054641517133 1004156092684145490568925)
                      ·
                        rfl

theorem cell23_1955587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_1955587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955587 prefixEnd_1955587 := by exact prefixLift 1955587
  have htrace : WordTrace (prefixWord ++ tailWord_1955587) baseStart_1955587 baseEnd_1955587 := by
    simpa [prefixWord, tailWord_1955587, baseEnd_1955587] using wordTrace_append hprefix tailTrace_1955587
  have hstable : (prefixWord ++ tailWord_1955587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955587).length < 2 ^ (prefixWord ++ tailWord_1955587).sum := by decide
  have hdescent : baseEnd_1955587 < baseStart_1955587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955607 : List Nat := [1, 1, 3, 4, 2, 1, 1, 4, 6]
def baseStart_1955607 : Nat := 118140960795 + 1955607 * 2 ^ 59
def prefixEnd_1955607 : Nat := 4983230072969 + 3 ^ 40 * 1955607 * 2
def baseEnd_1955607 : Nat := 111574040255248379146537

theorem tailTrace_1955607 : CollatzResearch.WordTrace tailWord_1955607 prefixEnd_1955607 111574040255248379146537 := by
  unfold tailWord_1955607
  simp only [CollatzResearch.WordTrace]
  refine ⟨71326847026177304930321075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47551231350784869953547383 71326847026177304930321075)
  ·
    refine ⟨106990270539265957395481613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71326847026177304930321075 106990270539265957395481613)
    ·
      refine ⟨40121351452224734023305605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106990270539265957395481613 40121351452224734023305605)
      ·
        refine ⟨7522753397292137629369801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40121351452224734023305605 7522753397292137629369801)
        ·
          refine ⟨5642065047969103222027351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7522753397292137629369801 5642065047969103222027351)
          ·
            refine ⟨8463097571953654833041027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642065047969103222027351 8463097571953654833041027)
            ·
              refine ⟨12694646357930482249561541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8463097571953654833041027 12694646357930482249561541)
              ·
                refine ⟨2380246192111965421792789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12694646357930482249561541 2380246192111965421792789)
                ·
                  refine ⟨111574040255248379146537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2380246192111965421792789 111574040255248379146537)
                  ·
                    rfl

theorem cell23_1955607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 4, 6].length) (baseStart_1955607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955607 prefixEnd_1955607 := by exact prefixLift 1955607
  have htrace : WordTrace (prefixWord ++ tailWord_1955607) baseStart_1955607 baseEnd_1955607 := by
    simpa [prefixWord, tailWord_1955607, baseEnd_1955607] using wordTrace_append hprefix tailTrace_1955607
  have hstable : (prefixWord ++ tailWord_1955607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955607).length < 2 ^ (prefixWord ++ tailWord_1955607).sum := by decide
  have hdescent : baseEnd_1955607 < baseStart_1955607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955634 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3]
def baseStart_1955634 : Nat := 118140960795 + 1955634 * 2 ^ 59
def prefixEnd_1955634 : Nat := 4983230072969 + 3 ^ 40 * 1955634 * 2
def baseEnd_1955634 : Nat := 1004180226274906806681209

theorem tailTrace_1955634 : CollatzResearch.WordTrace tailWord_1955634 prefixEnd_1955634 1004180226274906806681209 := by
  unfold tailWord_1955634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17831957949269872135388489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 47551887864719659027702637 17831957949269872135388489)
  ·
    refine ⟨13373968461952404101541367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17831957949269872135388489 13373968461952404101541367)
    ·
      refine ⟨20060952692928606152312051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13373968461952404101541367 20060952692928606152312051)
      ·
        refine ⟨30091429039392909228468077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20060952692928606152312051 30091429039392909228468077)
        ·
          refine ⟨11284285889772340960675529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30091429039392909228468077 11284285889772340960675529)
          ·
            refine ⟨8463214417329255720506647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11284285889772340960675529 8463214417329255720506647)
            ·
              refine ⟨12694821625993883580759971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8463214417329255720506647 12694821625993883580759971)
              ·
                refine ⟨19042232438990825371139957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12694821625993883580759971 19042232438990825371139957)
                ·
                  refine ⟨1785209291155389878544371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19042232438990825371139957 1785209291155389878544371)
                  ·
                    refine ⟨2677813936733084817816557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1785209291155389878544371 2677813936733084817816557)
                    ·
                      refine ⟨1004180226274906806681209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2677813936733084817816557 1004180226274906806681209)
                      ·
                        rfl

theorem cell23_1955634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_1955634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955634 prefixEnd_1955634 := by exact prefixLift 1955634
  have htrace : WordTrace (prefixWord ++ tailWord_1955634) baseStart_1955634 baseEnd_1955634 := by
    simpa [prefixWord, tailWord_1955634, baseEnd_1955634] using wordTrace_append hprefix tailTrace_1955634
  have hstable : (prefixWord ++ tailWord_1955634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955634).length < 2 ^ (prefixWord ++ tailWord_1955634).sum := by decide
  have hdescent : baseEnd_1955634 < baseStart_1955634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955638 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_1955638 : Nat := 118140960795 + 1955638 * 2 ^ 59
def prefixEnd_1955638 : Nat := 4983230072969 + 3 ^ 40 * 1955638 * 2
def baseEnd_1955638 : Nat := 1004182280197524791031191

theorem tailTrace_1955638 : CollatzResearch.WordTrace tailWord_1955638 prefixEnd_1955638 1004182280197524791031191 := by
  unfold tailWord_1955638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4457998605566562326543723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47551985126043331483133045 4457998605566562326543723)
  ·
    refine ⟨6686997908349843489815585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4457998605566562326543723 6686997908349843489815585)
    ·
      refine ⟨5015248431262382617361689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6686997908349843489815585 5015248431262382617361689)
      ·
        refine ⟨3761436323446786963021267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5015248431262382617361689 3761436323446786963021267)
        ·
          refine ⟨5642154485170180444531901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3761436323446786963021267 5642154485170180444531901)
          ·
            refine ⟨2115807931938817666699463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5642154485170180444531901 2115807931938817666699463)
            ·
              refine ⟨3173711897908226500049195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115807931938817666699463 3173711897908226500049195)
              ·
                refine ⟨4760567846862339750073793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3173711897908226500049195 4760567846862339750073793)
                ·
                  refine ⟨3570425885146754812555345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4760567846862339750073793 3570425885146754812555345)
                  ·
                    refine ⟨2677819413860066109416509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3570425885146754812555345 2677819413860066109416509)
                    ·
                      refine ⟨1004182280197524791031191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2677819413860066109416509 1004182280197524791031191)
                      ·
                        rfl

theorem cell23_1955638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_1955638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955638 prefixEnd_1955638 := by exact prefixLift 1955638
  have htrace : WordTrace (prefixWord ++ tailWord_1955638) baseStart_1955638 baseEnd_1955638 := by
    simpa [prefixWord, tailWord_1955638, baseEnd_1955638] using wordTrace_append hprefix tailTrace_1955638
  have hstable : (prefixWord ++ tailWord_1955638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955638).length < 2 ^ (prefixWord ++ tailWord_1955638).sum := by decide
  have hdescent : baseEnd_1955638 < baseStart_1955638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955651 : List Nat := [1, 1, 1, 3, 1, 5, 1, 5, 1, 1, 3]
def baseStart_1955651 : Nat := 118140960795 + 1955651 * 2 ^ 59
def prefixEnd_1955651 : Nat := 4983230072969 + 3 ^ 40 * 1955651 * 2
def baseEnd_1955651 : Nat := 1004188955446033240168631

theorem tailTrace_1955651 : CollatzResearch.WordTrace tailWord_1955651 prefixEnd_1955651 1004188955446033240168631 := by
  unfold tailWord_1955651
  simp only [CollatzResearch.WordTrace]
  refine ⟨71328451838017900444922807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47552301225345266963281871 71328451838017900444922807)
  ·
    refine ⟨106992677757026850667384211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71328451838017900444922807 106992677757026850667384211)
    ·
      refine ⟨160489016635540276001076317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106992677757026850667384211 160489016635540276001076317)
      ·
        refine ⟨60183381238327603500403619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160489016635540276001076317 60183381238327603500403619)
        ·
          refine ⟨90275071857491405250605429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60183381238327603500403619 90275071857491405250605429)
          ·
            refine ⟨8463287986639819242244259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90275071857491405250605429 8463287986639819242244259)
            ·
              refine ⟨12694931979959728863366389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8463287986639819242244259 12694931979959728863366389)
              ·
                refine ⟨1190149873121224580940599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12694931979959728863366389 1190149873121224580940599)
                ·
                  refine ⟨1785224809681836871410899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190149873121224580940599 1785224809681836871410899)
                  ·
                    refine ⟨2677837214522755307116349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1785224809681836871410899 2677837214522755307116349)
                    ·
                      refine ⟨1004188955446033240168631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2677837214522755307116349 1004188955446033240168631)
                      ·
                        rfl

theorem cell23_1955651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 1, 1, 3].length) (baseStart_1955651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955651 prefixEnd_1955651 := by exact prefixLift 1955651
  have htrace : WordTrace (prefixWord ++ tailWord_1955651) baseStart_1955651 baseEnd_1955651 := by
    simpa [prefixWord, tailWord_1955651, baseEnd_1955651] using wordTrace_append hprefix tailTrace_1955651
  have hstable : (prefixWord ++ tailWord_1955651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955651).length < 2 ^ (prefixWord ++ tailWord_1955651).sum := by decide
  have hdescent : baseEnd_1955651 < baseStart_1955651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955668 : List Nat := [2, 4, 1, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_1955668 : Nat := 118140960795 + 1955668 * 2 ^ 59
def prefixEnd_1955668 : Nat := 4983230072969 + 3 ^ 40 * 1955668 * 2
def baseEnd_1955668 : Nat := 1004197684617159673656053

theorem tailTrace_1955668 : CollatzResearch.WordTrace tailWord_1955668 prefixEnd_1955668 1004197684617159673656053 := by
  unfold tailWord_1955668
  simp only [CollatzResearch.WordTrace]
  refine ⟨35664535939478156174145829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47552714585970874898861105 35664535939478156174145829)
  ·
    refine ⟨6687100488652154282652343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35664535939478156174145829 6687100488652154282652343)
    ·
      refine ⟨10030650732978231423978515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6687100488652154282652343 10030650732978231423978515)
      ·
        refine ⟨15045976099467347135967773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10030650732978231423978515 15045976099467347135967773)
        ·
          refine ⟨5642241037300255175987915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15045976099467347135967773 5642241037300255175987915)
          ·
            refine ⟨8463361555950382763981873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642241037300255175987915 8463361555950382763981873)
            ·
              refine ⟨6347521166962787072986405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8463361555950382763981873 6347521166962787072986405)
              ·
                refine ⟨1190160218805522576184951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6347521166962787072986405 1190160218805522576184951)
                ·
                  refine ⟨1785240328208283864277427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190160218805522576184951 1785240328208283864277427)
                  ·
                    refine ⟨2677860492312425796416141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1785240328208283864277427 2677860492312425796416141)
                    ·
                      refine ⟨1004197684617159673656053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2677860492312425796416141 1004197684617159673656053)
                      ·
                        rfl

theorem cell23_1955668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_1955668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955668 prefixEnd_1955668 := by exact prefixLift 1955668
  have htrace : WordTrace (prefixWord ++ tailWord_1955668) baseStart_1955668 baseEnd_1955668 := by
    simpa [prefixWord, tailWord_1955668, baseEnd_1955668] using wordTrace_append hprefix tailTrace_1955668
  have hstable : (prefixWord ++ tailWord_1955668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955668).length < 2 ^ (prefixWord ++ tailWord_1955668).sum := by decide
  have hdescent : baseEnd_1955668 < baseStart_1955668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955687 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1955687 : Nat := 118140960795 + 1955687 * 2 ^ 59
def prefixEnd_1955687 : Nat := 4983230072969 + 3 ^ 40 * 1955687 * 2
def baseEnd_1955687 : Nat := 1004207440749595099318465

theorem tailTrace_1955687 : CollatzResearch.WordTrace tailWord_1955687 prefixEnd_1955687 1004207440749595099318465 := by
  unfold tailWord_1955687
  simp only [CollatzResearch.WordTrace]
  refine ⟨71329764865887478593233315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47553176577258319062155543 71329764865887478593233315)
  ·
    refine ⟨106994647298831217889849973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71329764865887478593233315 106994647298831217889849973)
    ·
      refine ⟨10030748184265426677173435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106994647298831217889849973 10030748184265426677173435)
      ·
        refine ⟨15046122276398140015760153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10030748184265426677173435 15046122276398140015760153)
        ·
          refine ⟨11284591707298605011820115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15046122276398140015760153 11284591707298605011820115)
          ·
            refine ⟨16926887560947907517730173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11284591707298605011820115 16926887560947907517730173)
            ·
              refine ⟨6347582835355465319148815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16926887560947907517730173 6347582835355465319148815)
              ·
                refine ⟨9521374253033197978723223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6347582835355465319148815 9521374253033197978723223)
                ·
                  refine ⟨14282061379549796968084835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9521374253033197978723223 14282061379549796968084835)
                  ·
                    refine ⟨21423092069324695452127253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14282061379549796968084835 21423092069324695452127253)
                    ·
                      refine ⟨1004207440749595099318465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21423092069324695452127253 1004207440749595099318465)
                      ·
                        rfl

theorem cell23_1955687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1955687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955687 prefixEnd_1955687 := by exact prefixLift 1955687
  have htrace : WordTrace (prefixWord ++ tailWord_1955687) baseStart_1955687 baseEnd_1955687 := by
    simpa [prefixWord, tailWord_1955687, baseEnd_1955687] using wordTrace_append hprefix tailTrace_1955687
  have hstable : (prefixWord ++ tailWord_1955687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955687).length < 2 ^ (prefixWord ++ tailWord_1955687).sum := by decide
  have hdescent : baseEnd_1955687 < baseStart_1955687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955702 : List Nat := [5, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_1955702 : Nat := 118140960795 + 1955702 * 2 ^ 59
def prefixEnd_1955702 : Nat := 4983230072969 + 3 ^ 40 * 1955702 * 2
def baseEnd_1955702 : Nat := 1004215142959412540630897

theorem tailTrace_1955702 : CollatzResearch.WordTrace tailWord_1955702 prefixEnd_1955702 1004215142959412540630897 := by
  unfold tailWord_1955702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4458144497552071009689335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47553541307222090770019573 4458144497552071009689335)
  ·
    refine ⟨6687216746328106514534003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4458144497552071009689335 6687216746328106514534003)
    ·
      refine ⟨10030825119492159771801005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6687216746328106514534003 10030825119492159771801005)
      ·
        refine ⟨3761559419809559914425377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10030825119492159771801005 3761559419809559914425377)
        ·
          refine ⟨2821169564857169935819033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3761559419809559914425377 2821169564857169935819033)
          ·
            refine ⟨2115877173642877451864275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821169564857169935819033 2115877173642877451864275)
            ·
              refine ⟨3173815760464316177796413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115877173642877451864275 3173815760464316177796413)
              ·
                refine ⟨1190180910174118566673655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3173815760464316177796413 1190180910174118566673655)
                ·
                  refine ⟨1785271365261177850010483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190180910174118566673655 1785271365261177850010483)
                  ·
                    refine ⟨2677907047891766775015725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1785271365261177850010483 2677907047891766775015725)
                    ·
                      refine ⟨1004215142959412540630897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2677907047891766775015725 1004215142959412540630897)
                      ·
                        rfl

theorem cell23_1955702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_1955702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955702 prefixEnd_1955702 := by exact prefixLift 1955702
  have htrace : WordTrace (prefixWord ++ tailWord_1955702) baseStart_1955702 baseEnd_1955702 := by
    simpa [prefixWord, tailWord_1955702, baseEnd_1955702] using wordTrace_append hprefix tailTrace_1955702
  have hstable : (prefixWord ++ tailWord_1955702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955702).length < 2 ^ (prefixWord ++ tailWord_1955702).sum := by decide
  have hdescent : baseEnd_1955702 < baseStart_1955702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955707 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 3]
def baseStart_1955707 : Nat := 118140960795 + 1955707 * 2 ^ 59
def prefixEnd_1955707 : Nat := 4983230072969 + 3 ^ 40 * 1955707 * 2
def baseEnd_1955707 : Nat := 1004217710362685021068373

theorem tailTrace_1955707 : CollatzResearch.WordTrace tailWord_1955707 prefixEnd_1955707 1004217710362685021068373 := by
  unfold tailWord_1955707
  simp only [CollatzResearch.WordTrace]
  refine ⟨71330494325815022008961375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47553662883876681339307583 71330494325815022008961375)
  ·
    refine ⟨106995741488722533013442063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71330494325815022008961375 106995741488722533013442063)
    ·
      refine ⟨160493612233083799520163095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106995741488722533013442063 160493612233083799520163095)
      ·
        refine ⟨240740418349625699280244643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160493612233083799520163095 240740418349625699280244643)
        ·
          refine ⟨361110627524438548920366965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240740418349625699280244643 361110627524438548920366965)
          ·
            refine ⟨33854121330416113961284403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 361110627524438548920366965 33854121330416113961284403)
            ·
              refine ⟨50781181995624170941926605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33854121330416113961284403 50781181995624170941926605)
              ·
                refine ⟨19042943248359064103222477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50781181995624170941926605 19042943248359064103222477)
                ·
                  refine ⟨7141103718134649038708429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19042943248359064103222477 7141103718134649038708429)
                  ·
                    refine ⟨2677913894300493389515661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7141103718134649038708429 2677913894300493389515661)
                    ·
                      refine ⟨1004217710362685021068373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2677913894300493389515661 1004217710362685021068373)
                      ·
                        rfl

theorem cell23_1955707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 3, 3].length) (baseStart_1955707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955707 prefixEnd_1955707 := by exact prefixLift 1955707
  have htrace : WordTrace (prefixWord ++ tailWord_1955707) baseStart_1955707 baseEnd_1955707 := by
    simpa [prefixWord, tailWord_1955707, baseEnd_1955707] using wordTrace_append hprefix tailTrace_1955707
  have hstable : (prefixWord ++ tailWord_1955707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955707).length < 2 ^ (prefixWord ++ tailWord_1955707).sum := by decide
  have hdescent : baseEnd_1955707 < baseStart_1955707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955742 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1955742 : Nat := 118140960795 + 1955742 * 2 ^ 59
def prefixEnd_1955742 : Nat := 4983230072969 + 3 ^ 40 * 1955742 * 2
def baseEnd_1955742 : Nat := 1004235682185592384130713

theorem tailTrace_1955742 : CollatzResearch.WordTrace tailWord_1955742 prefixEnd_1955742 1004235682185592384130713 := by
  unfold tailWord_1955742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8916471360086027873310685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47554513920458815324323653 8916471360086027873310685)
  ·
    refine ⟨3343676760032260452491507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8916471360086027873310685 3343676760032260452491507)
    ·
      refine ⟨5015515140048390678737261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3343676760032260452491507 5015515140048390678737261)
      ·
        refine ⟨1880818177518146504526473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5015515140048390678737261 1880818177518146504526473)
        ·
          refine ⟨1410613633138609878394855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1880818177518146504526473 1410613633138609878394855)
          ·
            refine ⟨2115920449707914817592283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410613633138609878394855 2115920449707914817592283)
            ·
              refine ⟨3173880674561872226388425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115920449707914817592283 3173880674561872226388425)
              ·
                refine ⟨2380410505921404169791319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3173880674561872226388425 2380410505921404169791319)
                ·
                  refine ⟨3570615758882106254686979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380410505921404169791319 3570615758882106254686979)
                  ·
                    refine ⟨5355923638323159382030469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3570615758882106254686979 5355923638323159382030469)
                    ·
                      refine ⟨1004235682185592384130713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5355923638323159382030469 1004235682185592384130713)
                      ·
                        rfl

theorem cell23_1955742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1955742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955742 prefixEnd_1955742 := by exact prefixLift 1955742
  have htrace : WordTrace (prefixWord ++ tailWord_1955742) baseStart_1955742 baseEnd_1955742 := by
    simpa [prefixWord, tailWord_1955742, baseEnd_1955742] using wordTrace_append hprefix tailTrace_1955742
  have hstable : (prefixWord ++ tailWord_1955742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955742).length < 2 ^ (prefixWord ++ tailWord_1955742).sum := by decide
  have hdescent : baseEnd_1955742 < baseStart_1955742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955745 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1955745 : Nat := 118140960795 + 1955745 * 2 ^ 59
def prefixEnd_1955745 : Nat := 4983230072969 + 3 ^ 40 * 1955745 * 2
def baseEnd_1955745 : Nat := 1004237222627555872393199

theorem tailTrace_1955745 : CollatzResearch.WordTrace tailWord_1955745 prefixEnd_1955745 1004237222627555872393199 := by
  unfold tailWord_1955745
  simp only [CollatzResearch.WordTrace]
  refine ⟨71331880299677354498844689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47554586866451569665896459 71331880299677354498844689)
  ·
    refine ⟨53498910224758015874133517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71331880299677354498844689 53498910224758015874133517)
    ·
      refine ⟨20062091334284255952800069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53498910224758015874133517 20062091334284255952800069)
      ·
        refine ⟨3761642125178297991150013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20062091334284255952800069 3761642125178297991150013)
        ·
          refine ⟨1410615796941861746681255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3761642125178297991150013 1410615796941861746681255)
          ·
            refine ⟨2115923695412792620021883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410615796941861746681255 2115923695412792620021883)
            ·
              refine ⟨3173885543119188930032825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2115923695412792620021883 3173885543119188930032825)
              ·
                refine ⟨2380414157339391697524619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3173885543119188930032825 2380414157339391697524619)
                ·
                  refine ⟨3570621236009087546286929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380414157339391697524619 3570621236009087546286929)
                  ·
                    refine ⟨2677965927006815659715197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3570621236009087546286929 2677965927006815659715197)
                    ·
                      refine ⟨1004237222627555872393199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2677965927006815659715197 1004237222627555872393199)
                      ·
                        rfl

theorem cell23_1955745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1955745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955745 prefixEnd_1955745 := by exact prefixLift 1955745
  have htrace : WordTrace (prefixWord ++ tailWord_1955745) baseStart_1955745 baseEnd_1955745 := by
    simpa [prefixWord, tailWord_1955745, baseEnd_1955745] using wordTrace_append hprefix tailTrace_1955745
  have hstable : (prefixWord ++ tailWord_1955745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955745).length < 2 ^ (prefixWord ++ tailWord_1955745).sum := by decide
  have hdescent : baseEnd_1955745 < baseStart_1955745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955768 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 1, 3, 2]
def baseStart_1955768 : Nat := 118140960795 + 1955768 * 2 ^ 59
def prefixEnd_1955768 : Nat := 4983230072969 + 3 ^ 40 * 1955768 * 2
def baseEnd_1955768 : Nat := 1004249032682609282405593

theorem tailTrace_1955768 : CollatzResearch.WordTrace tailWord_1955768 prefixEnd_1955768 1004249032682609282405593 := by
  unfold tailWord_1955768
  simp only [CollatzResearch.WordTrace]
  refine ⟨35666359589297014713465979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47555146119062686284621305 35666359589297014713465979)
  ·
    refine ⟨53499539383945522070198969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35666359589297014713465979 53499539383945522070198969)
    ·
      refine ⟨40124654537959141552649227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53499539383945522070198969 40124654537959141552649227)
      ·
        refine ⟨60186981806938712328973841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40124654537959141552649227 60186981806938712328973841)
        ·
          refine ⟨45140236355204034246730381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60186981806938712328973841 45140236355204034246730381)
          ·
            refine ⟨16927588633201512842523893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45140236355204034246730381 16927588633201512842523893)
            ·
              refine ⟨1586961434362641828986615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16927588633201512842523893 1586961434362641828986615)
              ·
                refine ⟨2380442151543962743479923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1586961434362641828986615 2380442151543962743479923)
                ·
                  refine ⟨3570663227315944115219885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380442151543962743479923 3570663227315944115219885)
                  ·
                    refine ⟨1338998710243479043207457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3570663227315944115219885 1338998710243479043207457)
                    ·
                      refine ⟨1004249032682609282405593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1338998710243479043207457 1004249032682609282405593)
                      ·
                        rfl

theorem cell23_1955768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_1955768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955768 prefixEnd_1955768 := by exact prefixLift 1955768
  have htrace : WordTrace (prefixWord ++ tailWord_1955768) baseStart_1955768 baseEnd_1955768 := by
    simpa [prefixWord, tailWord_1955768, baseEnd_1955768] using wordTrace_append hprefix tailTrace_1955768
  have hstable : (prefixWord ++ tailWord_1955768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955768).length < 2 ^ (prefixWord ++ tailWord_1955768).sum := by decide
  have hdescent : baseEnd_1955768 < baseStart_1955768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955784 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_1955784 : Nat := 118140960795 + 1955784 * 2 ^ 59
def prefixEnd_1955784 : Nat := 4983230072969 + 3 ^ 40 * 1955784 * 2
def baseEnd_1955784 : Nat := 1004257248373081219805519

theorem tailTrace_1955784 : CollatzResearch.WordTrace tailWord_1955784 prefixEnd_1955784 1004257248373081219805519 := by
  unfold tailWord_1955784
  simp only [CollatzResearch.WordTrace]
  refine ⟨35666651373268032079757203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47555535164357376106342937 35666651373268032079757203)
  ·
    refine ⟨53499977059902048119635805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35666651373268032079757203 53499977059902048119635805)
    ·
      refine ⟨20062491397463268044863427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53499977059902048119635805 20062491397463268044863427)
      ·
        refine ⟨30093737096194902067295141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20062491397463268044863427 30093737096194902067295141)
        ·
          refine ⟨5642575705536544137617839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30093737096194902067295141 5642575705536544137617839)
          ·
            refine ⟨8463863558304816206426759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642575705536544137617839 8463863558304816206426759)
            ·
              refine ⟨12695795337457224309640139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8463863558304816206426759 12695795337457224309640139)
              ·
                refine ⟨19043693006185836464460209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12695795337457224309640139 19043693006185836464460209)
                ·
                  refine ⟨14282769754639377348345157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19043693006185836464460209 14282769754639377348345157)
                  ·
                    refine ⟨2678019328994883252814717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14282769754639377348345157 2678019328994883252814717)
                    ·
                      refine ⟨1004257248373081219805519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2678019328994883252814717 1004257248373081219805519)
                      ·
                        rfl

theorem cell23_1955784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_1955784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955784 prefixEnd_1955784 := by exact prefixLift 1955784
  have htrace : WordTrace (prefixWord ++ tailWord_1955784) baseStart_1955784 baseEnd_1955784 := by
    simpa [prefixWord, tailWord_1955784, baseEnd_1955784] using wordTrace_append hprefix tailTrace_1955784
  have hstable : (prefixWord ++ tailWord_1955784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955784).length < 2 ^ (prefixWord ++ tailWord_1955784).sum := by decide
  have hdescent : baseEnd_1955784 < baseStart_1955784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955787 : List Nat := [1, 1, 1, 1, 3, 4, 2, 3, 7]
def baseStart_1955787 : Nat := 118140960795 + 1955787 * 2 ^ 59
def prefixEnd_1955787 : Nat := 4983230072969 + 3 ^ 40 * 1955787 * 2
def baseEnd_1955787 : Nat := 111584309868338300896445

theorem tailTrace_1955787 : CollatzResearch.WordTrace tailWord_1955787 prefixEnd_1955787 111584309868338300896445 := by
  unfold tailWord_1955787
  simp only [CollatzResearch.WordTrace]
  refine ⟨71333412165525195671873615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47555608110350130447915743 71333412165525195671873615)
  ·
    refine ⟨107000118248287793507810423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71333412165525195671873615 107000118248287793507810423)
    ·
      refine ⟨160500177372431690261715635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107000118248287793507810423 160500177372431690261715635)
      ·
        refine ⟨240750266058647535392573453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160500177372431690261715635 240750266058647535392573453)
        ·
          refine ⟨90281349771992825772215045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240750266058647535392573453 90281349771992825772215045)
          ·
            refine ⟨16927753082248654832290321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90281349771992825772215045 16927753082248654832290321)
            ·
              refine ⟨12695814811686491124217741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16927753082248654832290321 12695814811686491124217741)
              ·
                refine ⟨4760930554382434171581653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12695814811686491124217741 4760930554382434171581653)
                ·
                  refine ⟨111584309868338300896445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4760930554382434171581653 111584309868338300896445)
                  ·
                    rfl

theorem cell23_1955787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 3, 7].length) (baseStart_1955787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955787 prefixEnd_1955787 := by exact prefixLift 1955787
  have htrace : WordTrace (prefixWord ++ tailWord_1955787) baseStart_1955787 baseEnd_1955787 := by
    simpa [prefixWord, tailWord_1955787, baseEnd_1955787] using wordTrace_append hprefix tailTrace_1955787
  have hstable : (prefixWord ++ tailWord_1955787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955787).length < 2 ^ (prefixWord ++ tailWord_1955787).sum := by decide
  have hdescent : baseEnd_1955787 < baseStart_1955787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955827 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 5]
def baseStart_1955827 : Nat := 118140960795 + 1955827 * 2 ^ 59
def prefixEnd_1955827 : Nat := 4983230072969 + 3 ^ 40 * 1955827 * 2
def baseEnd_1955827 : Nat := 1004279328041224551567821

theorem tailTrace_1955827 : CollatzResearch.WordTrace tailWord_1955827 prefixEnd_1955827 1004279328041224551567821 := by
  unfold tailWord_1955827
  simp only [CollatzResearch.WordTrace]
  refine ⟨71334871085380282503329735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47556580723586855002219823 71334871085380282503329735)
  ·
    refine ⟨107002306628070423754994603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71334871085380282503329735 107002306628070423754994603)
    ·
      refine ⟨160503459942105635632491905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107002306628070423754994603 160503459942105635632491905)
      ·
        refine ⟨120377594956579226724368929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160503459942105635632491905 120377594956579226724368929)
        ·
          refine ⟨90283196217434420043276697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120377594956579226724368929 90283196217434420043276697)
          ·
            refine ⟨67712397163075815032457523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90283196217434420043276697 67712397163075815032457523)
            ·
              refine ⟨101568595744613722548686285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67712397163075815032457523 101568595744613722548686285)
              ·
                refine ⟨38088223404230145955757357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101568595744613722548686285 38088223404230145955757357)
                ·
                  refine ⟨14283083776586304733409009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38088223404230145955757357 14283083776586304733409009)
                  ·
                    refine ⟨10712312832439728550056757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14283083776586304733409009 10712312832439728550056757)
                    ·
                      refine ⟨1004279328041224551567821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10712312832439728550056757 1004279328041224551567821)
                      ·
                        rfl

theorem cell23_1955827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_1955827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955827 prefixEnd_1955827 := by exact prefixLift 1955827
  have htrace : WordTrace (prefixWord ++ tailWord_1955827) baseStart_1955827 baseEnd_1955827 := by
    simpa [prefixWord, tailWord_1955827, baseEnd_1955827] using wordTrace_append hprefix tailTrace_1955827
  have hstable : (prefixWord ++ tailWord_1955827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955827).length < 2 ^ (prefixWord ++ tailWord_1955827).sum := by decide
  have hdescent : baseEnd_1955827 < baseStart_1955827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955838 : List Nat := [4, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_1955838 : Nat := 118140960795 + 1955838 * 2 ^ 59
def prefixEnd_1955838 : Nat := 4983230072969 + 3 ^ 40 * 1955838 * 2
def baseEnd_1955838 : Nat := 111587219592047112058919

theorem tailTrace_1955838 : CollatzResearch.WordTrace tailWord_1955838 prefixEnd_1955838 111587219592047112058919 := by
  unfold tailWord_1955838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8916909036042553922747521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47556848192226954254653445 8916909036042553922747521)
  ·
    refine ⟨6687681777031915442060641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8916909036042553922747521 6687681777031915442060641)
    ·
      refine ⟨5015761332773936581545481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6687681777031915442060641 5015761332773936581545481)
      ·
        refine ⟨3761820999580452436159111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5015761332773936581545481 3761820999580452436159111)
        ·
          refine ⟨5642731499370678654238667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3761820999580452436159111 5642731499370678654238667)
          ·
            refine ⟨8464097249056017981358001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642731499370678654238667 8464097249056017981358001)
            ·
              refine ⟨6348072936792013486018501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8464097249056017981358001 6348072936792013486018501)
              ·
                refine ⟨1190263675648502528628469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6348072936792013486018501 1190263675648502528628469)
                ·
                  refine ⟨111587219592047112058919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1190263675648502528628469 111587219592047112058919)
                  ·
                    rfl

theorem cell23_1955838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_1955838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955838 prefixEnd_1955838 := by exact prefixLift 1955838
  have htrace : WordTrace (prefixWord ++ tailWord_1955838) baseStart_1955838 baseEnd_1955838 := by
    simpa [prefixWord, tailWord_1955838, baseEnd_1955838] using wordTrace_append hprefix tailTrace_1955838
  have hstable : (prefixWord ++ tailWord_1955838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955838).length < 2 ^ (prefixWord ++ tailWord_1955838).sum := by decide
  have hdescent : baseEnd_1955838 < baseStart_1955838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955854 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1955854 : Nat := 118140960795 + 1955854 * 2 ^ 59
def prefixEnd_1955854 : Nat := 4983230072969 + 3 ^ 40 * 1955854 * 2
def baseEnd_1955854 : Nat := 1004293192018895945930197

theorem tailTrace_1955854 : CollatzResearch.WordTrace tailWord_1955854 prefixEnd_1955854 1004293192018895945930197 := by
  unfold tailWord_1955854
  simp only [CollatzResearch.WordTrace]
  refine ⟨8916981982035308264320327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47557237237521644076375077 8916981982035308264320327)
  ·
    refine ⟨13375472973052962396480491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8916981982035308264320327 13375472973052962396480491)
    ·
      refine ⟨20063209459579443594720737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13375472973052962396480491 20063209459579443594720737)
      ·
        refine ⟨15047407094684582696040553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20063209459579443594720737 15047407094684582696040553)
        ·
          refine ⟨11285555321013437022030415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15047407094684582696040553 11285555321013437022030415)
          ·
            refine ⟨16928332981520155533045623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11285555321013437022030415 16928332981520155533045623)
            ·
              refine ⟨25392499472280233299568435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16928332981520155533045623 25392499472280233299568435)
              ·
                refine ⟨38088749208420349949352653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25392499472280233299568435 38088749208420349949352653)
                ·
                  refine ⟨14283280953157631231007245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38088749208420349949352653 14283280953157631231007245)
                  ·
                    refine ⟨5356230357434111711627717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14283280953157631231007245 5356230357434111711627717)
                    ·
                      refine ⟨1004293192018895945930197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5356230357434111711627717 1004293192018895945930197)
                      ·
                        rfl

theorem cell23_1955854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1955854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955854 prefixEnd_1955854 := by exact prefixLift 1955854
  have htrace : WordTrace (prefixWord ++ tailWord_1955854) baseStart_1955854 baseEnd_1955854 := by
    simpa [prefixWord, tailWord_1955854, baseEnd_1955854] using wordTrace_append hprefix tailTrace_1955854
  have hstable : (prefixWord ++ tailWord_1955854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955854).length < 2 ^ (prefixWord ++ tailWord_1955854).sum := by decide
  have hdescent : baseEnd_1955854 < baseStart_1955854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955867 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 6]
def baseStart_1955867 : Nat := 118140960795 + 1955867 * 2 ^ 59
def prefixEnd_1955867 : Nat := 4983230072969 + 3 ^ 40 * 1955867 * 2
def baseEnd_1955867 : Nat := 1004299867267404395067637

theorem tailTrace_1955867 : CollatzResearch.WordTrace tailWord_1955867 prefixEnd_1955867 1004299867267404395067637 := by
  unfold tailWord_1955867
  simp only [CollatzResearch.WordTrace]
  refine ⟨71336330005235369334785855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47557553336823579556523903 71336330005235369334785855)
  ·
    refine ⟨107004495007853054002178783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71336330005235369334785855 107004495007853054002178783)
    ·
      refine ⟨160506742511779581003268175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107004495007853054002178783 160506742511779581003268175)
      ·
        refine ⟨240760113767669371504902263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160506742511779581003268175 240760113767669371504902263)
        ·
          refine ⟨361140170651504057257353395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240760113767669371504902263 361140170651504057257353395)
          ·
            refine ⟨541710255977256085886030093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361140170651504057257353395 541710255977256085886030093)
            ·
              refine ⟨203141345991471032207261285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541710255977256085886030093 203141345991471032207261285)
              ·
                refine ⟨38089002373400818538861491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203141345991471032207261285 38089002373400818538861491)
                ·
                  refine ⟨57133503560101227808292237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38089002373400818538861491 57133503560101227808292237)
                  ·
                    refine ⟨21425063835037960428109589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57133503560101227808292237 21425063835037960428109589)
                    ·
                      refine ⟨1004299867267404395067637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21425063835037960428109589 1004299867267404395067637)
                      ·
                        rfl

theorem cell23_1955867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_1955867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955867 prefixEnd_1955867 := by exact prefixLift 1955867
  have htrace : WordTrace (prefixWord ++ tailWord_1955867) baseStart_1955867 baseEnd_1955867 := by
    simpa [prefixWord, tailWord_1955867, baseEnd_1955867] using wordTrace_append hprefix tailTrace_1955867
  have hstable : (prefixWord ++ tailWord_1955867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955867).length < 2 ^ (prefixWord ++ tailWord_1955867).sum := by decide
  have hdescent : baseEnd_1955867 < baseStart_1955867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955921 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 5, 1, 3]
def baseStart_1955921 : Nat := 118140960795 + 1955921 * 2 ^ 59
def prefixEnd_1955921 : Nat := 4983230072969 + 3 ^ 40 * 1955921 * 2
def baseEnd_1955921 : Nat := 1004327595222747183792389

theorem tailTrace_1955921 : CollatzResearch.WordTrace tailWord_1955921 prefixEnd_1955921 1004327595222747183792389 := by
  unfold tailWord_1955921
  simp only [CollatzResearch.WordTrace]
  refine ⟨71338299547039736557251617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47558866364693157704834411 71338299547039736557251617)
  ·
    refine ⟨53503724660279802417938713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71338299547039736557251617 53503724660279802417938713)
    ·
      refine ⟨40127793495209851813454035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53503724660279802417938713 40127793495209851813454035)
      ·
        refine ⟨60191690242814777720181053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40127793495209851813454035 60191690242814777720181053)
        ·
          refine ⟨22571883841055541645067895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60191690242814777720181053 22571883841055541645067895)
          ·
            refine ⟨33857825761583312467601843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22571883841055541645067895 33857825761583312467601843)
            ·
              refine ⟨50786738642374968701402765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33857825761583312467601843 50786738642374968701402765)
              ·
                refine ⟨19045026990890613263026037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50786738642374968701402765 19045026990890613263026037)
                ·
                  refine ⟨1785471280395994993408691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19045026990890613263026037 1785471280395994993408691)
                  ·
                    refine ⟨2678206920593992490113037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1785471280395994993408691 2678206920593992490113037)
                    ·
                      refine ⟨1004327595222747183792389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2678206920593992490113037 1004327595222747183792389)
                      ·
                        rfl

theorem cell23_1955921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_1955921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955921 prefixEnd_1955921 := by exact prefixLift 1955921
  have htrace : WordTrace (prefixWord ++ tailWord_1955921) baseStart_1955921 baseEnd_1955921 := by
    simpa [prefixWord, tailWord_1955921, baseEnd_1955921] using wordTrace_append hprefix tailTrace_1955921
  have hstable : (prefixWord ++ tailWord_1955921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955921).length < 2 ^ (prefixWord ++ tailWord_1955921).sum := by decide
  have hdescent : baseEnd_1955921 < baseStart_1955921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955948 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 2, 3, 2]
def baseStart_1955948 : Nat := 118140960795 + 1955948 * 2 ^ 59
def prefixEnd_1955948 : Nat := 4983230072969 + 3 ^ 40 * 1955948 * 2
def baseEnd_1955948 : Nat := 1004341459200418578154765

theorem tailTrace_1955948 : CollatzResearch.WordTrace tailWord_1955948 prefixEnd_1955948 1004341459200418578154765 := by
  unfold tailWord_1955948
  simp only [CollatzResearch.WordTrace]
  refine ⟨35669642158970960084242249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47559522878627946778989665 35669642158970960084242249)
  ·
    refine ⟨26752231619228220063181687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35669642158970960084242249 26752231619228220063181687)
    ·
      refine ⟨40128347428842330094772531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26752231619228220063181687 40128347428842330094772531)
      ·
        refine ⟨60192521143263495142158797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40128347428842330094772531 60192521143263495142158797)
        ·
          refine ⟨22572195428723810678309549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60192521143263495142158797 22572195428723810678309549)
          ·
            refine ⟨8464573285771429004366081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22572195428723810678309549 8464573285771429004366081)
            ·
              refine ⟨6348429964328571753274561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8464573285771429004366081 6348429964328571753274561)
              ·
                refine ⟨4761322473246428814955921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6348429964328571753274561 4761322473246428814955921)
                ·
                  refine ⟨3570991854934821611216941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4761322473246428814955921 3570991854934821611216941)
                  ·
                    refine ⟨1339121945600558104206353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3570991854934821611216941 1339121945600558104206353)
                    ·
                      refine ⟨1004341459200418578154765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1339121945600558104206353 1004341459200418578154765)
                      ·
                        rfl

theorem cell23_1955948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_1955948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955948 prefixEnd_1955948 := by exact prefixLift 1955948
  have htrace : WordTrace (prefixWord ++ tailWord_1955948) baseStart_1955948 baseEnd_1955948 := by
    simpa [prefixWord, tailWord_1955948, baseEnd_1955948] using wordTrace_append hprefix tailTrace_1955948
  have hstable : (prefixWord ++ tailWord_1955948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955948).length < 2 ^ (prefixWord ++ tailWord_1955948).sum := by decide
  have hdescent : baseEnd_1955948 < baseStart_1955948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955961 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1955961 : Nat := 118140960795 + 1955961 * 2 ^ 59
def prefixEnd_1955961 : Nat := 4983230072969 + 3 ^ 40 * 1955961 * 2
def baseEnd_1955961 : Nat := 1004348134448927027292205

theorem tailTrace_1955961 : CollatzResearch.WordTrace tailWord_1955961 prefixEnd_1955961 1004348134448927027292205 := by
  unfold tailWord_1955961
  simp only [CollatzResearch.WordTrace]
  refine ⟨71339758466894823388707737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47559838977929882259138491 71339758466894823388707737)
  ·
    refine ⟨53504818850171117541530803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71339758466894823388707737 53504818850171117541530803)
    ·
      refine ⟨80257228275256676312296205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53504818850171117541530803 80257228275256676312296205)
      ·
        refine ⟨30096460603221253617111077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80257228275256676312296205 30096460603221253617111077)
        ·
          refine ⟨5643086363103985053208327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30096460603221253617111077 5643086363103985053208327)
          ·
            refine ⟨8464629544655977579812491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5643086363103985053208327 8464629544655977579812491)
            ·
              refine ⟨12696944316983966369718737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464629544655977579812491 12696944316983966369718737)
              ·
                refine ⟨9522708237737974777289053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12696944316983966369718737 9522708237737974777289053)
                ·
                  refine ⟨3571015589151740541483395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9522708237737974777289053 3571015589151740541483395)
                  ·
                    refine ⟨5356523383727610812225093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3571015589151740541483395 5356523383727610812225093)
                    ·
                      refine ⟨1004348134448927027292205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5356523383727610812225093 1004348134448927027292205)
                      ·
                        rfl

theorem cell23_1955961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1955961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955961 prefixEnd_1955961 := by exact prefixLift 1955961
  have htrace : WordTrace (prefixWord ++ tailWord_1955961) baseStart_1955961 baseEnd_1955961 := by
    simpa [prefixWord, tailWord_1955961, baseEnd_1955961] using wordTrace_append hprefix tailTrace_1955961
  have hstable : (prefixWord ++ tailWord_1955961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955961).length < 2 ^ (prefixWord ++ tailWord_1955961).sum := by decide
  have hdescent : baseEnd_1955961 < baseStart_1955961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955971 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 1, 6]
def baseStart_1955971 : Nat := 118140960795 + 1955971 * 2 ^ 59
def prefixEnd_1955971 : Nat := 4983230072969 + 3 ^ 40 * 1955971 * 2
def baseEnd_1955971 : Nat := 334784423085157329389053

theorem tailTrace_1955971 : CollatzResearch.WordTrace tailWord_1955971 prefixEnd_1955971 334784423085157329389053 := by
  unfold tailWord_1955971
  simp only [CollatzResearch.WordTrace]
  refine ⟨71340123196858595096571767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47560082131239063397714511 71340123196858595096571767)
  ·
    refine ⟨107010184795287892644857651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71340123196858595096571767 107010184795287892644857651)
    ·
      refine ⟨160515277192931838967286477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107010184795287892644857651 160515277192931838967286477)
      ·
        refine ⟨60193228947349439612732429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160515277192931838967286477 60193228947349439612732429)
        ·
          refine ⟨22572460855256039854774661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60193228947349439612732429 22572460855256039854774661)
          ·
            refine ⟨4232336410360507472770249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22572460855256039854774661 4232336410360507472770249)
            ·
              refine ⟨3174252307770380604577687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4232336410360507472770249 3174252307770380604577687)
              ·
                refine ⟨4761378461655570906866531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174252307770380604577687 4761378461655570906866531)
                ·
                  refine ⟨7142067692483356360299797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761378461655570906866531 7142067692483356360299797)
                  ·
                    refine ⟨334784423085157329389053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7142067692483356360299797 334784423085157329389053)
                    ·
                      rfl

theorem cell23_1955971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 6].length) (baseStart_1955971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955971 prefixEnd_1955971 := by exact prefixLift 1955971
  have htrace : WordTrace (prefixWord ++ tailWord_1955971) baseStart_1955971 baseEnd_1955971 := by
    simpa [prefixWord, tailWord_1955971, baseEnd_1955971] using wordTrace_append hprefix tailTrace_1955971
  have hstable : (prefixWord ++ tailWord_1955971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955971).length < 2 ^ (prefixWord ++ tailWord_1955971).sum := by decide
  have hdescent : baseEnd_1955971 < baseStart_1955971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955982 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2]
def baseStart_1955982 : Nat := 118140960795 + 1955982 * 2 ^ 59
def prefixEnd_1955982 : Nat := 4983230072969 + 3 ^ 40 * 1955982 * 2
def baseEnd_1955982 : Nat := 1004358917542671445129609

theorem tailTrace_1955982 : CollatzResearch.WordTrace tailWord_1955982 prefixEnd_1955982 1004358917542671445129609 := by
  unfold tailWord_1955982
  simp only [CollatzResearch.WordTrace]
  refine ⟨8917565549977342996902775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47560349599879162650148133 8917565549977342996902775)
  ·
    refine ⟨13376348324966014495354163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8917565549977342996902775 13376348324966014495354163)
    ·
      refine ⟨20064522487449021743031245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13376348324966014495354163 20064522487449021743031245)
      ·
        refine ⟨7524195932793383153636717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20064522487449021743031245 7524195932793383153636717)
        ·
          refine ⟨2821573474797518682613769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7524195932793383153636717 2821573474797518682613769)
          ·
            refine ⟨2116180106098139011960327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2821573474797518682613769 2116180106098139011960327)
            ·
              refine ⟨3174270159147208517940491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116180106098139011960327 3174270159147208517940491)
              ·
                refine ⟨4761405238720812776910737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174270159147208517940491 4761405238720812776910737)
                ·
                  refine ⟨3571053929040609582683053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4761405238720812776910737 3571053929040609582683053)
                  ·
                    refine ⟨1339145223390228593506145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571053929040609582683053 1339145223390228593506145)
                    ·
                      refine ⟨1004358917542671445129609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1339145223390228593506145 1004358917542671445129609)
                      ·
                        rfl

theorem cell23_1955982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_1955982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955982 prefixEnd_1955982 := by exact prefixLift 1955982
  have htrace : WordTrace (prefixWord ++ tailWord_1955982) baseStart_1955982 baseEnd_1955982 := by
    simpa [prefixWord, tailWord_1955982, baseEnd_1955982] using wordTrace_append hprefix tailTrace_1955982
  have hstable : (prefixWord ++ tailWord_1955982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955982).length < 2 ^ (prefixWord ++ tailWord_1955982).sum := by decide
  have hdescent : baseEnd_1955982 < baseStart_1955982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1955992 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 1, 5]
def baseStart_1955992 : Nat := 118140960795 + 1955992 * 2 ^ 59
def prefixEnd_1955992 : Nat := 4983230072969 + 3 ^ 40 * 1955992 * 2
def baseEnd_1955992 : Nat := 334788017449738802001521

theorem tailTrace_1955992 : CollatzResearch.WordTrace tailWord_1955992 prefixEnd_1955992 334788017449738802001521 := by
  unfold tailWord_1955992
  simp only [CollatzResearch.WordTrace]
  refine ⟨35670444564891257841543115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47560592753188343788724153 35670444564891257841543115)
  ·
    refine ⟨53505666847336886762314673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35670444564891257841543115 53505666847336886762314673)
    ·
      refine ⟨40129250135502665071736005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53505666847336886762314673 40129250135502665071736005)
      ·
        refine ⟨7524234400406749700950501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40129250135502665071736005 7524234400406749700950501)
        ·
          refine ⟨1410793950076265568928219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7524234400406749700950501 1410793950076265568928219)
          ·
            refine ⟨2116190925114398353392329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1410793950076265568928219 2116190925114398353392329)
            ·
              refine ⟨1587143193835798765044247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116190925114398353392329 1587143193835798765044247)
              ·
                refine ⟨2380714790753698147566371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587143193835798765044247 2380714790753698147566371)
                ·
                  refine ⟨3571072186130547221349557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380714790753698147566371 3571072186130547221349557)
                  ·
                    refine ⟨334788017449738802001521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3571072186130547221349557 334788017449738802001521)
                    ·
                      rfl

theorem cell23_1955992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_1955992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1955992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1955992 prefixEnd_1955992 := by exact prefixLift 1955992
  have htrace : WordTrace (prefixWord ++ tailWord_1955992) baseStart_1955992 baseEnd_1955992 := by
    simpa [prefixWord, tailWord_1955992, baseEnd_1955992] using wordTrace_append hprefix tailTrace_1955992
  have hstable : (prefixWord ++ tailWord_1955992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1955992).length < 2 ^ (prefixWord ++ tailWord_1955992).sum := by decide
  have hdescent : baseEnd_1955992 < baseStart_1955992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1955992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956081 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_1956081 : Nat := 118140960795 + 1956081 * 2 ^ 59
def prefixEnd_1956081 : Nat := 4983230072969 + 3 ^ 40 * 1956081 * 2
def baseEnd_1956081 : Nat := 1004409752127466557791653

theorem tailTrace_1956081 : CollatzResearch.WordTrace tailWord_1956081 prefixEnd_1956081 1004409752127466557791653 := by
  unfold tailWord_1956081
  simp only [CollatzResearch.WordTrace]
  refine ⟨71344135226460083883076097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47562756817640055922050731 71344135226460083883076097)
  ·
    refine ⟨53508101419845062912307073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71344135226460083883076097 53508101419845062912307073)
    ·
      refine ⟨40131076064883797184230305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53508101419845062912307073 40131076064883797184230305)
      ·
        refine ⟨30098307048662847888172729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40131076064883797184230305 30098307048662847888172729)
        ·
          refine ⟨22573730286497135916129547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30098307048662847888172729 22573730286497135916129547)
          ·
            refine ⟨33860595429745703874194321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22573730286497135916129547 33860595429745703874194321)
            ·
              refine ⟨25395446572309277905645741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33860595429745703874194321 25395446572309277905645741)
              ·
                refine ⟨9523292464615979214617153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25395446572309277905645741 9523292464615979214617153)
                ·
                  refine ⟨7142469348461984410962865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9523292464615979214617153 7142469348461984410962865)
                  ·
                    refine ⟨5356852011346488308222149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7142469348461984410962865 5356852011346488308222149)
                    ·
                      refine ⟨1004409752127466557791653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5356852011346488308222149 1004409752127466557791653)
                      ·
                        rfl

theorem cell23_1956081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_1956081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956081 prefixEnd_1956081 := by exact prefixLift 1956081
  have htrace : WordTrace (prefixWord ++ tailWord_1956081) baseStart_1956081 baseEnd_1956081 := by
    simpa [prefixWord, tailWord_1956081, baseEnd_1956081] using wordTrace_append hprefix tailTrace_1956081
  have hstable : (prefixWord ++ tailWord_1956081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956081).length < 2 ^ (prefixWord ++ tailWord_1956081).sum := by decide
  have hdescent : baseEnd_1956081 < baseStart_1956081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956101 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 3, 5, 3]
def baseStart_1956101 : Nat := 118140960795 + 1956101 * 2 ^ 59
def prefixEnd_1956101 : Nat := 4983230072969 + 3 ^ 40 * 1956101 * 2
def baseEnd_1956101 : Nat := 1004420021740556479541561

theorem tailTrace_1956101 : CollatzResearch.WordTrace tailWord_1956101 prefixEnd_1956101 1004420021740556479541561 := by
  unfold tailWord_1956101
  simp only [CollatzResearch.WordTrace]
  refine ⟨71344864686387627298804157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47563243124258418199202771 71344864686387627298804157)
  ·
    refine ⟨26754324257395360237051559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71344864686387627298804157 26754324257395360237051559)
    ·
      refine ⟨40131486386093040355577339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26754324257395360237051559 40131486386093040355577339)
      ·
        refine ⟨60197229579139560533366009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40131486386093040355577339 60197229579139560533366009)
        ·
          refine ⟨45147922184354670400024507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60197229579139560533366009 45147922184354670400024507)
          ·
            refine ⟨67721883276532005600036761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45147922184354670400024507 67721883276532005600036761)
            ·
              refine ⟨50791412457399004200027571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67721883276532005600036761 50791412457399004200027571)
              ·
                refine ⟨76187118686098506300041357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50791412457399004200027571 76187118686098506300041357)
                ·
                  refine ⟨28570169507286939862515509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76187118686098506300041357 28570169507286939862515509)
                  ·
                    refine ⟨2678453391308150612110829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28570169507286939862515509 2678453391308150612110829)
                    ·
                      refine ⟨1004420021740556479541561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2678453391308150612110829 1004420021740556479541561)
                      ·
                        rfl

theorem cell23_1956101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_1956101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956101 prefixEnd_1956101 := by exact prefixLift 1956101
  have htrace : WordTrace (prefixWord ++ tailWord_1956101) baseStart_1956101 baseEnd_1956101 := by
    simpa [prefixWord, tailWord_1956101, baseEnd_1956101] using wordTrace_append hprefix tailTrace_1956101
  have hstable : (prefixWord ++ tailWord_1956101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956101).length < 2 ^ (prefixWord ++ tailWord_1956101).sum := by decide
  have hdescent : baseEnd_1956101 < baseStart_1956101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956108 : List Nat := [2, 2, 1, 2, 2, 2, 2, 5, 5]
def baseStart_1956108 : Nat := 118140960795 + 1956108 * 2 ^ 59
def prefixEnd_1956108 : Nat := 4983230072969 + 3 ^ 40 * 1956108 * 2
def baseEnd_1956108 : Nat := 111602624011681994683781

theorem tailTrace_1956108 : CollatzResearch.WordTrace tailWord_1956108 prefixEnd_1956108 111602624011681994683781 := by
  unfold tailWord_1956108
  simp only [CollatzResearch.WordTrace]
  refine ⟨35672559998681133747154489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47563413331574844996205985 35672559998681133747154489)
  ·
    refine ⟨26754419999010850310365867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35672559998681133747154489 26754419999010850310365867)
    ·
      refine ⟨40131629998516275465548801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26754419999010850310365867 40131629998516275465548801)
      ·
        refine ⟨30098722498887206599161601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40131629998516275465548801 30098722498887206599161601)
        ·
          refine ⟨22574041874165404949371201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30098722498887206599161601 22574041874165404949371201)
          ·
            refine ⟨16930531405624053712028401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22574041874165404949371201 16930531405624053712028401)
            ·
              refine ⟨12697898554218040284021301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16930531405624053712028401 12697898554218040284021301)
              ·
                refine ⟨1190427989457941276626997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12697898554218040284021301 1190427989457941276626997)
                ·
                  refine ⟨111602624011681994683781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1190427989457941276626997 111602624011681994683781)
                  ·
                    rfl

theorem cell23_1956108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_1956108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956108 prefixEnd_1956108 := by exact prefixLift 1956108
  have htrace : WordTrace (prefixWord ++ tailWord_1956108) baseStart_1956108 baseEnd_1956108 := by
    simpa [prefixWord, tailWord_1956108, baseEnd_1956108] using wordTrace_append hprefix tailTrace_1956108
  have hstable : (prefixWord ++ tailWord_1956108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956108).length < 2 ^ (prefixWord ++ tailWord_1956108).sum := by decide
  have hdescent : baseEnd_1956108 < baseStart_1956108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956131 : List Nat := [1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 5]
def baseStart_1956131 : Nat := 118140960795 + 1956131 * 2 ^ 59
def prefixEnd_1956131 : Nat := 4983230072969 + 3 ^ 40 * 1956131 * 2
def baseEnd_1956131 : Nat := 1004435426160191362166423

theorem tailTrace_1956131 : CollatzResearch.WordTrace tailWord_1956131 prefixEnd_1956131 1004435426160191362166423 := by
  unfold tailWord_1956131
  simp only [CollatzResearch.WordTrace]
  refine ⟨71345958876278942422396247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47563972584185961614930831 71345958876278942422396247)
  ·
    refine ⟨107018938314418413633594371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71345958876278942422396247 107018938314418413633594371)
    ·
      refine ⟨160528407471627620450391557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107018938314418413633594371 160528407471627620450391557)
      ·
        refine ⟨30099076400930178834448417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160528407471627620450391557 30099076400930178834448417)
        ·
          refine ⟨22574307300697634125836313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30099076400930178834448417 22574307300697634125836313)
          ·
            refine ⟨16930730475523225594377235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22574307300697634125836313 16930730475523225594377235)
            ·
              refine ⟨25396095713284838391565853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16930730475523225594377235 25396095713284838391565853)
              ·
                refine ⟨9523535892481814396837195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25396095713284838391565853 9523535892481814396837195)
                ·
                  refine ⟨14285303838722721595255793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9523535892481814396837195 14285303838722721595255793)
                  ·
                    refine ⟨10713977879042041196441845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14285303838722721595255793 10713977879042041196441845)
                    ·
                      refine ⟨1004435426160191362166423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10713977879042041196441845 1004435426160191362166423)
                      ·
                        rfl

theorem cell23_1956131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_1956131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956131 prefixEnd_1956131 := by exact prefixLift 1956131
  have htrace : WordTrace (prefixWord ++ tailWord_1956131) baseStart_1956131 baseEnd_1956131 := by
    simpa [prefixWord, tailWord_1956131, baseEnd_1956131] using wordTrace_append hprefix tailTrace_1956131
  have hstable : (prefixWord ++ tailWord_1956131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956131).length < 2 ^ (prefixWord ++ tailWord_1956131).sum := by decide
  have hdescent : baseEnd_1956131 < baseStart_1956131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956201 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_1956201 : Nat := 118140960795 + 1956201 * 2 ^ 59
def prefixEnd_1956201 : Nat := 4983230072969 + 3 ^ 40 * 1956201 * 2
def baseEnd_1956201 : Nat := 1004471369806006088291101

theorem tailTrace_1956201 : CollatzResearch.WordTrace tailWord_1956201 prefixEnd_1956201 1004471369806006088291101 := by
  unfold tailWord_1956201
  simp only [CollatzResearch.WordTrace]
  refine ⟨71348511986025344377444457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47565674657350229584962971 71348511986025344377444457)
  ·
    refine ⟨53511383989519008283083343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71348511986025344377444457 53511383989519008283083343)
    ·
      refine ⟨80267075984278512424625015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53511383989519008283083343 80267075984278512424625015)
      ·
        refine ⟨120400613976417768636937523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80267075984278512424625015 120400613976417768636937523)
        ·
          refine ⟨180600920964626652955406285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120400613976417768636937523 180600920964626652955406285)
          ·
            refine ⟨67725345361734994858277357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180600920964626652955406285 67725345361734994858277357)
            ·
              refine ⟨25397004510650623071854009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67725345361734994858277357 25397004510650623071854009)
              ·
                refine ⟨19047753382987967303890507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25397004510650623071854009 19047753382987967303890507)
                ·
                  refine ⟨28571630074481950955835761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19047753382987967303890507 28571630074481950955835761)
                  ·
                    refine ⟨21428722555861463216876821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28571630074481950955835761 21428722555861463216876821)
                    ·
                      refine ⟨1004471369806006088291101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21428722555861463216876821 1004471369806006088291101)
                      ·
                        rfl

theorem cell23_1956201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_1956201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956201 prefixEnd_1956201 := by exact prefixLift 1956201
  have htrace : WordTrace (prefixWord ++ tailWord_1956201) baseStart_1956201 baseEnd_1956201 := by
    simpa [prefixWord, tailWord_1956201, baseEnd_1956201] using wordTrace_append hprefix tailTrace_1956201
  have hstable : (prefixWord ++ tailWord_1956201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956201).length < 2 ^ (prefixWord ++ tailWord_1956201).sum := by decide
  have hdescent : baseEnd_1956201 < baseStart_1956201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956235 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 4, 3, 2]
def baseStart_1956235 : Nat := 118140960795 + 1956235 * 2 ^ 59
def prefixEnd_1956235 : Nat := 4983230072969 + 3 ^ 40 * 1956235 * 2
def baseEnd_1956235 : Nat := 1004488828148258955265945

theorem tailTrace_1956235 : CollatzResearch.WordTrace tailWord_1956235 prefixEnd_1956235 1004488828148258955265945 := by
  unfold tailWord_1956235
  simp only [CollatzResearch.WordTrace]
  refine ⟨71349752067902168184182159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47566501378601445456121439 71349752067902168184182159)
  ·
    refine ⟨107024628101853252276273239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71349752067902168184182159 107024628101853252276273239)
    ·
      refine ⟨160536942152779878414409859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107024628101853252276273239 160536942152779878414409859)
      ·
        refine ⟨240805413229169817621614789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160536942152779878414409859 240805413229169817621614789)
        ·
          refine ⟨45151014980469340804052773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240805413229169817621614789 45151014980469340804052773)
          ·
            refine ⟨8465815308838001400759895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45151014980469340804052773 8465815308838001400759895)
            ·
              refine ⟨12698722963257002101139843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8465815308838001400759895 12698722963257002101139843)
              ·
                refine ⟨19048084444885503151709765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12698722963257002101139843 19048084444885503151709765)
                ·
                  refine ⟨3571515833416031840945581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19048084444885503151709765 3571515833416031840945581)
                  ·
                    refine ⟨1339318437531011940354593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3571515833416031840945581 1339318437531011940354593)
                    ·
                      refine ⟨1004488828148258955265945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1339318437531011940354593 1004488828148258955265945)
                      ·
                        rfl

theorem cell23_1956235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 3, 2].length) (baseStart_1956235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956235 prefixEnd_1956235 := by exact prefixLift 1956235
  have htrace : WordTrace (prefixWord ++ tailWord_1956235) baseStart_1956235 baseEnd_1956235 := by
    simpa [prefixWord, tailWord_1956235, baseEnd_1956235] using wordTrace_append hprefix tailTrace_1956235
  have hstable : (prefixWord ++ tailWord_1956235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956235).length < 2 ^ (prefixWord ++ tailWord_1956235).sum := by decide
  have hdescent : baseEnd_1956235 < baseStart_1956235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956241 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 2, 10]
def baseStart_1956241 : Nat := 118140960795 + 1956241 * 2 ^ 59
def prefixEnd_1956241 : Nat := 4983230072969 + 3 ^ 40 * 1956241 * 2
def baseEnd_1956241 : Nat := 334830636344061977263639

theorem tailTrace_1956241 : CollatzResearch.WordTrace tailWord_1956241 prefixEnd_1956241 334830636344061977263639 := by
  unfold tailWord_1956241
  simp only [CollatzResearch.WordTrace]
  refine ⟨71349970905880431208900577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47566647270586954139267051 71349970905880431208900577)
  ·
    refine ⟨53512478179410323406675433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71349970905880431208900577 53512478179410323406675433)
    ·
      refine ⟨40134358634557742555006575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53512478179410323406675433 40134358634557742555006575)
      ·
        refine ⟨60201537951836613832509863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40134358634557742555006575 60201537951836613832509863)
        ·
          refine ⟨90302306927754920748764795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60201537951836613832509863 90302306927754920748764795)
          ·
            refine ⟨135453460391632381123147193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90302306927754920748764795 135453460391632381123147193)
            ·
              refine ⟨101590095293724285842360395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135453460391632381123147193 101590095293724285842360395)
              ·
                refine ⟨152385142940586428763540593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101590095293724285842360395 152385142940586428763540593)
                ·
                  refine ⟨114288857205439821572655445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152385142940586428763540593 114288857205439821572655445)
                  ·
                    refine ⟨334830636344061977263639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 114288857205439821572655445 334830636344061977263639)
                    ·
                      rfl

theorem cell23_1956241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_1956241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956241 prefixEnd_1956241 := by exact prefixLift 1956241
  have htrace : WordTrace (prefixWord ++ tailWord_1956241) baseStart_1956241 baseEnd_1956241 := by
    simpa [prefixWord, tailWord_1956241, baseEnd_1956241] using wordTrace_append hprefix tailTrace_1956241
  have hstable : (prefixWord ++ tailWord_1956241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956241).length < 2 ^ (prefixWord ++ tailWord_1956241).sum := by decide
  have hdescent : baseEnd_1956241 < baseStart_1956241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956285 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_1956285 : Nat := 118140960795 + 1956285 * 2 ^ 59
def prefixEnd_1956285 : Nat := 4983230072969 + 3 ^ 40 * 1956285 * 2
def baseEnd_1956285 : Nat := 1004514502180983759640715

theorem tailTrace_1956285 : CollatzResearch.WordTrace tailWord_1956285 prefixEnd_1956285 1004514502180983759640715 := by
  unfold tailWord_1956285
  simp only [CollatzResearch.WordTrace]
  refine ⟨71351575717721026723502309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47567717145147351149001539 71351575717721026723502309)
  ·
    refine ⟨13378420447072692510656683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71351575717721026723502309 13378420447072692510656683)
    ·
      refine ⟨20067630670609038765985025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13378420447072692510656683 20067630670609038765985025)
      ·
        refine ⟨15050723002956779074488769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20067630670609038765985025 15050723002956779074488769)
        ·
          refine ⟨11288042252217584305866577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15050723002956779074488769 11288042252217584305866577)
          ·
            refine ⟨8466031689163188229399933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11288042252217584305866577 8466031689163188229399933)
            ·
              refine ⟨3174761883436195586024975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8466031689163188229399933 3174761883436195586024975)
              ·
                refine ⟨4762142825154293379037463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174761883436195586024975 4762142825154293379037463)
                ·
                  refine ⟨7143214237731440068556195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762142825154293379037463 7143214237731440068556195)
                  ·
                    refine ⟨10714821356597160102834293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7143214237731440068556195 10714821356597160102834293)
                    ·
                      refine ⟨1004514502180983759640715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10714821356597160102834293 1004514502180983759640715)
                      ·
                        rfl

theorem cell23_1956285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_1956285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956285 prefixEnd_1956285 := by exact prefixLift 1956285
  have htrace : WordTrace (prefixWord ++ tailWord_1956285) baseStart_1956285 baseEnd_1956285 := by
    simpa [prefixWord, tailWord_1956285, baseEnd_1956285] using wordTrace_append hprefix tailTrace_1956285
  have hstable : (prefixWord ++ tailWord_1956285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956285).length < 2 ^ (prefixWord ++ tailWord_1956285).sum := by decide
  have hdescent : baseEnd_1956285 < baseStart_1956285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956333 : List Nat := [1, 5, 1, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_1956333 : Nat := 118140960795 + 1956333 * 2 ^ 59
def prefixEnd_1956333 : Nat := 4983230072969 + 3 ^ 40 * 1956333 * 2
def baseEnd_1956333 : Nat := 1004539149252399571840495

theorem tailTrace_1956333 : CollatzResearch.WordTrace tailWord_1956333 prefixEnd_1956333 1004539149252399571840495 := by
  unfold tailWord_1956333
  simp only [CollatzResearch.WordTrace]
  refine ⟨71353326421547130921249653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47568884281031420614166435 71353326421547130921249653)
  ·
    refine ⟨6689374352020043523867155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71353326421547130921249653 6689374352020043523867155)
    ·
      refine ⟨10034061528030065285800733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6689374352020043523867155 10034061528030065285800733)
      ·
        refine ⟨3762773073011274482175275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10034061528030065285800733 3762773073011274482175275)
        ·
          refine ⟨5644159609516911723262913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3762773073011274482175275 5644159609516911723262913)
          ·
            refine ⟨4233119707137683792447185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5644159609516911723262913 4233119707137683792447185)
            ·
              refine ⟨3174839780353262844335389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4233119707137683792447185 3174839780353262844335389)
              ·
                refine ⟨1190564917632473566625771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3174839780353262844335389 1190564917632473566625771)
                ·
                  refine ⟨1785847376448710349938657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1190564917632473566625771 1785847376448710349938657)
                  ·
                    refine ⟨1339385532336532762453993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1785847376448710349938657 1339385532336532762453993)
                    ·
                      refine ⟨1004539149252399571840495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1339385532336532762453993 1004539149252399571840495)
                      ·
                        rfl

theorem cell23_1956333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_1956333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956333 prefixEnd_1956333 := by exact prefixLift 1956333
  have htrace : WordTrace (prefixWord ++ tailWord_1956333) baseStart_1956333 baseEnd_1956333 := by
    simpa [prefixWord, tailWord_1956333, baseEnd_1956333] using wordTrace_append hprefix tailTrace_1956333
  have hstable : (prefixWord ++ tailWord_1956333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956333).length < 2 ^ (prefixWord ++ tailWord_1956333).sum := by decide
  have hdescent : baseEnd_1956333 < baseStart_1956333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956366 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3]
def baseStart_1956366 : Nat := 118140960795 + 1956366 * 2 ^ 59
def prefixEnd_1956366 : Nat := 4983230072969 + 3 ^ 40 * 1956366 * 2
def baseEnd_1956366 : Nat := 1004556094113997942727843

theorem tailTrace_1956366 : CollatzResearch.WordTrace tailWord_1956366 prefixEnd_1956366 1004556094113997942727843 := by
  unfold tailWord_1956366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8919316253803447194650119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 47569686686951718371467301 8919316253803447194650119)
  ·
    refine ⟨13378974380705170791975179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8919316253803447194650119 13378974380705170791975179)
    ·
      refine ⟨20068461571057756187962769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13378974380705170791975179 20068461571057756187962769)
      ·
        refine ⟨15051346178293317140972077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20068461571057756187962769 15051346178293317140972077)
        ·
          refine ⟨5644254816859993927864529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15051346178293317140972077 5644254816859993927864529)
          ·
            refine ⟨4233191112644995445898397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5644254816859993927864529 4233191112644995445898397)
            ·
              refine ⟨1587446667241873292211899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4233191112644995445898397 1587446667241873292211899)
              ·
                refine ⟨2381170000862809938317849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587446667241873292211899 2381170000862809938317849)
                ·
                  refine ⟨1785877500647107453738387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2381170000862809938317849 1785877500647107453738387)
                  ·
                    refine ⟨2678816250970661180607581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1785877500647107453738387 2678816250970661180607581)
                    ·
                      refine ⟨1004556094113997942727843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2678816250970661180607581 1004556094113997942727843)
                      ·
                        rfl

theorem cell23_1956366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_1956366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956366 prefixEnd_1956366 := by exact prefixLift 1956366
  have htrace : WordTrace (prefixWord ++ tailWord_1956366) baseStart_1956366 baseEnd_1956366 := by
    simpa [prefixWord, tailWord_1956366, baseEnd_1956366] using wordTrace_append hprefix tailTrace_1956366
  have hstable : (prefixWord ++ tailWord_1956366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956366).length < 2 ^ (prefixWord ++ tailWord_1956366).sum := by decide
  have hdescent : baseEnd_1956366 < baseStart_1956366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956368 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_1956368 : Nat := 118140960795 + 1956368 * 2 ^ 59
def prefixEnd_1956368 : Nat := 4983230072969 + 3 ^ 40 * 1956368 * 2
def baseEnd_1956368 : Nat := 1004557121075306934902833

theorem tailTrace_1956368 : CollatzResearch.WordTrace tailWord_1956368 prefixEnd_1956368 1004557121075306934902833 := by
  unfold tailWord_1956368
  simp only [CollatzResearch.WordTrace]
  refine ⟨35677301488210165949386879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47569735317613554599182505 35677301488210165949386879)
  ·
    refine ⟨53515952232315248924080319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35677301488210165949386879 53515952232315248924080319)
    ·
      refine ⟨80273928348472873386120479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53515952232315248924080319 80273928348472873386120479)
      ·
        refine ⟨120410892522709310079180719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80273928348472873386120479 120410892522709310079180719)
        ·
          refine ⟨180616338784063965118771079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120410892522709310079180719 180616338784063965118771079)
          ·
            refine ⟨270924508176095947678156619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180616338784063965118771079 270924508176095947678156619)
            ·
              refine ⟨406386762264143921517234929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270924508176095947678156619 406386762264143921517234929)
              ·
                refine ⟨304790071698107941137926197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406386762264143921517234929 304790071698107941137926197)
                ·
                  refine ⟨28574069221697619481680581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304790071698107941137926197 28574069221697619481680581)
                  ·
                    refine ⟨5357637979068303652815109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28574069221697619481680581 5357637979068303652815109)
                    ·
                      refine ⟨1004557121075306934902833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5357637979068303652815109 1004557121075306934902833)
                      ·
                        rfl

theorem cell23_1956368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_1956368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956368 prefixEnd_1956368 := by exact prefixLift 1956368
  have htrace : WordTrace (prefixWord ++ tailWord_1956368) baseStart_1956368 baseEnd_1956368 := by
    simpa [prefixWord, tailWord_1956368, baseEnd_1956368] using wordTrace_append hprefix tailTrace_1956368
  have hstable : (prefixWord ++ tailWord_1956368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956368).length < 2 ^ (prefixWord ++ tailWord_1956368).sum := by decide
  have hdescent : baseEnd_1956368 < baseStart_1956368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956392 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1956392 : Nat := 118140960795 + 1956392 * 2 ^ 59
def prefixEnd_1956392 : Nat := 4983230072969 + 3 ^ 40 * 1956392 * 2
def baseEnd_1956392 : Nat := 1004569444611014841002723

theorem tailTrace_1956392 : CollatzResearch.WordTrace tailWord_1956392 prefixEnd_1956392 1004569444611014841002723 := by
  unfold tailWord_1956392
  simp only [CollatzResearch.WordTrace]
  refine ⟨35677739164166691998823715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47570318885555589331764953 35677739164166691998823715)
  ·
    refine ⟨53516608746250037998235573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35677739164166691998823715 53516608746250037998235573)
    ·
      refine ⟨5017182069960941062334585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53516608746250037998235573 5017182069960941062334585)
      ·
        refine ⟨3762886552470705796750939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5017182069960941062334585 3762886552470705796750939)
        ·
          refine ⟨5644329828706058695126409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3762886552470705796750939 5644329828706058695126409)
          ·
            refine ⟨4233247371529544021344807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5644329828706058695126409 4233247371529544021344807)
            ·
              refine ⟨6349871057294316032017211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233247371529544021344807 6349871057294316032017211)
              ·
                refine ⟨9524806585941474048025817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6349871057294316032017211 9524806585941474048025817)
                ·
                  refine ⟨7143604939456105536019363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9524806585941474048025817 7143604939456105536019363)
                  ·
                    refine ⟨10715407409184158304029045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7143604939456105536019363 10715407409184158304029045)
                    ·
                      refine ⟨1004569444611014841002723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10715407409184158304029045 1004569444611014841002723)
                      ·
                        rfl

theorem cell23_1956392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1956392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956392 prefixEnd_1956392 := by exact prefixLift 1956392
  have htrace : WordTrace (prefixWord ++ tailWord_1956392) baseStart_1956392 baseEnd_1956392 := by
    simpa [prefixWord, tailWord_1956392, baseEnd_1956392] using wordTrace_append hprefix tailTrace_1956392
  have hstable : (prefixWord ++ tailWord_1956392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956392).length < 2 ^ (prefixWord ++ tailWord_1956392).sum := by decide
  have hdescent : baseEnd_1956392 < baseStart_1956392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956406 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_1956406 : Nat := 118140960795 + 1956406 * 2 ^ 59
def prefixEnd_1956406 : Nat := 4983230072969 + 3 ^ 40 * 1956406 * 2
def baseEnd_1956406 : Nat := 1004576633340177786227659

theorem tailTrace_1956406 : CollatzResearch.WordTrace tailWord_1956406 prefixEnd_1956406 1004576633340177786227659 := by
  unfold tailWord_1956406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4459749309392666524291067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 47570659300188442925771381 4459749309392666524291067)
  ·
    refine ⟨6689623964088999786436601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4459749309392666524291067 6689623964088999786436601)
    ·
      refine ⟨5017217973066749839827451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6689623964088999786436601 5017217973066749839827451)
      ·
        refine ⟨7525826959600124759741177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5017217973066749839827451 7525826959600124759741177)
        ·
          refine ⟨5644370219700093569805883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7525826959600124759741177 5644370219700093569805883)
          ·
            refine ⟨8466555329550140354708825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5644370219700093569805883 8466555329550140354708825)
            ·
              refine ⟨6349916497162605266031619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8466555329550140354708825 6349916497162605266031619)
              ·
                refine ⟨9524874745743907899047429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6349916497162605266031619 9524874745743907899047429)
                ·
                  refine ⟨1785914014826982731071393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9524874745743907899047429 1785914014826982731071393)
                  ·
                    refine ⟨1339435511120237048303545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1785914014826982731071393 1339435511120237048303545)
                    ·
                      refine ⟨1004576633340177786227659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1339435511120237048303545 1004576633340177786227659)
                      ·
                        rfl

theorem cell23_1956406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_1956406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956406 prefixEnd_1956406 := by exact prefixLift 1956406
  have htrace : WordTrace (prefixWord ++ tailWord_1956406) baseStart_1956406 baseEnd_1956406 := by
    simpa [prefixWord, tailWord_1956406, baseEnd_1956406] using wordTrace_append hprefix tailTrace_1956406
  have hstable : (prefixWord ++ tailWord_1956406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956406).length < 2 ^ (prefixWord ++ tailWord_1956406).sum := by decide
  have hdescent : baseEnd_1956406 < baseStart_1956406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956412 : List Nat := [2, 2, 2, 2, 3, 3, 1, 1, 7]
def baseStart_1956412 : Nat := 118140960795 + 1956412 * 2 ^ 59
def prefixEnd_1956412 : Nat := 4983230072969 + 3 ^ 40 * 1956412 * 2
def baseEnd_1956412 : Nat := 111619968247122751416959

theorem tailTrace_1956412 : CollatzResearch.WordTrace tailWord_1956412 prefixEnd_1956412 111619968247122751416959 := by
  unfold tailWord_1956412
  simp only [CollatzResearch.WordTrace]
  refine ⟨35678103894130463706687745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 47570805192173951608916993 35678103894130463706687745)
  ·
    refine ⟨26758577920597847780015809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35678103894130463706687745 26758577920597847780015809)
    ·
      refine ⟨20068933440448385835011857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26758577920597847780015809 20068933440448385835011857)
      ·
        refine ⟨15051700080336289376258893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20068933440448385835011857 15051700080336289376258893)
        ·
          refine ⟨5644387530126108516097085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15051700080336289376258893 5644387530126108516097085)
          ·
            refine ⟨2116645323797290693536407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5644387530126108516097085 2116645323797290693536407)
            ·
              refine ⟨3174967985695936040304611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2116645323797290693536407 3174967985695936040304611)
              ·
                refine ⟨4762451978543904060456917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174967985695936040304611 4762451978543904060456917)
                ·
                  refine ⟨111619968247122751416959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4762451978543904060456917 111619968247122751416959)
                  ·
                    rfl

theorem cell23_1956412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_1956412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956412 prefixEnd_1956412 := by exact prefixLift 1956412
  have htrace : WordTrace (prefixWord ++ tailWord_1956412) baseStart_1956412 baseEnd_1956412 := by
    simpa [prefixWord, tailWord_1956412, baseEnd_1956412] using wordTrace_append hprefix tailTrace_1956412
  have hstable : (prefixWord ++ tailWord_1956412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956412).length < 2 ^ (prefixWord ++ tailWord_1956412).sum := by decide
  have hdescent : baseEnd_1956412 < baseStart_1956412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956423 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 2, 2, 2]
def baseStart_1956423 : Nat := 118140960795 + 1956423 * 2 ^ 59
def prefixEnd_1956423 : Nat := 4983230072969 + 3 ^ 40 * 1956423 * 2
def baseEnd_1956423 : Nat := 1004585362511304219715081

theorem tailTrace_1956423 : CollatzResearch.WordTrace tailWord_1956423 prefixEnd_1956423 1004585362511304219715081 := by
  unfold tailWord_1956423
  simp only [CollatzResearch.WordTrace]
  refine ⟨71356608991221076292025923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47571072660814050861350615 71356608991221076292025923)
  ·
    refine ⟨107034913486831614438038885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71356608991221076292025923 107034913486831614438038885)
    ·
      refine ⟨20069046278780927707132291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107034913486831614438038885 20069046278780927707132291)
      ·
        refine ⟨30103569418171391560698437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20069046278780927707132291 30103569418171391560698437)
        ·
          refine ⟨5644419265907135917630957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30103569418171391560698437 5644419265907135917630957)
          ·
            refine ⟨2116657224715175969111609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5644419265907135917630957 2116657224715175969111609)
            ·
              refine ⟨1587492918536381976833707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2116657224715175969111609 1587492918536381976833707)
              ·
                refine ⟨2381239377804572965250561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1587492918536381976833707 2381239377804572965250561)
                ·
                  refine ⟨1785929533353429723937921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2381239377804572965250561 1785929533353429723937921)
                  ·
                    refine ⟨1339447150015072292953441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1785929533353429723937921 1339447150015072292953441)
                    ·
                      refine ⟨1004585362511304219715081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1339447150015072292953441 1004585362511304219715081)
                      ·
                        rfl

theorem cell23_1956423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_1956423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956423 prefixEnd_1956423 := by exact prefixLift 1956423
  have htrace : WordTrace (prefixWord ++ tailWord_1956423) baseStart_1956423 baseEnd_1956423 := by
    simpa [prefixWord, tailWord_1956423, baseEnd_1956423] using wordTrace_append hprefix tailTrace_1956423
  have hstable : (prefixWord ++ tailWord_1956423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956423).length < 2 ^ (prefixWord ++ tailWord_1956423).sum := by decide
  have hdescent : baseEnd_1956423 < baseStart_1956423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1956465 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 5, 4, 3]
def baseStart_1956465 : Nat := 118140960795 + 1956465 * 2 ^ 59
def prefixEnd_1956465 : Nat := 4983230072969 + 3 ^ 40 * 1956465 * 2
def baseEnd_1956465 : Nat := 1004606928698793055389887

theorem tailTrace_1956465 : CollatzResearch.WordTrace tailWord_1956465 prefixEnd_1956465 1004606928698793055389887 := by
  unfold tailWord_1956465
  simp only [CollatzResearch.WordTrace]
  refine ⟨71358140857068917465054849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 47572093904712611643369899 71358140857068917465054849)
  ·
    refine ⟨53518605642801688098791137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71358140857068917465054849 53518605642801688098791137)
    ·
      refine ⟨40138954232101266074093353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53518605642801688098791137 40138954232101266074093353)
      ·
        refine ⟨30104215674075949555570015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40138954232101266074093353 30104215674075949555570015)
        ·
          refine ⟨45156323511113924333355023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30104215674075949555570015 45156323511113924333355023)
          ·
            refine ⟨67734485266670886500032535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45156323511113924333355023 67734485266670886500032535)
            ·
              refine ⟨101601727900006329750048803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67734485266670886500032535 101601727900006329750048803)
              ·
                refine ⟨152402591850009494625073205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101601727900006329750048803 152402591850009494625073205)
                ·
                  refine ⟨14287742985938390121100613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152402591850009494625073205 14287742985938390121100613)
                  ·
                    refine ⟨2678951809863448147706365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14287742985938390121100613 2678951809863448147706365)
                    ·
                      refine ⟨1004606928698793055389887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2678951809863448147706365 1004606928698793055389887)
                      ·
                        rfl

theorem cell23_1956465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_1956465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1956465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1956465 prefixEnd_1956465 := by exact prefixLift 1956465
  have htrace : WordTrace (prefixWord ++ tailWord_1956465) baseStart_1956465 baseEnd_1956465 := by
    simpa [prefixWord, tailWord_1956465, baseEnd_1956465] using wordTrace_append hprefix tailTrace_1956465
  have hstable : (prefixWord ++ tailWord_1956465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1956465).length < 2 ^ (prefixWord ++ tailWord_1956465).sum := by decide
  have hdescent : baseEnd_1956465 < baseStart_1956465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1956465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
