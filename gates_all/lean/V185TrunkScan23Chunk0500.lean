import V185TrunkScan23Chunk0499

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2957691 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 1, 3, 2]
def baseStart_2957691 : Nat := 118140960795 + 2957691 * 2 ^ 59
def prefixEnd_2957691 : Nat := 4983230072969 + 3 ^ 40 * 2957691 * 2
def baseEnd_2957691 : Nat := 1518717110477292754060333

theorem tailTrace_2957691 : CollatzResearch.WordTrace tailWord_2957691 prefixEnd_2957691 1518717110477292754060333 := by
  unfold tailWord_2957691
  simp only [CollatzResearch.WordTrace]
  refine ⟨107875853127798115252184927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71917235418532076834789951 107875853127798115252184927)
  ·
    refine ⟨161813779691697172878277391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107875853127798115252184927 161813779691697172878277391)
    ·
      refine ⟨242720669537545759317416087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161813779691697172878277391 242720669537545759317416087)
      ·
        refine ⟨364081004306318638976124131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242720669537545759317416087 364081004306318638976124131)
        ·
          refine ⟨546121506459477958464186197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364081004306318638976124131 546121506459477958464186197)
          ·
            refine ⟨3199930701911003662876091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 546121506459477958464186197 3199930701911003662876091)
            ·
              refine ⟨4799896052866505494314137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3199930701911003662876091 4799896052866505494314137)
              ·
                refine ⟨3599922039649879120735603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4799896052866505494314137 3599922039649879120735603)
                ·
                  refine ⟨5399883059474818681103405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3599922039649879120735603 5399883059474818681103405)
                  ·
                    refine ⟨2024956147303057005413777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5399883059474818681103405 2024956147303057005413777)
                    ·
                      refine ⟨1518717110477292754060333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024956147303057005413777 1518717110477292754060333)
                      ·
                        rfl

theorem cell23_2957691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 1, 3, 2].length) (baseStart_2957691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957691 prefixEnd_2957691 := by exact prefixLift 2957691
  have htrace : WordTrace (prefixWord ++ tailWord_2957691) baseStart_2957691 baseEnd_2957691 := by
    simpa [prefixWord, tailWord_2957691, baseEnd_2957691] using wordTrace_append hprefix tailTrace_2957691
  have hstable : (prefixWord ++ tailWord_2957691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957691).length < 2 ^ (prefixWord ++ tailWord_2957691).sum := by decide
  have hdescent : baseEnd_2957691 < baseStart_2957691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957704 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 1, 4, 2]
def baseStart_2957704 : Nat := 118140960795 + 2957704 * 2 ^ 59
def prefixEnd_2957704 : Nat := 4983230072969 + 3 ^ 40 * 2957704 * 2
def baseEnd_2957704 : Nat := 1518723785725801203197773

theorem tailTrace_2957704 : CollatzResearch.WordTrace tailWord_2957704 prefixEnd_2957704 1518723785725801203197773 := by
  unfold tailWord_2957704
  simp only [CollatzResearch.WordTrace]
  refine ⟨53938163638375509236204083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71917551517834012314938777 53938163638375509236204083)
  ·
    refine ⟨80907245457563263854306125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53938163638375509236204083 80907245457563263854306125)
    ·
      refine ⟨30340217046586223945364797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80907245457563263854306125 30340217046586223945364797)
      ·
        refine ⟨11377581392469833979511799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30340217046586223945364797 11377581392469833979511799)
        ·
          refine ⟨17066372088704750969267699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11377581392469833979511799 17066372088704750969267699)
          ·
            refine ⟨25599558133057126453901549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17066372088704750969267699 25599558133057126453901549)
            ·
              refine ⟨9599834299896422420213081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25599558133057126453901549 9599834299896422420213081)
              ·
                refine ⟨7199875724922316815159811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9599834299896422420213081 7199875724922316815159811)
                ·
                  refine ⟨10799813587383475222739717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7199875724922316815159811 10799813587383475222739717)
                  ·
                    refine ⟨2024965047634401604263697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10799813587383475222739717 2024965047634401604263697)
                    ·
                      refine ⟨1518723785725801203197773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024965047634401604263697 1518723785725801203197773)
                      ·
                        rfl

theorem cell23_2957704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_2957704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957704 prefixEnd_2957704 := by exact prefixLift 2957704
  have htrace : WordTrace (prefixWord ++ tailWord_2957704) baseStart_2957704 baseEnd_2957704 := by
    simpa [prefixWord, tailWord_2957704, baseEnd_2957704] using wordTrace_append hprefix tailTrace_2957704
  have hstable : (prefixWord ++ tailWord_2957704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957704).length < 2 ^ (prefixWord ++ tailWord_2957704).sum := by decide
  have hdescent : baseEnd_2957704 < baseStart_2957704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957721 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 2, 2, 2]
def baseStart_2957721 : Nat := 118140960795 + 2957721 * 2 ^ 59
def prefixEnd_2957721 : Nat := 4983230072969 + 3 ^ 40 * 2957721 * 2
def baseEnd_2957721 : Nat := 1518732514896927636685195

theorem tailTrace_2957721 : CollatzResearch.WordTrace tailWord_2957721 prefixEnd_2957721 1518732514896927636685195 := by
  unfold tailWord_2957721
  simp only [CollatzResearch.WordTrace]
  refine ⟨107876947317689430375777017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71917964878459620250518011 107876947317689430375777017)
  ·
    refine ⟨80907710488267072781832763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107876947317689430375777017 80907710488267072781832763)
    ·
      refine ⟨121361565732400609172749145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80907710488267072781832763 121361565732400609172749145)
      ·
        refine ⟨91021174299300456879561859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121361565732400609172749145 91021174299300456879561859)
        ·
          refine ⟨136531761448950685319342789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91021174299300456879561859 136531761448950685319342789)
          ·
            refine ⟨25599705271678253497376773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136531761448950685319342789 25599705271678253497376773)
            ·
              refine ⟨4799944738439672530758145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25599705271678253497376773 4799944738439672530758145)
              ·
                refine ⟨3599958553829754398068609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4799944738439672530758145 3599958553829754398068609)
                ·
                  refine ⟨2699968915372315798551457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3599958553829754398068609 2699968915372315798551457)
                  ·
                    refine ⟨2024976686529236848913593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2699968915372315798551457 2024976686529236848913593)
                    ·
                      refine ⟨1518732514896927636685195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2024976686529236848913593 1518732514896927636685195)
                      ·
                        rfl

theorem cell23_2957721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_2957721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957721 prefixEnd_2957721 := by exact prefixLift 2957721
  have htrace : WordTrace (prefixWord ++ tailWord_2957721) baseStart_2957721 baseEnd_2957721 := by
    simpa [prefixWord, tailWord_2957721, baseEnd_2957721] using wordTrace_append hprefix tailTrace_2957721
  have hstable : (prefixWord ++ tailWord_2957721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957721).length < 2 ^ (prefixWord ++ tailWord_2957721).sum := by decide
  have hdescent : baseEnd_2957721 < baseStart_2957721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957740 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_2957740 : Nat := 118140960795 + 2957740 * 2 ^ 59
def prefixEnd_2957740 : Nat := 4983230072969 + 3 ^ 40 * 2957740 * 2
def baseEnd_2957740 : Nat := 506247423676454354115869

theorem tailTrace_2957740 : CollatzResearch.WordTrace tailWord_2957740 prefixEnd_2957740 506247423676454354115869 := by
  unfold tailWord_2957740
  simp only [CollatzResearch.WordTrace]
  refine ⟨53938820152310298310359337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71918426869747064413812449 53938820152310298310359337)
  ·
    refine ⟨40454115114232723732769503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53938820152310298310359337 40454115114232723732769503)
    ·
      refine ⟨60681172671349085599154255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40454115114232723732769503 60681172671349085599154255)
      ·
        refine ⟨91021759007023628398731383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60681172671349085599154255 91021759007023628398731383)
        ·
          refine ⟨136532638510535442598097075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91021759007023628398731383 136532638510535442598097075)
          ·
            refine ⟨204798957765803163897145613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136532638510535442598097075 204798957765803163897145613)
            ·
              refine ⟨76799609162176186461429605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 204798957765803163897145613 76799609162176186461429605)
              ·
                refine ⟨14399926717908034961518051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76799609162176186461429605 14399926717908034961518051)
                ·
                  refine ⟨21599890076862052442277077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14399926717908034961518051 21599890076862052442277077)
                  ·
                    refine ⟨506247423676454354115869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21599890076862052442277077 506247423676454354115869)
                    ·
                      rfl

theorem cell23_2957740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_2957740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957740 prefixEnd_2957740 := by exact prefixLift 2957740
  have htrace : WordTrace (prefixWord ++ tailWord_2957740) baseStart_2957740 baseEnd_2957740 := by
    simpa [prefixWord, tailWord_2957740, baseEnd_2957740] using wordTrace_append hprefix tailTrace_2957740
  have hstable : (prefixWord ++ tailWord_2957740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957740).length < 2 ^ (prefixWord ++ tailWord_2957740).sum := by decide
  have hdescent : baseEnd_2957740 < baseStart_2957740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957757 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_2957757 : Nat := 118140960795 + 2957757 * 2 ^ 59
def prefixEnd_2957757 : Nat := 4983230072969 + 3 ^ 40 * 2957757 * 2
def baseEnd_2957757 : Nat := 506250333400163165278343

theorem tailTrace_2957757 : CollatzResearch.WordTrace tailWord_2957757 prefixEnd_2957757 506250333400163165278343 := by
  unfold tailWord_2957757
  simp only [CollatzResearch.WordTrace]
  refine ⟨107878260345559008524087525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71918840230372672349391683 107878260345559008524087525)
  ·
    refine ⟨20227173814792314098266411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107878260345559008524087525 20227173814792314098266411)
    ·
      refine ⟨30340760722188471147399617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20227173814792314098266411 30340760722188471147399617)
      ·
        refine ⟨22755570541641353360549713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30340760722188471147399617 22755570541641353360549713)
        ·
          refine ⟨17066677906231015020412285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22755570541641353360549713 17066677906231015020412285)
          ·
            refine ⟨6400004214836630632654607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17066677906231015020412285 6400004214836630632654607)
            ·
              refine ⟨9600006322254945948981911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6400004214836630632654607 9600006322254945948981911)
              ·
                refine ⟨14400009483382418923472867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9600006322254945948981911 14400009483382418923472867)
                ·
                  refine ⟨21600014225073628385209301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14400009483382418923472867 21600014225073628385209301)
                  ·
                    refine ⟨506250333400163165278343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21600014225073628385209301 506250333400163165278343)
                    ·
                      rfl

theorem cell23_2957757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_2957757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957757 prefixEnd_2957757 := by exact prefixLift 2957757
  have htrace : WordTrace (prefixWord ++ tailWord_2957757) baseStart_2957757 baseEnd_2957757 := by
    simpa [prefixWord, tailWord_2957757, baseEnd_2957757] using wordTrace_append hprefix tailTrace_2957757
  have hstable : (prefixWord ++ tailWord_2957757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957757).length < 2 ^ (prefixWord ++ tailWord_2957757).sum := by decide
  have hdescent : baseEnd_2957757 < baseStart_2957757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957777 : List Nat := [1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_2957777 : Nat := 118140960795 + 2957777 * 2 ^ 59
def prefixEnd_2957777 : Nat := 4983230072969 + 3 ^ 40 * 2957777 * 2
def baseEnd_2957777 : Nat := 1518761269813579417584937

theorem tailTrace_2957777 : CollatzResearch.WordTrace tailWord_2957777 prefixEnd_2957777 1518761269813579417584937 := by
  unfold tailWord_2957777
  simp only [CollatzResearch.WordTrace]
  refine ⟨107878989805486551939815585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71919326536991034626543723 107878989805486551939815585)
  ·
    refine ⟨80909242354114913954861689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107878989805486551939815585 80909242354114913954861689)
    ·
      refine ⟨60681931765586185466146267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80909242354114913954861689 60681931765586185466146267)
      ·
        refine ⟨91022897648379278199219401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60681931765586185466146267 91022897648379278199219401)
        ·
          refine ⟨68267173236284458649414551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91022897648379278199219401 68267173236284458649414551)
          ·
            refine ⟨102400759854426687974121827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68267173236284458649414551 102400759854426687974121827)
            ·
              refine ⟨153601139781640031961182741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102400759854426687974121827 153601139781640031961182741)
              ·
                refine ⟨7200053427264376498180441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153601139781640031961182741 7200053427264376498180441)
                ·
                  refine ⟨5400040070448282373635331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7200053427264376498180441 5400040070448282373635331)
                  ·
                    refine ⟨8100060105672423560452997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5400040070448282373635331 8100060105672423560452997)
                    ·
                      refine ⟨1518761269813579417584937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8100060105672423560452997 1518761269813579417584937)
                      ·
                        rfl

theorem cell23_2957777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_2957777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957777 prefixEnd_2957777 := by exact prefixLift 2957777
  have htrace : WordTrace (prefixWord ++ tailWord_2957777) baseStart_2957777 baseEnd_2957777 := by
    simpa [prefixWord, tailWord_2957777, baseEnd_2957777] using wordTrace_append hprefix tailTrace_2957777
  have hstable : (prefixWord ++ tailWord_2957777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957777).length < 2 ^ (prefixWord ++ tailWord_2957777).sum := by decide
  have hdescent : baseEnd_2957777 < baseStart_2957777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957814 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_2957814 : Nat := 118140960795 + 2957814 * 2 ^ 59
def prefixEnd_2957814 : Nat := 4983230072969 + 3 ^ 40 * 2957814 * 2
def baseEnd_2957814 : Nat := 1518780268597795772822267

theorem tailTrace_2957814 : CollatzResearch.WordTrace tailWord_2957814 prefixEnd_2957814 1518780268597795772822267 := by
  unfold tailWord_2957814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6742521206647031703682031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71920226204235004839274997 6742521206647031703682031)
  ·
    refine ⟨10113781809970547555523047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6742521206647031703682031 10113781809970547555523047)
    ·
      refine ⟨15170672714955821333284571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10113781809970547555523047 15170672714955821333284571)
      ·
        refine ⟨22756009072433731999926857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15170672714955821333284571 22756009072433731999926857)
        ·
          refine ⟨17067006804325298999945143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22756009072433731999926857 17067006804325298999945143)
          ·
            refine ⟨25600510206487948499917715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17067006804325298999945143 25600510206487948499917715)
            ·
              refine ⟨38400765309731922749876573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25600510206487948499917715 38400765309731922749876573)
              ·
                refine ⟨14400286991149471031203715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38400765309731922749876573 14400286991149471031203715)
                ·
                  refine ⟨21600430486724206546805573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14400286991149471031203715 21600430486724206546805573)
                  ·
                    refine ⟨4050080716260788727526045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21600430486724206546805573 4050080716260788727526045)
                    ·
                      refine ⟨1518780268597795772822267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4050080716260788727526045 1518780268597795772822267)
                      ·
                        rfl

theorem cell23_2957814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_2957814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957814 prefixEnd_2957814 := by exact prefixLift 2957814
  have htrace : WordTrace (prefixWord ++ tailWord_2957814) baseStart_2957814 baseEnd_2957814 := by
    simpa [prefixWord, tailWord_2957814, baseEnd_2957814] using wordTrace_append hprefix tailTrace_2957814
  have hstable : (prefixWord ++ tailWord_2957814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957814).length < 2 ^ (prefixWord ++ tailWord_2957814).sum := by decide
  have hdescent : baseEnd_2957814 < baseStart_2957814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957831 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_2957831 : Nat := 118140960795 + 2957831 * 2 ^ 59
def prefixEnd_2957831 : Nat := 4983230072969 + 3 ^ 40 * 2957831 * 2
def baseEnd_2957831 : Nat := 1518788997768922206309689

theorem tailTrace_2957831 : CollatzResearch.WordTrace tailWord_2957831 prefixEnd_2957831 1518788997768922206309689 := by
  unfold tailWord_2957831
  simp only [CollatzResearch.WordTrace]
  refine ⟨107880959347290919162281347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71920639564860612774854231 107880959347290919162281347)
  ·
    refine ⟨161821439020936378743422021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107880959347290919162281347 161821439020936378743422021)
    ·
      refine ⟨30341519816425571014391629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161821439020936378743422021 30341519816425571014391629)
      ·
        refine ⟨11378069931159589130396861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30341519816425571014391629 11378069931159589130396861)
        ·
          refine ⟨4266776224184845923898823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11378069931159589130396861 4266776224184845923898823)
          ·
            refine ⟨6400164336277268885848235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266776224184845923898823 6400164336277268885848235)
            ·
              refine ⟨9600246504415903328772353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6400164336277268885848235 9600246504415903328772353)
              ·
                refine ⟨7200184878311927496579265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9600246504415903328772353 7200184878311927496579265)
                ·
                  refine ⟨5400138658733945622434449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7200184878311927496579265 5400138658733945622434449)
                  ·
                    refine ⟨4050103994050459216825837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5400138658733945622434449 4050103994050459216825837)
                    ·
                      refine ⟨1518788997768922206309689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4050103994050459216825837 1518788997768922206309689)
                      ·
                        rfl

theorem cell23_2957831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_2957831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957831 prefixEnd_2957831 := by exact prefixLift 2957831
  have htrace : WordTrace (prefixWord ++ tailWord_2957831) baseStart_2957831 baseEnd_2957831 := by
    simpa [prefixWord, tailWord_2957831, baseEnd_2957831] using wordTrace_append hprefix tailTrace_2957831
  have hstable : (prefixWord ++ tailWord_2957831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957831).length < 2 ^ (prefixWord ++ tailWord_2957831).sum := by decide
  have hdescent : baseEnd_2957831 < baseStart_2957831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957881 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 1, 5]
def baseStart_2957881 : Nat := 118140960795 + 2957881 * 2 ^ 59
def prefixEnd_2957881 : Nat := 4983230072969 + 3 ^ 40 * 2957881 * 2
def baseEnd_2957881 : Nat := 506271557267215670228153

theorem tailTrace_2957881 : CollatzResearch.WordTrace tailWord_2957881 prefixEnd_2957881 506271557267215670228153 := by
  unfold tailWord_2957881
  simp only [CollatzResearch.WordTrace]
  refine ⟨107882782997109777701601497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71921855331406518467734331 107882782997109777701601497)
  ·
    refine ⟨80912087247832333276201123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107882782997109777701601497 80912087247832333276201123)
    ·
      refine ⟨121368130871748499914301685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80912087247832333276201123 121368130871748499914301685)
      ·
        refine ⟨11378262269226421866965783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121368130871748499914301685 11378262269226421866965783)
        ·
          refine ⟨17067393403839632800448675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11378262269226421866965783 17067393403839632800448675)
          ·
            refine ⟨25601090105759449200673013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17067393403839632800448675 25601090105759449200673013)
            ·
              refine ⟨2400102197414948362563095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25601090105759449200673013 2400102197414948362563095)
              ·
                refine ⟨3600153296122422543844643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400102197414948362563095 3600153296122422543844643)
                ·
                  refine ⟨5400229944183633815766965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600153296122422543844643 5400229944183633815766965)
                  ·
                    refine ⟨506271557267215670228153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5400229944183633815766965 506271557267215670228153)
                    ·
                      rfl

theorem cell23_2957881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 1, 5].length) (baseStart_2957881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957881 prefixEnd_2957881 := by exact prefixLift 2957881
  have htrace : WordTrace (prefixWord ++ tailWord_2957881) baseStart_2957881 baseEnd_2957881 := by
    simpa [prefixWord, tailWord_2957881, baseEnd_2957881] using wordTrace_append hprefix tailTrace_2957881
  have hstable : (prefixWord ++ tailWord_2957881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957881).length < 2 ^ (prefixWord ++ tailWord_2957881).sum := by decide
  have hdescent : baseEnd_2957881 < baseStart_2957881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957895 : List Nat := [1, 1, 4, 1, 4, 1, 4, 2, 1, 1, 3]
def baseStart_2957895 : Nat := 118140960795 + 2957895 * 2 ^ 59
def prefixEnd_2957895 : Nat := 4983230072969 + 3 ^ 40 * 2957895 * 2
def baseEnd_2957895 : Nat := 1518821860530809955909395

theorem tailTrace_2957895 : CollatzResearch.WordTrace tailWord_2957895 prefixEnd_2957895 1518821860530809955909395 := by
  unfold tailWord_2957895
  simp only [CollatzResearch.WordTrace]
  refine ⟨107883293619059058092611139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71922195746039372061740759 107883293619059058092611139)
  ·
    refine ⟨161824940428588587138916709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107883293619059058092611139 161824940428588587138916709)
    ·
      refine ⟨30342176330360360088546883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161824940428588587138916709 30342176330360360088546883)
      ·
        refine ⟨45513264495540540132820325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30342176330360360088546883 45513264495540540132820325)
        ·
          refine ⟨8533737092913851274903811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45513264495540540132820325 8533737092913851274903811)
          ·
            refine ⟨12800605639370776912355717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8533737092913851274903811 12800605639370776912355717)
            ·
              refine ⟨2400113557382020671066697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12800605639370776912355717 2400113557382020671066697)
              ·
                refine ⟨1800085168036515503300023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2400113557382020671066697 1800085168036515503300023)
                ·
                  refine ⟨2700127752054773254950035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800085168036515503300023 2700127752054773254950035)
                  ·
                    refine ⟨4050191628082159882425053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2700127752054773254950035 4050191628082159882425053)
                    ·
                      refine ⟨1518821860530809955909395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4050191628082159882425053 1518821860530809955909395)
                      ·
                        rfl

theorem cell23_2957895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_2957895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957895 prefixEnd_2957895 := by exact prefixLift 2957895
  have htrace : WordTrace (prefixWord ++ tailWord_2957895) baseStart_2957895 baseEnd_2957895 := by
    simpa [prefixWord, tailWord_2957895, baseEnd_2957895] using wordTrace_append hprefix tailTrace_2957895
  have hstable : (prefixWord ++ tailWord_2957895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957895).length < 2 ^ (prefixWord ++ tailWord_2957895).sum := by decide
  have hdescent : baseEnd_2957895 < baseStart_2957895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957901 : List Nat := [1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2957901 : Nat := 118140960795 + 2957901 * 2 ^ 59
def prefixEnd_2957901 : Nat := 4983230072969 + 3 ^ 40 * 2957901 * 2
def baseEnd_2957901 : Nat := 1518824941414736932434367

theorem tailTrace_2957901 : CollatzResearch.WordTrace tailWord_2957901 prefixEnd_2957901 1518824941414736932434367 := by
  unfold tailWord_2957901
  simp only [CollatzResearch.WordTrace]
  refine ⟨107883512457037321117329557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71922341638024880744886371 107883512457037321117329557)
  ·
    refine ⟨5057039646423624427374823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107883512457037321117329557 5057039646423624427374823)
    ·
      refine ⟨7585559469635436641062235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5057039646423624427374823 7585559469635436641062235)
      ·
        refine ⟨11378339204453154961593353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7585559469635436641062235 11378339204453154961593353)
        ·
          refine ⟨8533754403339866221195015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11378339204453154961593353 8533754403339866221195015)
          ·
            refine ⟨12800631605009799331792523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8533754403339866221195015 12800631605009799331792523)
            ·
              refine ⟨19200947407514698997688785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12800631605009799331792523 19200947407514698997688785)
              ·
                refine ⟨14400710555636024248266589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19200947407514698997688785 14400710555636024248266589)
                ·
                  refine ⟨5400266458363509093099971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14400710555636024248266589 5400266458363509093099971)
                  ·
                    refine ⟨8100399687545263639649957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5400266458363509093099971 8100399687545263639649957)
                    ·
                      refine ⟨1518824941414736932434367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8100399687545263639649957 1518824941414736932434367)
                      ·
                        rfl

theorem cell23_2957901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2957901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957901 prefixEnd_2957901 := by exact prefixLift 2957901
  have htrace : WordTrace (prefixWord ++ tailWord_2957901) baseStart_2957901 baseEnd_2957901 := by
    simpa [prefixWord, tailWord_2957901, baseEnd_2957901] using wordTrace_append hprefix tailTrace_2957901
  have hstable : (prefixWord ++ tailWord_2957901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957901).length < 2 ^ (prefixWord ++ tailWord_2957901).sum := by decide
  have hdescent : baseEnd_2957901 < baseStart_2957901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957922 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_2957922 : Nat := 118140960795 + 2957922 * 2 ^ 59
def prefixEnd_2957922 : Nat := 4983230072969 + 3 ^ 40 * 2957922 * 2
def baseEnd_2957922 : Nat := 1518835724508481350271771

theorem tailTrace_2957922 : CollatzResearch.WordTrace tailWord_2957922 prefixEnd_2957922 1518835724508481350271771 := by
  unfold tailWord_2957922
  simp only [CollatzResearch.WordTrace]
  refine ⟨26971069597490310425961005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71922852259974161135896013 26971069597490310425961005)
  ·
    refine ⟨10114151099058866409735377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26971069597490310425961005 10114151099058866409735377)
    ·
      refine ⟨7585613324294149807301533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10114151099058866409735377 7585613324294149807301533)
      ·
        refine ⟨2844604996610306177738075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7585613324294149807301533 2844604996610306177738075)
        ·
          refine ⟨4266907494915459266607113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844604996610306177738075 4266907494915459266607113)
          ·
            refine ⟨3200180621186594449955335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4266907494915459266607113 3200180621186594449955335)
            ·
              refine ⟨4800270931779891674933003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200180621186594449955335 4800270931779891674933003)
              ·
                refine ⟨7200406397669837512399505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4800270931779891674933003 7200406397669837512399505)
                ·
                  refine ⟨5400304798252378134299629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7200406397669837512399505 5400304798252378134299629)
                  ·
                    refine ⟨2025114299344641800362361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5400304798252378134299629 2025114299344641800362361)
                    ·
                      refine ⟨1518835724508481350271771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025114299344641800362361 1518835724508481350271771)
                      ·
                        rfl

theorem cell23_2957922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_2957922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957922 prefixEnd_2957922 := by exact prefixLift 2957922
  have htrace : WordTrace (prefixWord ++ tailWord_2957922) baseStart_2957922 baseEnd_2957922 := by
    simpa [prefixWord, tailWord_2957922, baseEnd_2957922] using wordTrace_append hprefix tailTrace_2957922
  have hstable : (prefixWord ++ tailWord_2957922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957922).length < 2 ^ (prefixWord ++ tailWord_2957922).sum := by decide
  have hdescent : baseEnd_2957922 < baseStart_2957922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957924 : List Nat := [2, 3, 1, 1, 2, 2, 5, 7]
def baseStart_2957924 : Nat := 118140960795 + 2957924 * 2 ^ 59
def prefixEnd_2957924 : Nat := 4983230072969 + 3 ^ 40 * 2957924 * 2
def baseEnd_2957924 : Nat := 56253213017399642312843

theorem tailTrace_2957924 : CollatzResearch.WordTrace tailWord_2957924 prefixEnd_2957924 56253213017399642312843 := by
  unfold tailWord_2957924
  simp only [CollatzResearch.WordTrace]
  refine ⟨53942175667976998022708413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71922900890635997363611217 53942175667976998022708413)
  ·
    refine ⟨20228315875491374258515655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53942175667976998022708413 20228315875491374258515655)
    ·
      refine ⟨30342473813237061387773483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20228315875491374258515655 30342473813237061387773483)
      ·
        refine ⟨45513710719855592081660225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30342473813237061387773483 45513710719855592081660225)
        ·
          refine ⟨34135283039891694061245169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45513710719855592081660225 34135283039891694061245169)
          ·
            refine ⟨25601462279918770545933877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34135283039891694061245169 25601462279918770545933877)
            ·
              refine ⟨2400137088742384738681301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25601462279918770545933877 2400137088742384738681301)
              ·
                refine ⟨56253213017399642312843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2400137088742384738681301 56253213017399642312843)
                ·
                  rfl

theorem cell23_2957924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 7].length) (baseStart_2957924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957924 prefixEnd_2957924 := by exact prefixLift 2957924
  have htrace : WordTrace (prefixWord ++ tailWord_2957924) baseStart_2957924 baseEnd_2957924 := by
    simpa [prefixWord, tailWord_2957924, baseEnd_2957924] using wordTrace_append hprefix tailTrace_2957924
  have hstable : (prefixWord ++ tailWord_2957924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957924).length < 2 ^ (prefixWord ++ tailWord_2957924).sum := by decide
  have hdescent : baseEnd_2957924 < baseStart_2957924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957938 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_2957938 : Nat := 118140960795 + 2957938 * 2 ^ 59
def prefixEnd_2957938 : Nat := 4983230072969 + 3 ^ 40 * 2957938 * 2
def baseEnd_2957938 : Nat := 1518843940198953287671697

theorem tailTrace_2957938 : CollatzResearch.WordTrace tailWord_2957938 prefixEnd_2957938 1518843940198953287671697 := by
  unfold tailWord_2957938
  simp only [CollatzResearch.WordTrace]
  refine ⟨26971215489475819109106617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71923241305268850957617645 26971215489475819109106617)
  ·
    refine ⟨20228411617106864331829963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26971215489475819109106617 20228411617106864331829963)
    ·
      refine ⟨30342617425660296497744945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20228411617106864331829963 30342617425660296497744945)
      ·
        refine ⟨22756963069245222373308709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30342617425660296497744945 22756963069245222373308709)
        ·
          refine ⟨4266930575483479194995383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22756963069245222373308709 4266930575483479194995383)
          ·
            refine ⟨6400395863225218792493075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4266930575483479194995383 6400395863225218792493075)
            ·
              refine ⟨9600593794837828188739613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6400395863225218792493075 9600593794837828188739613)
              ·
                refine ⟨3600222673064185570777355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9600593794837828188739613 3600222673064185570777355)
                ·
                  refine ⟨5400334009596278356166033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600222673064185570777355 5400334009596278356166033)
                  ·
                    refine ⟨4050250507197208767124525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5400334009596278356166033 4050250507197208767124525)
                    ·
                      refine ⟨1518843940198953287671697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4050250507197208767124525 1518843940198953287671697)
                      ·
                        rfl

theorem cell23_2957938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_2957938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957938 prefixEnd_2957938 := by exact prefixLift 2957938
  have htrace : WordTrace (prefixWord ++ tailWord_2957938) baseStart_2957938 baseEnd_2957938 := by
    simpa [prefixWord, tailWord_2957938, baseEnd_2957938] using wordTrace_append hprefix tailTrace_2957938
  have hstable : (prefixWord ++ tailWord_2957938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957938).length < 2 ^ (prefixWord ++ tailWord_2957938).sum := by decide
  have hdescent : baseEnd_2957938 < baseStart_2957938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957947 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 5]
def baseStart_2957947 : Nat := 118140960795 + 2957947 * 2 ^ 59
def prefixEnd_2957947 : Nat := 4983230072969 + 3 ^ 40 * 2957947 * 2
def baseEnd_2957947 : Nat := 1518848561524843752459155

theorem tailTrace_2957947 : CollatzResearch.WordTrace tailWord_2957947 prefixEnd_2957947 1518848561524843752459155 := by
  unfold tailWord_2957947
  simp only [CollatzResearch.WordTrace]
  refine ⟨107885190214870670973504095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71923460143247113982336063 107885190214870670973504095)
  ·
    refine ⟨161827785322306006460256143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107885190214870670973504095 161827785322306006460256143)
    ·
      refine ⟨242741677983459009690384215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161827785322306006460256143 242741677983459009690384215)
      ·
        refine ⟨364112516975188514535576323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242741677983459009690384215 364112516975188514535576323)
        ·
          refine ⟨546168775462782771803364485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364112516975188514535576323 546168775462782771803364485)
          ·
            refine ⟨102406645399271769713130841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 546168775462782771803364485 102406645399271769713130841)
            ·
              refine ⟨76804984049453827284848131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102406645399271769713130841 76804984049453827284848131)
              ·
                refine ⟨115207476074180740927272197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76804984049453827284848131 115207476074180740927272197)
                ·
                  refine ⟨21601401763908888923863537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115207476074180740927272197 21601401763908888923863537)
                  ·
                    refine ⟨16201051322931666692897653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21601401763908888923863537 16201051322931666692897653)
                    ·
                      refine ⟨1518848561524843752459155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16201051322931666692897653 1518848561524843752459155)
                      ·
                        rfl

theorem cell23_2957947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_2957947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957947 prefixEnd_2957947 := by exact prefixLift 2957947
  have htrace : WordTrace (prefixWord ++ tailWord_2957947) baseStart_2957947 baseEnd_2957947 := by
    simpa [prefixWord, tailWord_2957947, baseEnd_2957947] using wordTrace_append hprefix tailTrace_2957947
  have hstable : (prefixWord ++ tailWord_2957947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957947).length < 2 ^ (prefixWord ++ tailWord_2957947).sum := by decide
  have hdescent : baseEnd_2957947 < baseStart_2957947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2957951 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 3]
def baseStart_2957951 : Nat := 118140960795 + 2957951 * 2 ^ 59
def prefixEnd_2957951 : Nat := 4983230072969 + 3 ^ 40 * 2957951 * 2
def baseEnd_2957951 : Nat := 1518850615447461736809137

theorem tailTrace_2957951 : CollatzResearch.WordTrace tailWord_2957951 prefixEnd_2957951 1518850615447461736809137 := by
  unfold tailWord_2957951
  simp only [CollatzResearch.WordTrace]
  refine ⟨107885336106856179656649707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71923557404570786437766471 107885336106856179656649707)
  ·
    refine ⟨161828004160284269484974561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107885336106856179656649707 161828004160284269484974561)
    ·
      refine ⟨121371003120213202113730921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161828004160284269484974561 121371003120213202113730921)
      ·
        refine ⟨91028252340159901585298191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121371003120213202113730921 91028252340159901585298191)
        ·
          refine ⟨136542378510239852377947287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91028252340159901585298191 136542378510239852377947287)
          ·
            refine ⟨204813567765359778566920931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136542378510239852377947287 204813567765359778566920931)
            ·
              refine ⟨307220351648039667850381397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204813567765359778566920931 307220351648039667850381397)
              ·
                refine ⟨3600238495875464857621657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 307220351648039667850381397 3600238495875464857621657)
                ·
                  refine ⟨2700178871906598643216243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3600238495875464857621657 2700178871906598643216243)
                  ·
                    refine ⟨4050268307859897964824365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2700178871906598643216243 4050268307859897964824365)
                    ·
                      refine ⟨1518850615447461736809137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4050268307859897964824365 1518850615447461736809137)
                      ·
                        rfl

theorem cell23_2957951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_2957951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2957951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2957951 prefixEnd_2957951 := by exact prefixLift 2957951
  have htrace : WordTrace (prefixWord ++ tailWord_2957951) baseStart_2957951 baseEnd_2957951 := by
    simpa [prefixWord, tailWord_2957951, baseEnd_2957951] using wordTrace_append hprefix tailTrace_2957951
  have hstable : (prefixWord ++ tailWord_2957951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2957951).length < 2 ^ (prefixWord ++ tailWord_2957951).sum := by decide
  have hdescent : baseEnd_2957951 < baseStart_2957951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2957951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958029 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_2958029 : Nat := 118140960795 + 2958029 * 2 ^ 59
def prefixEnd_2958029 : Nat := 4983230072969 + 3 ^ 40 * 2958029 * 2
def baseEnd_2958029 : Nat := 1518890666938512431633779

theorem tailTrace_2958029 : CollatzResearch.WordTrace tailWord_2958029 prefixEnd_2958029 1518890666938512431633779 := by
  unfold tailWord_2958029
  simp only [CollatzResearch.WordTrace]
  refine ⟨107888181000573598977989141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71925454000382399318659427 107888181000573598977989141)
  ·
    refine ⟨5057258484401887452093241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107888181000573598977989141 5057258484401887452093241)
    ·
      refine ⟨3792943863301415589069931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5057258484401887452093241 3792943863301415589069931)
      ·
        refine ⟨5689415794952123383604897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3792943863301415589069931 5689415794952123383604897)
        ·
          refine ⟨4267061846214092537703673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5689415794952123383604897 4267061846214092537703673)
          ·
            refine ⟨3200296384660569403277755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4267061846214092537703673 3200296384660569403277755)
            ·
              refine ⟨4800444576990854104916633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200296384660569403277755 4800444576990854104916633)
              ·
                refine ⟨3600333432743140578687475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4800444576990854104916633 3600333432743140578687475)
                ·
                  refine ⟨5400500149114710868031213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600333432743140578687475 5400500149114710868031213)
                  ·
                    refine ⟨2025187555918016575511705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5400500149114710868031213 2025187555918016575511705)
                    ·
                      refine ⟨1518890666938512431633779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025187555918016575511705 1518890666938512431633779)
                      ·
                        rfl

theorem cell23_2958029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_2958029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958029 prefixEnd_2958029 := by exact prefixLift 2958029
  have htrace : WordTrace (prefixWord ++ tailWord_2958029) baseStart_2958029 baseEnd_2958029 := by
    simpa [prefixWord, tailWord_2958029, baseEnd_2958029] using wordTrace_append hprefix tailTrace_2958029
  have hstable : (prefixWord ++ tailWord_2958029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958029).length < 2 ^ (prefixWord ++ tailWord_2958029).sum := by decide
  have hdescent : baseEnd_2958029 < baseStart_2958029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958061 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_2958061 : Nat := 118140960795 + 2958061 * 2 ^ 59
def prefixEnd_2958061 : Nat := 4983230072969 + 3 ^ 40 * 2958061 * 2
def baseEnd_2958061 : Nat := 506302366106485435477877

theorem tailTrace_2958061 : CollatzResearch.WordTrace tailWord_2958061 prefixEnd_2958061 506302366106485435477877 := by
  unfold tailWord_2958061
  simp only [CollatzResearch.WordTrace]
  refine ⟨107889348136457668443154037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71926232090971778962102691 107889348136457668443154037)
  ·
    refine ⟨10114626387792906416545691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107889348136457668443154037 10114626387792906416545691)
    ·
      refine ⟨15171939581689359624818537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10114626387792906416545691 15171939581689359624818537)
      ·
        refine ⟨11378954686267019718613903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15171939581689359624818537 11378954686267019718613903)
        ·
          refine ⟨17068432029400529577920855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11378954686267019718613903 17068432029400529577920855)
          ·
            refine ⟨25602648044100794366881283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17068432029400529577920855 25602648044100794366881283)
            ·
              refine ⟨38403972066151191550321925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25602648044100794366881283 38403972066151191550321925)
              ·
                refine ⟨7200744762403348415685361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38403972066151191550321925 7200744762403348415685361)
                ·
                  refine ⟨5400558571802511311764021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7200744762403348415685361 5400558571802511311764021)
                  ·
                    refine ⟨506302366106485435477877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5400558571802511311764021 506302366106485435477877)
                    ·
                      rfl

theorem cell23_2958061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_2958061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958061 prefixEnd_2958061 := by exact prefixLift 2958061
  have htrace : WordTrace (prefixWord ++ tailWord_2958061) baseStart_2958061 baseEnd_2958061 := by
    simpa [prefixWord, tailWord_2958061, baseEnd_2958061] using wordTrace_append hprefix tailTrace_2958061
  have hstable : (prefixWord ++ tailWord_2958061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958061).length < 2 ^ (prefixWord ++ tailWord_2958061).sum := by decide
  have hdescent : baseEnd_2958061 < baseStart_2958061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958101 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_2958101 : Nat := 118140960795 + 2958101 * 2 ^ 59
def prefixEnd_2958101 : Nat := 4983230072969 + 3 ^ 40 * 2958101 * 2
def baseEnd_2958101 : Nat := 1518927637545636149933447

theorem tailTrace_2958101 : CollatzResearch.WordTrace tailWord_2958101 prefixEnd_2958101 1518927637545636149933447 := by
  unfold tailWord_2958101
  simp only [CollatzResearch.WordTrace]
  refine ⟨107890807056312755274610157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71927204704208503516406771 107890807056312755274610157)
  ·
    refine ⟨40459052646117283227978809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107890807056312755274610157 40459052646117283227978809)
    ·
      refine ⟨30344289484587962420984107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40459052646117283227978809 30344289484587962420984107)
      ·
        refine ⟨45516434226881943631476161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30344289484587962420984107 45516434226881943631476161)
        ·
          refine ⟨34137325670161457723607121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45516434226881943631476161 34137325670161457723607121)
          ·
            refine ⟨25602994252621093292705341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34137325670161457723607121 25602994252621093292705341)
            ·
              refine ⟨9601122844732909984764503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25602994252621093292705341 9601122844732909984764503)
              ·
                refine ⟨14401684267099364977146755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9601122844732909984764503 14401684267099364977146755)
                ·
                  refine ⟨21602526400649047465720133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14401684267099364977146755 21602526400649047465720133)
                  ·
                    refine ⟨4050473700121696399822525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21602526400649047465720133 4050473700121696399822525)
                    ·
                      refine ⟨1518927637545636149933447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4050473700121696399822525 1518927637545636149933447)
                      ·
                        rfl

theorem cell23_2958101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_2958101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958101 prefixEnd_2958101 := by exact prefixLift 2958101
  have htrace : WordTrace (prefixWord ++ tailWord_2958101) baseStart_2958101 baseEnd_2958101 := by
    simpa [prefixWord, tailWord_2958101, baseEnd_2958101] using wordTrace_append hprefix tailTrace_2958101
  have hstable : (prefixWord ++ tailWord_2958101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958101).length < 2 ^ (prefixWord ++ tailWord_2958101).sum := by decide
  have hdescent : baseEnd_2958101 < baseStart_2958101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958104 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 8]
def baseStart_2958104 : Nat := 118140960795 + 2958104 * 2 ^ 59
def prefixEnd_2958104 : Nat := 4983230072969 + 3 ^ 40 * 2958104 * 2
def baseEnd_2958104 : Nat := 168769908665288848688437

theorem tailTrace_2958104 : CollatzResearch.WordTrace tailWord_2958104 prefixEnd_2958104 168769908665288848688437 := by
  unfold tailWord_2958104
  simp only [CollatzResearch.WordTrace]
  refine ⟨53945458237650943393484683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71927277650201257857979577 53945458237650943393484683)
  ·
    refine ⟨80918187356476415090227025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53945458237650943393484683 80918187356476415090227025)
    ·
      refine ⟨60688640517357311317670269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80918187356476415090227025 60688640517357311317670269)
      ·
        refine ⟨22758240194008991744126351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60688640517357311317670269 22758240194008991744126351)
        ·
          refine ⟨34137360291013487616189527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22758240194008991744126351 34137360291013487616189527)
          ·
            refine ⟨51206040436520231424284291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34137360291013487616189527 51206040436520231424284291)
            ·
              refine ⟨76809060654780347136426437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51206040436520231424284291 76809060654780347136426437)
              ·
                refine ⟨14401698872771315088079957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76809060654780347136426437 14401698872771315088079957)
                ·
                  refine ⟨168769908665288848688437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14401698872771315088079957 168769908665288848688437)
                  ·
                    rfl

theorem cell23_2958104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 8].length) (baseStart_2958104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958104 prefixEnd_2958104 := by exact prefixLift 2958104
  have htrace : WordTrace (prefixWord ++ tailWord_2958104) baseStart_2958104 baseEnd_2958104 := by
    simpa [prefixWord, tailWord_2958104, baseEnd_2958104] using wordTrace_append hprefix tailTrace_2958104
  have hstable : (prefixWord ++ tailWord_2958104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958104).length < 2 ^ (prefixWord ++ tailWord_2958104).sum := by decide
  have hdescent : baseEnd_2958104 < baseStart_2958104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958124 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_2958124 : Nat := 118140960795 + 2958124 * 2 ^ 59
def prefixEnd_2958124 : Nat := 4983230072969 + 3 ^ 40 * 2958124 * 2
def baseEnd_2958124 : Nat := 1518939447600689559945841

theorem tailTrace_2958124 : CollatzResearch.WordTrace tailWord_2958124 prefixEnd_2958124 1518939447600689559945841 := by
  unfold tailWord_2958124
  simp only [CollatzResearch.WordTrace]
  refine ⟨53945822967614715101348713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71927763956819620135131617 53945822967614715101348713)
  ·
    refine ⟨40459367225711036326011535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53945822967614715101348713 40459367225711036326011535)
    ·
      refine ⟨60689050838566554489017303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40459367225711036326011535 60689050838566554489017303)
      ·
        refine ⟨91033576257849831733525955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60689050838566554489017303 91033576257849831733525955)
        ·
          refine ⟨136550364386774747600288933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91033576257849831733525955 136550364386774747600288933)
          ·
            refine ⟨25603193322520265175054175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136550364386774747600288933 25603193322520265175054175)
            ·
              refine ⟨38404789983780397762581263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25603193322520265175054175 38404789983780397762581263)
              ·
                refine ⟨57607184975670596643871895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38404789983780397762581263 57607184975670596643871895)
                ·
                  refine ⟨86410777463505894965807843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57607184975670596643871895 86410777463505894965807843)
                  ·
                    refine ⟨129616166195258842448711765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86410777463505894965807843 129616166195258842448711765)
                    ·
                      refine ⟨1518939447600689559945841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 129616166195258842448711765 1518939447600689559945841)
                      ·
                        rfl

theorem cell23_2958124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_2958124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958124 prefixEnd_2958124 := by exact prefixLift 2958124
  have htrace : WordTrace (prefixWord ++ tailWord_2958124) baseStart_2958124 baseEnd_2958124 := by
    simpa [prefixWord, tailWord_2958124, baseEnd_2958124] using wordTrace_append hprefix tailTrace_2958124
  have hstable : (prefixWord ++ tailWord_2958124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958124).length < 2 ^ (prefixWord ++ tailWord_2958124).sum := by decide
  have hdescent : baseEnd_2958124 < baseStart_2958124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958144 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_2958144 : Nat := 118140960795 + 2958144 * 2 ^ 59
def prefixEnd_2958144 : Nat := 4983230072969 + 3 ^ 40 * 2958144 * 2
def baseEnd_2958144 : Nat := 1518949717213779481695749

theorem tailTrace_2958144 : CollatzResearch.WordTrace tailWord_2958144 prefixEnd_2958144 1518949717213779481695749 := by
  unfold tailWord_2958144
  simp only [CollatzResearch.WordTrace]
  refine ⟨53946187697578486809212743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71928250263437982412283657 53946187697578486809212743)
  ·
    refine ⟨80919281546367730213819115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53946187697578486809212743 80919281546367730213819115)
    ·
      refine ⟨121378922319551595320728673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80919281546367730213819115 121378922319551595320728673)
      ·
        refine ⟨91034191739663696490546505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121378922319551595320728673 91034191739663696490546505)
        ·
          refine ⟨68275643804747772367909879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91034191739663696490546505 68275643804747772367909879)
          ·
            refine ⟨102413465707121658551864819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68275643804747772367909879 102413465707121658551864819)
            ·
              refine ⟨153620198560682487827797229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102413465707121658551864819 153620198560682487827797229)
              ·
                refine ⟨57607574460255932935423961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 153620198560682487827797229 57607574460255932935423961)
                ·
                  refine ⟨43205680845191949701567971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57607574460255932935423961 43205680845191949701567971)
                  ·
                    refine ⟨64808521267787924552351957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43205680845191949701567971 64808521267787924552351957)
                    ·
                      refine ⟨1518949717213779481695749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64808521267787924552351957 1518949717213779481695749)
                      ·
                        rfl

theorem cell23_2958144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_2958144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958144 prefixEnd_2958144 := by exact prefixLift 2958144
  have htrace : WordTrace (prefixWord ++ tailWord_2958144) baseStart_2958144 baseEnd_2958144 := by
    simpa [prefixWord, tailWord_2958144, baseEnd_2958144] using wordTrace_append hprefix tailTrace_2958144
  have hstable : (prefixWord ++ tailWord_2958144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958144).length < 2 ^ (prefixWord ++ tailWord_2958144).sum := by decide
  have hdescent : baseEnd_2958144 < baseStart_2958144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958158 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2]
def baseStart_2958158 : Nat := 118140960795 + 2958158 * 2 ^ 59
def prefixEnd_2958158 : Nat := 4983230072969 + 3 ^ 40 * 2958158 * 2
def baseEnd_2958158 : Nat := 1518956905942942426920685

theorem tailTrace_2958158 : CollatzResearch.WordTrace tailWord_2958158 prefixEnd_2958158 1518956905942942426920685 := by
  unfold tailWord_2958158
  simp only [CollatzResearch.WordTrace]
  refine ⟨13486610752138281751179391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71928590678070836006290085 13486610752138281751179391)
  ·
    refine ⟨20229916128207422626769087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13486610752138281751179391 20229916128207422626769087)
    ·
      refine ⟨30344874192311133940153631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20229916128207422626769087 30344874192311133940153631)
      ·
        refine ⟨45517311288466700910230447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30344874192311133940153631 45517311288466700910230447)
        ·
          refine ⟨68275966932700051365345671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45517311288466700910230447 68275966932700051365345671)
          ·
            refine ⟨102413950399050077048018507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68275966932700051365345671 102413950399050077048018507)
            ·
              refine ⟨153620925598575115572027761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102413950399050077048018507 153620925598575115572027761)
              ·
                refine ⟨115215694198931336679020821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153620925598575115572027761 115215694198931336679020821)
                ·
                  refine ⟨5400735665574906406829101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115215694198931336679020821 5400735665574906406829101)
                  ·
                    refine ⟨2025275874590589902560913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5400735665574906406829101 2025275874590589902560913)
                    ·
                      refine ⟨1518956905942942426920685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025275874590589902560913 1518956905942942426920685)
                      ·
                        rfl

theorem cell23_2958158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_2958158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958158 prefixEnd_2958158 := by exact prefixLift 2958158
  have htrace : WordTrace (prefixWord ++ tailWord_2958158) baseStart_2958158 baseEnd_2958158 := by
    simpa [prefixWord, tailWord_2958158, baseEnd_2958158] using wordTrace_append hprefix tailTrace_2958158
  have hstable : (prefixWord ++ tailWord_2958158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958158).length < 2 ^ (prefixWord ++ tailWord_2958158).sum := by decide
  have hdescent : baseEnd_2958158 < baseStart_2958158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958201 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_2958201 : Nat := 118140960795 + 2958201 * 2 ^ 59
def prefixEnd_2958201 : Nat := 4983230072969 + 3 ^ 40 * 2958201 * 2
def baseEnd_2958201 : Nat := 1518978985611085758682987

theorem tailTrace_2958201 : CollatzResearch.WordTrace tailWord_2958201 prefixEnd_2958201 1518978985611085758682987 := by
  unfold tailWord_2958201
  simp only [CollatzResearch.WordTrace]
  refine ⟨107894454355950472353250457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71929636237300314902166971 107894454355950472353250457)
  ·
    refine ⟨80920840766962854264937843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107894454355950472353250457 80920840766962854264937843)
    ·
      refine ⟨121381261150444281397406765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80920840766962854264937843 121381261150444281397406765)
      ·
        refine ⟨45517972931416605524027537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121381261150444281397406765 45517972931416605524027537)
        ·
          refine ⟨34138479698562454143020653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45517972931416605524027537 34138479698562454143020653)
          ·
            refine ⟨12801929886960920303632745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34138479698562454143020653 12801929886960920303632745)
            ·
              refine ⟨9601447415220690227724559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12801929886960920303632745 9601447415220690227724559)
              ·
                refine ⟨14402171122831035341586839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9601447415220690227724559 14402171122831035341586839)
                ·
                  refine ⟨21603256684246553012380259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14402171122831035341586839 21603256684246553012380259)
                  ·
                    refine ⟨32404885026369829518570389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21603256684246553012380259 32404885026369829518570389)
                    ·
                      refine ⟨1518978985611085758682987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32404885026369829518570389 1518978985611085758682987)
                      ·
                        rfl

theorem cell23_2958201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_2958201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958201 prefixEnd_2958201 := by exact prefixLift 2958201
  have htrace : WordTrace (prefixWord ++ tailWord_2958201) baseStart_2958201 baseEnd_2958201 := by
    simpa [prefixWord, tailWord_2958201, baseEnd_2958201] using wordTrace_append hprefix tailTrace_2958201
  have hstable : (prefixWord ++ tailWord_2958201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958201).length < 2 ^ (prefixWord ++ tailWord_2958201).sum := by decide
  have hdescent : baseEnd_2958201 < baseStart_2958201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958205 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 3, 2, 2]
def baseStart_2958205 : Nat := 118140960795 + 2958205 * 2 ^ 59
def prefixEnd_2958205 : Nat := 4983230072969 + 3 ^ 40 * 2958205 * 2
def baseEnd_2958205 : Nat := 1518981039533703743032969

theorem tailTrace_2958205 : CollatzResearch.WordTrace tailWord_2958205 prefixEnd_2958205 1518981039533703743032969 := by
  unfold tailWord_2958205
  simp only [CollatzResearch.WordTrace]
  refine ⟨107894600247935981036396069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71929733498623987357597379 107894600247935981036396069)
  ·
    refine ⟨20230237546487996444324263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107894600247935981036396069 20230237546487996444324263)
    ·
      refine ⟨30345356319731994666486395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20230237546487996444324263 30345356319731994666486395)
      ·
        refine ⟨45518034479597991999729593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30345356319731994666486395 45518034479597991999729593)
        ·
          refine ⟨34138525859698493999797195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45518034479597991999729593 34138525859698493999797195)
          ·
            refine ⟨51207788789547740999695793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34138525859698493999797195 51207788789547740999695793)
            ·
              refine ⟨38405841592160805749771845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51207788789547740999695793 38405841592160805749771845)
              ·
                refine ⟨7201095298530151078082221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38405841592160805749771845 7201095298530151078082221)
                ·
                  refine ⟨2700410736948806654280833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7201095298530151078082221 2700410736948806654280833)
                  ·
                    refine ⟨2025308052711604990710625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2700410736948806654280833 2025308052711604990710625)
                    ·
                      refine ⟨1518981039533703743032969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025308052711604990710625 1518981039533703743032969)
                      ·
                        rfl

theorem cell23_2958205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_2958205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958205 prefixEnd_2958205 := by exact prefixLift 2958205
  have htrace : WordTrace (prefixWord ++ tailWord_2958205) baseStart_2958205 baseEnd_2958205 := by
    simpa [prefixWord, tailWord_2958205, baseEnd_2958205] using wordTrace_append hprefix tailTrace_2958205
  have hstable : (prefixWord ++ tailWord_2958205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958205).length < 2 ^ (prefixWord ++ tailWord_2958205).sum := by decide
  have hdescent : baseEnd_2958205 < baseStart_2958205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958208 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 3]
def baseStart_2958208 : Nat := 118140960795 + 2958208 * 2 ^ 59
def prefixEnd_2958208 : Nat := 4983230072969 + 3 ^ 40 * 2958208 * 2
def baseEnd_2958208 : Nat := 1518982579975667231295455

theorem tailTrace_2958208 : CollatzResearch.WordTrace tailWord_2958208 prefixEnd_2958208 1518982579975667231295455 := by
  unfold tailWord_2958208
  simp only [CollatzResearch.WordTrace]
  refine ⟨53947354833462556274377639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71929806444616741699170185 53947354833462556274377639)
  ·
    refine ⟨80921032250193834411566459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53947354833462556274377639 80921032250193834411566459)
    ·
      refine ⟨121381548375290751617349689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80921032250193834411566459 121381548375290751617349689)
      ·
        refine ⟨91036161281468063713012267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121381548375290751617349689 91036161281468063713012267)
        ·
          refine ⟨136554241922202095569518401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91036161281468063713012267 136554241922202095569518401)
          ·
            refine ⟨102415681441651571677138801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136554241922202095569518401 102415681441651571677138801)
            ·
              refine ⟨76811761081238678757854101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102415681441651571677138801 76811761081238678757854101)
              ·
                refine ⟨3600551300683063066774411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76811761081238678757854101 3600551300683063066774411)
                ·
                  refine ⟨5400826951024594600161617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600551300683063066774411 5400826951024594600161617)
                  ·
                    refine ⟨4050620213268445950121213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5400826951024594600161617 4050620213268445950121213)
                    ·
                      refine ⟨1518982579975667231295455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4050620213268445950121213 1518982579975667231295455)
                      ·
                        rfl

theorem cell23_2958208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_2958208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958208 prefixEnd_2958208 := by exact prefixLift 2958208
  have htrace : WordTrace (prefixWord ++ tailWord_2958208) baseStart_2958208 baseEnd_2958208 := by
    simpa [prefixWord, tailWord_2958208, baseEnd_2958208] using wordTrace_append hprefix tailTrace_2958208
  have hstable : (prefixWord ++ tailWord_2958208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958208).length < 2 ^ (prefixWord ++ tailWord_2958208).sum := by decide
  have hdescent : baseEnd_2958208 < baseStart_2958208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958218 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2958218 : Nat := 118140960795 + 2958218 * 2 ^ 59
def prefixEnd_2958218 : Nat := 4983230072969 + 3 ^ 40 * 2958218 * 2
def baseEnd_2958218 : Nat := 1518987714782212192170409

theorem tailTrace_2958218 : CollatzResearch.WordTrace tailWord_2958218 prefixEnd_2958218 1518987714782212192170409 := by
  unfold tailWord_2958218
  simp only [CollatzResearch.WordTrace]
  refine ⟨26973768599222221064154827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71930049597925922837746205 26973768599222221064154827)
  ·
    refine ⟨40460652898833331596232241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26973768599222221064154827 40460652898833331596232241)
    ·
      refine ⟨30345489674124998697174181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40460652898833331596232241 30345489674124998697174181)
      ·
        refine ⟨5689779313898437255720159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30345489674124998697174181 5689779313898437255720159)
        ·
          refine ⟨8534668970847655883580239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5689779313898437255720159 8534668970847655883580239)
          ·
            refine ⟨12802003456271483825370359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8534668970847655883580239 12802003456271483825370359)
            ·
              refine ⟨19203005184407225738055539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12802003456271483825370359 19203005184407225738055539)
              ·
                refine ⟨28804507776610838607083309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19203005184407225738055539 28804507776610838607083309)
                ·
                  refine ⟨10801690416229064477656241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28804507776610838607083309 10801690416229064477656241)
                  ·
                    refine ⟨8101267812171798358242181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10801690416229064477656241 8101267812171798358242181)
                    ·
                      refine ⟨1518987714782212192170409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8101267812171798358242181 1518987714782212192170409)
                      ·
                        rfl

theorem cell23_2958218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2958218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958218 prefixEnd_2958218 := by exact prefixLift 2958218
  have htrace : WordTrace (prefixWord ++ tailWord_2958218) baseStart_2958218 baseEnd_2958218 := by
    simpa [prefixWord, tailWord_2958218, baseEnd_2958218] using wordTrace_append hprefix tailTrace_2958218
  have hstable : (prefixWord ++ tailWord_2958218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958218).length < 2 ^ (prefixWord ++ tailWord_2958218).sum := by decide
  have hdescent : baseEnd_2958218 < baseStart_2958218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958239 : List Nat := [1, 1, 2, 5, 2, 2, 1, 4, 1, 2, 2]
def baseStart_2958239 : Nat := 118140960795 + 2958239 * 2 ^ 59
def prefixEnd_2958239 : Nat := 4983230072969 + 3 ^ 40 * 2958239 * 2
def baseEnd_2958239 : Nat := 1518998497875956610007813

theorem tailTrace_2958239 : CollatzResearch.WordTrace tailWord_2958239 prefixEnd_2958239 1518998497875956610007813 := by
  unfold tailWord_2958239
  simp only [CollatzResearch.WordTrace]
  refine ⟨107895840329812804843133771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71930560219875203228755847 107895840329812804843133771)
  ·
    refine ⟨161843760494719207264700657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107895840329812804843133771 161843760494719207264700657)
    ·
      refine ⟨121382820371039405448525493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161843760494719207264700657 121382820371039405448525493)
      ·
        refine ⟨11379639409784944260799265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121382820371039405448525493 11379639409784944260799265)
        ·
          refine ⟨8534729557338708195599449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11379639409784944260799265 8534729557338708195599449)
          ·
            refine ⟨6401047168004031146699587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8534729557338708195599449 6401047168004031146699587)
            ·
              refine ⟨9601570752006046720049381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6401047168004031146699587 9601570752006046720049381)
              ·
                refine ⟨1800294516001133760009259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9601570752006046720049381 1800294516001133760009259)
                ·
                  refine ⟨2700441774001700640013889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800294516001133760009259 2700441774001700640013889)
                  ·
                    refine ⟨2025331330501275480010417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2700441774001700640013889 2025331330501275480010417)
                    ·
                      refine ⟨1518998497875956610007813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025331330501275480010417 1518998497875956610007813)
                      ·
                        rfl

theorem cell23_2958239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_2958239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958239 prefixEnd_2958239 := by exact prefixLift 2958239
  have htrace : WordTrace (prefixWord ++ tailWord_2958239) baseStart_2958239 baseEnd_2958239 := by
    simpa [prefixWord, tailWord_2958239, baseEnd_2958239] using wordTrace_append hprefix tailTrace_2958239
  have hstable : (prefixWord ++ tailWord_2958239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958239).length < 2 ^ (prefixWord ++ tailWord_2958239).sum := by decide
  have hdescent : baseEnd_2958239 < baseStart_2958239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958265 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 3, 3, 2]
def baseStart_2958265 : Nat := 118140960795 + 2958265 * 2 ^ 59
def prefixEnd_2958265 : Nat := 4983230072969 + 3 ^ 40 * 2958265 * 2
def baseEnd_2958265 : Nat := 1519011848372973508282693

theorem tailTrace_2958265 : CollatzResearch.WordTrace tailWord_2958265 prefixEnd_2958265 1519011848372973508282693 := by
  unfold tailWord_2958265
  simp only [CollatzResearch.WordTrace]
  refine ⟨107896788627718611283580249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71931192418479074189053499 107896788627718611283580249)
  ·
    refine ⟨80922591470788958462685187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107896788627718611283580249 80922591470788958462685187)
    ·
      refine ⟨121383887206183437694027781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80922591470788958462685187 121383887206183437694027781)
      ·
        refine ⟨22759478851159394567630209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121383887206183437694027781 22759478851159394567630209)
        ·
          refine ⟨17069609138369545925722657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22759478851159394567630209 17069609138369545925722657)
          ·
            refine ⟨12802206853777159444291993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17069609138369545925722657 12802206853777159444291993)
            ·
              refine ⟨9601655140332869583218995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12802206853777159444291993 9601655140332869583218995)
              ·
                refine ⟨14402482710499304374828493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9601655140332869583218995 14402482710499304374828493)
                ·
                  refine ⟨5400931016437239140560685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14402482710499304374828493 5400931016437239140560685)
                  ·
                    refine ⟨2025349131163964677710257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5400931016437239140560685 2025349131163964677710257)
                    ·
                      refine ⟨1519011848372973508282693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025349131163964677710257 1519011848372973508282693)
                      ·
                        rfl

theorem cell23_2958265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_2958265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958265 prefixEnd_2958265 := by exact prefixLift 2958265
  have htrace : WordTrace (prefixWord ++ tailWord_2958265) baseStart_2958265 baseEnd_2958265 := by
    simpa [prefixWord, tailWord_2958265, baseEnd_2958265] using wordTrace_append hprefix tailTrace_2958265
  have hstable : (prefixWord ++ tailWord_2958265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958265).length < 2 ^ (prefixWord ++ tailWord_2958265).sum := by decide
  have hdescent : baseEnd_2958265 < baseStart_2958265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958276 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2958276 : Nat := 118140960795 + 2958276 * 2 ^ 59
def prefixEnd_2958276 : Nat := 4983230072969 + 3 ^ 40 * 2958276 * 2
def baseEnd_2958276 : Nat := 1519017496660172965245143

theorem tailTrace_2958276 : CollatzResearch.WordTrace tailWord_2958276 prefixEnd_2958276 1519017496660172965245143 := by
  unfold tailWord_2958276
  simp only [CollatzResearch.WordTrace]
  refine ⟨53948594915339380081115341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71931459887119173441487121 53948594915339380081115341)
  ·
    refine ⟨20230723093252267530418253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53948594915339380081115341 20230723093252267530418253)
    ·
      refine ⟨7586521159969600323906845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20230723093252267530418253 7586521159969600323906845)
      ·
        refine ⟨2844945434988600121465067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7586521159969600323906845 2844945434988600121465067)
        ·
          refine ⟨4267418152482900182197601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2844945434988600121465067 4267418152482900182197601)
          ·
            refine ⟨3200563614362175136648201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4267418152482900182197601 3200563614362175136648201)
            ·
              refine ⟨2400422710771631352486151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3200563614362175136648201 2400422710771631352486151)
              ·
                refine ⟨3600634066157447028729227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400422710771631352486151 3600634066157447028729227)
                ·
                  refine ⟨5400951099236170543093841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600634066157447028729227 5400951099236170543093841)
                  ·
                    refine ⟨4050713324427127907320381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5400951099236170543093841 4050713324427127907320381)
                    ·
                      refine ⟨1519017496660172965245143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4050713324427127907320381 1519017496660172965245143)
                      ·
                        rfl

theorem cell23_2958276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2958276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958276 prefixEnd_2958276 := by exact prefixLift 2958276
  have htrace : WordTrace (prefixWord ++ tailWord_2958276) baseStart_2958276 baseEnd_2958276 := by
    simpa [prefixWord, tailWord_2958276, baseEnd_2958276] using wordTrace_append hprefix tailTrace_2958276
  have hstable : (prefixWord ++ tailWord_2958276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958276).length < 2 ^ (prefixWord ++ tailWord_2958276).sum := by decide
  have hdescent : baseEnd_2958276 < baseStart_2958276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958306 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_2958306 : Nat := 118140960795 + 2958306 * 2 ^ 59
def prefixEnd_2958306 : Nat := 4983230072969 + 3 ^ 40 * 2958306 * 2
def baseEnd_2958306 : Nat := 1519032901079807847870005

theorem tailTrace_2958306 : CollatzResearch.WordTrace tailWord_2958306 prefixEnd_2958306 1519032901079807847870005 := by
  unfold tailWord_2958306
  simp only [CollatzResearch.WordTrace]
  refine ⟨26974571005142518821455693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71932189347046716857215181 26974571005142518821455693)
  ·
    refine ⟨10115464126928444558045885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26974571005142518821455693 10115464126928444558045885)
    ·
      refine ⟨3793299047598166709267207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10115464126928444558045885 3793299047598166709267207)
      ·
        refine ⟨5689948571397250063900811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793299047598166709267207 5689948571397250063900811)
        ·
          refine ⟨8534922857095875095851217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5689948571397250063900811 8534922857095875095851217)
          ·
            refine ⟨6401192142821906321888413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8534922857095875095851217 6401192142821906321888413)
            ·
              refine ⟨2400447053558214870708155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6401192142821906321888413 2400447053558214870708155)
              ·
                refine ⟨3600670580337322306062233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400447053558214870708155 3600670580337322306062233)
                ·
                  refine ⟨2700502935252991729546675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3600670580337322306062233 2700502935252991729546675)
                  ·
                    refine ⟨4050754402879487594320013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2700502935252991729546675 4050754402879487594320013)
                    ·
                      refine ⟨1519032901079807847870005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4050754402879487594320013 1519032901079807847870005)
                      ·
                        rfl

theorem cell23_2958306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_2958306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958306 prefixEnd_2958306 := by exact prefixLift 2958306
  have htrace : WordTrace (prefixWord ++ tailWord_2958306) baseStart_2958306 baseEnd_2958306 := by
    simpa [prefixWord, tailWord_2958306, baseEnd_2958306] using wordTrace_append hprefix tailTrace_2958306
  have hstable : (prefixWord ++ tailWord_2958306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958306).length < 2 ^ (prefixWord ++ tailWord_2958306).sum := by decide
  have hdescent : baseEnd_2958306 < baseStart_2958306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958312 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_2958312 : Nat := 118140960795 + 2958312 * 2 ^ 59
def prefixEnd_2958312 : Nat := 4983230072969 + 3 ^ 40 * 2958312 * 2
def baseEnd_2958312 : Nat := 1519035981963734824394977

theorem tailTrace_2958312 : CollatzResearch.WordTrace tailWord_2958312 prefixEnd_2958312 1519035981963734824394977 := by
  unfold tailWord_2958312
  simp only [CollatzResearch.WordTrace]
  refine ⟨53949251429274169155270595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71932335239032225540360793 53949251429274169155270595)
  ·
    refine ⟨80923877143911253732905893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53949251429274169155270595 80923877143911253732905893)
    ·
      refine ⟨15173226964483360074919855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80923877143911253732905893 15173226964483360074919855)
      ·
        refine ⟨22759840446725040112379783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15173226964483360074919855 22759840446725040112379783)
        ·
          refine ⟨34139760670087560168569675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22759840446725040112379783 34139760670087560168569675)
          ·
            refine ⟨51209641005131340252854513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34139760670087560168569675 51209641005131340252854513)
            ·
              refine ⟨38407230753848505189640885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51209641005131340252854513 38407230753848505189640885)
              ·
                refine ⟨3600677883173297361528833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38407230753848505189640885 3600677883173297361528833)
                ·
                  refine ⟨2700508412379973021146625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3600677883173297361528833 2700508412379973021146625)
                  ·
                    refine ⟨2025381309284979765859969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2700508412379973021146625 2025381309284979765859969)
                    ·
                      refine ⟨1519035981963734824394977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025381309284979765859969 1519035981963734824394977)
                      ·
                        rfl

theorem cell23_2958312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_2958312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958312 prefixEnd_2958312 := by exact prefixLift 2958312
  have htrace : WordTrace (prefixWord ++ tailWord_2958312) baseStart_2958312 baseEnd_2958312 := by
    simpa [prefixWord, tailWord_2958312, baseEnd_2958312] using wordTrace_append hprefix tailTrace_2958312
  have hstable : (prefixWord ++ tailWord_2958312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958312).length < 2 ^ (prefixWord ++ tailWord_2958312).sum := by decide
  have hdescent : baseEnd_2958312 < baseStart_2958312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958324 : List Nat := [2, 6, 2, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2958324 : Nat := 118140960795 + 2958324 * 2 ^ 59
def prefixEnd_2958324 : Nat := 4983230072969 + 3 ^ 40 * 2958324 * 2
def baseEnd_2958324 : Nat := 1519042143731588777444923

theorem tailTrace_2958324 : CollatzResearch.WordTrace tailWord_2958324 prefixEnd_2958324 1519042143731588777444923 := by
  unfold tailWord_2958324
  simp only [CollatzResearch.WordTrace]
  refine ⟨53949470267252432179989013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71932627023003242906652017 53949470267252432179989013)
  ·
    refine ⟨2528881418777457758436985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53949470267252432179989013 2528881418777457758436985)
    ·
      refine ⟨1896661064083093318827739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2528881418777457758436985 1896661064083093318827739)
      ·
        refine ⟨2844991596124639978241609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1896661064083093318827739 2844991596124639978241609)
        ·
          refine ⟨2133743697093479983681207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2844991596124639978241609 2133743697093479983681207)
          ·
            refine ⟨3200615545640219975521811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2133743697093479983681207 3200615545640219975521811)
            ·
              refine ⟨4800923318460329963282717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200615545640219975521811 4800923318460329963282717)
              ·
                refine ⟨1800346244422623736231019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4800923318460329963282717 1800346244422623736231019)
                ·
                  refine ⟨2700519366633935604346529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800346244422623736231019 2700519366633935604346529)
                  ·
                    refine ⟨2025389524975451703259897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2700519366633935604346529 2025389524975451703259897)
                    ·
                      refine ⟨1519042143731588777444923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025389524975451703259897 1519042143731588777444923)
                      ·
                        rfl

theorem cell23_2958324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2958324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958324 prefixEnd_2958324 := by exact prefixLift 2958324
  have htrace : WordTrace (prefixWord ++ tailWord_2958324) baseStart_2958324 baseEnd_2958324 := by
    simpa [prefixWord, tailWord_2958324, baseEnd_2958324] using wordTrace_append hprefix tailTrace_2958324
  have hstable : (prefixWord ++ tailWord_2958324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958324).length < 2 ^ (prefixWord ++ tailWord_2958324).sum := by decide
  have hdescent : baseEnd_2958324 < baseStart_2958324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958348 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_2958348 : Nat := 118140960795 + 2958348 * 2 ^ 59
def prefixEnd_2958348 : Nat := 4983230072969 + 3 ^ 40 * 2958348 * 2
def baseEnd_2958348 : Nat := 506351489089098894514937

theorem tailTrace_2958348 : CollatzResearch.WordTrace tailWord_2958348 prefixEnd_2958348 506351489089098894514937 := by
  unfold tailWord_2958348
  simp only [CollatzResearch.WordTrace]
  refine ⟨53949907943208958229425849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71933210590945277639234465 53949907943208958229425849)
  ·
    refine ⟨40462430957406718672069387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53949907943208958229425849 40462430957406718672069387)
    ·
      refine ⟨60693646436110078008104081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40462430957406718672069387 60693646436110078008104081)
      ·
        refine ⟨45520234827082558506078061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60693646436110078008104081 45520234827082558506078061)
        ·
          refine ⟨17070088060155959439779273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45520234827082558506078061 17070088060155959439779273)
          ·
            refine ⟨12802566045116969579834455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17070088060155959439779273 12802566045116969579834455)
            ·
              refine ⟨19203849067675454369751683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12802566045116969579834455 19203849067675454369751683)
              ·
                refine ⟨28805773601513181554627525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19203849067675454369751683 28805773601513181554627525)
                ·
                  refine ⟨5401082550283721541492661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28805773601513181554627525 5401082550283721541492661)
                  ·
                    refine ⟨506351489089098894514937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5401082550283721541492661 506351489089098894514937)
                    ·
                      rfl

theorem cell23_2958348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_2958348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958348 prefixEnd_2958348 := by exact prefixLift 2958348
  have htrace : WordTrace (prefixWord ++ tailWord_2958348) baseStart_2958348 baseEnd_2958348 := by
    simpa [prefixWord, tailWord_2958348, baseEnd_2958348] using wordTrace_append hprefix tailTrace_2958348
  have hstable : (prefixWord ++ tailWord_2958348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958348).length < 2 ^ (prefixWord ++ tailWord_2958348).sum := by decide
  have hdescent : baseEnd_2958348 < baseStart_2958348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958385 : List Nat := [1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 4]
def baseStart_2958385 : Nat := 118140960795 + 2958385 * 2 ^ 59
def prefixEnd_2958385 : Nat := 4983230072969 + 3 ^ 40 * 2958385 * 2
def baseEnd_2958385 : Nat := 1519073466051513038782141

theorem tailTrace_2958385 : CollatzResearch.WordTrace tailWord_2958385 prefixEnd_2958385 1519073466051513038782141 := by
  unfold tailWord_2958385
  simp only [CollatzResearch.WordTrace]
  refine ⟨107901165387283871777948609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71934110258189247851965739 107901165387283871777948609)
  ·
    refine ⟨80925874040462903833461457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107901165387283871777948609 80925874040462903833461457)
    ·
      refine ⟨60694405530347177875096093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80925874040462903833461457 60694405530347177875096093)
      ·
        refine ⟨22760402073880191703161035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60694405530347177875096093 22760402073880191703161035)
        ·
          refine ⟨34140603110820287554741553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22760402073880191703161035 34140603110820287554741553)
          ·
            refine ⟨25605452333115215666056165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34140603110820287554741553 25605452333115215666056165)
            ·
              refine ⟨4801022312459102937385531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25605452333115215666056165 4801022312459102937385531)
              ·
                refine ⟨7201533468688654406078297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4801022312459102937385531 7201533468688654406078297)
                ·
                  refine ⟨5401150101516490804558723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7201533468688654406078297 5401150101516490804558723)
                  ·
                    refine ⟨8101725152274736206838085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5401150101516490804558723 8101725152274736206838085)
                    ·
                      refine ⟨1519073466051513038782141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8101725152274736206838085 1519073466051513038782141)
                      ·
                        rfl

theorem cell23_2958385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_2958385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958385 prefixEnd_2958385 := by exact prefixLift 2958385
  have htrace : WordTrace (prefixWord ++ tailWord_2958385) baseStart_2958385 baseEnd_2958385 := by
    simpa [prefixWord, tailWord_2958385, baseEnd_2958385] using wordTrace_append hprefix tailTrace_2958385
  have hstable : (prefixWord ++ tailWord_2958385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958385).length < 2 ^ (prefixWord ++ tailWord_2958385).sum := by decide
  have hdescent : baseEnd_2958385 < baseStart_2958385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958405 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 2, 2, 3]
def baseStart_2958405 : Nat := 118140960795 + 2958405 * 2 ^ 59
def prefixEnd_2958405 : Nat := 4983230072969 + 3 ^ 40 * 2958405 * 2
def baseEnd_2958405 : Nat := 1519083735664602960532049

theorem tailTrace_2958405 : CollatzResearch.WordTrace tailWord_2958405 prefixEnd_2958405 1519083735664602960532049 := by
  unfold tailWord_2958405
  simp only [CollatzResearch.WordTrace]
  refine ⟨107901894847211415193676669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71934596564807610129117779 107901894847211415193676669)
  ·
    refine ⟨40463210567704280697628751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107901894847211415193676669 40463210567704280697628751)
    ·
      refine ⟨60694815851556421046443127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40463210567704280697628751 60694815851556421046443127)
      ·
        refine ⟨91042223777334631569664691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60694815851556421046443127 91042223777334631569664691)
        ·
          refine ⟨136563335666001947354497037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91042223777334631569664691 136563335666001947354497037)
          ·
            refine ⟨51211250874750730257936389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136563335666001947354497037 51211250874750730257936389)
            ·
              refine ⟨9602109539015761923363073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51211250874750730257936389 9602109539015761923363073)
              ·
                refine ⟨7201582154261821442522305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9602109539015761923363073 7201582154261821442522305)
                ·
                  refine ⟨5401186615696366081891729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7201582154261821442522305 5401186615696366081891729)
                  ·
                    refine ⟨4050889961772274561418797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5401186615696366081891729 4050889961772274561418797)
                    ·
                      refine ⟨1519083735664602960532049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4050889961772274561418797 1519083735664602960532049)
                      ·
                        rfl

theorem cell23_2958405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_2958405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958405 prefixEnd_2958405 := by exact prefixLift 2958405
  have htrace : WordTrace (prefixWord ++ tailWord_2958405) baseStart_2958405 baseEnd_2958405 := by
    simpa [prefixWord, tailWord_2958405, baseEnd_2958405] using wordTrace_append hprefix tailTrace_2958405
  have hstable : (prefixWord ++ tailWord_2958405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958405).length < 2 ^ (prefixWord ++ tailWord_2958405).sum := by decide
  have hdescent : baseEnd_2958405 < baseStart_2958405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958429 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2958429 : Nat := 118140960795 + 2958429 * 2 ^ 59
def prefixEnd_2958429 : Nat := 4983230072969 + 3 ^ 40 * 2958429 * 2
def baseEnd_2958429 : Nat := 506365353066770288877313

theorem tailTrace_2958429 : CollatzResearch.WordTrace tailWord_2958429 prefixEnd_2958429 506365353066770288877313 := by
  unfold tailWord_2958429
  simp only [CollatzResearch.WordTrace]
  refine ⟨107902770199124467292550341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71935180132749644861700227 107902770199124467292550341)
  ·
    refine ⟨20231769412335837617353189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107902770199124467292550341 20231769412335837617353189)
    ·
      refine ⟨3793456764812969553253723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20231769412335837617353189 3793456764812969553253723)
      ·
        refine ⟨5690185147219454329880585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3793456764812969553253723 5690185147219454329880585)
        ·
          refine ⟨4267638860414590747410439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5690185147219454329880585 4267638860414590747410439)
          ·
            refine ⟨6401458290621886121115659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267638860414590747410439 6401458290621886121115659)
            ·
              refine ⟨9602187435932829181673489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6401458290621886121115659 9602187435932829181673489)
              ·
                refine ⟨7201640576949621886255117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9602187435932829181673489 7201640576949621886255117)
                ·
                  refine ⟨2700615216356108207345669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7201640576949621886255117 2700615216356108207345669)
                  ·
                    refine ⟨506365353066770288877313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2700615216356108207345669 506365353066770288877313)
                    ·
                      rfl

theorem cell23_2958429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2958429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958429 prefixEnd_2958429 := by exact prefixLift 2958429
  have htrace : WordTrace (prefixWord ++ tailWord_2958429) baseStart_2958429 baseEnd_2958429 := by
    simpa [prefixWord, tailWord_2958429, baseEnd_2958429] using wordTrace_append hprefix tailTrace_2958429
  have hstable : (prefixWord ++ tailWord_2958429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958429).length < 2 ^ (prefixWord ++ tailWord_2958429).sum := by decide
  have hdescent : baseEnd_2958429 < baseStart_2958429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958455 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 1, 5]
def baseStart_2958455 : Nat := 118140960795 + 2958455 * 2 ^ 59
def prefixEnd_2958455 : Nat := 4983230072969 + 3 ^ 40 * 2958455 * 2
def baseEnd_2958455 : Nat := 506369803232442588302273

theorem tailTrace_2958455 : CollatzResearch.WordTrace tailWord_2958455 prefixEnd_2958455 506369803232442588302273 := by
  unfold tailWord_2958455
  simp only [CollatzResearch.WordTrace]
  refine ⟨107903718497030273732996819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71935812331353515821997879 107903718497030273732996819)
  ·
    refine ⟨161855577745545410599495229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107903718497030273732996819 161855577745545410599495229)
    ·
      refine ⟨60695841654579528974810711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161855577745545410599495229 60695841654579528974810711)
      ·
        refine ⟨91043762481869293462216067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60695841654579528974810711 91043762481869293462216067)
        ·
          refine ⟨136565643722803940193324101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91043762481869293462216067 136565643722803940193324101)
          ·
            refine ⟨25606058198025738786248269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136565643722803940193324101 25606058198025738786248269)
            ·
              refine ⟨9602271824259652044843101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25606058198025738786248269 9602271824259652044843101)
              ·
                refine ⟨3600851934097369516816163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9602271824259652044843101 3600851934097369516816163)
                ·
                  refine ⟨5401277901146054275224245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600851934097369516816163 5401277901146054275224245)
                  ·
                    refine ⟨506369803232442588302273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5401277901146054275224245 506369803232442588302273)
                    ·
                      rfl

theorem cell23_2958455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_2958455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958455 prefixEnd_2958455 := by exact prefixLift 2958455
  have htrace : WordTrace (prefixWord ++ tailWord_2958455) baseStart_2958455 baseEnd_2958455 := by
    simpa [prefixWord, tailWord_2958455, baseEnd_2958455] using wordTrace_append hprefix tailTrace_2958455
  have hstable : (prefixWord ++ tailWord_2958455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958455).length < 2 ^ (prefixWord ++ tailWord_2958455).sum := by decide
  have hdescent : baseEnd_2958455 < baseStart_2958455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958469 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 3, 1, 3]
def baseStart_2958469 : Nat := 118140960795 + 2958469 * 2 ^ 59
def prefixEnd_2958469 : Nat := 4983230072969 + 3 ^ 40 * 2958469 * 2
def baseEnd_2958469 : Nat := 1519116598426490710131755

theorem tailTrace_2958469 : CollatzResearch.WordTrace tailWord_2958469 prefixEnd_2958469 1519116598426490710131755 := by
  unfold tailWord_2958469
  simp only [CollatzResearch.WordTrace]
  refine ⟨107904229118979554124006461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71936152745986369416004307 107904229118979554124006461)
  ·
    refine ⟨40464085919617332796502423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107904229118979554124006461 40464085919617332796502423)
    ·
      refine ⟨60696128879425999194753635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40464085919617332796502423 60696128879425999194753635)
      ·
        refine ⟨91044193319138998792130453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60696128879425999194753635 91044193319138998792130453)
        ·
          refine ⟨4267696561834640568381115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91044193319138998792130453 4267696561834640568381115)
          ·
            refine ⟨6401544842751960852571673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267696561834640568381115 6401544842751960852571673)
            ·
              refine ⟨4801158632063970639428755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6401544842751960852571673 4801158632063970639428755)
              ·
                refine ⟨7201737948095955959143133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4801158632063970639428755 7201737948095955959143133)
                ·
                  refine ⟨2700651730535983484678675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7201737948095955959143133 2700651730535983484678675)
                  ·
                    refine ⟨4050977595803975227018013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2700651730535983484678675 4050977595803975227018013)
                    ·
                      refine ⟨1519116598426490710131755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4050977595803975227018013 1519116598426490710131755)
                      ·
                        rfl

theorem cell23_2958469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_2958469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958469 prefixEnd_2958469 := by exact prefixLift 2958469
  have htrace : WordTrace (prefixWord ++ tailWord_2958469) baseStart_2958469 baseEnd_2958469 := by
    simpa [prefixWord, tailWord_2958469, baseEnd_2958469] using wordTrace_append hprefix tailTrace_2958469
  have hstable : (prefixWord ++ tailWord_2958469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958469).length < 2 ^ (prefixWord ++ tailWord_2958469).sum := by decide
  have hdescent : baseEnd_2958469 < baseStart_2958469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958492 : List Nat := [2, 2, 3, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2958492 : Nat := 118140960795 + 2958492 * 2 ^ 59
def prefixEnd_2958492 : Nat := 4983230072969 + 3 ^ 40 * 2958492 * 2
def baseEnd_2958492 : Nat := 1519128408481544120144149

theorem tailTrace_2958492 : CollatzResearch.WordTrace tailWord_2958492 prefixEnd_2958492 1519128408481544120144149 := by
  unfold tailWord_2958492
  simp only [CollatzResearch.WordTrace]
  refine ⟨53952533998948114526046865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71936711998597486034729153 53952533998948114526046865)
  ·
    refine ⟨40464400499211085894535149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53952533998948114526046865 40464400499211085894535149)
    ·
      refine ⟨15174150187204157210450681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40464400499211085894535149 15174150187204157210450681)
      ·
        refine ⟨11380612640403117907838011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15174150187204157210450681 11380612640403117907838011)
        ·
          refine ⟨17070918960604676861757017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11380612640403117907838011 17070918960604676861757017)
          ·
            refine ⟨12803189220453507646317763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17070918960604676861757017 12803189220453507646317763)
            ·
              refine ⟨19204783830680261469476645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12803189220453507646317763 19204783830680261469476645)
              ·
                refine ⟨3600896968252549025526871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19204783830680261469476645 3600896968252549025526871)
                ·
                  refine ⟨5401345452378823538290307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3600896968252549025526871 5401345452378823538290307)
                  ·
                    refine ⟨8102018178568235307435461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5401345452378823538290307 8102018178568235307435461)
                    ·
                      refine ⟨1519128408481544120144149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8102018178568235307435461 1519128408481544120144149)
                      ·
                        rfl

theorem cell23_2958492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2958492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958492 prefixEnd_2958492 := by exact prefixLift 2958492
  have htrace : WordTrace (prefixWord ++ tailWord_2958492) baseStart_2958492 baseEnd_2958492 := by
    simpa [prefixWord, tailWord_2958492, baseEnd_2958492] using wordTrace_append hprefix tailTrace_2958492
  have hstable : (prefixWord ++ tailWord_2958492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958492).length < 2 ^ (prefixWord ++ tailWord_2958492).sum := by decide
  have hdescent : baseEnd_2958492 < baseStart_2958492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958503 : List Nat := [1, 1, 6, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_2958503 : Nat := 118140960795 + 2958503 * 2 ^ 59
def prefixEnd_2958503 : Nat := 4983230072969 + 3 ^ 40 * 2958503 * 2
def baseEnd_2958503 : Nat := 1519134056768743577106599

theorem tailTrace_2958503 : CollatzResearch.WordTrace tailWord_2958503 prefixEnd_2958503 1519134056768743577106599 := by
  unfold tailWord_2958503
  simp only [CollatzResearch.WordTrace]
  refine ⟨107905469200856377930744163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71936979467237585287162775 107905469200856377930744163)
  ·
    refine ⟨161858203801284566896116245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107905469200856377930744163 161858203801284566896116245)
    ·
      refine ⟨7587103303185214073255449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 161858203801284566896116245 7587103303185214073255449)
      ·
        refine ⟨5690327477388910554941587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7587103303185214073255449 5690327477388910554941587)
        ·
          refine ⟨8535491216083365832412381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5690327477388910554941587 8535491216083365832412381)
          ·
            refine ⟨3200809206031262187154643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8535491216083365832412381 3200809206031262187154643)
            ·
              refine ⟨4801213809046893280731965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3200809206031262187154643 4801213809046893280731965)
              ·
                refine ⟨1800455178392584980274487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4801213809046893280731965 1800455178392584980274487)
                ·
                  refine ⟨2700682767588877470411731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800455178392584980274487 2700682767588877470411731)
                  ·
                    refine ⟨4051024151383316205617597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2700682767588877470411731 4051024151383316205617597)
                    ·
                      refine ⟨1519134056768743577106599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4051024151383316205617597 1519134056768743577106599)
                      ·
                        rfl

theorem cell23_2958503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_2958503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958503 prefixEnd_2958503 := by exact prefixLift 2958503
  have htrace : WordTrace (prefixWord ++ tailWord_2958503) baseStart_2958503 baseEnd_2958503 := by
    simpa [prefixWord, tailWord_2958503, baseEnd_2958503] using wordTrace_append hprefix tailTrace_2958503
  have hstable : (prefixWord ++ tailWord_2958503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958503).length < 2 ^ (prefixWord ++ tailWord_2958503).sum := by decide
  have hdescent : baseEnd_2958503 < baseStart_2958503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958526 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_2958526 : Nat := 118140960795 + 2958526 * 2 ^ 59
def prefixEnd_2958526 : Nat := 4983230072969 + 3 ^ 40 * 2958526 * 2
def baseEnd_2958526 : Nat := 1519145866823796987118993

theorem tailTrace_2958526 : CollatzResearch.WordTrace tailWord_2958526 prefixEnd_2958526 1519145866823796987118993 := by
  unfold tailWord_2958526
  simp only [CollatzResearch.WordTrace]
  refine ⟨13488288509971631607353929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71937538719848701905887621 13488288509971631607353929)
  ·
    refine ⟨10116216382478723705515447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13488288509971631607353929 10116216382478723705515447)
    ·
      refine ⟨15174324573718085558273171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10116216382478723705515447 15174324573718085558273171)
      ·
        refine ⟨22761486860577128337409757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15174324573718085558273171 22761486860577128337409757)
        ·
          refine ⟨8535557572716423126528659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22761486860577128337409757 8535557572716423126528659)
          ·
            refine ⟨12803336359074634689792989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8535557572716423126528659 12803336359074634689792989)
            ·
              refine ⟨4801251134652988008672371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12803336359074634689792989 4801251134652988008672371)
              ·
                refine ⟨7201876701979482013008557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4801251134652988008672371 7201876701979482013008557)
                ·
                  refine ⟨2700703763242305754878209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7201876701979482013008557 2700703763242305754878209)
                  ·
                    refine ⟨2025527822431729316158657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2700703763242305754878209 2025527822431729316158657)
                    ·
                      refine ⟨1519145866823796987118993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025527822431729316158657 1519145866823796987118993)
                      ·
                        rfl

theorem cell23_2958526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_2958526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958526 prefixEnd_2958526 := by exact prefixLift 2958526
  have htrace : WordTrace (prefixWord ++ tailWord_2958526) baseStart_2958526 baseEnd_2958526 := by
    simpa [prefixWord, tailWord_2958526, baseEnd_2958526] using wordTrace_append hprefix tailTrace_2958526
  have hstable : (prefixWord ++ tailWord_2958526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958526).length < 2 ^ (prefixWord ++ tailWord_2958526).sum := by decide
  have hdescent : baseEnd_2958526 < baseStart_2958526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958532 : List Nat := [2, 3, 3, 1, 3, 1, 2, 8]
def baseStart_2958532 : Nat := 118140960795 + 2958532 * 2 ^ 59
def prefixEnd_2958532 : Nat := 4983230072969 + 3 ^ 40 * 2958532 * 2
def baseEnd_2958532 : Nat := 56264775841026813468295

theorem tailTrace_2958532 : CollatzResearch.WordTrace tailWord_2958532 prefixEnd_2958532 56264775841026813468295 := by
  unfold tailWord_2958532
  simp only [CollatzResearch.WordTrace]
  refine ⟨53953263458875657941774925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71937684611834210589033233 53953263458875657941774925)
  ·
    refine ⟨20232473797078371728165597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53953263458875657941774925 20232473797078371728165597)
    ·
      refine ⟨7587177673904389398062099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20232473797078371728165597 7587177673904389398062099)
      ·
        refine ⟨11380766510856584097093149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7587177673904389398062099 11380766510856584097093149)
        ·
          refine ⟨4267787441571219036409931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11380766510856584097093149 4267787441571219036409931)
          ·
            refine ⟨6401681162356828554614897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4267787441571219036409931 6401681162356828554614897)
            ·
              refine ⟨4801260871767621415961173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6401681162356828554614897 4801260871767621415961173)
              ·
                refine ⟨56264775841026813468295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4801260871767621415961173 56264775841026813468295)
                ·
                  rfl

theorem cell23_2958532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 8].length) (baseStart_2958532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958532 prefixEnd_2958532 := by exact prefixLift 2958532
  have htrace : WordTrace (prefixWord ++ tailWord_2958532) baseStart_2958532 baseEnd_2958532 := by
    simpa [prefixWord, tailWord_2958532, baseEnd_2958532] using wordTrace_append hprefix tailTrace_2958532
  have hstable : (prefixWord ++ tailWord_2958532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958532).length < 2 ^ (prefixWord ++ tailWord_2958532).sum := by decide
  have hdescent : baseEnd_2958532 < baseStart_2958532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958585 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 1, 6, 3]
def baseStart_2958585 : Nat := 118140960795 + 2958585 * 2 ^ 59
def prefixEnd_2958585 : Nat := 4983230072969 + 3 ^ 40 * 2958585 * 2
def baseEnd_2958585 : Nat := 1519176162182412256281221

theorem tailTrace_2958585 : CollatzResearch.WordTrace tailWord_2958585 prefixEnd_2958585 1519176162182412256281221 := by
  unfold tailWord_2958585
  simp only [CollatzResearch.WordTrace]
  refine ⟨107908459986559305935229209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71938973324372870623486139 107908459986559305935229209)
  ·
    refine ⟨80931344989919479451421907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107908459986559305935229209 80931344989919479451421907)
    ·
      refine ⟨121397017484879219177132861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80931344989919479451421907 121397017484879219177132861)
      ·
        refine ⟨45523881556829707191424823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121397017484879219177132861 45523881556829707191424823)
        ·
          refine ⟨68285822335244560787137235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45523881556829707191424823 68285822335244560787137235)
          ·
            refine ⟨102428733502866841180705853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68285822335244560787137235 102428733502866841180705853)
            ·
              refine ⟨38410775063575065442764695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102428733502866841180705853 38410775063575065442764695)
              ·
                refine ⟨57616162595362598164147043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38410775063575065442764695 57616162595362598164147043)
                ·
                  refine ⟨86424243893043897246220565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57616162595362598164147043 86424243893043897246220565)
                  ·
                    refine ⟨4051136432486432683416589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86424243893043897246220565 4051136432486432683416589)
                    ·
                      refine ⟨1519176162182412256281221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4051136432486432683416589 1519176162182412256281221)
                      ·
                        rfl

theorem cell23_2958585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_2958585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958585 prefixEnd_2958585 := by exact prefixLift 2958585
  have htrace : WordTrace (prefixWord ++ tailWord_2958585) baseStart_2958585 baseEnd_2958585 := by
    simpa [prefixWord, tailWord_2958585, baseEnd_2958585] using wordTrace_append hprefix tailTrace_2958585
  have hstable : (prefixWord ++ tailWord_2958585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958585).length < 2 ^ (prefixWord ++ tailWord_2958585).sum := by decide
  have hdescent : baseEnd_2958585 < baseStart_2958585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958595 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 4]
def baseStart_2958595 : Nat := 118140960795 + 2958595 * 2 ^ 59
def prefixEnd_2958595 : Nat := 4983230072969 + 3 ^ 40 * 2958595 * 2
def baseEnd_2958595 : Nat := 1519181296988957217156175

theorem tailTrace_2958595 : CollatzResearch.WordTrace tailWord_2958595 prefixEnd_2958595 1519181296988957217156175 := by
  unfold tailWord_2958595
  simp only [CollatzResearch.WordTrace]
  refine ⟨107908824716523077643093239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71939216477682051762062159 107908824716523077643093239)
  ·
    refine ⟨161863237074784616464639859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107908824716523077643093239 161863237074784616464639859)
    ·
      refine ⟨242794855612176924696959789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161863237074784616464639859 242794855612176924696959789)
      ·
        refine ⟨91048070854566346761359921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242794855612176924696959789 91048070854566346761359921)
        ·
          refine ⟨68286053140924760071019941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91048070854566346761359921 68286053140924760071019941)
          ·
            refine ⟨12803634963923392513316239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68286053140924760071019941 12803634963923392513316239)
            ·
              refine ⟨19205452445885088769974359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12803634963923392513316239 19205452445885088769974359)
              ·
                refine ⟨28808178668827633154961539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19205452445885088769974359 28808178668827633154961539)
                ·
                  refine ⟨43212268003241449732442309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28808178668827633154961539 43212268003241449732442309)
                  ·
                    refine ⟨8102300250607771824832933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43212268003241449732442309 8102300250607771824832933)
                    ·
                      refine ⟨1519181296988957217156175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8102300250607771824832933 1519181296988957217156175)
                      ·
                        rfl

theorem cell23_2958595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_2958595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958595 prefixEnd_2958595 := by exact prefixLift 2958595
  have htrace : WordTrace (prefixWord ++ tailWord_2958595) baseStart_2958595 baseEnd_2958595 := by
    simpa [prefixWord, tailWord_2958595, baseEnd_2958595] using wordTrace_append hprefix tailTrace_2958595
  have hstable : (prefixWord ++ tailWord_2958595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958595).length < 2 ^ (prefixWord ++ tailWord_2958595).sum := by decide
  have hdescent : baseEnd_2958595 < baseStart_2958595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958672 : List Nat := [2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 4]
def baseStart_2958672 : Nat := 118140960795 + 2958672 * 2 ^ 59
def prefixEnd_2958672 : Nat := 4983230072969 + 3 ^ 40 * 2958672 * 2
def baseEnd_2958672 : Nat := 1519220834999353415893321

theorem tailTrace_2958672 : CollatzResearch.WordTrace tailWord_2958672 prefixEnd_2958672 1519220834999353415893321 := by
  unfold tailWord_2958672
  simp only [CollatzResearch.WordTrace]
  refine ⟨53955816568622059896823135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71941088758162746529097513 53955816568622059896823135)
  ·
    refine ⟨80933724852933089845234703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53955816568622059896823135 80933724852933089845234703)
    ·
      refine ⟨121400587279399634767852055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80933724852933089845234703 121400587279399634767852055)
      ·
        refine ⟨182100880919099452151778083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121400587279399634767852055 182100880919099452151778083)
        ·
          refine ⟨273151321378649178227667125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182100880919099452151778083 273151321378649178227667125)
          ·
            refine ⟨25607936379248360458843793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273151321378649178227667125 25607936379248360458843793)
            ·
              refine ⟨19205952284436270344132845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25607936379248360458843793 19205952284436270344132845)
              ·
                refine ⟨7202232106663601379049817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19205952284436270344132845 7202232106663601379049817)
                ·
                  refine ⟨5401674079997701034287363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7202232106663601379049817 5401674079997701034287363)
                  ·
                    refine ⟨8102511119996551551431045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5401674079997701034287363 8102511119996551551431045)
                    ·
                      refine ⟨1519220834999353415893321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8102511119996551551431045 1519220834999353415893321)
                      ·
                        rfl

theorem cell23_2958672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_2958672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958672 prefixEnd_2958672 := by exact prefixLift 2958672
  have htrace : WordTrace (prefixWord ++ tailWord_2958672) baseStart_2958672 baseEnd_2958672 := by
    simpa [prefixWord, tailWord_2958672, baseEnd_2958672] using wordTrace_append hprefix tailTrace_2958672
  have hstable : (prefixWord ++ tailWord_2958672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958672).length < 2 ^ (prefixWord ++ tailWord_2958672).sum := by decide
  have hdescent : baseEnd_2958672 < baseStart_2958672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958682 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_2958682 : Nat := 118140960795 + 2958682 * 2 ^ 59
def prefixEnd_2958682 : Nat := 4983230072969 + 3 ^ 40 * 2958682 * 2
def baseEnd_2958682 : Nat := 506408656601966125589425

theorem tailTrace_2958682 : CollatzResearch.WordTrace tailWord_2958682 prefixEnd_2958682 506408656601966125589425 := by
  unfold tailWord_2958682
  simp only [CollatzResearch.WordTrace]
  refine ⟨26977999466801972875377575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71941331911471927667673533 26977999466801972875377575)
  ·
    refine ⟨40466999200202959313066363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26977999466801972875377575 40466999200202959313066363)
    ·
      refine ⟨60700498800304438969599545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40466999200202959313066363 60700498800304438969599545)
      ·
        refine ⟨45525374100228329227199659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60700498800304438969599545 45525374100228329227199659)
        ·
          refine ⟨68288061150342493840799489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45525374100228329227199659 68288061150342493840799489)
          ·
            refine ⟨51216045862756870380599617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68288061150342493840799489 51216045862756870380599617)
            ·
              refine ⟨38412034397067652785449713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51216045862756870380599617 38412034397067652785449713)
              ·
                refine ⟨28809025797800739589087285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38412034397067652785449713 28809025797800739589087285)
                ·
                  refine ⟨2700846168543819336476933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28809025797800739589087285 2700846168543819336476933)
                  ·
                    refine ⟨506408656601966125589425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2700846168543819336476933 506408656601966125589425)
                    ·
                      rfl

theorem cell23_2958682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_2958682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958682 prefixEnd_2958682 := by exact prefixLift 2958682
  have htrace : WordTrace (prefixWord ++ tailWord_2958682) baseStart_2958682 baseEnd_2958682 := by
    simpa [prefixWord, tailWord_2958682, baseEnd_2958682] using wordTrace_append hprefix tailTrace_2958682
  have hstable : (prefixWord ++ tailWord_2958682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958682).length < 2 ^ (prefixWord ++ tailWord_2958682).sum := by decide
  have hdescent : baseEnd_2958682 < baseStart_2958682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958750 : List Nat := [4, 3, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2958750 : Nat := 118140960795 + 2958750 * 2 ^ 59
def prefixEnd_2958750 : Nat := 4983230072969 + 3 ^ 40 * 2958750 * 2
def baseEnd_2958750 : Nat := 506420295496801370239321

theorem tailTrace_2958750 : CollatzResearch.WordTrace tailWord_2958750 prefixEnd_2958750 506420295496801370239321 := by
  unfold tailWord_2958750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13489309753870192389373213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71942985353974359409990469 13489309753870192389373213)
  ·
    refine ⟨5058491157701322146014955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13489309753870192389373213 5058491157701322146014955)
    ·
      refine ⟨7587736736551983219022433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5058491157701322146014955 7587736736551983219022433)
      ·
        refine ⟨5690802552413987414266825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7587736736551983219022433 5690802552413987414266825)
        ·
          refine ⟨4268101914310490560700119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5690802552413987414266825 4268101914310490560700119)
          ·
            refine ⟨6402152871465735841050179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268101914310490560700119 6402152871465735841050179)
            ·
              refine ⟨9603229307198603761575269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402152871465735841050179 9603229307198603761575269)
              ·
                refine ⟨1800605495099738205295363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9603229307198603761575269 1800605495099738205295363)
                ·
                  refine ⟨2700908242649607307943045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800605495099738205295363 2700908242649607307943045)
                  ·
                    refine ⟨506420295496801370239321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2700908242649607307943045 506420295496801370239321)
                    ·
                      rfl

theorem cell23_2958750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2958750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958750 prefixEnd_2958750 := by exact prefixLift 2958750
  have htrace : WordTrace (prefixWord ++ tailWord_2958750) baseStart_2958750 baseEnd_2958750 := by
    simpa [prefixWord, tailWord_2958750, baseEnd_2958750] using wordTrace_append hprefix tailTrace_2958750
  have hstable : (prefixWord ++ tailWord_2958750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958750).length < 2 ^ (prefixWord ++ tailWord_2958750).sum := by decide
  have hdescent : baseEnd_2958750 < baseStart_2958750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958796 : List Nat := [2, 2, 1, 4, 2, 2, 1, 3, 1, 1, 4]
def baseStart_2958796 : Nat := 118140960795 + 2958796 * 2 ^ 59
def prefixEnd_2958796 : Nat := 4983230072969 + 3 ^ 40 * 2958796 * 2
def baseEnd_2958796 : Nat := 1519284506600510930742751

theorem tailTrace_2958796 : CollatzResearch.WordTrace tailWord_2958796 prefixEnd_2958796 1519284506600510930742751 := by
  unfold tailWord_2958796
  simp only [CollatzResearch.WordTrace]
  refine ⟨53958077894397444485580121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71944103859196592647440161 53958077894397444485580121)
  ·
    refine ⟨40468558420798083364185091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53958077894397444485580121 40468558420798083364185091)
    ·
      refine ⟨60702837631197125046277637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40468558420798083364185091 60702837631197125046277637)
      ·
        refine ⟨11381782055849460946177057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60702837631197125046277637 11381782055849460946177057)
        ·
          refine ⟨8536336541887095709632793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11381782055849460946177057 8536336541887095709632793)
          ·
            refine ⟨6402252406415321782224595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8536336541887095709632793 6402252406415321782224595)
            ·
              refine ⟨9603378609622982673336893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402252406415321782224595 9603378609622982673336893)
              ·
                refine ⟨3601266978608618502501335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9603378609622982673336893 3601266978608618502501335)
                ·
                  refine ⟨5401900467912927753752003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601266978608618502501335 5401900467912927753752003)
                  ·
                    refine ⟨8102850701869391630628005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5401900467912927753752003 8102850701869391630628005)
                    ·
                      refine ⟨1519284506600510930742751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8102850701869391630628005 1519284506600510930742751)
                      ·
                        rfl

theorem cell23_2958796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_2958796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958796 prefixEnd_2958796 := by exact prefixLift 2958796
  have htrace : WordTrace (prefixWord ++ tailWord_2958796) baseStart_2958796 baseEnd_2958796 := by
    simpa [prefixWord, tailWord_2958796, baseEnd_2958796] using wordTrace_append hprefix tailTrace_2958796
  have hstable : (prefixWord ++ tailWord_2958796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958796).length < 2 ^ (prefixWord ++ tailWord_2958796).sum := by decide
  have hdescent : baseEnd_2958796 < baseStart_2958796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958813 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_2958813 : Nat := 118140960795 + 2958813 * 2 ^ 59
def prefixEnd_2958813 : Nat := 4983230072969 + 3 ^ 40 * 2958813 * 2
def baseEnd_2958813 : Nat := 1519293235771637364230173

theorem tailTrace_2958813 : CollatzResearch.WordTrace tailWord_2958813 prefixEnd_2958813 1519293235771637364230173 := by
  unfold tailWord_2958813
  simp only [CollatzResearch.WordTrace]
  refine ⟨107916775829733300874529093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71944517219822200583019395 107916775829733300874529093)
  ·
    refine ⟨20234395468074993913974205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107916775829733300874529093 20234395468074993913974205)
    ·
      refine ⟨7587898300528122717740327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20234395468074993913974205 7587898300528122717740327)
      ·
        refine ⟨11381847450792184076610491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7587898300528122717740327 11381847450792184076610491)
        ·
          refine ⟨17072771176188276114915737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11381847450792184076610491 17072771176188276114915737)
          ·
            refine ⟨12804578382141207086186803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17072771176188276114915737 12804578382141207086186803)
            ·
              refine ⟨19206867573211810629280205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12804578382141207086186803 19206867573211810629280205)
              ·
                refine ⟨7202575339954428985980077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19206867573211810629280205 7202575339954428985980077)
                ·
                  refine ⟨2700965752482910869742529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7202575339954428985980077 2700965752482910869742529)
                  ·
                    refine ⟨2025724314362183152306897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2700965752482910869742529 2025724314362183152306897)
                    ·
                      refine ⟨1519293235771637364230173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025724314362183152306897 1519293235771637364230173)
                      ·
                        rfl

theorem cell23_2958813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_2958813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958813 prefixEnd_2958813 := by exact prefixLift 2958813
  have htrace : WordTrace (prefixWord ++ tailWord_2958813) baseStart_2958813 baseEnd_2958813 := by
    simpa [prefixWord, tailWord_2958813, baseEnd_2958813] using wordTrace_append hprefix tailTrace_2958813
  have hstable : (prefixWord ++ tailWord_2958813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958813).length < 2 ^ (prefixWord ++ tailWord_2958813).sum := by decide
  have hdescent : baseEnd_2958813 < baseStart_2958813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958823 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 2, 4]
def baseStart_2958823 : Nat := 118140960795 + 2958823 * 2 ^ 59
def prefixEnd_2958823 : Nat := 4983230072969 + 3 ^ 40 * 2958823 * 2
def baseEnd_2958823 : Nat := 506432790192727441701709

theorem tailTrace_2958823 : CollatzResearch.WordTrace tailWord_2958823 prefixEnd_2958823 506432790192727441701709 := by
  unfold tailWord_2958823
  simp only [CollatzResearch.WordTrace]
  refine ⟨107917140559697072582393123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71944760373131381721595415 107917140559697072582393123)
  ·
    refine ⟨161875710839545608873589685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107917140559697072582393123 161875710839545608873589685)
    ·
      refine ⟨15175847891207400831899033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161875710839545608873589685 15175847891207400831899033)
      ·
        refine ⟨11381885918405550623924275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15175847891207400831899033 11381885918405550623924275)
        ·
          refine ⟨17072828877608325935886413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11381885918405550623924275 17072828877608325935886413)
          ·
            refine ⟨6402310829103122225957405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17072828877608325935886413 6402310829103122225957405)
            ·
              refine ⟨2400866560913670834734027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6402310829103122225957405 2400866560913670834734027)
              ·
                refine ⟨3601299841370506252101041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400866560913670834734027 3601299841370506252101041)
                ·
                  refine ⟨2700974881027879689075781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3601299841370506252101041 2700974881027879689075781)
                  ·
                    refine ⟨506432790192727441701709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2700974881027879689075781 506432790192727441701709)
                    ·
                      rfl

theorem cell23_2958823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_2958823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958823 prefixEnd_2958823 := by exact prefixLift 2958823
  have htrace : WordTrace (prefixWord ++ tailWord_2958823) baseStart_2958823 baseEnd_2958823 := by
    simpa [prefixWord, tailWord_2958823, baseEnd_2958823] using wordTrace_append hprefix tailTrace_2958823
  have hstable : (prefixWord ++ tailWord_2958823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958823).length < 2 ^ (prefixWord ++ tailWord_2958823).sum := by decide
  have hdescent : baseEnd_2958823 < baseStart_2958823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958842 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_2958842 : Nat := 118140960795 + 2958842 * 2 ^ 59
def prefixEnd_2958842 : Nat := 4983230072969 + 3 ^ 40 * 2958842 * 2
def baseEnd_2958842 : Nat := 1519308126710617750767539

theorem tailTrace_2958842 : CollatzResearch.WordTrace tailWord_2958842 prefixEnd_2958842 1519308126710617750767539 := by
  unfold tailWord_2958842
  simp only [CollatzResearch.WordTrace]
  refine ⟨26979458386657059706833695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71945222364418825884889853 26979458386657059706833695)
  ·
    refine ⟨40469187579985589560250543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26979458386657059706833695 40469187579985589560250543)
    ·
      refine ⟨60703781369978384340375815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40469187579985589560250543 60703781369978384340375815)
      ·
        refine ⟨91055672054967576510563723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60703781369978384340375815 91055672054967576510563723)
        ·
          refine ⟨136583508082451364765845585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91055672054967576510563723 136583508082451364765845585)
          ·
            refine ⟨102437631061838523574384189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136583508082451364765845585 102437631061838523574384189)
            ·
              refine ⟨38414111648189446340394071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102437631061838523574384189 38414111648189446340394071)
              ·
                refine ⟨57621167472284169510591107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38414111648189446340394071 57621167472284169510591107)
                ·
                  refine ⟨86431751208426254265886661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57621167472284169510591107 86431751208426254265886661)
                  ·
                    refine ⟨16205953351579922674853749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86431751208426254265886661 16205953351579922674853749)
                    ·
                      refine ⟨1519308126710617750767539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16205953351579922674853749 1519308126710617750767539)
                      ·
                        rfl

theorem cell23_2958842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_2958842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958842 prefixEnd_2958842 := by exact prefixLift 2958842
  have htrace : WordTrace (prefixWord ++ tailWord_2958842) baseStart_2958842 baseEnd_2958842 := by
    simpa [prefixWord, tailWord_2958842, baseEnd_2958842] using wordTrace_append hprefix tailTrace_2958842
  have hstable : (prefixWord ++ tailWord_2958842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958842).length < 2 ^ (prefixWord ++ tailWord_2958842).sum := by decide
  have hdescent : baseEnd_2958842 < baseStart_2958842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958880 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 2, 1, 3]
def baseStart_2958880 : Nat := 118140960795 + 2958880 * 2 ^ 59
def prefixEnd_2958880 : Nat := 4983230072969 + 3 ^ 40 * 2958880 * 2
def baseEnd_2958880 : Nat := 1519327638975488602092365

theorem tailTrace_2958880 : CollatzResearch.WordTrace tailWord_2958880 prefixEnd_2958880 1519327638975488602092365 := by
  unfold tailWord_2958880
  simp only [CollatzResearch.WordTrace]
  refine ⟨53959609760245285658609047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71946146346993714211478729 53959609760245285658609047)
  ·
    refine ⟨80939414640367928487913571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53959609760245285658609047 80939414640367928487913571)
    ·
      refine ⟨121409121960551892731870357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80939414640367928487913571 121409121960551892731870357)
      ·
        refine ⟨5691052591900869971806423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121409121960551892731870357 5691052591900869971806423)
        ·
          refine ⟨8536578887851304957709635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5691052591900869971806423 8536578887851304957709635)
          ·
            refine ⟨12804868331776957436564453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8536578887851304957709635 12804868331776957436564453)
            ·
              refine ⟨2400912812208179519355835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12804868331776957436564453 2400912812208179519355835)
              ·
                refine ⟨3601369218312269279033753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2400912812208179519355835 3601369218312269279033753)
                ·
                  refine ⟨2701026913734201959275315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3601369218312269279033753 2701026913734201959275315)
                  ·
                    refine ⟨4051540370601302938912973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2701026913734201959275315 4051540370601302938912973)
                    ·
                      refine ⟨1519327638975488602092365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4051540370601302938912973 1519327638975488602092365)
                      ·
                        rfl

theorem cell23_2958880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_2958880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958880 prefixEnd_2958880 := by exact prefixLift 2958880
  have htrace : WordTrace (prefixWord ++ tailWord_2958880) baseStart_2958880 baseEnd_2958880 := by
    simpa [prefixWord, tailWord_2958880, baseEnd_2958880] using wordTrace_append hprefix tailTrace_2958880
  have hstable : (prefixWord ++ tailWord_2958880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958880).length < 2 ^ (prefixWord ++ tailWord_2958880).sum := by decide
  have hdescent : baseEnd_2958880 < baseStart_2958880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2958976 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 4, 4, 2]
def baseStart_2958976 : Nat := 118140960795 + 2958976 * 2 ^ 59
def prefixEnd_2958976 : Nat := 4983230072969 + 3 ^ 40 * 2958976 * 2
def baseEnd_2958976 : Nat := 1519376933118320226491923

theorem tailTrace_2958976 : CollatzResearch.WordTrace tailWord_2958976 prefixEnd_2958976 1519376933118320226491923 := by
  unfold tailWord_2958976
  simp only [CollatzResearch.WordTrace]
  refine ⟨53961360464071389856356391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71948480618761853141808521 53961360464071389856356391)
  ·
    refine ⟨80942040696107084784534587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53961360464071389856356391 80942040696107084784534587)
    ·
      refine ⟨121413061044160627176801881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80942040696107084784534587 121413061044160627176801881)
      ·
        refine ⟨91059795783120470382601411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121413061044160627176801881 91059795783120470382601411)
        ·
          refine ⟨136589693674680705573902117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91059795783120470382601411 136589693674680705573902117)
          ·
            refine ⟨25610567564002632295106647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136589693674680705573902117 25610567564002632295106647)
            ·
              refine ⟨38415851346003948442659971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25610567564002632295106647 38415851346003948442659971)
              ·
                refine ⟨57623777019005922663989957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38415851346003948442659971 57623777019005922663989957)
                ·
                  refine ⟨10804458191063610499498117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57623777019005922663989957 10804458191063610499498117)
                  ·
                    refine ⟨2025835910824426968655897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10804458191063610499498117 2025835910824426968655897)
                    ·
                      refine ⟨1519376933118320226491923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025835910824426968655897 1519376933118320226491923)
                      ·
                        rfl

theorem cell23_2958976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 4, 2].length) (baseStart_2958976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2958976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2958976 prefixEnd_2958976 := by exact prefixLift 2958976
  have htrace : WordTrace (prefixWord ++ tailWord_2958976) baseStart_2958976 baseEnd_2958976 := by
    simpa [prefixWord, tailWord_2958976, baseEnd_2958976] using wordTrace_append hprefix tailTrace_2958976
  have hstable : (prefixWord ++ tailWord_2958976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2958976).length < 2 ^ (prefixWord ++ tailWord_2958976).sum := by decide
  have hdescent : baseEnd_2958976 < baseStart_2958976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2958976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959030 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2959030 : Nat := 118140960795 + 2959030 * 2 ^ 59
def prefixEnd_2959030 : Nat := 4983230072969 + 3 ^ 40 * 2959030 * 2
def baseEnd_2959030 : Nat := 1519404661073663015216675

theorem tailTrace_2959030 : CollatzResearch.WordTrace tailWord_2959030 prefixEnd_2959030 1519404661073663015216675 := by
  unfold tailWord_2959030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745293154371696683448659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71949793646631431290119029 6745293154371696683448659)
  ·
    refine ⟨10117939731557545025172989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6745293154371696683448659 10117939731557545025172989)
    ·
      refine ⟨3794227399334079384439871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10117939731557545025172989 3794227399334079384439871)
      ·
        refine ⟨5691341099001119076659807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3794227399334079384439871 5691341099001119076659807)
        ·
          refine ⟨8537011648501678614989711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5691341099001119076659807 8537011648501678614989711)
          ·
            refine ⟨12805517472752517922484567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8537011648501678614989711 12805517472752517922484567)
            ·
              refine ⟨19208276209128776883726851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12805517472752517922484567 19208276209128776883726851)
              ·
                refine ⟨28812414313693165325590277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19208276209128776883726851 28812414313693165325590277)
                ·
                  refine ⟨5402327683817468498548177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28812414313693165325590277 5402327683817468498548177)
                  ·
                    refine ⟨4051745762863101373911133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5402327683817468498548177 4051745762863101373911133)
                    ·
                      refine ⟨1519404661073663015216675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4051745762863101373911133 1519404661073663015216675)
                      ·
                        rfl

theorem cell23_2959030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2959030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959030 prefixEnd_2959030 := by exact prefixLift 2959030
  have htrace : WordTrace (prefixWord ++ tailWord_2959030) baseStart_2959030 baseEnd_2959030 := by
    simpa [prefixWord, tailWord_2959030, baseEnd_2959030] using wordTrace_append hprefix tailTrace_2959030
  have hstable : (prefixWord ++ tailWord_2959030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959030).length < 2 ^ (prefixWord ++ tailWord_2959030).sum := by decide
  have hdescent : baseEnd_2959030 < baseStart_2959030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959050 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 6]
def baseStart_2959050 : Nat := 118140960795 + 2959050 * 2 ^ 59
def prefixEnd_2959050 : Nat := 4983230072969 + 3 ^ 40 * 2959050 * 2
def baseEnd_2959050 : Nat := 168823881187416992996287

theorem tailTrace_2959050 : CollatzResearch.WordTrace tailWord_2959050 prefixEnd_2959050 168823881187416992996287 := by
  unfold tailWord_2959050
  simp only [CollatzResearch.WordTrace]
  refine ⟨26981354982468672587726651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71950279953249793567271069 26981354982468672587726651)
  ·
    refine ⟨40472032473703008881589977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26981354982468672587726651 40472032473703008881589977)
    ·
      refine ⟨30354024355277256661192483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40472032473703008881589977 30354024355277256661192483)
      ·
        refine ⟨45531036532915884991788725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30354024355277256661192483 45531036532915884991788725)
        ·
          refine ⟨4268534674960864217980193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45531036532915884991788725 4268534674960864217980193)
          ·
            refine ⟨3201401006220648163485145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4268534674960864217980193 3201401006220648163485145)
            ·
              refine ⟨2401050754665486122613859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3201401006220648163485145 2401050754665486122613859)
              ·
                refine ⟨3601576131998229183920789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401050754665486122613859 3601576131998229183920789)
                ·
                  refine ⟨168823881187416992996287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3601576131998229183920789 168823881187416992996287)
                  ·
                    rfl

theorem cell23_2959050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_2959050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959050 prefixEnd_2959050 := by exact prefixLift 2959050
  have htrace : WordTrace (prefixWord ++ tailWord_2959050) baseStart_2959050 baseEnd_2959050 := by
    simpa [prefixWord, tailWord_2959050, baseEnd_2959050] using wordTrace_append hprefix tailTrace_2959050
  have hstable : (prefixWord ++ tailWord_2959050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959050).length < 2 ^ (prefixWord ++ tailWord_2959050).sum := by decide
  have hdescent : baseEnd_2959050 < baseStart_2959050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959076 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 1, 6]
def baseStart_2959076 : Nat := 118140960795 + 2959076 * 2 ^ 59
def prefixEnd_2959076 : Nat := 4983230072969 + 3 ^ 40 * 2959076 * 2
def baseEnd_2959076 : Nat := 506476093727923278413821

theorem tailTrace_2959076 : CollatzResearch.WordTrace tailWord_2959076 prefixEnd_2959076 506476093727923278413821 := by
  unfold tailWord_2959076
  simp only [CollatzResearch.WordTrace]
  refine ⟨53963184113890248395676541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71950912151853664527568721 53963184113890248395676541)
  ·
    refine ⟨20236194042708843148378703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53963184113890248395676541 20236194042708843148378703)
    ·
      refine ⟨30354291064063264722568055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20236194042708843148378703 30354291064063264722568055)
      ·
        refine ⟨45531436596094897083852083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30354291064063264722568055 45531436596094897083852083)
        ·
          refine ⟨68297154894142345625778125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45531436596094897083852083 68297154894142345625778125)
          ·
            refine ⟨25611433085303379609666797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68297154894142345625778125 25611433085303379609666797)
            ·
              refine ⟨9604287406988767353625049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25611433085303379609666797 9604287406988767353625049)
              ·
                refine ⟨7203215555241575515218787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9604287406988767353625049 7203215555241575515218787)
                ·
                  refine ⟨10804823332862363272828181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7203215555241575515218787 10804823332862363272828181)
                  ·
                    refine ⟨506476093727923278413821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10804823332862363272828181 506476093727923278413821)
                    ·
                      rfl

theorem cell23_2959076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_2959076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959076 prefixEnd_2959076 := by exact prefixLift 2959076
  have htrace : WordTrace (prefixWord ++ tailWord_2959076) baseStart_2959076 baseEnd_2959076 := by
    simpa [prefixWord, tailWord_2959076, baseEnd_2959076] using wordTrace_append hprefix tailTrace_2959076
  have hstable : (prefixWord ++ tailWord_2959076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959076).length < 2 ^ (prefixWord ++ tailWord_2959076).sum := by decide
  have hdescent : baseEnd_2959076 < baseStart_2959076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959080 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 1, 5]
def baseStart_2959080 : Nat := 118140960795 + 2959080 * 2 ^ 59
def prefixEnd_2959080 : Nat := 4983230072969 + 3 ^ 40 * 2959080 * 2
def baseEnd_2959080 : Nat := 506476778368795939863815

theorem tailTrace_2959080 : CollatzResearch.WordTrace tailWord_2959080 prefixEnd_2959080 506476778368795939863815 := by
  unfold tailWord_2959080
  simp only [CollatzResearch.WordTrace]
  refine ⟨53963257059883002737249347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71951009413177336982999129 53963257059883002737249347)
  ·
    refine ⟨80944885589824504105874021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53963257059883002737249347 80944885589824504105874021)
    ·
      refine ⟨15177166048092094519851379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80944885589824504105874021 15177166048092094519851379)
      ·
        refine ⟨22765749072138141779777069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15177166048092094519851379 22765749072138141779777069)
        ·
          refine ⟨8537155902051803167416401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22765749072138141779777069 8537155902051803167416401)
          ·
            refine ⟨6402866926538852375562301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8537155902051803167416401 6402866926538852375562301)
            ·
              refine ⟨2401075097452069640835863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6402866926538852375562301 2401075097452069640835863)
              ·
                refine ⟨3601612646178104461253795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401075097452069640835863 3601612646178104461253795)
                ·
                  refine ⟨5402418969267156691880693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601612646178104461253795 5402418969267156691880693)
                  ·
                    refine ⟨506476778368795939863815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5402418969267156691880693 506476778368795939863815)
                    ·
                      rfl

theorem cell23_2959080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_2959080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959080 prefixEnd_2959080 := by exact prefixLift 2959080
  have htrace : WordTrace (prefixWord ++ tailWord_2959080) baseStart_2959080 baseEnd_2959080 := by
    simpa [prefixWord, tailWord_2959080, baseEnd_2959080] using wordTrace_append hprefix tailTrace_2959080
  have hstable : (prefixWord ++ tailWord_2959080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959080).length < 2 ^ (prefixWord ++ tailWord_2959080).sum := by decide
  have hdescent : baseEnd_2959080 < baseStart_2959080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959089 : List Nat := [1, 2, 2, 2, 2, 14]
def baseStart_2959089 : Nat := 118140960795 + 2959089 * 2 ^ 59
def prefixEnd_2959089 : Nat := 4983230072969 + 3 ^ 40 * 2959089 * 2
def baseEnd_2959089 : Nat := 6252818750750116396621

theorem tailTrace_2959089 : CollatzResearch.WordTrace tailWord_2959089 prefixEnd_2959089 6252818750750116396621 := by
  unfold tailWord_2959089
  simp only [CollatzResearch.WordTrace]
  refine ⟨107926842376733400011576321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71951228251155600007717547 107926842376733400011576321)
  ·
    refine ⟨80945131782550050008682241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107926842376733400011576321 80945131782550050008682241)
    ·
      refine ⟨60708848836912537506511681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80945131782550050008682241 60708848836912537506511681)
      ·
        refine ⟨45531636627684403129883761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60708848836912537506511681 45531636627684403129883761)
        ·
          refine ⟨34148727470763302347412821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45531636627684403129883761 34148727470763302347412821)
          ·
            refine ⟨6252818750750116396621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 34148727470763302347412821 6252818750750116396621)
            ·
              rfl

theorem cell23_2959089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 14].length) (baseStart_2959089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959089 prefixEnd_2959089 := by exact prefixLift 2959089
  have htrace : WordTrace (prefixWord ++ tailWord_2959089) baseStart_2959089 baseEnd_2959089 := by
    simpa [prefixWord, tailWord_2959089, baseEnd_2959089] using wordTrace_append hprefix tailTrace_2959089
  have hstable : (prefixWord ++ tailWord_2959089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959089).length < 2 ^ (prefixWord ++ tailWord_2959089).sum := by decide
  have hdescent : baseEnd_2959089 < baseStart_2959089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959094 : List Nat := [5, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_2959094 : Nat := 118140960795 + 2959094 * 2 ^ 59
def prefixEnd_2959094 : Nat := 4983230072969 + 3 ^ 40 * 2959094 * 2
def baseEnd_2959094 : Nat := 1519437523835550764816381

theorem tailTrace_2959094 : CollatzResearch.WordTrace tailWord_2959094 prefixEnd_2959094 1519437523835550764816381 := by
  unfold tailWord_2959094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6745439046357205366594271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71951349827810190577005557 6745439046357205366594271)
  ·
    refine ⟨10118158569535808049891407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6745439046357205366594271 10118158569535808049891407)
    ·
      refine ⟨15177237854303712074837111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10118158569535808049891407 15177237854303712074837111)
      ·
        refine ⟨22765856781455568112255667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15177237854303712074837111 22765856781455568112255667)
        ·
          refine ⟨34148785172183352168383501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22765856781455568112255667 34148785172183352168383501)
          ·
            refine ⟨12805794439568757063143813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34148785172183352168383501 12805794439568757063143813)
            ·
              refine ⟨2401086457419141949339465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12805794439568757063143813 2401086457419141949339465)
              ·
                refine ⟨1800814843064356462004599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2401086457419141949339465 1800814843064356462004599)
                ·
                  refine ⟨2701222264596534693006899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800814843064356462004599 2701222264596534693006899)
                  ·
                    refine ⟨4051833396894802039510349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2701222264596534693006899 4051833396894802039510349)
                    ·
                      refine ⟨1519437523835550764816381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4051833396894802039510349 1519437523835550764816381)
                      ·
                        rfl

theorem cell23_2959094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_2959094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959094 prefixEnd_2959094 := by exact prefixLift 2959094
  have htrace : WordTrace (prefixWord ++ tailWord_2959094) baseStart_2959094 baseEnd_2959094 := by
    simpa [prefixWord, tailWord_2959094, baseEnd_2959094] using wordTrace_append hprefix tailTrace_2959094
  have hstable : (prefixWord ++ tailWord_2959094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959094).length < 2 ^ (prefixWord ++ tailWord_2959094).sum := by decide
  have hdescent : baseEnd_2959094 < baseStart_2959094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959099 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7]
def baseStart_2959099 : Nat := 118140960795 + 2959099 * 2 ^ 59
def prefixEnd_2959099 : Nat := 4983230072969 + 3 ^ 40 * 2959099 * 2
def baseEnd_2959099 : Nat := 1519440091238823245253857

theorem tailTrace_2959099 : CollatzResearch.WordTrace tailWord_2959099 prefixEnd_2959099 1519440091238823245253857 := by
  unfold tailWord_2959099
  simp only [CollatzResearch.WordTrace]
  refine ⟨107927207106697171719440351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71951471404464781146293567 107927207106697171719440351)
  ·
    refine ⟨161890810660045757579160527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107927207106697171719440351 161890810660045757579160527)
    ·
      refine ⟨242836215990068636368740791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161890810660045757579160527 242836215990068636368740791)
      ·
        refine ⟨364254323985102954553111187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242836215990068636368740791 364254323985102954553111187)
        ·
          refine ⟨546381485977654431829666781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364254323985102954553111187 546381485977654431829666781)
          ·
            refine ⟨204893057241620411936125043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 546381485977654431829666781 204893057241620411936125043)
            ·
              refine ⟨307339585862430617904187565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204893057241620411936125043 307339585862430617904187565)
              ·
                refine ⟨115252344698411481714070337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 307339585862430617904187565 115252344698411481714070337)
                ·
                  refine ⟨86439258523808611285552753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115252344698411481714070337 86439258523808611285552753)
                  ·
                    refine ⟨64829443892856458464164565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 86439258523808611285552753 64829443892856458464164565)
                    ·
                      refine ⟨1519440091238823245253857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64829443892856458464164565 1519440091238823245253857)
                      ·
                        rfl

theorem cell23_2959099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_2959099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959099 prefixEnd_2959099 := by exact prefixLift 2959099
  have htrace : WordTrace (prefixWord ++ tailWord_2959099) baseStart_2959099 baseEnd_2959099 := by
    simpa [prefixWord, tailWord_2959099, baseEnd_2959099] using wordTrace_append hprefix tailTrace_2959099
  have hstable : (prefixWord ++ tailWord_2959099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959099).length < 2 ^ (prefixWord ++ tailWord_2959099).sum := by decide
  have hdescent : baseEnd_2959099 < baseStart_2959099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959100 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 3, 2, 2]
def baseStart_2959100 : Nat := 118140960795 + 2959100 * 2 ^ 59
def prefixEnd_2959100 : Nat := 4983230072969 + 3 ^ 40 * 2959100 * 2
def baseEnd_2959100 : Nat := 1519440604719477741341353

theorem tailTrace_2959100 : CollatzResearch.WordTrace tailWord_2959100 prefixEnd_2959100 1519440604719477741341353 := by
  unfold tailWord_2959100
  simp only [CollatzResearch.WordTrace]
  refine ⟨53963621789846774445113377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71951495719795699260151169 53963621789846774445113377)
  ·
    refine ⟨40472716342385080833835033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53963621789846774445113377 40472716342385080833835033)
    ·
      refine ⟨30354537256788810625376275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40472716342385080833835033 30354537256788810625376275)
      ·
        refine ⟨45531805885183215938064413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30354537256788810625376275 45531805885183215938064413)
        ·
          refine ⟨17074427206943705976774155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45531805885183215938064413 17074427206943705976774155)
          ·
            refine ⟨25611640810415558965161233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17074427206943705976774155 25611640810415558965161233)
            ·
              refine ⟨19208730607811669223870925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25611640810415558965161233 19208730607811669223870925)
              ·
                refine ⟨7203273977929375958951597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19208730607811669223870925 7203273977929375958951597)
                ·
                  refine ⟨2701227741723515984606849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7203273977929375958951597 2701227741723515984606849)
                  ·
                    refine ⟨2025920806292636988455137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701227741723515984606849 2025920806292636988455137)
                    ·
                      refine ⟨1519440604719477741341353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025920806292636988455137 1519440604719477741341353)
                      ·
                        rfl

theorem cell23_2959100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_2959100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959100 prefixEnd_2959100 := by exact prefixLift 2959100
  have htrace : WordTrace (prefixWord ++ tailWord_2959100) baseStart_2959100 baseEnd_2959100 := by
    simpa [prefixWord, tailWord_2959100, baseEnd_2959100] using wordTrace_append hprefix tailTrace_2959100
  have hstable : (prefixWord ++ tailWord_2959100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959100).length < 2 ^ (prefixWord ++ tailWord_2959100).sum := by decide
  have hdescent : baseEnd_2959100 < baseStart_2959100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959134 : List Nat := [4, 3, 2, 2, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2959134 : Nat := 118140960795 + 2959134 * 2 ^ 59
def prefixEnd_2959134 : Nat := 4983230072969 + 3 ^ 40 * 2959134 * 2
def baseEnd_2959134 : Nat := 1519458063061730608316197

theorem tailTrace_2959134 : CollatzResearch.WordTrace tailWord_2959134 prefixEnd_2959134 1519458063061730608316197 := by
  unfold tailWord_2959134
  simp only [CollatzResearch.WordTrace]
  refine ⟨13491060457696296587120557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71952322441046915131309637 13491060457696296587120557)
  ·
    refine ⟨5059147671636111220170209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13491060457696296587120557 5059147671636111220170209)
    ·
      refine ⟨3794360753727083415127657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5059147671636111220170209 3794360753727083415127657)
      ·
        refine ⟨2845770565295312561345743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3794360753727083415127657 2845770565295312561345743)
        ·
          refine ⟨4268655847942968842018615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2845770565295312561345743 4268655847942968842018615)
          ·
            refine ⟨6402983771914453263027923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4268655847942968842018615 6402983771914453263027923)
            ·
              refine ⟨9604475657871679894541885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6402983771914453263027923 9604475657871679894541885)
              ·
                refine ⟨3601678371701879960453207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9604475657871679894541885 3601678371701879960453207)
                ·
                  refine ⟨5402517557552819940679811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601678371701879960453207 5402517557552819940679811)
                  ·
                    refine ⟨8103776336329229911019717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5402517557552819940679811 8103776336329229911019717)
                    ·
                      refine ⟨1519458063061730608316197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8103776336329229911019717 1519458063061730608316197)
                      ·
                        rfl

theorem cell23_2959134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2959134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959134 prefixEnd_2959134 := by exact prefixLift 2959134
  have htrace : WordTrace (prefixWord ++ tailWord_2959134) baseStart_2959134 baseEnd_2959134 := by
    simpa [prefixWord, tailWord_2959134, baseEnd_2959134] using wordTrace_append hprefix tailTrace_2959134
  have hstable : (prefixWord ++ tailWord_2959134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959134).length < 2 ^ (prefixWord ++ tailWord_2959134).sum := by decide
  have hdescent : baseEnd_2959134 < baseStart_2959134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959137 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 1, 2, 3]
def baseStart_2959137 : Nat := 118140960795 + 2959137 * 2 ^ 59
def prefixEnd_2959137 : Nat := 4983230072969 + 3 ^ 40 * 2959137 * 2
def baseEnd_2959137 : Nat := 1519459603503694096578683

theorem tailTrace_2959137 : CollatzResearch.WordTrace tailWord_2959137 prefixEnd_2959137 1519459603503694096578683 := by
  unfold tailWord_2959137
  simp only [CollatzResearch.WordTrace]
  refine ⟨107928593080559504209323665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71952395387039669472882443 107928593080559504209323665)
  ·
    refine ⟨80946444810419628156992749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107928593080559504209323665 80946444810419628156992749)
    ·
      refine ⟨30354916803907360558872281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80946444810419628156992749 30354916803907360558872281)
      ·
        refine ⟨22766187602930520419154211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30354916803907360558872281 22766187602930520419154211)
        ·
          refine ⟨34149281404395780628731317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22766187602930520419154211 34149281404395780628731317)
          ·
            refine ⟨3201495131662104433943561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34149281404395780628731317 3201495131662104433943561)
            ·
              refine ⟨2401121348746578325457671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3201495131662104433943561 2401121348746578325457671)
              ·
                refine ⟨3601682023119867488186507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401121348746578325457671 3601682023119867488186507)
                ·
                  refine ⟨5402523034679801232279761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3601682023119867488186507 5402523034679801232279761)
                  ·
                    refine ⟨4051892276009850924209821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5402523034679801232279761 4051892276009850924209821)
                    ·
                      refine ⟨1519459603503694096578683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4051892276009850924209821 1519459603503694096578683)
                      ·
                        rfl

theorem cell23_2959137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_2959137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959137 prefixEnd_2959137 := by exact prefixLift 2959137
  have htrace : WordTrace (prefixWord ++ tailWord_2959137) baseStart_2959137 baseEnd_2959137 := by
    simpa [prefixWord, tailWord_2959137, baseEnd_2959137] using wordTrace_append hprefix tailTrace_2959137
  have hstable : (prefixWord ++ tailWord_2959137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959137).length < 2 ^ (prefixWord ++ tailWord_2959137).sum := by decide
  have hdescent : baseEnd_2959137 < baseStart_2959137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959167 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 1, 3, 3]
def baseStart_2959167 : Nat := 118140960795 + 2959167 * 2 ^ 59
def prefixEnd_2959167 : Nat := 4983230072969 + 3 ^ 40 * 2959167 * 2
def baseEnd_2959167 : Nat := 1519475007923328979203545

theorem tailTrace_2959167 : CollatzResearch.WordTrace tailWord_2959167 prefixEnd_2959167 1519475007923328979203545 := by
  unfold tailWord_2959167
  simp only [CollatzResearch.WordTrace]
  refine ⟨107929687270450819332915755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71953124846967212888610503 107929687270450819332915755)
  ·
    refine ⟨161894530905676228999373633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107929687270450819332915755 161894530905676228999373633)
    ·
      refine ⟨121420898179257171749530225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161894530905676228999373633 121420898179257171749530225)
      ·
        refine ⟨91065673634442878812147669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121420898179257171749530225 91065673634442878812147669)
        ·
          refine ⟨2134351725807254972159711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 91065673634442878812147669 2134351725807254972159711)
          ·
            refine ⟨3201527588710882458239567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134351725807254972159711 3201527588710882458239567)
            ·
              refine ⟨4802291383066323687359351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201527588710882458239567 4802291383066323687359351)
              ·
                refine ⟨7203437074599485531039027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4802291383066323687359351 7203437074599485531039027)
                ·
                  refine ⟨10805155611899228296558541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7203437074599485531039027 10805155611899228296558541)
                  ·
                    refine ⟨4051933354462210611209453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10805155611899228296558541 4051933354462210611209453)
                    ·
                      refine ⟨1519475007923328979203545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4051933354462210611209453 1519475007923328979203545)
                      ·
                        rfl

theorem cell23_2959167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_2959167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959167 prefixEnd_2959167 := by exact prefixLift 2959167
  have htrace : WordTrace (prefixWord ++ tailWord_2959167) baseStart_2959167 baseEnd_2959167 := by
    simpa [prefixWord, tailWord_2959167, baseEnd_2959167] using wordTrace_append hprefix tailTrace_2959167
  have hstable : (prefixWord ++ tailWord_2959167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959167).length < 2 ^ (prefixWord ++ tailWord_2959167).sum := by decide
  have hdescent : baseEnd_2959167 < baseStart_2959167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959207 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_2959207 : Nat := 118140960795 + 2959207 * 2 ^ 59
def prefixEnd_2959207 : Nat := 4983230072969 + 3 ^ 40 * 2959207 * 2
def baseEnd_2959207 : Nat := 1519495547149508822703361

theorem tailTrace_2959207 : CollatzResearch.WordTrace tailWord_2959207 prefixEnd_2959207 1519495547149508822703361 := by
  unfold tailWord_2959207
  simp only [CollatzResearch.WordTrace]
  refine ⟨107931146190305906164371875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71954097460203937442914583 107931146190305906164371875)
  ·
    refine ⟨161896719285458859246557813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107931146190305906164371875 161896719285458859246557813)
    ·
      refine ⟨15177817433011768054364795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 161896719285458859246557813 15177817433011768054364795)
      ·
        refine ⟨22766726149517652081547193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15177817433011768054364795 22766726149517652081547193)
        ·
          refine ⟨17075044612138239061160395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22766726149517652081547193 17075044612138239061160395)
          ·
            refine ⟨25612566918207358591740593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17075044612138239061160395 25612566918207358591740593)
            ·
              refine ⟨19209425188655518943805445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25612566918207358591740593 19209425188655518943805445)
              ·
                refine ⟨3601767222872909801963521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19209425188655518943805445 3601767222872909801963521)
                ·
                  refine ⟨2701325417154682351472641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3601767222872909801963521 2701325417154682351472641)
                  ·
                    refine ⟨2025994062866011763604481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701325417154682351472641 2025994062866011763604481)
                    ·
                      refine ⟨1519495547149508822703361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2025994062866011763604481 1519495547149508822703361)
                      ·
                        rfl

theorem cell23_2959207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_2959207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959207 prefixEnd_2959207 := by exact prefixLift 2959207
  have htrace : WordTrace (prefixWord ++ tailWord_2959207) baseStart_2959207 baseEnd_2959207 := by
    simpa [prefixWord, tailWord_2959207, baseEnd_2959207] using wordTrace_append hprefix tailTrace_2959207
  have hstable : (prefixWord ++ tailWord_2959207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959207).length < 2 ^ (prefixWord ++ tailWord_2959207).sum := by decide
  have hdescent : baseEnd_2959207 < baseStart_2959207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959213 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 7]
def baseStart_2959213 : Nat := 118140960795 + 2959213 * 2 ^ 59
def prefixEnd_2959213 : Nat := 4983230072969 + 3 ^ 40 * 2959213 * 2
def baseEnd_2959213 : Nat := 168833180892603977692037

theorem tailTrace_2959213 : CollatzResearch.WordTrace tailWord_2959213 prefixEnd_2959213 168833180892603977692037 := by
  unfold tailWord_2959213
  simp only [CollatzResearch.WordTrace]
  refine ⟨107931365028284169189090293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71954243352189446126060195 107931365028284169189090293)
  ·
    refine ⟨10118565471401640861477215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107931365028284169189090293 10118565471401640861477215)
    ·
      refine ⟨15177848207102461292215823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10118565471401640861477215 15177848207102461292215823)
      ·
        refine ⟨22766772310653691938323735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15177848207102461292215823 22766772310653691938323735)
        ·
          refine ⟨34150158465980537907485603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22766772310653691938323735 34150158465980537907485603)
          ·
            refine ⟨51225237698970806861228405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34150158465980537907485603 51225237698970806861228405)
            ·
              refine ⟨4802366034278513143240163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51225237698970806861228405 4802366034278513143240163)
              ·
                refine ⟨7203549051417769714860245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4802366034278513143240163 7203549051417769714860245)
                ·
                  refine ⟨168833180892603977692037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7203549051417769714860245 168833180892603977692037)
                  ·
                    rfl

theorem cell23_2959213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_2959213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959213 prefixEnd_2959213 := by exact prefixLift 2959213
  have htrace : WordTrace (prefixWord ++ tailWord_2959213) baseStart_2959213 baseEnd_2959213 := by
    simpa [prefixWord, tailWord_2959213, baseEnd_2959213] using wordTrace_append hprefix tailTrace_2959213
  have hstable : (prefixWord ++ tailWord_2959213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959213).length < 2 ^ (prefixWord ++ tailWord_2959213).sum := by decide
  have hdescent : baseEnd_2959213 < baseStart_2959213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959226 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_2959226 : Nat := 118140960795 + 2959226 * 2 ^ 59
def prefixEnd_2959226 : Nat := 4983230072969 + 3 ^ 40 * 2959226 * 2
def baseEnd_2959226 : Nat := 506501767760648082788591

theorem tailTrace_2959226 : CollatzResearch.WordTrace tailWord_2959226 prefixEnd_2959226 506501767760648082788591 := by
  unfold tailWord_2959226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26982959794309268102328383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71954559451491381606209021 26982959794309268102328383)
  ·
    refine ⟨40474439691463902153492575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26982959794309268102328383 40474439691463902153492575)
    ·
      refine ⟨60711659537195853230238863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40474439691463902153492575 60711659537195853230238863)
      ·
        refine ⟨91067489305793779845358295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60711659537195853230238863 91067489305793779845358295)
        ·
          refine ⟨136601233958690669768037443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91067489305793779845358295 136601233958690669768037443)
          ·
            refine ⟨204901850938036004652056165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136601233958690669768037443 204901850938036004652056165)
            ·
              refine ⟨38419097050881750872260531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 204901850938036004652056165 38419097050881750872260531)
              ·
                refine ⟨57628645576322626308390797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38419097050881750872260531 57628645576322626308390797)
                ·
                  refine ⟨21610742091120984865646549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57628645576322626308390797 21610742091120984865646549)
                  ·
                    refine ⟨506501767760648082788591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21610742091120984865646549 506501767760648082788591)
                    ·
                      rfl

theorem cell23_2959226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_2959226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959226 prefixEnd_2959226 := by exact prefixLift 2959226
  have htrace : WordTrace (prefixWord ++ tailWord_2959226) baseStart_2959226 baseEnd_2959226 := by
    simpa [prefixWord, tailWord_2959226, baseEnd_2959226] using wordTrace_append hprefix tailTrace_2959226
  have hstable : (prefixWord ++ tailWord_2959226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959226).length < 2 ^ (prefixWord ++ tailWord_2959226).sum := by decide
  have hdescent : baseEnd_2959226 < baseStart_2959226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959260 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 2, 5]
def baseStart_2959260 : Nat := 118140960795 + 2959260 * 2 ^ 59
def prefixEnd_2959260 : Nat := 4983230072969 + 3 ^ 40 * 2959260 * 2
def baseEnd_2959260 : Nat := 506507587208065705113539

theorem tailTrace_2959260 : CollatzResearch.WordTrace tailWord_2959260 prefixEnd_2959260 506507587208065705113539 := by
  unfold tailWord_2959260
  simp only [CollatzResearch.WordTrace]
  refine ⟨53966539629556948108025617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71955386172742597477367489 53966539629556948108025617)
  ·
    refine ⟨40474904722167711081019213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53966539629556948108025617 40474904722167711081019213)
    ·
      refine ⟨15178089270812891655382205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40474904722167711081019213 15178089270812891655382205)
      ·
        refine ⟨5691783476554834370768327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15178089270812891655382205 5691783476554834370768327)
        ·
          refine ⟨8537675214832251556152491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5691783476554834370768327 8537675214832251556152491)
          ·
            refine ⟨12806512822248377334228737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8537675214832251556152491 12806512822248377334228737)
            ·
              refine ⟨9604884616686283000671553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12806512822248377334228737 9604884616686283000671553)
              ·
                refine ⟨7203663462514712250503665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9604884616686283000671553 7203663462514712250503665)
                ·
                  refine ⟨5402747596886034187877749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7203663462514712250503665 5402747596886034187877749)
                  ·
                    refine ⟨506507587208065705113539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5402747596886034187877749 506507587208065705113539)
                    ·
                      rfl

theorem cell23_2959260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_2959260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959260 prefixEnd_2959260 := by exact prefixLift 2959260
  have htrace : WordTrace (prefixWord ++ tailWord_2959260) baseStart_2959260 baseEnd_2959260 := by
    simpa [prefixWord, tailWord_2959260, baseEnd_2959260] using wordTrace_append hprefix tailTrace_2959260
  have hstable : (prefixWord ++ tailWord_2959260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959260).length < 2 ^ (prefixWord ++ tailWord_2959260).sum := by decide
  have hdescent : baseEnd_2959260 < baseStart_2959260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959283 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 3]
def baseStart_2959283 : Nat := 118140960795 + 2959283 * 2 ^ 59
def prefixEnd_2959283 : Nat := 4983230072969 + 3 ^ 40 * 2959283 * 2
def baseEnd_2959283 : Nat := 1519534571679250525353011

theorem tailTrace_2959283 : CollatzResearch.WordTrace tailWord_2959283 prefixEnd_2959283 1519534571679250525353011 := by
  unfold tailWord_2959283
  simp only [CollatzResearch.WordTrace]
  refine ⟨107933918138030571144138503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71955945425353714096092335 107933918138030571144138503)
  ·
    refine ⟨161900877207045856716207755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107933918138030571144138503 161900877207045856716207755)
    ·
      refine ⟨242851315810568785074311633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161900877207045856716207755 242851315810568785074311633)
      ·
        refine ⟨182138486857926588805733725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242851315810568785074311633 182138486857926588805733725)
        ·
          refine ⟨68301932571722470802150147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182138486857926588805733725 68301932571722470802150147)
          ·
            refine ⟨102452898857583706203225221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68301932571722470802150147 102452898857583706203225221)
            ·
              refine ⟨19209918535796944913104729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102452898857583706203225221 19209918535796944913104729)
              ·
                refine ⟨14407438901847708684828547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19209918535796944913104729 14407438901847708684828547)
                ·
                  refine ⟨21611158352771563027242821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14407438901847708684828547 21611158352771563027242821)
                  ·
                    refine ⟨4052092191144668067608029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21611158352771563027242821 4052092191144668067608029)
                    ·
                      refine ⟨1519534571679250525353011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4052092191144668067608029 1519534571679250525353011)
                      ·
                        rfl

theorem cell23_2959283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 3].length) (baseStart_2959283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959283 prefixEnd_2959283 := by exact prefixLift 2959283
  have htrace : WordTrace (prefixWord ++ tailWord_2959283) baseStart_2959283 baseEnd_2959283 := by
    simpa [prefixWord, tailWord_2959283, baseEnd_2959283] using wordTrace_append hprefix tailTrace_2959283
  have hstable : (prefixWord ++ tailWord_2959283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959283).length < 2 ^ (prefixWord ++ tailWord_2959283).sum := by decide
  have hdescent : baseEnd_2959283 < baseStart_2959283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959307 : List Nat := [1, 1, 1, 1, 3, 4, 4, 3, 1, 4]
def baseStart_2959307 : Nat := 118140960795 + 2959307 * 2 ^ 59
def prefixEnd_2959307 : Nat := 4983230072969 + 3 ^ 40 * 2959307 * 2
def baseEnd_2959307 : Nat := 506515631738319477150967

theorem tailTrace_2959307 : CollatzResearch.WordTrace tailWord_2959307 prefixEnd_2959307 506515631738319477150967 := by
  unfold tailWord_2959307
  simp only [CollatzResearch.WordTrace]
  refine ⟨107934793489943623243012175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71956528993295748828674783 107934793489943623243012175)
  ·
    refine ⟨161902190234915434864518263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107934793489943623243012175 161902190234915434864518263)
    ·
      refine ⟨242853285352373152296777395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161902190234915434864518263 242853285352373152296777395)
      ·
        refine ⟨364279928028559728445166093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242853285352373152296777395 364279928028559728445166093)
        ·
          refine ⟨136604973010709898166937285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364279928028559728445166093 136604973010709898166937285)
          ·
            refine ⟨25613432439508105906300741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 136604973010709898166937285 25613432439508105906300741)
            ·
              refine ⟨4802518582407769857431389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25613432439508105906300741 4802518582407769857431389)
              ·
                refine ⟨1800944468402913696536771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4802518582407769857431389 1800944468402913696536771)
                ·
                  refine ⟨2701416702604370544805157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1800944468402913696536771 2701416702604370544805157)
                  ·
                    refine ⟨506515631738319477150967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2701416702604370544805157 506515631738319477150967)
                    ·
                      rfl

theorem cell23_2959307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 1, 4].length) (baseStart_2959307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959307 prefixEnd_2959307 := by exact prefixLift 2959307
  have htrace : WordTrace (prefixWord ++ tailWord_2959307) baseStart_2959307 baseEnd_2959307 := by
    simpa [prefixWord, tailWord_2959307, baseEnd_2959307] using wordTrace_append hprefix tailTrace_2959307
  have hstable : (prefixWord ++ tailWord_2959307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959307).length < 2 ^ (prefixWord ++ tailWord_2959307).sum := by decide
  have hdescent : baseEnd_2959307 < baseStart_2959307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959363 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 1, 6]
def baseStart_2959363 : Nat := 118140960795 + 2959363 * 2 ^ 59
def prefixEnd_2959363 : Nat := 4983230072969 + 3 ^ 40 * 2959363 * 2
def baseEnd_2959363 : Nat := 506525216710536737450881

theorem tailTrace_2959363 : CollatzResearch.WordTrace tailWord_2959363 prefixEnd_2959363 506525216710536737450881 := by
  unfold tailWord_2959363
  simp only [CollatzResearch.WordTrace]
  refine ⟨107936835977740744807050743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71957890651827163204700495 107936835977740744807050743)
  ·
    refine ⟨161905253966611117210576115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107936835977740744807050743 161905253966611117210576115)
    ·
      refine ⟨242857880949916675815864173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161905253966611117210576115 242857880949916675815864173)
      ·
        refine ⟨91071705356218753430949065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 242857880949916675815864173 91071705356218753430949065)
        ·
          refine ⟨68303779017164065073211799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91071705356218753430949065 68303779017164065073211799)
          ·
            refine ⟨102455668525746097609817699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68303779017164065073211799 102455668525746097609817699)
            ·
              refine ⟨153683502788619146414726549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102455668525746097609817699 153683502788619146414726549)
              ·
                refine ⟨7203914193216522488190307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153683502788619146414726549 7203914193216522488190307)
                ·
                  refine ⟨10805871289824783732285461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7203914193216522488190307 10805871289824783732285461)
                  ·
                    refine ⟨506525216710536737450881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10805871289824783732285461 506525216710536737450881)
                    ·
                      rfl

theorem cell23_2959363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 1, 6].length) (baseStart_2959363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959363 prefixEnd_2959363 := by exact prefixLift 2959363
  have htrace : WordTrace (prefixWord ++ tailWord_2959363) baseStart_2959363 baseEnd_2959363 := by
    simpa [prefixWord, tailWord_2959363, baseEnd_2959363] using wordTrace_append hprefix tailTrace_2959363
  have hstable : (prefixWord ++ tailWord_2959363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959363).length < 2 ^ (prefixWord ++ tailWord_2959363).sum := by decide
  have hdescent : baseEnd_2959363 < baseStart_2959363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959381 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 3, 1, 3]
def baseStart_2959381 : Nat := 118140960795 + 2959381 * 2 ^ 59
def prefixEnd_2959381 : Nat := 4983230072969 + 3 ^ 40 * 2959381 * 2
def baseEnd_2959381 : Nat := 1519584892783391141927561

theorem tailTrace_2959381 : CollatzResearch.WordTrace tailWord_2959381 prefixEnd_2959381 1519584892783391141927561 := by
  unfold tailWord_2959381
  simp only [CollatzResearch.WordTrace]
  refine ⟨107937492491675533881205997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71958328327783689254137331 107937492491675533881205997)
  ·
    refine ⟨40476559684378325205452249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107937492491675533881205997 40476559684378325205452249)
    ·
      refine ⟨30357419763283743904089187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40476559684378325205452249 30357419763283743904089187)
      ·
        refine ⟨45536129644925615856133781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30357419763283743904089187 45536129644925615856133781)
        ·
          refine ⟨2134506077105888243256271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45536129644925615856133781 2134506077105888243256271)
          ·
            refine ⟨3201759115658832364884407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134506077105888243256271 3201759115658832364884407)
            ·
              refine ⟨4802638673488248547326611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201759115658832364884407 4802638673488248547326611)
              ·
                refine ⟨7203958010232372820989917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4802638673488248547326611 7203958010232372820989917)
                ·
                  refine ⟨2701484253837139807871219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7203958010232372820989917 2701484253837139807871219)
                  ·
                    refine ⟨4052226380755709711806829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2701484253837139807871219 4052226380755709711806829)
                    ·
                      refine ⟨1519584892783391141927561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4052226380755709711806829 1519584892783391141927561)
                      ·
                        rfl

theorem cell23_2959381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_2959381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959381 prefixEnd_2959381 := by exact prefixLift 2959381
  have htrace : WordTrace (prefixWord ++ tailWord_2959381) baseStart_2959381 baseEnd_2959381 := by
    simpa [prefixWord, tailWord_2959381, baseEnd_2959381] using wordTrace_append hprefix tailTrace_2959381
  have hstable : (prefixWord ++ tailWord_2959381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959381).length < 2 ^ (prefixWord ++ tailWord_2959381).sum := by decide
  have hdescent : baseEnd_2959381 < baseStart_2959381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959387 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 3, 2, 2]
def baseStart_2959387 : Nat := 118140960795 + 2959387 * 2 ^ 59
def prefixEnd_2959387 : Nat := 4983230072969 + 3 ^ 40 * 2959387 * 2
def baseEnd_2959387 : Nat := 1519587973667318118452533

theorem tailTrace_2959387 : CollatzResearch.WordTrace tailWord_2959387 prefixEnd_2959387 1519587973667318118452533 := by
  unfold tailWord_2959387
  simp only [CollatzResearch.WordTrace]
  refine ⟨107937711329653796905924415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71958474219769197937282943 107937711329653796905924415)
  ·
    refine ⟨161906566994480695358886623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107937711329653796905924415 161906566994480695358886623)
    ·
      refine ⟨242859850491721043038329935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161906566994480695358886623 242859850491721043038329935)
      ·
        refine ⟨364289775737581564557494903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242859850491721043038329935 364289775737581564557494903)
        ·
          refine ⟨546434663606372346836242355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364289775737581564557494903 546434663606372346836242355)
          ·
            refine ⟨819651995409558520254363533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546434663606372346836242355 819651995409558520254363533)
            ·
              refine ⟨307369498278584445095386325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 819651995409558520254363533 307369498278584445095386325)
              ·
                refine ⟨7203972615904322931923117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 307369498278584445095386325 7203972615904322931923117)
                ·
                  refine ⟨2701489730964121099471169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7203972615904322931923117 2701489730964121099471169)
                  ·
                    refine ⟨2026117298223090824603377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701489730964121099471169 2026117298223090824603377)
                    ·
                      refine ⟨1519587973667318118452533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026117298223090824603377 1519587973667318118452533)
                      ·
                        rfl

theorem cell23_2959387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 2, 2].length) (baseStart_2959387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959387 prefixEnd_2959387 := by exact prefixLift 2959387
  have htrace : WordTrace (prefixWord ++ tailWord_2959387) baseStart_2959387 baseEnd_2959387 := by
    simpa [prefixWord, tailWord_2959387, baseEnd_2959387] using wordTrace_append hprefix tailTrace_2959387
  have hstable : (prefixWord ++ tailWord_2959387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959387).length < 2 ^ (prefixWord ++ tailWord_2959387).sum := by decide
  have hdescent : baseEnd_2959387 < baseStart_2959387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959397 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_2959397 : Nat := 118140960795 + 2959397 * 2 ^ 59
def prefixEnd_2959397 : Nat := 4983230072969 + 3 ^ 40 * 2959397 * 2
def baseEnd_2959397 : Nat := 506531036157954359775829

theorem tailTrace_2959397 : CollatzResearch.WordTrace tailWord_2959397 prefixEnd_2959397 506531036157954359775829 := by
  unfold tailWord_2959397
  simp only [CollatzResearch.WordTrace]
  refine ⟨107938076059617568613788445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71958717373078379075858963 107938076059617568613788445)
  ·
    refine ⟨40476778522356588230170667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107938076059617568613788445 40476778522356588230170667)
    ·
      refine ⟨60715167783534882345256001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40476778522356588230170667 60715167783534882345256001)
      ·
        refine ⟨45536375837651161758942001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60715167783534882345256001 45536375837651161758942001)
        ·
          refine ⟨34152281878238371319206501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45536375837651161758942001 34152281878238371319206501)
          ·
            refine ⟨6403552852169694622351219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34152281878238371319206501 6403552852169694622351219)
            ·
              refine ⟨9605329278254541933526829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6403552852169694622351219 9605329278254541933526829)
              ·
                refine ⟨3601998479345453225072561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9605329278254541933526829 3601998479345453225072561)
                ·
                  refine ⟨2701498859509089918804421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3601998479345453225072561 2701498859509089918804421)
                  ·
                    refine ⟨506531036157954359775829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2701498859509089918804421 506531036157954359775829)
                    ·
                      rfl

theorem cell23_2959397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_2959397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959397 prefixEnd_2959397 := by exact prefixLift 2959397
  have htrace : WordTrace (prefixWord ++ tailWord_2959397) baseStart_2959397 baseEnd_2959397 := by
    simpa [prefixWord, tailWord_2959397, baseEnd_2959397] using wordTrace_append hprefix tailTrace_2959397
  have hstable : (prefixWord ++ tailWord_2959397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959397).length < 2 ^ (prefixWord ++ tailWord_2959397).sum := by decide
  have hdescent : baseEnd_2959397 < baseStart_2959397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959417 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2959417 : Nat := 118140960795 + 2959417 * 2 ^ 59
def prefixEnd_2959417 : Nat := 4983230072969 + 3 ^ 40 * 2959417 * 2
def baseEnd_2959417 : Nat := 1519603378086953001077395

theorem tailTrace_2959417 : CollatzResearch.WordTrace tailWord_2959417 prefixEnd_2959417 1519603378086953001077395 := by
  unfold tailWord_2959417
  simp only [CollatzResearch.WordTrace]
  refine ⟨107938805519545112029516505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71959203679696741353011003 107938805519545112029516505)
  ·
    refine ⟨80954104139658834022137379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107938805519545112029516505 80954104139658834022137379)
    ·
      refine ⟨121431156209488251033206069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80954104139658834022137379 121431156209488251033206069)
      ·
        refine ⟨11384170894639523534363069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121431156209488251033206069 11384170894639523534363069)
        ·
          refine ⟨4269064085489821325386151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11384170894639523534363069 4269064085489821325386151)
          ·
            refine ⟨6403596128234731988079227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269064085489821325386151 6403596128234731988079227)
            ·
              refine ⟨9605394192352097982118841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6403596128234731988079227 9605394192352097982118841)
              ·
                refine ⟨7204045644264073486589131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9605394192352097982118841 7204045644264073486589131)
                ·
                  refine ⟨10806068466396110229883697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7204045644264073486589131 10806068466396110229883697)
                  ·
                    refine ⟨8104551349797082672412773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10806068466396110229883697 8104551349797082672412773)
                    ·
                      refine ⟨1519603378086953001077395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8104551349797082672412773 1519603378086953001077395)
                      ·
                        rfl

theorem cell23_2959417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2959417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959417 prefixEnd_2959417 := by exact prefixLift 2959417
  have htrace : WordTrace (prefixWord ++ tailWord_2959417) baseStart_2959417 baseEnd_2959417 := by
    simpa [prefixWord, tailWord_2959417, baseEnd_2959417] using wordTrace_append hprefix tailTrace_2959417
  have hstable : (prefixWord ++ tailWord_2959417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959417).length < 2 ^ (prefixWord ++ tailWord_2959417).sum := by decide
  have hdescent : baseEnd_2959417 < baseStart_2959417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959421 : List Nat := [1, 4, 1, 3, 1, 1, 2, 5, 1, 2, 2]
def baseStart_2959421 : Nat := 118140960795 + 2959421 * 2 ^ 59
def prefixEnd_2959421 : Nat := 4983230072969 + 3 ^ 40 * 2959421 * 2
def baseEnd_2959421 : Nat := 1519605432009570985427377

theorem tailTrace_2959421 : CollatzResearch.WordTrace tailWord_2959421 prefixEnd_2959421 1519605432009570985427377 := by
  unfold tailWord_2959421
  simp only [CollatzResearch.WordTrace]
  refine ⟨107938951411530620712662117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71959300941020413808441411 107938951411530620712662117)
  ·
    refine ⟨20238553389661991383624147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107938951411530620712662117 20238553389661991383624147)
    ·
      refine ⟨30357830084492987075436221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20238553389661991383624147 30357830084492987075436221)
      ·
        refine ⟨11384186281684870153288583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30357830084492987075436221 11384186281684870153288583)
        ·
          refine ⟨17076279422527305229932875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11384186281684870153288583 17076279422527305229932875)
          ·
            refine ⟨25614419133790957844899313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17076279422527305229932875 25614419133790957844899313)
            ·
              refine ⟨19210814350343218383674485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25614419133790957844899313 19210814350343218383674485)
              ·
                refine ⟨1801013845344676723469483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19210814350343218383674485 1801013845344676723469483)
                ·
                  refine ⟨2701520768017015085204225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801013845344676723469483 2701520768017015085204225)
                  ·
                    refine ⟨2026140576012761313903169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701520768017015085204225 2026140576012761313903169)
                    ·
                      refine ⟨1519605432009570985427377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026140576012761313903169 1519605432009570985427377)
                      ·
                        rfl

theorem cell23_2959421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_2959421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959421 prefixEnd_2959421 := by exact prefixLift 2959421
  have htrace : WordTrace (prefixWord ++ tailWord_2959421) baseStart_2959421 baseEnd_2959421 := by
    simpa [prefixWord, tailWord_2959421, baseEnd_2959421] using wordTrace_append hprefix tailTrace_2959421
  have hstable : (prefixWord ++ tailWord_2959421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959421).length < 2 ^ (prefixWord ++ tailWord_2959421).sum := by decide
  have hdescent : baseEnd_2959421 < baseStart_2959421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959424 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 1, 2, 3]
def baseStart_2959424 : Nat := 118140960795 + 2959424 * 2 ^ 59
def prefixEnd_2959424 : Nat := 4983230072969 + 3 ^ 40 * 2959424 * 2
def baseEnd_2959424 : Nat := 1519606972451534473689863

theorem tailTrace_2959424 : CollatzResearch.WordTrace tailWord_2959424 prefixEnd_2959424 1519606972451534473689863 := by
  unfold tailWord_2959424
  simp only [CollatzResearch.WordTrace]
  refine ⟨53969530415259876112510663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71959373887013168150014217 53969530415259876112510663)
  ·
    refine ⟨80954295622889814168765995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53969530415259876112510663 80954295622889814168765995)
    ·
      refine ⟨121431443434334721253148993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80954295622889814168765995 121431443434334721253148993)
      ·
        refine ⟨91073582575751040939861745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121431443434334721253148993 91073582575751040939861745)
        ·
          refine ⟨68305186931813280704896309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91073582575751040939861745 68305186931813280704896309)
          ·
            refine ⟨6403611274857495066084029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68305186931813280704896309 6403611274857495066084029)
            ·
              refine ⟨2401354228071560649781511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6403611274857495066084029 2401354228071560649781511)
              ·
                refine ⟨3602031342107340974672267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401354228071560649781511 3602031342107340974672267)
                ·
                  refine ⟨5403047013161011462008401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3602031342107340974672267 5403047013161011462008401)
                  ·
                    refine ⟨4052285259870758596506301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5403047013161011462008401 4052285259870758596506301)
                    ·
                      refine ⟨1519606972451534473689863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4052285259870758596506301 1519606972451534473689863)
                      ·
                        rfl

theorem cell23_2959424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_2959424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959424 prefixEnd_2959424 := by exact prefixLift 2959424
  have htrace : WordTrace (prefixWord ++ tailWord_2959424) baseStart_2959424 baseEnd_2959424 := by
    simpa [prefixWord, tailWord_2959424, baseEnd_2959424] using wordTrace_append hprefix tailTrace_2959424
  have hstable : (prefixWord ++ tailWord_2959424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959424).length < 2 ^ (prefixWord ++ tailWord_2959424).sum := by decide
  have hdescent : baseEnd_2959424 < baseStart_2959424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959437 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2959437 : Nat := 118140960795 + 2959437 * 2 ^ 59
def prefixEnd_2959437 : Nat := 4983230072969 + 3 ^ 40 * 2959437 * 2
def baseEnd_2959437 : Nat := 1519613647700042922827303

theorem tailTrace_2959437 : CollatzResearch.WordTrace tailWord_2959437 prefixEnd_2959437 1519613647700042922827303 := by
  unfold tailWord_2959437
  simp only [CollatzResearch.WordTrace]
  refine ⟨107939534979472655445244565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71959689986315103630163043 107939534979472655445244565)
  ·
    refine ⟨5059665702162780723995839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107939534979472655445244565 5059665702162780723995839)
    ·
      refine ⟨7589498553244171085993759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5059665702162780723995839 7589498553244171085993759)
      ·
        refine ⟨11384247829866256628990639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7589498553244171085993759 11384247829866256628990639)
        ·
          refine ⟨17076371744799384943485959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11384247829866256628990639 17076371744799384943485959)
          ·
            refine ⟨25614557617199077415228939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17076371744799384943485959 25614557617199077415228939)
            ·
              refine ⟨38421836425798616122843409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25614557617199077415228939 38421836425798616122843409)
              ·
                refine ⟨28816377319348962092132557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38421836425798616122843409 28816377319348962092132557)
                ·
                  refine ⟨10806141494755860784549709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28816377319348962092132557 10806141494755860784549709)
                  ·
                    refine ⟨4052303060533447794206141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10806141494755860784549709 4052303060533447794206141)
                    ·
                      refine ⟨1519613647700042922827303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4052303060533447794206141 1519613647700042922827303)
                      ·
                        rfl

theorem cell23_2959437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2959437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959437 prefixEnd_2959437 := by exact prefixLift 2959437
  have htrace : WordTrace (prefixWord ++ tailWord_2959437) baseStart_2959437 baseEnd_2959437 := by
    simpa [prefixWord, tailWord_2959437, baseEnd_2959437] using wordTrace_append hprefix tailTrace_2959437
  have hstable : (prefixWord ++ tailWord_2959437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959437).length < 2 ^ (prefixWord ++ tailWord_2959437).sum := by decide
  have hdescent : baseEnd_2959437 < baseStart_2959437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959438 : List Nat := [4, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2]
def baseStart_2959438 : Nat := 118140960795 + 2959438 * 2 ^ 59
def prefixEnd_2959438 : Nat := 4983230072969 + 3 ^ 40 * 2959438 * 2
def baseEnd_2959438 : Nat := 1519614161180697418914799

theorem tailTrace_2959438 : CollatzResearch.WordTrace tailWord_2959438 prefixEnd_2959438 1519614161180697418914799 := by
  unfold tailWord_2959438
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492446431558629077003871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71959714301646021744020645 13492446431558629077003871)
  ·
    refine ⟨20238669647337943615505807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13492446431558629077003871 20238669647337943615505807)
    ·
      refine ⟨30358004471006915423258711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20238669647337943615505807 30358004471006915423258711)
      ·
        refine ⟨45537006706510373134888067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30358004471006915423258711 45537006706510373134888067)
        ·
          refine ⟨68305510059765559702332101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45537006706510373134888067 68305510059765559702332101)
          ·
            refine ⟨12807283136206042444187269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68305510059765559702332101 12807283136206042444187269)
            ·
              refine ⟨2401365588038632958285113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12807283136206042444187269 2401365588038632958285113)
              ·
                refine ⟨1801024191028974718713835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2401365588038632958285113 1801024191028974718713835)
                ·
                  refine ⟨2701536286543462078070753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801024191028974718713835 2701536286543462078070753)
                  ·
                    refine ⟨2026152214907596558553065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2701536286543462078070753 2026152214907596558553065)
                    ·
                      refine ⟨1519614161180697418914799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026152214907596558553065 1519614161180697418914799)
                      ·
                        rfl

theorem cell23_2959438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_2959438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959438 prefixEnd_2959438 := by exact prefixLift 2959438
  have htrace : WordTrace (prefixWord ++ tailWord_2959438) baseStart_2959438 baseEnd_2959438 := by
    simpa [prefixWord, tailWord_2959438, baseEnd_2959438] using wordTrace_append hprefix tailTrace_2959438
  have hstable : (prefixWord ++ tailWord_2959438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959438).length < 2 ^ (prefixWord ++ tailWord_2959438).sum := by decide
  have hdescent : baseEnd_2959438 < baseStart_2959438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959447 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 3, 3, 2]
def baseStart_2959447 : Nat := 118140960795 + 2959447 * 2 ^ 59
def prefixEnd_2959447 : Nat := 4983230072969 + 3 ^ 40 * 2959447 * 2
def baseEnd_2959447 : Nat := 1519618782506587883702257

theorem tailTrace_2959447 : CollatzResearch.WordTrace tailWord_2959447 prefixEnd_2959447 1519618782506587883702257 := by
  unfold tailWord_2959447
  simp only [CollatzResearch.WordTrace]
  refine ⟨107939899709436427153108595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71959933139624284768739063 107939899709436427153108595)
  ·
    refine ⟨161909849564154640729662893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107939899709436427153108595 161909849564154640729662893)
    ·
      refine ⟨60716193586557990273623585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161909849564154640729662893 60716193586557990273623585)
      ·
        refine ⟨45537145189918492705217689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60716193586557990273623585 45537145189918492705217689)
        ·
          refine ⟨34152858892438869528913267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45537145189918492705217689 34152858892438869528913267)
          ·
            refine ⟨51229288338658304293369901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34152858892438869528913267 51229288338658304293369901)
            ·
              refine ⟨19210983126996864110013713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51229288338658304293369901 19210983126996864110013713)
              ·
                refine ⟨14408237345247648082510285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19210983126996864110013713 14408237345247648082510285)
                ·
                  refine ⟨5403089004467868030941357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14408237345247648082510285 5403089004467868030941357)
                  ·
                    refine ⟨2026158376675450511603009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5403089004467868030941357 2026158376675450511603009)
                    ·
                      refine ⟨1519618782506587883702257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026158376675450511603009 1519618782506587883702257)
                      ·
                        rfl

theorem cell23_2959447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_2959447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959447 prefixEnd_2959447 := by exact prefixLift 2959447
  have htrace : WordTrace (prefixWord ++ tailWord_2959447) baseStart_2959447 baseEnd_2959447 := by
    simpa [prefixWord, tailWord_2959447, baseEnd_2959447] using wordTrace_append hprefix tailTrace_2959447
  have hstable : (prefixWord ++ tailWord_2959447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959447).length < 2 ^ (prefixWord ++ tailWord_2959447).sum := by decide
  have hdescent : baseEnd_2959447 < baseStart_2959447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959470 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2959470 : Nat := 118140960795 + 2959470 * 2 ^ 59
def prefixEnd_2959470 : Nat := 4983230072969 + 3 ^ 40 * 2959470 * 2
def baseEnd_2959470 : Nat := 506543530853880431238217

theorem tailTrace_2959470 : CollatzResearch.WordTrace tailWord_2959470 prefixEnd_2959470 506543530853880431238217 := by
  unfold tailWord_2959470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13492592323544137760149483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71960492392235401387463909 13492592323544137760149483)
  ·
    refine ⟨20238888485316206640224225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13492592323544137760149483 20238888485316206640224225)
    ·
      refine ⟨15179166363987154980168169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20238888485316206640224225 15179166363987154980168169)
      ·
        refine ⟨11384374772990366235126127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15179166363987154980168169 11384374772990366235126127)
        ·
          refine ⟨17076562159485549352689191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11384374772990366235126127 17076562159485549352689191)
          ·
            refine ⟨25614843239228324029033787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17076562159485549352689191 25614843239228324029033787)
            ·
              refine ⟨38422264858842486043550681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25614843239228324029033787 38422264858842486043550681)
              ·
                refine ⟨28816698644131864532663011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38422264858842486043550681 28816698644131864532663011)
                ·
                  refine ⟨43225047966197796798994517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28816698644131864532663011 43225047966197796798994517)
                  ·
                    refine ⟨506543530853880431238217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43225047966197796798994517 506543530853880431238217)
                    ·
                      rfl

theorem cell23_2959470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2959470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959470 prefixEnd_2959470 := by exact prefixLift 2959470
  have htrace : WordTrace (prefixWord ++ tailWord_2959470) baseStart_2959470 baseEnd_2959470 := by
    simpa [prefixWord, tailWord_2959470, baseEnd_2959470] using wordTrace_append hprefix tailTrace_2959470
  have hstable : (prefixWord ++ tailWord_2959470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959470).length < 2 ^ (prefixWord ++ tailWord_2959470).sum := by decide
  have hdescent : baseEnd_2959470 < baseStart_2959470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959481 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 1, 3, 2]
def baseStart_2959481 : Nat := 118140960795 + 2959481 * 2 ^ 59
def prefixEnd_2959481 : Nat := 4983230072969 + 3 ^ 40 * 2959481 * 2
def baseEnd_2959481 : Nat := 1519636240848840750677101

theorem tailTrace_2959481 : CollatzResearch.WordTrace tailWord_2959481 prefixEnd_2959481 1519636240848840750677101 := by
  unfold tailWord_2959481
  simp only [CollatzResearch.WordTrace]
  refine ⟨107941139791313250959846297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71960759860875500639897531 107941139791313250959846297)
  ·
    refine ⟨80955854843484938219884723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107941139791313250959846297 80955854843484938219884723)
    ·
      refine ⟨121433782265227407329827085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80955854843484938219884723 121433782265227407329827085)
      ·
        refine ⟨45537668349460277748685157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121433782265227407329827085 45537668349460277748685157)
        ·
          refine ⟨8538312815523802077878467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45537668349460277748685157 8538312815523802077878467)
          ·
            refine ⟨12807469223285703116817701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8538312815523802077878467 12807469223285703116817701)
            ·
              refine ⟨2401400479366069334403319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12807469223285703116817701 2401400479366069334403319)
              ·
                refine ⟨3602100719049104001604979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2401400479366069334403319 3602100719049104001604979)
                ·
                  refine ⟨5403151078573656002407469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3602100719049104001604979 5403151078573656002407469)
                  ·
                    refine ⟨2026181654465121000902801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5403151078573656002407469 2026181654465121000902801)
                    ·
                      refine ⟨1519636240848840750677101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026181654465121000902801 1519636240848840750677101)
                      ·
                        rfl

theorem cell23_2959481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_2959481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959481 prefixEnd_2959481 := by exact prefixLift 2959481
  have htrace : WordTrace (prefixWord ++ tailWord_2959481) baseStart_2959481 baseEnd_2959481 := by
    simpa [prefixWord, tailWord_2959481, baseEnd_2959481] using wordTrace_append hprefix tailTrace_2959481
  have hstable : (prefixWord ++ tailWord_2959481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959481).length < 2 ^ (prefixWord ++ tailWord_2959481).sum := by decide
  have hdescent : baseEnd_2959481 < baseStart_2959481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959511 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 1, 4, 2]
def baseStart_2959511 : Nat := 118140960795 + 2959511 * 2 ^ 59
def prefixEnd_2959511 : Nat := 4983230072969 + 3 ^ 40 * 2959511 * 2
def baseEnd_2959511 : Nat := 1519651645268475633301963

theorem tailTrace_2959511 : CollatzResearch.WordTrace tailWord_2959511 prefixEnd_2959511 1519651645268475633301963 := by
  unfold tailWord_2959511
  simp only [CollatzResearch.WordTrace]
  refine ⟨107942233981204566083438387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71961489320803044055625591 107942233981204566083438387)
  ·
    refine ⟨161913350971806849125157581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107942233981204566083438387 161913350971806849125157581)
    ·
      refine ⟨60717506614427568421934093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161913350971806849125157581 60717506614427568421934093)
      ·
        refine ⟨22769064980410338158225285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60717506614427568421934093 22769064980410338158225285)
        ·
          refine ⟨4269199683826938404667241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22769064980410338158225285 4269199683826938404667241)
          ·
            refine ⟨3201899762870203803500431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4269199683826938404667241 3201899762870203803500431)
            ·
              refine ⟨4802849644305305705250647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3201899762870203803500431 4802849644305305705250647)
              ·
                refine ⟨7204274466457958557875971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4802849644305305705250647 7204274466457958557875971)
                ·
                  refine ⟨10806411699686937836813957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7204274466457958557875971 10806411699686937836813957)
                  ·
                    refine ⟨2026202193691300844402617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10806411699686937836813957 2026202193691300844402617)
                    ·
                      refine ⟨1519651645268475633301963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026202193691300844402617 1519651645268475633301963)
                      ·
                        rfl

theorem cell23_2959511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_2959511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959511 prefixEnd_2959511 := by exact prefixLift 2959511
  have htrace : WordTrace (prefixWord ++ tailWord_2959511) baseStart_2959511 baseEnd_2959511 := by
    simpa [prefixWord, tailWord_2959511, baseEnd_2959511] using wordTrace_append hprefix tailTrace_2959511
  have hstable : (prefixWord ++ tailWord_2959511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959511).length < 2 ^ (prefixWord ++ tailWord_2959511).sum := by decide
  have hdescent : baseEnd_2959511 < baseStart_2959511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959567 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 1, 6, 2]
def baseStart_2959567 : Nat := 118140960795 + 2959567 * 2 ^ 59
def prefixEnd_2959567 : Nat := 4983230072969 + 3 ^ 40 * 2959567 * 2
def baseEnd_2959567 : Nat := 1519680400185127414201705

theorem tailTrace_2959567 : CollatzResearch.WordTrace tailWord_2959567 prefixEnd_2959567 1519680400185127414201705 := by
  unfold tailWord_2959567
  simp only [CollatzResearch.WordTrace]
  refine ⟨107944276469001687647476955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71962850979334458431651303 107944276469001687647476955)
  ·
    refine ⟨161916414703502531471215433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107944276469001687647476955 161916414703502531471215433)
    ·
      refine ⟨121437311027626898603411575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161916414703502531471215433 121437311027626898603411575)
      ·
        refine ⟨182155966541440347905117363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121437311027626898603411575 182155966541440347905117363)
        ·
          refine ⟨273233949812160521857676045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182155966541440347905117363 273233949812160521857676045)
          ·
            refine ⟨102462731179560195696628517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273233949812160521857676045 102462731179560195696628517)
            ·
              refine ⟨19211762096167536693117847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102462731179560195696628517 19211762096167536693117847)
              ·
                refine ⟨28817643144251305039676771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19211762096167536693117847 28817643144251305039676771)
                ·
                  refine ⟨43226464716376957559515157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28817643144251305039676771 43226464716376957559515157)
                  ·
                    refine ⟨2026240533580169885602273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43226464716376957559515157 2026240533580169885602273)
                    ·
                      refine ⟨1519680400185127414201705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026240533580169885602273 1519680400185127414201705)
                      ·
                        rfl

theorem cell23_2959567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 6, 2].length) (baseStart_2959567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959567 prefixEnd_2959567 := by exact prefixLift 2959567
  have htrace : WordTrace (prefixWord ++ tailWord_2959567) baseStart_2959567 baseEnd_2959567 := by
    simpa [prefixWord, tailWord_2959567, baseEnd_2959567] using wordTrace_append hprefix tailTrace_2959567
  have hstable : (prefixWord ++ tailWord_2959567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959567).length < 2 ^ (prefixWord ++ tailWord_2959567).sum := by decide
  have hdescent : baseEnd_2959567 < baseStart_2959567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959577 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 3, 4]
def baseStart_2959577 : Nat := 118140960795 + 2959577 * 2 ^ 59
def prefixEnd_2959577 : Nat := 4983230072969 + 3 ^ 40 * 2959577 * 2
def baseEnd_2959577 : Nat := 506561844997224125025553

theorem tailTrace_2959577 : CollatzResearch.WordTrace tailWord_2959577 prefixEnd_2959577 506561844997224125025553 := by
  unfold tailWord_2959577
  simp only [CollatzResearch.WordTrace]
  refine ⟨107944641198965459355340985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71963094132643639570227323 107944641198965459355340985)
  ·
    refine ⟨80958480899224094516505739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107944641198965459355340985 80958480899224094516505739)
    ·
      refine ⟨121437721348836141774758609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80958480899224094516505739 121437721348836141774758609)
      ·
        refine ⟨91078291011627106331068957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121437721348836141774758609 91078291011627106331068957)
        ·
          refine ⟨34154359129360164874150859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91078291011627106331068957 34154359129360164874150859)
          ·
            refine ⟨51231538694040247311226289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34154359129360164874150859 51231538694040247311226289)
            ·
              refine ⟨38423654020530185483419717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51231538694040247311226289 38423654020530185483419717)
              ·
                refine ⟨7204435128849409778141197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38423654020530185483419717 7204435128849409778141197)
                ·
                  refine ⟨2701663173318528666802949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7204435128849409778141197 2701663173318528666802949)
                  ·
                    refine ⟨506561844997224125025553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2701663173318528666802949 506561844997224125025553)
                    ·
                      rfl

theorem cell23_2959577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 3, 4].length) (baseStart_2959577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959577 prefixEnd_2959577 := by exact prefixLift 2959577
  have htrace : WordTrace (prefixWord ++ tailWord_2959577) baseStart_2959577 baseEnd_2959577 := by
    simpa [prefixWord, tailWord_2959577, baseEnd_2959577] using wordTrace_append hprefix tailTrace_2959577
  have hstable : (prefixWord ++ tailWord_2959577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959577).length < 2 ^ (prefixWord ++ tailWord_2959577).sum := by decide
  have hdescent : baseEnd_2959577 < baseStart_2959577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959637 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_2959637 : Nat := 118140960795 + 2959637 * 2 ^ 59
def prefixEnd_2959637 : Nat := 4983230072969 + 3 ^ 40 * 2959637 * 2
def baseEnd_2959637 : Nat := 506572114610314046775461

theorem tailTrace_2959637 : CollatzResearch.WordTrace tailWord_2959637 prefixEnd_2959637 506572114610314046775461 := by
  unfold tailWord_2959637
  simp only [CollatzResearch.WordTrace]
  refine ⟨107946829578748089602525165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71964553052498726401683443 107946829578748089602525165)
  ·
    refine ⟨40480061092030533600946937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107946829578748089602525165 40480061092030533600946937)
    ·
      refine ⟨30360045819022900200710203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40480061092030533600946937 30360045819022900200710203)
      ·
        refine ⟨45540068728534350301065305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30360045819022900200710203 45540068728534350301065305)
        ·
          refine ⟨34155051546400762725798979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45540068728534350301065305 34155051546400762725798979)
          ·
            refine ⟨51232577319601144088698469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34155051546400762725798979 51232577319601144088698469)
            ·
              refine ⟨9606108247425214516630963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51232577319601144088698469 9606108247425214516630963)
              ·
                refine ⟨14409162371137821774946445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9606108247425214516630963 14409162371137821774946445)
                ·
                  refine ⟨5403435889176683165604917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14409162371137821774946445 5403435889176683165604917)
                  ·
                    refine ⟨506572114610314046775461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5403435889176683165604917 506572114610314046775461)
                    ·
                      rfl

theorem cell23_2959637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_2959637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959637 prefixEnd_2959637 := by exact prefixLift 2959637
  have htrace : WordTrace (prefixWord ++ tailWord_2959637) baseStart_2959637 baseEnd_2959637 := by
    simpa [prefixWord, tailWord_2959637, baseEnd_2959637] using wordTrace_append hprefix tailTrace_2959637
  have hstable : (prefixWord ++ tailWord_2959637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959637).length < 2 ^ (prefixWord ++ tailWord_2959637).sum := by decide
  have hdescent : baseEnd_2959637 < baseStart_2959637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959658 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 6]
def baseStart_2959658 : Nat := 118140960795 + 2959658 * 2 ^ 59
def prefixEnd_2959658 : Nat := 4983230072969 + 3 ^ 40 * 2959658 * 2
def baseEnd_2959658 : Nat := 168858569658298506462643

theorem tailTrace_2959658 : CollatzResearch.WordTrace tailWord_2959658 prefixEnd_2959658 168858569658298506462643 := by
  unfold tailWord_2959658
  simp only [CollatzResearch.WordTrace]
  refine ⟨26986898877918002547259907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71965063674448006792693085 26986898877918002547259907)
  ·
    refine ⟨40480348316877003820889861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26986898877918002547259907 40480348316877003820889861)
    ·
      refine ⟨7590065309414438216416849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40480348316877003820889861 7590065309414438216416849)
      ·
        refine ⟨5692548982060828662312637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7590065309414438216416849 5692548982060828662312637)
        ·
          refine ⟨2134705868272810748367239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5692548982060828662312637 2134705868272810748367239)
          ·
            refine ⟨3202058802409216122550859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2134705868272810748367239 3202058802409216122550859)
            ·
              refine ⟨4803088203613824183826289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202058802409216122550859 4803088203613824183826289)
              ·
                refine ⟨3602316152710368137869717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4803088203613824183826289 3602316152710368137869717)
                ·
                  refine ⟨168858569658298506462643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3602316152710368137869717 168858569658298506462643)
                  ·
                    rfl

theorem cell23_2959658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 6].length) (baseStart_2959658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959658 prefixEnd_2959658 := by exact prefixLift 2959658
  have htrace : WordTrace (prefixWord ++ tailWord_2959658) baseStart_2959658 baseEnd_2959658 := by
    simpa [prefixWord, tailWord_2959658, baseEnd_2959658] using wordTrace_append hprefix tailTrace_2959658
  have hstable : (prefixWord ++ tailWord_2959658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959658).length < 2 ^ (prefixWord ++ tailWord_2959658).sum := by decide
  have hdescent : baseEnd_2959658 < baseStart_2959658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959668 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_2959668 : Nat := 118140960795 + 2959668 * 2 ^ 59
def prefixEnd_2959668 : Nat := 4983230072969 + 3 ^ 40 * 2959668 * 2
def baseEnd_2959668 : Nat := 1519732261731231519038741

theorem tailTrace_2959668 : CollatzResearch.WordTrace tailWord_2959668 prefixEnd_2959668 1519732261731231519038741 := by
  unfold tailWord_2959668
  simp only [CollatzResearch.WordTrace]
  refine ⟨53973980120817890948451829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71965306827757187931269105 53973980120817890948451829)
  ·
    refine ⟨5060060636326677276417359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53973980120817890948451829 5060060636326677276417359)
    ·
      refine ⟨7590090954490015914626039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5060060636326677276417359 7590090954490015914626039)
      ·
        refine ⟨11385136431735023871939059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7590090954490015914626039 11385136431735023871939059)
        ·
          refine ⟨17077704647602535807908589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11385136431735023871939059 17077704647602535807908589)
          ·
            refine ⟨6404139242850950927965721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17077704647602535807908589 6404139242850950927965721)
            ·
              refine ⟨4803104432138213195974291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6404139242850950927965721 4803104432138213195974291)
              ·
                refine ⟨7204656648207319793961437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4803104432138213195974291 7204656648207319793961437)
                ·
                  refine ⟨2701746243077744922735539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7204656648207319793961437 2701746243077744922735539)
                  ·
                    refine ⟨4052619364616617384103309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2701746243077744922735539 4052619364616617384103309)
                    ·
                      refine ⟨1519732261731231519038741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4052619364616617384103309 1519732261731231519038741)
                      ·
                        rfl

theorem cell23_2959668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_2959668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959668 prefixEnd_2959668 := by exact prefixLift 2959668
  have htrace : WordTrace (prefixWord ++ tailWord_2959668) baseStart_2959668 baseEnd_2959668 := by
    simpa [prefixWord, tailWord_2959668, baseEnd_2959668] using wordTrace_append hprefix tailTrace_2959668
  have hstable : (prefixWord ++ tailWord_2959668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959668).length < 2 ^ (prefixWord ++ tailWord_2959668).sum := by decide
  have hdescent : baseEnd_2959668 < baseStart_2959668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959687 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_2959687 : Nat := 118140960795 + 2959687 * 2 ^ 59
def prefixEnd_2959687 : Nat := 4983230072969 + 3 ^ 40 * 2959687 * 2
def baseEnd_2959687 : Nat := 1519742017863666944701153

theorem tailTrace_2959687 : CollatzResearch.WordTrace tailWord_2959687 prefixEnd_2959687 1519742017863666944701153 := by
  unfold tailWord_2959687
  simp only [CollatzResearch.WordTrace]
  refine ⟨107948653228566948141845315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71965768819044632094563543 107948653228566948141845315)
  ·
    refine ⟨161922979842850422212767973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107948653228566948141845315 161922979842850422212767973)
    ·
      refine ⟨30360558720534454164893995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161922979842850422212767973 30360558720534454164893995)
      ·
        refine ⟨45540838080801681247340993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30360558720534454164893995 45540838080801681247340993)
        ·
          refine ⟨34155628560601260935505745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45540838080801681247340993 34155628560601260935505745)
          ·
            refine ⟨25616721420450945701629309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34155628560601260935505745 25616721420450945701629309)
            ·
              refine ⟨9606270532669104638110991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25616721420450945701629309 9606270532669104638110991)
              ·
                refine ⟨14409405799003656957166487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9606270532669104638110991 14409405799003656957166487)
                ·
                  refine ⟨21614108698505485435749731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14409405799003656957166487 21614108698505485435749731)
                  ·
                    refine ⟨32421163047758228153624597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21614108698505485435749731 32421163047758228153624597)
                    ·
                      refine ⟨1519742017863666944701153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32421163047758228153624597 1519742017863666944701153)
                      ·
                        rfl

theorem cell23_2959687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_2959687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959687 prefixEnd_2959687 := by exact prefixLift 2959687
  have htrace : WordTrace (prefixWord ++ tailWord_2959687) baseStart_2959687 baseEnd_2959687 := by
    simpa [prefixWord, tailWord_2959687, baseEnd_2959687] using wordTrace_append hprefix tailTrace_2959687
  have hstable : (prefixWord ++ tailWord_2959687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959687).length < 2 ^ (prefixWord ++ tailWord_2959687).sum := by decide
  have hdescent : baseEnd_2959687 < baseStart_2959687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959697 : List Nat := [1, 2, 2, 1, 4, 3, 1, 9]
def baseStart_2959697 : Nat := 118140960795 + 2959697 * 2 ^ 59
def prefixEnd_2959697 : Nat := 4983230072969 + 3 ^ 40 * 2959697 * 2
def baseEnd_2959697 : Nat := 56286931580378218725041

theorem tailTrace_2959697 : CollatzResearch.WordTrace tailWord_2959697 prefixEnd_2959697 56286931580378218725041 := by
  unfold tailWord_2959697
  simp only [CollatzResearch.WordTrace]
  refine ⟨107949017958530719849709345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71966011972353813233139563 107949017958530719849709345)
  ·
    refine ⟨80961763468898039887282009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107949017958530719849709345 80961763468898039887282009)
    ·
      refine ⟨60721322601673529915461507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80961763468898039887282009 60721322601673529915461507)
      ·
        refine ⟨91081983902510294873192261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60721322601673529915461507 91081983902510294873192261)
        ·
          refine ⟨17077871981720680288723549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91081983902510294873192261 17077871981720680288723549)
          ·
            refine ⟨6404201993145255108271331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17077871981720680288723549 6404201993145255108271331)
            ·
              refine ⟨9606302989717882662406997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6404201993145255108271331 9606302989717882662406997)
              ·
                refine ⟨56286931580378218725041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9606302989717882662406997 56286931580378218725041)
                ·
                  rfl

theorem cell23_2959697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 9].length) (baseStart_2959697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959697 prefixEnd_2959697 := by exact prefixLift 2959697
  have htrace : WordTrace (prefixWord ++ tailWord_2959697) baseStart_2959697 baseEnd_2959697 := by
    simpa [prefixWord, tailWord_2959697, baseEnd_2959697] using wordTrace_append hprefix tailTrace_2959697
  have hstable : (prefixWord ++ tailWord_2959697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959697).length < 2 ^ (prefixWord ++ tailWord_2959697).sum := by decide
  have hdescent : baseEnd_2959697 < baseStart_2959697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959714 : List Nat := [3, 3, 2, 1, 1, 4, 9]
def baseStart_2959714 : Nat := 118140960795 + 2959714 * 2 ^ 59
def prefixEnd_2959714 : Nat := 4983230072969 + 3 ^ 40 * 2959714 * 2
def baseEnd_2959714 : Nat := 18762418294337510358809

theorem tailTrace_2959714 : CollatzResearch.WordTrace tailWord_2959714 prefixEnd_2959714 18762418294337510358809 := by
  unfold tailWord_2959714
  simp only [CollatzResearch.WordTrace]
  refine ⟨26987409499867282938269549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71966425332979421168718797 26987409499867282938269549)
  ·
    refine ⟨10120278562450231101851081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26987409499867282938269549 10120278562450231101851081)
    ·
      refine ⟨7590208921837673326388311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10120278562450231101851081 7590208921837673326388311)
      ·
        refine ⟨11385313382756509989582467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7590208921837673326388311 11385313382756509989582467)
        ·
          refine ⟨17077970074134764984373701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11385313382756509989582467 17077970074134764984373701)
          ·
            refine ⟨3202119388900268434570069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17077970074134764984373701 3202119388900268434570069)
            ·
              refine ⟨18762418294337510358809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3202119388900268434570069 18762418294337510358809)
              ·
                rfl

theorem cell23_2959714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 9].length) (baseStart_2959714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959714 prefixEnd_2959714 := by exact prefixLift 2959714
  have htrace : WordTrace (prefixWord ++ tailWord_2959714) baseStart_2959714 baseEnd_2959714 := by
    simpa [prefixWord, tailWord_2959714, baseEnd_2959714] using wordTrace_append hprefix tailTrace_2959714
  have hstable : (prefixWord ++ tailWord_2959714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959714).length < 2 ^ (prefixWord ++ tailWord_2959714).sum := by decide
  have hdescent : baseEnd_2959714 < baseStart_2959714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959751 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 3, 3, 2]
def baseStart_2959751 : Nat := 118140960795 + 2959751 * 2 ^ 59
def prefixEnd_2959751 : Nat := 4983230072969 + 3 ^ 40 * 2959751 * 2
def baseEnd_2959751 : Nat := 1519774880625554694300859

theorem tailTrace_2959751 : CollatzResearch.WordTrace tailWord_2959751 prefixEnd_2959751 1519774880625554694300859 := by
  unfold tailWord_2959751
  simp only [CollatzResearch.WordTrace]
  refine ⟨107950987500335087072175107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71967325000223391381450071 107950987500335087072175107)
  ·
    refine ⟨161926481250502630608262661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107950987500335087072175107 161926481250502630608262661)
    ·
      refine ⟨30361215234469243239049249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161926481250502630608262661 30361215234469243239049249)
      ·
        refine ⟨22770911425851932429286937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30361215234469243239049249 22770911425851932429286937)
        ·
          refine ⟨17078183569388949321965203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22770911425851932429286937 17078183569388949321965203)
          ·
            refine ⟨25617275354083423982947805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17078183569388949321965203 25617275354083423982947805)
            ·
              refine ⟨9606478257781283993605427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25617275354083423982947805 9606478257781283993605427)
              ·
                refine ⟨14409717386671925990408141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9606478257781283993605427 14409717386671925990408141)
                ·
                  refine ⟨5403644020001972246403053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14409717386671925990408141 5403644020001972246403053)
                  ·
                    refine ⟨2026366507500739592401145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5403644020001972246403053 2026366507500739592401145)
                    ·
                      refine ⟨1519774880625554694300859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026366507500739592401145 1519774880625554694300859)
                      ·
                        rfl

theorem cell23_2959751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_2959751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959751 prefixEnd_2959751 := by exact prefixLift 2959751
  have htrace : WordTrace (prefixWord ++ tailWord_2959751) baseStart_2959751 baseEnd_2959751 := by
    simpa [prefixWord, tailWord_2959751, baseEnd_2959751] using wordTrace_append hprefix tailTrace_2959751
  have hstable : (prefixWord ++ tailWord_2959751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959751).length < 2 ^ (prefixWord ++ tailWord_2959751).sum := by decide
  have hdescent : baseEnd_2959751 < baseStart_2959751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959794 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_2959794 : Nat := 118140960795 + 2959794 * 2 ^ 59
def prefixEnd_2959794 : Nat := 4983230072969 + 3 ^ 40 * 2959794 * 2
def baseEnd_2959794 : Nat := 1519796960293698026063161

theorem tailTrace_2959794 : CollatzResearch.WordTrace tailWord_2959794 prefixEnd_2959794 1519796960293698026063161 := by
  unfold tailWord_2959794
  simp only [CollatzResearch.WordTrace]
  refine ⟨26988138959794826353997609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71968370559452870277326957 26988138959794826353997609)
  ·
    refine ⟨20241104219846119765498207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26988138959794826353997609 20241104219846119765498207)
    ·
      refine ⟨30361656329769179648247311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20241104219846119765498207 30361656329769179648247311)
      ·
        refine ⟨45542484494653769472370967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30361656329769179648247311 45542484494653769472370967)
        ·
          refine ⟨68313726741980654208556451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45542484494653769472370967 68313726741980654208556451)
          ·
            refine ⟨102470590112970981312834677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68313726741980654208556451 102470590112970981312834677)
            ·
              refine ⟨9606617823091029498078251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102470590112970981312834677 9606617823091029498078251)
              ·
                refine ⟨14409926734636544247117377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9606617823091029498078251 14409926734636544247117377)
                ·
                  refine ⟨10807445050977408185338033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14409926734636544247117377 10807445050977408185338033)
                  ·
                    refine ⟨8105583788233056139003525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10807445050977408185338033 8105583788233056139003525)
                    ·
                      refine ⟨1519796960293698026063161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8105583788233056139003525 1519796960293698026063161)
                      ·
                        rfl

theorem cell23_2959794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_2959794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959794 prefixEnd_2959794 := by exact prefixLift 2959794
  have htrace : WordTrace (prefixWord ++ tailWord_2959794) baseStart_2959794 baseEnd_2959794 := by
    simpa [prefixWord, tailWord_2959794, baseEnd_2959794] using wordTrace_append hprefix tailTrace_2959794
  have hstable : (prefixWord ++ tailWord_2959794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959794).length < 2 ^ (prefixWord ++ tailWord_2959794).sum := by decide
  have hdescent : baseEnd_2959794 < baseStart_2959794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959804 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 9]
def baseStart_2959804 : Nat := 118140960795 + 2959804 * 2 ^ 59
def prefixEnd_2959804 : Nat := 4983230072969 + 3 ^ 40 * 2959804 * 2
def baseEnd_2959804 : Nat := 168866899455582554104235

theorem tailTrace_2959804 : CollatzResearch.WordTrace tailWord_2959804 prefixEnd_2959804 168866899455582554104235 := by
  unfold tailWord_2959804
  simp only [CollatzResearch.WordTrace]
  refine ⟨53976460284571538561927233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71968613712762051415902977 53976460284571538561927233)
  ·
    refine ⟨40482345213428653921445425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53976460284571538561927233 40482345213428653921445425)
    ·
      refine ⟨30361758910071490441084069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40482345213428653921445425 30361758910071490441084069)
      ·
        refine ⟨5692829795638404457703263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30361758910071490441084069 5692829795638404457703263)
        ·
          refine ⟨8539244693457606686554895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5692829795638404457703263 8539244693457606686554895)
          ·
            refine ⟨12808867040186410029832343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8539244693457606686554895 12808867040186410029832343)
            ·
              refine ⟨19213300560279615044748515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12808867040186410029832343 19213300560279615044748515)
              ·
                refine ⟨28819950840419422567122773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19213300560279615044748515 28819950840419422567122773)
                ·
                  refine ⟨168866899455582554104235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28819950840419422567122773 168866899455582554104235)
                  ·
                    rfl

theorem cell23_2959804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_2959804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959804 prefixEnd_2959804 := by exact prefixLift 2959804
  have htrace : WordTrace (prefixWord ++ tailWord_2959804) baseStart_2959804 baseEnd_2959804 := by
    simpa [prefixWord, tailWord_2959804, baseEnd_2959804] using wordTrace_append hprefix tailTrace_2959804
  have hstable : (prefixWord ++ tailWord_2959804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959804).length < 2 ^ (prefixWord ++ tailWord_2959804).sum := by decide
  have hdescent : baseEnd_2959804 < baseStart_2959804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959834 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_2959834 : Nat := 118140960795 + 2959834 * 2 ^ 59
def prefixEnd_2959834 : Nat := 4983230072969 + 3 ^ 40 * 2959834 * 2
def baseEnd_2959834 : Nat := 506605833173292623187659

theorem tailTrace_2959834 : CollatzResearch.WordTrace tailWord_2959834 prefixEnd_2959834 506605833173292623187659 := by
  unfold tailWord_2959834
  simp only [CollatzResearch.WordTrace]
  refine ⟨26988503689758598061861639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71969343172689594831631037 26988503689758598061861639)
  ·
    refine ⟨40482755534637897092792459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26988503689758598061861639 40482755534637897092792459)
    ·
      refine ⟨60724133301956845639188689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40482755534637897092792459 60724133301956845639188689)
      ·
        refine ⟨45543099976467634229391517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60724133301956845639188689 45543099976467634229391517)
        ·
          refine ⟨17078662491175362836021819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45543099976467634229391517 17078662491175362836021819)
          ·
            refine ⟨25617993736763044254032729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17078662491175362836021819 25617993736763044254032729)
            ·
              refine ⟨19213495302572283190524547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25617993736763044254032729 19213495302572283190524547)
              ·
                refine ⟨28820242953858424785786821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19213495302572283190524547 28820242953858424785786821)
                ·
                  refine ⟨5403795553848454647335029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28820242953858424785786821 5403795553848454647335029)
                  ·
                    refine ⟨506605833173292623187659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5403795553848454647335029 506605833173292623187659)
                    ·
                      rfl

theorem cell23_2959834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_2959834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959834 prefixEnd_2959834 := by exact prefixLift 2959834
  have htrace : WordTrace (prefixWord ++ tailWord_2959834) baseStart_2959834 baseEnd_2959834 := by
    simpa [prefixWord, tailWord_2959834, baseEnd_2959834] using wordTrace_append hprefix tailTrace_2959834
  have hstable : (prefixWord ++ tailWord_2959834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959834).length < 2 ^ (prefixWord ++ tailWord_2959834).sum := by decide
  have hdescent : baseEnd_2959834 < baseStart_2959834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959885 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_2959885 : Nat := 118140960795 + 2959885 * 2 ^ 59
def prefixEnd_2959885 : Nat := 4983230072969 + 3 ^ 40 * 2959885 * 2
def baseEnd_2959885 : Nat := 506614562344419056675081

theorem tailTrace_2959885 : CollatzResearch.WordTrace tailWord_2959885 prefixEnd_2959885 506614562344419056675081 := by
  unfold tailWord_2959885
  simp only [CollatzResearch.WordTrace]
  refine ⟨107955874881849627957553109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71970583254566418638368739 107955874881849627957553109)
  ·
    refine ⟨2530215817543350655255151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 107955874881849627957553109 2530215817543350655255151)
    ·
      refine ⟨3795323726315025982882727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2530215817543350655255151 3795323726315025982882727)
      ·
        refine ⟨5692985589472538974324091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3795323726315025982882727 5692985589472538974324091)
        ·
          refine ⟨8539478384208808461486137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5692985589472538974324091 8539478384208808461486137)
          ·
            refine ⟨6404608788156606346114603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8539478384208808461486137 6404608788156606346114603)
            ·
              refine ⟨9606913182234909519171905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6404608788156606346114603 9606913182234909519171905)
              ·
                refine ⟨7205184886676182139378929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9606913182234909519171905 7205184886676182139378929)
                ·
                  refine ⟨5403888665007136604534197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7205184886676182139378929 5403888665007136604534197)
                  ·
                    refine ⟨506614562344419056675081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5403888665007136604534197 506614562344419056675081)
                    ·
                      rfl

theorem cell23_2959885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_2959885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959885 prefixEnd_2959885 := by exact prefixLift 2959885
  have htrace : WordTrace (prefixWord ++ tailWord_2959885) baseStart_2959885 baseEnd_2959885 := by
    simpa [prefixWord, tailWord_2959885, baseEnd_2959885] using wordTrace_append hprefix tailTrace_2959885
  have hstable : (prefixWord ++ tailWord_2959885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959885).length < 2 ^ (prefixWord ++ tailWord_2959885).sum := by decide
  have hdescent : baseEnd_2959885 < baseStart_2959885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959891 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 3]
def baseStart_2959891 : Nat := 118140960795 + 2959891 * 2 ^ 59
def prefixEnd_2959891 : Nat := 4983230072969 + 3 ^ 40 * 2959891 * 2
def baseEnd_2959891 : Nat := 1519846767917184146550215

theorem tailTrace_2959891 : CollatzResearch.WordTrace tailWord_2959891 prefixEnd_2959891 1519846767917184146550215 := by
  unfold tailWord_2959891
  simp only [CollatzResearch.WordTrace]
  refine ⟨107956093719827890982271527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71970729146551927321514351 107956093719827890982271527)
  ·
    refine ⟨161934140579741836473407291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107956093719827890982271527 161934140579741836473407291)
    ·
      refine ⟨242901210869612754710110937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161934140579741836473407291 242901210869612754710110937)
      ·
        refine ⟨182175908152209566032583203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242901210869612754710110937 182175908152209566032583203)
        ·
          refine ⟨273263862228314349048874805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182175908152209566032583203 273263862228314349048874805)
          ·
            refine ⟨25618487083904470223332013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 273263862228314349048874805 25618487083904470223332013)
            ·
              refine ⟨9606932656464176333749505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25618487083904470223332013 9606932656464176333749505)
              ·
                refine ⟨7205199492348132250312129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9606932656464176333749505 7205199492348132250312129)
                ·
                  refine ⟨5403899619261099187734097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7205199492348132250312129 5403899619261099187734097)
                  ·
                    refine ⟨4052924714445824390800573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5403899619261099187734097 4052924714445824390800573)
                    ·
                      refine ⟨1519846767917184146550215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4052924714445824390800573 1519846767917184146550215)
                      ·
                        rfl

theorem cell23_2959891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 2, 3].length) (baseStart_2959891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959891 prefixEnd_2959891 := by exact prefixLift 2959891
  have htrace : WordTrace (prefixWord ++ tailWord_2959891) baseStart_2959891 baseEnd_2959891 := by
    simpa [prefixWord, tailWord_2959891, baseEnd_2959891] using wordTrace_append hprefix tailTrace_2959891
  have hstable : (prefixWord ++ tailWord_2959891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959891).length < 2 ^ (prefixWord ++ tailWord_2959891).sum := by decide
  have hdescent : baseEnd_2959891 < baseStart_2959891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959898 : List Nat := [3, 1, 1, 3, 1, 1, 2, 6, 1, 4]
def baseStart_2959898 : Nat := 118140960795 + 2959898 * 2 ^ 59
def prefixEnd_2959898 : Nat := 4983230072969 + 3 ^ 40 * 2959898 * 2
def baseEnd_2959898 : Nat := 506616787427255206387561

theorem tailTrace_2959898 : CollatzResearch.WordTrace tailWord_2959898 prefixEnd_2959898 506616787427255206387561 := by
  unfold tailWord_2959898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26989087257700632794444087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71970899353868354118517565 26989087257700632794444087)
  ·
    refine ⟨40483630886550949191666131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26989087257700632794444087 40483630886550949191666131)
    ·
      refine ⟨60725446329826423787499197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40483630886550949191666131 60725446329826423787499197)
      ·
        refine ⟨22772042373684908920312199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60725446329826423787499197 22772042373684908920312199)
        ·
          refine ⟨34158063560527363380468299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22772042373684908920312199 34158063560527363380468299)
          ·
            refine ⟨51237095340791045070702449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34158063560527363380468299 51237095340791045070702449)
            ·
              refine ⟨38427821505593283803026837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51237095340791045070702449 38427821505593283803026837)
              ·
                refine ⟨1801304133074685178266883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38427821505593283803026837 1801304133074685178266883)
                ·
                  refine ⟨2701956199612027767400325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801304133074685178266883 2701956199612027767400325)
                  ·
                    refine ⟨506616787427255206387561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2701956199612027767400325 506616787427255206387561)
                    ·
                      rfl

theorem cell23_2959898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_2959898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959898 prefixEnd_2959898 := by exact prefixLift 2959898
  have htrace : WordTrace (prefixWord ++ tailWord_2959898) baseStart_2959898 baseEnd_2959898 := by
    simpa [prefixWord, tailWord_2959898, baseEnd_2959898] using wordTrace_append hprefix tailTrace_2959898
  have hstable : (prefixWord ++ tailWord_2959898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959898).length < 2 ^ (prefixWord ++ tailWord_2959898).sum := by decide
  have hdescent : baseEnd_2959898 < baseStart_2959898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959948 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 2, 3, 2]
def baseStart_2959948 : Nat := 118140960795 + 2959948 * 2 ^ 59
def prefixEnd_2959948 : Nat := 4983230072969 + 3 ^ 40 * 2959948 * 2
def baseEnd_2959948 : Nat := 1519876036314490423537453

theorem tailTrace_2959948 : CollatzResearch.WordTrace tailWord_2959948 prefixEnd_2959948 1519876036314490423537453 := by
  unfold tailWord_2959948
  simp only [CollatzResearch.WordTrace]
  refine ⟨53979086340310694858548249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71972115120414259811397665 53979086340310694858548249)
  ·
    refine ⟨40484314755233021143911187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53979086340310694858548249 40484314755233021143911187)
    ·
      refine ⟨60726472132849531715866781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40484314755233021143911187 60726472132849531715866781)
      ·
        refine ⟨22772427049818574393450043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60726472132849531715866781 22772427049818574393450043)
        ·
          refine ⟨34158640574727861590175065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22772427049818574393450043 34158640574727861590175065)
          ·
            refine ⟨25618980431045896192631299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34158640574727861590175065 25618980431045896192631299)
            ·
              refine ⟨38428470646568844288946949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25618980431045896192631299 38428470646568844288946949)
              ·
                refine ⟨7205338246231658304177553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38428470646568844288946949 7205338246231658304177553)
                ·
                  refine ⟨5404003684673743728133165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7205338246231658304177553 5404003684673743728133165)
                  ·
                    refine ⟨2026501381752653898049937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5404003684673743728133165 2026501381752653898049937)
                    ·
                      refine ⟨1519876036314490423537453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026501381752653898049937 1519876036314490423537453)
                      ·
                        rfl

theorem cell23_2959948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_2959948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959948 prefixEnd_2959948 := by exact prefixLift 2959948
  have htrace : WordTrace (prefixWord ++ tailWord_2959948) baseStart_2959948 baseEnd_2959948 := by
    simpa [prefixWord, tailWord_2959948, baseEnd_2959948] using wordTrace_append hprefix tailTrace_2959948
  have hstable : (prefixWord ++ tailWord_2959948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959948).length < 2 ^ (prefixWord ++ tailWord_2959948).sum := by decide
  have hdescent : baseEnd_2959948 < baseStart_2959948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959949 : List Nat := [1, 6, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_2959949 : Nat := 118140960795 + 2959949 * 2 ^ 59
def prefixEnd_2959949 : Nat := 4983230072969 + 3 ^ 40 * 2959949 * 2
def baseEnd_2959949 : Nat := 506625516598381639874983

theorem tailTrace_2959949 : CollatzResearch.WordTrace tailWord_2959949 prefixEnd_2959949 506625516598381639874983 := by
  unfold tailWord_2959949
  simp only [CollatzResearch.WordTrace]
  refine ⟨107958209153617766887882901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71972139435745177925255267 107958209153617766887882901)
  ·
    refine ⟨5060541054075832822869511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107958209153617766887882901 5060541054075832822869511)
    ·
      refine ⟨7590811581113749234304267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5060541054075832822869511 7590811581113749234304267)
      ·
        refine ⟨11386217371670623851456401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7590811581113749234304267 11386217371670623851456401)
        ·
          refine ⟨8539663028752967888592301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11386217371670623851456401 8539663028752967888592301)
          ·
            refine ⟨3202373635782362958222113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8539663028752967888592301 3202373635782362958222113)
            ·
              refine ⟨2401780226836772218666585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3202373635782362958222113 2401780226836772218666585)
              ·
                refine ⟨1801335170127579163999939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2401780226836772218666585 1801335170127579163999939)
                ·
                  refine ⟨2702002755191368745999909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801335170127579163999939 2702002755191368745999909)
                  ·
                    refine ⟨506625516598381639874983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2702002755191368745999909 506625516598381639874983)
                    ·
                      rfl

theorem cell23_2959949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_2959949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959949 prefixEnd_2959949 := by exact prefixLift 2959949
  have htrace : WordTrace (prefixWord ++ tailWord_2959949) baseStart_2959949 baseEnd_2959949 := by
    simpa [prefixWord, tailWord_2959949, baseEnd_2959949] using wordTrace_append hprefix tailTrace_2959949
  have hstable : (prefixWord ++ tailWord_2959949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959949).length < 2 ^ (prefixWord ++ tailWord_2959949).sum := by decide
  have hdescent : baseEnd_2959949 < baseStart_2959949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959961 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 4, 6, 2]
def baseStart_2959961 : Nat := 118140960795 + 2959961 * 2 ^ 59
def prefixEnd_2959961 : Nat := 4983230072969 + 3 ^ 40 * 2959961 * 2
def baseEnd_2959961 : Nat := 1519882711562998872674893

theorem tailTrace_2959961 : CollatzResearch.WordTrace tailWord_2959961 prefixEnd_2959961 1519882711562998872674893 := by
  unfold tailWord_2959961
  simp only [CollatzResearch.WordTrace]
  refine ⟨107958646829574292937319737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71972431219716195291546491 107958646829574292937319737)
  ·
    refine ⟨80968985122180719702989803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107958646829574292937319737 80968985122180719702989803)
    ·
      refine ⟨121453477683271079554484705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80968985122180719702989803 121453477683271079554484705)
      ·
        refine ⟨91090108262453309665863529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121453477683271079554484705 91090108262453309665863529)
        ·
          refine ⟨68317581196839982249397647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91090108262453309665863529 68317581196839982249397647)
          ·
            refine ⟨102476371795259973374096471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68317581196839982249397647 102476371795259973374096471)
            ·
              refine ⟨153714557692889960061144707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102476371795259973374096471 153714557692889960061144707)
              ·
                refine ⟨230571836539334940091717061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153714557692889960061144707 230571836539334940091717061)
                ·
                  refine ⟨43232219351125301267196949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 230571836539334940091717061 43232219351125301267196949)
                  ·
                    refine ⟨2026510282083998496899857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43232219351125301267196949 2026510282083998496899857)
                    ·
                      refine ⟨1519882711562998872674893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026510282083998496899857 1519882711562998872674893)
                      ·
                        rfl

theorem cell23_2959961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_2959961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959961 prefixEnd_2959961 := by exact prefixLift 2959961
  have htrace : WordTrace (prefixWord ++ tailWord_2959961) baseStart_2959961 baseEnd_2959961 := by
    simpa [prefixWord, tailWord_2959961, baseEnd_2959961] using wordTrace_append hprefix tailTrace_2959961
  have hstable : (prefixWord ++ tailWord_2959961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959961).length < 2 ^ (prefixWord ++ tailWord_2959961).sum := by decide
  have hdescent : baseEnd_2959961 < baseStart_2959961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959971 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 1, 6]
def baseStart_2959971 : Nat := 118140960795 + 2959971 * 2 ^ 59
def prefixEnd_2959971 : Nat := 4983230072969 + 3 ^ 40 * 2959971 * 2
def baseEnd_2959971 : Nat := 506629282123181277849949

theorem tailTrace_2959971 : CollatzResearch.WordTrace tailWord_2959971 prefixEnd_2959971 506629282123181277849949 := by
  unfold tailWord_2959971
  simp only [CollatzResearch.WordTrace]
  refine ⟨107959011559538064645183767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71972674373025376430122511 107959011559538064645183767)
  ·
    refine ⟨161938517339307096967775651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107959011559538064645183767 161938517339307096967775651)
    ·
      refine ⟨242907776008960645451663477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161938517339307096967775651 242907776008960645451663477)
      ·
        refine ⟨22772604000840060511093451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 242907776008960645451663477 22772604000840060511093451)
        ·
          refine ⟨34158906001260090766640177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22772604000840060511093451 34158906001260090766640177)
          ·
            refine ⟨25619179500945068074980133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34158906001260090766640177 25619179500945068074980133)
            ·
              refine ⟨4803596156427200264058775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25619179500945068074980133 4803596156427200264058775)
              ·
                refine ⟨7205394234640800396088163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4803596156427200264058775 7205394234640800396088163)
                ·
                  refine ⟨10808091351961200594132245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7205394234640800396088163 10808091351961200594132245)
                  ·
                    refine ⟨506629282123181277849949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10808091351961200594132245 506629282123181277849949)
                    ·
                      rfl

theorem cell23_2959971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 6].length) (baseStart_2959971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959971 prefixEnd_2959971 := by exact prefixLift 2959971
  have htrace : WordTrace (prefixWord ++ tailWord_2959971) baseStart_2959971 baseEnd_2959971 := by
    simpa [prefixWord, tailWord_2959971, baseEnd_2959971] using wordTrace_append hprefix tailTrace_2959971
  have hstable : (prefixWord ++ tailWord_2959971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959971).length < 2 ^ (prefixWord ++ tailWord_2959971).sum := by decide
  have hdescent : baseEnd_2959971 < baseStart_2959971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959978 : List Nat := [3, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_2959978 : Nat := 118140960795 + 2959978 * 2 ^ 59
def prefixEnd_2959978 : Nat := 4983230072969 + 3 ^ 40 * 2959978 * 2
def baseEnd_2959978 : Nat := 1519891440734125306162315

theorem tailTrace_2959978 : CollatzResearch.WordTrace tailWord_2959978 prefixEnd_2959978 1519891440734125306162315 := by
  unfold tailWord_2959978
  simp only [CollatzResearch.WordTrace]
  refine ⟨26989816717628176210172147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71972844580341803227125725 26989816717628176210172147)
  ·
    refine ⟨40484725076442264315258221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26989816717628176210172147 40484725076442264315258221)
    ·
      refine ⟨15181771903665849118221833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40484725076442264315258221 15181771903665849118221833)
      ·
        refine ⟨11386328927749386838666375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15181771903665849118221833 11386328927749386838666375)
        ·
          refine ⟨17079493391624080257999563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11386328927749386838666375 17079493391624080257999563)
          ·
            refine ⟨25619240087436120386999345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17079493391624080257999563 25619240087436120386999345)
            ·
              refine ⟨19214430065577090290249509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25619240087436120386999345 19214430065577090290249509)
              ·
                refine ⟨3602705637295704429421783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19214430065577090290249509 3602705637295704429421783)
                ·
                  refine ⟨5404058455943556644132675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3602705637295704429421783 5404058455943556644132675)
                  ·
                    refine ⟨8106087683915334966199013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5404058455943556644132675 8106087683915334966199013)
                    ·
                      refine ⟨1519891440734125306162315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8106087683915334966199013 1519891440734125306162315)
                      ·
                        rfl

theorem cell23_2959978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_2959978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959978 prefixEnd_2959978 := by exact prefixLift 2959978
  have htrace : WordTrace (prefixWord ++ tailWord_2959978) baseStart_2959978 baseEnd_2959978 := by
    simpa [prefixWord, tailWord_2959978, baseEnd_2959978] using wordTrace_append hprefix tailTrace_2959978
  have hstable : (prefixWord ++ tailWord_2959978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959978).length < 2 ^ (prefixWord ++ tailWord_2959978).sum := by decide
  have hdescent : baseEnd_2959978 < baseStart_2959978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959982 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_2959982 : Nat := 118140960795 + 2959982 * 2 ^ 59
def prefixEnd_2959982 : Nat := 4983230072969 + 3 ^ 40 * 2959982 * 2
def baseEnd_2959982 : Nat := 1519893494656743290512297

theorem tailTrace_2959982 : CollatzResearch.WordTrace tailWord_2959982 prefixEnd_2959982 1519893494656743290512297 := by
  unfold tailWord_2959982
  simp only [CollatzResearch.WordTrace]
  refine ⟨13494926595312276690479275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71972941841665475682556133 13494926595312276690479275)
  ·
    refine ⟨20242389892968415035718913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13494926595312276690479275 20242389892968415035718913)
    ·
      refine ⟨15181792419726311276789185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20242389892968415035718913 15181792419726311276789185)
      ·
        refine ⟨11386344314794733457591889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15181792419726311276789185 11386344314794733457591889)
        ·
          refine ⟨8539758236096050093193917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11386344314794733457591889 8539758236096050093193917)
          ·
            refine ⟨3202409338536018784947719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8539758236096050093193917 3202409338536018784947719)
            ·
              refine ⟨4803614007804028177421579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202409338536018784947719 4803614007804028177421579)
              ·
                refine ⟨7205421011706042266132369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4803614007804028177421579 7205421011706042266132369)
                ·
                  refine ⟨5404065758779531699599277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7205421011706042266132369 5404065758779531699599277)
                  ·
                    refine ⟨2026524659542324387349729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5404065758779531699599277 2026524659542324387349729)
                    ·
                      refine ⟨1519893494656743290512297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026524659542324387349729 1519893494656743290512297)
                      ·
                        rfl

theorem cell23_2959982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_2959982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959982 prefixEnd_2959982 := by exact prefixLift 2959982
  have htrace : WordTrace (prefixWord ++ tailWord_2959982) baseStart_2959982 baseEnd_2959982 := by
    simpa [prefixWord, tailWord_2959982, baseEnd_2959982] using wordTrace_append hprefix tailTrace_2959982
  have hstable : (prefixWord ++ tailWord_2959982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959982).length < 2 ^ (prefixWord ++ tailWord_2959982).sum := by decide
  have hdescent : baseEnd_2959982 < baseStart_2959982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959989 : List Nat := [1, 3, 4, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2959989 : Nat := 118140960795 + 2959989 * 2 ^ 59
def prefixEnd_2959989 : Nat := 4983230072969 + 3 ^ 40 * 2959989 * 2
def baseEnd_2959989 : Nat := 1519897089021324763124765

theorem tailTrace_2959989 : CollatzResearch.WordTrace tailWord_2959989 prefixEnd_2959989 1519897089021324763124765 := by
  unfold tailWord_2959989
  simp only [CollatzResearch.WordTrace]
  refine ⟨107959668073472853719339021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71973112048981902479559347 107959668073472853719339021)
  ·
    refine ⟨40484875527552320144752133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107959668073472853719339021 40484875527552320144752133)
    ·
      refine ⟨7590914161416060027141025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40484875527552320144752133 7590914161416060027141025)
      ·
        refine ⟨5693185621062045020355769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7590914161416060027141025 5693185621062045020355769)
        ·
          refine ⟨4269889215796533765266827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5693185621062045020355769 4269889215796533765266827)
          ·
            refine ⟨6404833823694800647900241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4269889215796533765266827 6404833823694800647900241)
            ·
              refine ⟨4803625367771100485925181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6404833823694800647900241 4803625367771100485925181)
              ·
                refine ⟨1801359512914162682221943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4803625367771100485925181 1801359512914162682221943)
                ·
                  refine ⟨2702039269371244023332915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801359512914162682221943 2702039269371244023332915)
                  ·
                    refine ⟨4053058904056866034999373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2702039269371244023332915 4053058904056866034999373)
                    ·
                      refine ⟨1519897089021324763124765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4053058904056866034999373 1519897089021324763124765)
                      ·
                        rfl

theorem cell23_2959989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2959989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959989 prefixEnd_2959989 := by exact prefixLift 2959989
  have htrace : WordTrace (prefixWord ++ tailWord_2959989) baseStart_2959989 baseEnd_2959989 := by
    simpa [prefixWord, tailWord_2959989, baseEnd_2959989] using wordTrace_append hprefix tailTrace_2959989
  have hstable : (prefixWord ++ tailWord_2959989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959989).length < 2 ^ (prefixWord ++ tailWord_2959989).sum := by decide
  have hdescent : baseEnd_2959989 < baseStart_2959989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959991 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_2959991 : Nat := 118140960795 + 2959991 * 2 ^ 59
def prefixEnd_2959991 : Nat := 4983230072969 + 3 ^ 40 * 2959991 * 2
def baseEnd_2959991 : Nat := 1519898115982633755299755

theorem tailTrace_2959991 : CollatzResearch.WordTrace tailWord_2959991 prefixEnd_2959991 1519898115982633755299755 := by
  unfold tailWord_2959991
  simp only [CollatzResearch.WordTrace]
  refine ⟨107959741019465608060911827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71973160679643738707274551 107959741019465608060911827)
  ·
    refine ⟨161939611529198412091367741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107959741019465608060911827 161939611529198412091367741)
    ·
      refine ⟨60727354323449404534262903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 161939611529198412091367741 60727354323449404534262903)
      ·
        refine ⟨91091031485174106801394355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60727354323449404534262903 91091031485174106801394355)
        ·
          refine ⟨136636547227761160202091533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91091031485174106801394355 136636547227761160202091533)
          ·
            refine ⟨51238705210410435075784325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136636547227761160202091533 51238705210410435075784325)
            ·
              refine ⟨9607257226951956576709561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51238705210410435075784325 9607257226951956576709561)
              ·
                refine ⟨7205442920213967432532171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9607257226951956576709561 7205442920213967432532171)
                ·
                  refine ⟨10808164380320951148798257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7205442920213967432532171 10808164380320951148798257)
                  ·
                    refine ⟨8106123285240713361598693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10808164380320951148798257 8106123285240713361598693)
                    ·
                      refine ⟨1519898115982633755299755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8106123285240713361598693 1519898115982633755299755)
                      ·
                        rfl

theorem cell23_2959991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_2959991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959991 prefixEnd_2959991 := by exact prefixLift 2959991
  have htrace : WordTrace (prefixWord ++ tailWord_2959991) baseStart_2959991 baseEnd_2959991 := by
    simpa [prefixWord, tailWord_2959991, baseEnd_2959991] using wordTrace_append hprefix tailTrace_2959991
  have hstable : (prefixWord ++ tailWord_2959991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959991).length < 2 ^ (prefixWord ++ tailWord_2959991).sum := by decide
  have hdescent : baseEnd_2959991 < baseStart_2959991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2959994 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_2959994 : Nat := 118140960795 + 2959994 * 2 ^ 59
def prefixEnd_2959994 : Nat := 4983230072969 + 3 ^ 40 * 2959994 * 2
def baseEnd_2959994 : Nat := 1519899656424597243562241

theorem tailTrace_2959994 : CollatzResearch.WordTrace tailWord_2959994 prefixEnd_2959994 1519899656424597243562241 := by
  unfold tailWord_2959994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26989962609613684893317759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71973233625636493048847357 26989962609613684893317759)
  ·
    refine ⟨40484943914420527339976639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26989962609613684893317759 40484943914420527339976639)
    ·
      refine ⟨60727415871630791009964959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40484943914420527339976639 60727415871630791009964959)
      ·
        refine ⟨91091123807446186514947439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60727415871630791009964959 91091123807446186514947439)
        ·
          refine ⟨136636685711169279772421159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91091123807446186514947439 136636685711169279772421159)
          ·
            refine ⟨204955028566753919658631739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136636685711169279772421159 204955028566753919658631739)
            ·
              refine ⟨307432542850130879487947609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204955028566753919658631739 307432542850130879487947609)
              ·
                refine ⟨230574407137598159615960707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307432542850130879487947609 230574407137598159615960707)
                ·
                  refine ⟨345861610706397239423941061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230574407137598159615960707 345861610706397239423941061)
                  ·
                    refine ⟨64849052007449482391988949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 345861610706397239423941061 64849052007449482391988949)
                    ·
                      refine ⟨1519899656424597243562241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64849052007449482391988949 1519899656424597243562241)
                      ·
                        rfl

theorem cell23_2959994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_2959994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2959994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2959994 prefixEnd_2959994 := by exact prefixLift 2959994
  have htrace : WordTrace (prefixWord ++ tailWord_2959994) baseStart_2959994 baseEnd_2959994 := by
    simpa [prefixWord, tailWord_2959994, baseEnd_2959994] using wordTrace_append hprefix tailTrace_2959994
  have hstable : (prefixWord ++ tailWord_2959994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2959994).length < 2 ^ (prefixWord ++ tailWord_2959994).sum := by decide
  have hdescent : baseEnd_2959994 < baseStart_2959994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2959994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960005 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_2960005 : Nat := 118140960795 + 2960005 * 2 ^ 59
def prefixEnd_2960005 : Nat := 4983230072969 + 3 ^ 40 * 2960005 * 2
def baseEnd_2960005 : Nat := 506635101570598900174897

theorem tailTrace_2960005 : CollatzResearch.WordTrace tailWord_2960005 prefixEnd_2960005 506635101570598900174897 := by
  unfold tailWord_2960005
  simp only [CollatzResearch.WordTrace]
  refine ⟨107960251641414888451921469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71973501094276592301280979 107960251641414888451921469)
  ·
    refine ⟨40485094365530583169470551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107960251641414888451921469 40485094365530583169470551)
    ·
      refine ⟨60727641548295874754205827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40485094365530583169470551 60727641548295874754205827)
      ·
        refine ⟨91091462322443812131308741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60727641548295874754205827 91091462322443812131308741)
        ·
          refine ⟨17079649185458214774620389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91091462322443812131308741 17079649185458214774620389)
          ·
            refine ⟨3202434222273415270241323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17079649185458214774620389 3202434222273415270241323)
            ·
              refine ⟨4803651333410122905361985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202434222273415270241323 4803651333410122905361985)
              ·
                refine ⟨3602738500057592179021489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4803651333410122905361985 3602738500057592179021489)
                ·
                  refine ⟨2702053875043194134266117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3602738500057592179021489 2702053875043194134266117)
                  ·
                    refine ⟨506635101570598900174897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2702053875043194134266117 506635101570598900174897)
                    ·
                      rfl

theorem cell23_2960005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_2960005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960005 prefixEnd_2960005 := by exact prefixLift 2960005
  have htrace : WordTrace (prefixWord ++ tailWord_2960005) baseStart_2960005 baseEnd_2960005 := by
    simpa [prefixWord, tailWord_2960005, baseEnd_2960005] using wordTrace_append hprefix tailTrace_2960005
  have hstable : (prefixWord ++ tailWord_2960005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960005).length < 2 ^ (prefixWord ++ tailWord_2960005).sum := by decide
  have hdescent : baseEnd_2960005 < baseStart_2960005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960045 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_2960045 : Nat := 118140960795 + 2960045 * 2 ^ 59
def prefixEnd_2960045 : Nat := 4983230072969 + 3 ^ 40 * 2960045 * 2
def baseEnd_2960045 : Nat := 1519925843937976544024507

theorem tailTrace_2960045 : CollatzResearch.WordTrace tailWord_2960045 prefixEnd_2960045 1519925843937976544024507 := by
  unfold tailWord_2960045
  simp only [CollatzResearch.WordTrace]
  refine ⟨107961710561269975283377589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71974473707513316855585059 107961710561269975283377589)
  ·
    refine ⟨10121410365119060182816649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107961710561269975283377589 10121410365119060182816649)
    ·
      refine ⟨7591057773839295137112487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10121410365119060182816649 7591057773839295137112487)
      ·
        refine ⟨11386586660758942705668731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7591057773839295137112487 11386586660758942705668731)
        ·
          refine ⟨17079879991138414058503097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11386586660758942705668731 17079879991138414058503097)
          ·
            refine ⟨12809909993353810543877323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17079879991138414058503097 12809909993353810543877323)
            ·
              refine ⟨19214864990030715815815985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12809909993353810543877323 19214864990030715815815985)
              ·
                refine ⟨14411148742523036861861989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19214864990030715815815985 14411148742523036861861989)
                ·
                  refine ⟨2702090389223069411599123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14411148742523036861861989 2702090389223069411599123)
                  ·
                    refine ⟨4053135583834604117398685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2702090389223069411599123 4053135583834604117398685)
                    ·
                      refine ⟨1519925843937976544024507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4053135583834604117398685 1519925843937976544024507)
                      ·
                        rfl

theorem cell23_2960045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_2960045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960045 prefixEnd_2960045 := by exact prefixLift 2960045
  have htrace : WordTrace (prefixWord ++ tailWord_2960045) baseStart_2960045 baseEnd_2960045 := by
    simpa [prefixWord, tailWord_2960045, baseEnd_2960045] using wordTrace_append hprefix tailTrace_2960045
  have hstable : (prefixWord ++ tailWord_2960045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960045).length < 2 ^ (prefixWord ++ tailWord_2960045).sum := by decide
  have hdescent : baseEnd_2960045 < baseStart_2960045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960046 : List Nat := [4, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2960046 : Nat := 118140960795 + 2960046 * 2 ^ 59
def prefixEnd_2960046 : Nat := 4983230072969 + 3 ^ 40 * 2960046 * 2
def baseEnd_2960046 : Nat := 1519926357418631040112003

theorem tailTrace_2960046 : CollatzResearch.WordTrace tailWord_2960046 prefixEnd_2960046 1519926357418631040112003 := by
  unfold tailWord_2960046
  simp only [CollatzResearch.WordTrace]
  refine ⟨13495218379283294056770499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71974498022844234969442661 13495218379283294056770499)
  ·
    refine ⟨20242827568924941085155749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13495218379283294056770499 20242827568924941085155749)
    ·
      refine ⟨3795530169173426453466703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20242827568924941085155749 3795530169173426453466703)
      ·
        refine ⟨5693295253760139680200055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3795530169173426453466703 5693295253760139680200055)
        ·
          refine ⟨8539942880640209520300083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693295253760139680200055 8539942880640209520300083)
          ·
            refine ⟨12809914320960314280450125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8539942880640209520300083 12809914320960314280450125)
            ·
              refine ⟨4803717870360117855168797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12809914320960314280450125 4803717870360117855168797)
              ·
                refine ⟨1801394201385044195688299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4803717870360117855168797 1801394201385044195688299)
                ·
                  refine ⟨2702091302077566293532449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801394201385044195688299 2702091302077566293532449)
                  ·
                    refine ⟨2026568476558174720149337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2702091302077566293532449 2026568476558174720149337)
                    ·
                      refine ⟨1519926357418631040112003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026568476558174720149337 1519926357418631040112003)
                      ·
                        rfl

theorem cell23_2960046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2960046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960046 prefixEnd_2960046 := by exact prefixLift 2960046
  have htrace : WordTrace (prefixWord ++ tailWord_2960046) baseStart_2960046 baseEnd_2960046 := by
    simpa [prefixWord, tailWord_2960046, baseEnd_2960046] using wordTrace_append hprefix tailTrace_2960046
  have hstable : (prefixWord ++ tailWord_2960046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960046).length < 2 ^ (prefixWord ++ tailWord_2960046).sum := by decide
  have hdescent : baseEnd_2960046 < baseStart_2960046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960081 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_2960081 : Nat := 118140960795 + 2960081 * 2 ^ 59
def prefixEnd_2960081 : Nat := 4983230072969 + 3 ^ 40 * 2960081 * 2
def baseEnd_2960081 : Nat := 1519944329241538403174341

theorem tailTrace_2960081 : CollatzResearch.WordTrace tailWord_2960081 prefixEnd_2960081 1519944329241538403174341 := by
  unfold tailWord_2960081
  simp only [CollatzResearch.WordTrace]
  refine ⟨107963023589139553431688097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71975349059426368954458731 107963023589139553431688097)
  ·
    refine ⟨80972267691854665073766073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107963023589139553431688097 80972267691854665073766073)
    ·
      refine ⟨60729200768890998805324555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80972267691854665073766073 60729200768890998805324555)
      ·
        refine ⟨91093801153336498207986833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60729200768890998805324555 91093801153336498207986833)
        ·
          refine ⟨68320350865002373655990125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91093801153336498207986833 68320350865002373655990125)
          ·
            refine ⟨25620131574375890120996297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68320350865002373655990125 25620131574375890120996297)
            ·
              refine ⟨19215098680781917590747223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25620131574375890120996297 19215098680781917590747223)
              ·
                refine ⟨28822648021172876386120835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19215098680781917590747223 28822648021172876386120835)
                ·
                  refine ⟨43233972031759314579181253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28822648021172876386120835 43233972031759314579181253)
                  ·
                    refine ⟨8106369755954871483596485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43233972031759314579181253 8106369755954871483596485)
                    ·
                      refine ⟨1519944329241538403174341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8106369755954871483596485 1519944329241538403174341)
                      ·
                        rfl

theorem cell23_2960081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_2960081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960081 prefixEnd_2960081 := by exact prefixLift 2960081
  have htrace : WordTrace (prefixWord ++ tailWord_2960081) baseStart_2960081 baseEnd_2960081 := by
    simpa [prefixWord, tailWord_2960081, baseEnd_2960081] using wordTrace_append hprefix tailTrace_2960081
  have hstable : (prefixWord ++ tailWord_2960081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960081).length < 2 ^ (prefixWord ++ tailWord_2960081).sum := by decide
  have hdescent : baseEnd_2960081 < baseStart_2960081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960108 : List Nat := [2, 2, 1, 1, 2, 2, 1, 7, 5]
def baseStart_2960108 : Nat := 118140960795 + 2960108 * 2 ^ 59
def prefixEnd_2960108 : Nat := 4983230072969 + 3 ^ 40 * 2960108 * 2
def baseEnd_2960108 : Nat := 168884243691023310837413

theorem tailTrace_2960108 : CollatzResearch.WordTrace tailWord_2960108 prefixEnd_2960108 168884243691023310837413 := by
  unfold tailWord_2960108
  simp only [CollatzResearch.WordTrace]
  refine ⟨53982004180020868521460489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71976005573361158028613985 53982004180020868521460489)
  ·
    refine ⟨40486503135015651391095367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53982004180020868521460489 40486503135015651391095367)
    ·
      refine ⟨60729754702523477086643051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40486503135015651391095367 60729754702523477086643051)
      ·
        refine ⟨91094632053785215629964577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60729754702523477086643051 91094632053785215629964577)
        ·
          refine ⟨68320974040338911722473433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91094632053785215629964577 68320974040338911722473433)
          ·
            refine ⟨51240730530254183791855075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68320974040338911722473433 51240730530254183791855075)
            ·
              refine ⟨76861095795381275687782613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51240730530254183791855075 76861095795381275687782613)
              ·
                refine ⟨1801431932704248648932405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76861095795381275687782613 1801431932704248648932405)
                ·
                  refine ⟨168884243691023310837413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1801431932704248648932405 168884243691023310837413)
                  ·
                    rfl

theorem cell23_2960108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 5].length) (baseStart_2960108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960108 prefixEnd_2960108 := by exact prefixLift 2960108
  have htrace : WordTrace (prefixWord ++ tailWord_2960108) baseStart_2960108 baseEnd_2960108 := by
    simpa [prefixWord, tailWord_2960108, baseEnd_2960108] using wordTrace_append hprefix tailTrace_2960108
  have hstable : (prefixWord ++ tailWord_2960108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960108).length < 2 ^ (prefixWord ++ tailWord_2960108).sum := by decide
  have hdescent : baseEnd_2960108 < baseStart_2960108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960135 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2960135 : Nat := 118140960795 + 2960135 * 2 ^ 59
def prefixEnd_2960135 : Nat := 4983230072969 + 3 ^ 40 * 2960135 * 2
def baseEnd_2960135 : Nat := 1519972057196881191899093

theorem tailTrace_2960135 : CollatzResearch.WordTrace tailWord_2960135 prefixEnd_2960135 1519972057196881191899093 := by
  unfold tailWord_2960135
  simp only [CollatzResearch.WordTrace]
  refine ⟨107964993130943920654153859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71976662087295947102769239 107964993130943920654153859)
  ·
    refine ⟨161947489696415880981230789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107964993130943920654153859 161947489696415880981230789)
    ·
      refine ⟨30365154318077977683980773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 161947489696415880981230789 30365154318077977683980773)
      ·
        refine ⟨5693466434639620815746395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30365154318077977683980773 5693466434639620815746395)
        ·
          refine ⟨8540199651959431223619593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5693466434639620815746395 8540199651959431223619593)
          ·
            refine ⟨6405149738969573417714695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8540199651959431223619593 6405149738969573417714695)
            ·
              refine ⟨9607724608454360126572043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405149738969573417714695 9607724608454360126572043)
              ·
                refine ⟨14411586912681540189858065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9607724608454360126572043 14411586912681540189858065)
                ·
                  refine ⟨10808690184511155142393549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14411586912681540189858065 10808690184511155142393549)
                  ·
                    refine ⟨4053258819191683178397581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10808690184511155142393549 4053258819191683178397581)
                    ·
                      refine ⟨1519972057196881191899093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4053258819191683178397581 1519972057196881191899093)
                      ·
                        rfl

theorem cell23_2960135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2960135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960135 prefixEnd_2960135 := by exact prefixLift 2960135
  have htrace : WordTrace (prefixWord ++ tailWord_2960135) baseStart_2960135 baseEnd_2960135 := by
    simpa [prefixWord, tailWord_2960135, baseEnd_2960135] using wordTrace_append hprefix tailTrace_2960135
  have hstable : (prefixWord ++ tailWord_2960135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960135).length < 2 ^ (prefixWord ++ tailWord_2960135).sum := by decide
  have hdescent : baseEnd_2960135 < baseStart_2960135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960171 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 6]
def baseStart_2960171 : Nat := 118140960795 + 2960171 * 2 ^ 59
def prefixEnd_2960171 : Nat := 4983230072969 + 3 ^ 40 * 2960171 * 2
def baseEnd_2960171 : Nat := 1519990542500443051048927

theorem tailTrace_2960171 : CollatzResearch.WordTrace tailWord_2960171 prefixEnd_2960171 1519990542500443051048927 := by
  unfold tailWord_2960171
  simp only [CollatzResearch.WordTrace]
  refine ⟨107966306158813498802464367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71977537439208999201642911 107966306158813498802464367)
  ·
    refine ⟨161949459238220248203696551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107966306158813498802464367 161949459238220248203696551)
    ·
      refine ⟨242924188857330372305544827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161949459238220248203696551 242924188857330372305544827)
      ·
        refine ⟨364386283285995558458317241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242924188857330372305544827 364386283285995558458317241)
        ·
          refine ⟨273289712464496668843737931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364386283285995558458317241 273289712464496668843737931)
          ·
            refine ⟨409934568696745003265606897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273289712464496668843737931 409934568696745003265606897)
            ·
              refine ⟨307450926522558752449205173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409934568696745003265606897 307450926522558752449205173)
              ·
                refine ⟨28823524361489883042112985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 307450926522558752449205173 28823524361489883042112985)
                ·
                  refine ⟨21617643271117412281584739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28823524361489883042112985 21617643271117412281584739)
                  ·
                    refine ⟨32426464906676118422377109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21617643271117412281584739 32426464906676118422377109)
                    ·
                      refine ⟨1519990542500443051048927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32426464906676118422377109 1519990542500443051048927)
                      ·
                        rfl

theorem cell23_2960171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 6].length) (baseStart_2960171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960171 prefixEnd_2960171 := by exact prefixLift 2960171
  have htrace : WordTrace (prefixWord ++ tailWord_2960171) baseStart_2960171 baseEnd_2960171 := by
    simpa [prefixWord, tailWord_2960171, baseEnd_2960171] using wordTrace_append hprefix tailTrace_2960171
  have hstable : (prefixWord ++ tailWord_2960171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960171).length < 2 ^ (prefixWord ++ tailWord_2960171).sum := by decide
  have hdescent : baseEnd_2960171 < baseStart_2960171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960211 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 2, 9]
def baseStart_2960211 : Nat := 118140960795 + 2960211 * 2 ^ 59
def prefixEnd_2960211 : Nat := 4983230072969 + 3 ^ 40 * 2960211 * 2
def baseEnd_2960211 : Nat := 506670360575540964849581

theorem tailTrace_2960211 : CollatzResearch.WordTrace tailWord_2960211 prefixEnd_2960211 506670360575540964849581 := by
  unfold tailWord_2960211
  simp only [CollatzResearch.WordTrace]
  refine ⟨107967765078668585633920487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71978510052445723755946991 107967765078668585633920487)
  ·
    refine ⟨161951647618002878450880731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107967765078668585633920487 161951647618002878450880731)
    ·
      refine ⟨242927471427004317676321097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161951647618002878450880731 242927471427004317676321097)
      ·
        refine ⟨182195603570253238257240823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242927471427004317676321097 182195603570253238257240823)
        ·
          refine ⟨273293405355379857385861235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182195603570253238257240823 273293405355379857385861235)
          ·
            refine ⟨409940108033069786078791853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273293405355379857385861235 409940108033069786078791853)
            ·
              refine ⟨153727540512401169779546945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 409940108033069786078791853 153727540512401169779546945)
              ·
                refine ⟨115295655384300877334660209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153727540512401169779546945 115295655384300877334660209)
                ·
                  refine ⟨86471741538225658000995157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115295655384300877334660209 86471741538225658000995157)
                  ·
                    refine ⟨506670360575540964849581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 86471741538225658000995157 506670360575540964849581)
                    ·
                      rfl

theorem cell23_2960211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 9].length) (baseStart_2960211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960211 prefixEnd_2960211 := by exact prefixLift 2960211
  have htrace : WordTrace (prefixWord ++ tailWord_2960211) baseStart_2960211 baseEnd_2960211 := by
    simpa [prefixWord, tailWord_2960211, baseEnd_2960211] using wordTrace_append hprefix tailTrace_2960211
  have hstable : (prefixWord ++ tailWord_2960211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960211).length < 2 ^ (prefixWord ++ tailWord_2960211).sum := by decide
  have hdescent : baseEnd_2960211 < baseStart_2960211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960235 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 4, 3, 2]
def baseStart_2960235 : Nat := 118140960795 + 2960235 * 2 ^ 59
def prefixEnd_2960235 : Nat := 4983230072969 + 3 ^ 40 * 2960235 * 2
def baseEnd_2960235 : Nat := 1520023405262330800648633

theorem tailTrace_2960235 : CollatzResearch.WordTrace tailWord_2960235 prefixEnd_2960235 1520023405262330800648633 := by
  unfold tailWord_2960235
  simp only [CollatzResearch.WordTrace]
  refine ⟨107968640430581637732794159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71979093620387758488529439 107968640430581637732794159)
  ·
    refine ⟨161952960645872456599191239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107968640430581637732794159 161952960645872456599191239)
    ·
      refine ⟨242929440968808684898786859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161952960645872456599191239 242929440968808684898786859)
      ·
        refine ⟨364394161453213027348180289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242929440968808684898786859 364394161453213027348180289)
        ·
          refine ⟨273295621089909770511135217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364394161453213027348180289 273295621089909770511135217)
          ·
            refine ⟨204971715817432327883351413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273295621089909770511135217 204971715817432327883351413)
            ·
              refine ⟨19216098357884280739064195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 204971715817432327883351413 19216098357884280739064195)
              ·
                refine ⟨28824147536826421108596293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19216098357884280739064195 28824147536826421108596293)
                ·
                  refine ⟨5404527663154953957861805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28824147536826421108596293 5404527663154953957861805)
                  ·
                    refine ⟨2026697873683107734198177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5404527663154953957861805 2026697873683107734198177)
                    ·
                      refine ⟨1520023405262330800648633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026697873683107734198177 1520023405262330800648633)
                      ·
                        rfl

theorem cell23_2960235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 3, 2].length) (baseStart_2960235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960235 prefixEnd_2960235 := by exact prefixLift 2960235
  have htrace : WordTrace (prefixWord ++ tailWord_2960235) baseStart_2960235 baseEnd_2960235 := by
    simpa [prefixWord, tailWord_2960235, baseEnd_2960235] using wordTrace_append hprefix tailTrace_2960235
  have hstable : (prefixWord ++ tailWord_2960235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960235).length < 2 ^ (prefixWord ++ tailWord_2960235).sum := by decide
  have hdescent : baseEnd_2960235 < baseStart_2960235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960242 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 3, 1, 3]
def baseStart_2960242 : Nat := 118140960795 + 2960242 * 2 ^ 59
def prefixEnd_2960242 : Nat := 4983230072969 + 3 ^ 40 * 2960242 * 2
def baseEnd_2960242 : Nat := 1520026999626912273261101

theorem tailTrace_2960242 : CollatzResearch.WordTrace tailWord_2960242 prefixEnd_2960242 1520026999626912273261101 := by
  unfold tailWord_2960242
  simp only [CollatzResearch.WordTrace]
  refine ⟨26992223935389069482074745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71979263827704185285532653 26992223935389069482074745)
  ·
    refine ⟨20244167951541802111556059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26992223935389069482074745 20244167951541802111556059)
    ·
      refine ⟨30366251927312703167334089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20244167951541802111556059 30366251927312703167334089)
      ·
        refine ⟨22774688945484527375500567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30366251927312703167334089 22774688945484527375500567)
        ·
          refine ⟨34162033418226791063250851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22774688945484527375500567 34162033418226791063250851)
          ·
            refine ⟨51243050127340186594876277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34162033418226791063250851 51243050127340186594876277)
            ·
              refine ⟨4804035949438142493269651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51243050127340186594876277 4804035949438142493269651)
              ·
                refine ⟨7206053924157213739904477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4804035949438142493269651 7206053924157213739904477)
                ·
                  refine ⟨2702270221558955152464179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7206053924157213739904477 2702270221558955152464179)
                  ·
                    refine ⟨4053405332338432728696269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2702270221558955152464179 4053405332338432728696269)
                    ·
                      refine ⟨1520026999626912273261101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4053405332338432728696269 1520026999626912273261101)
                      ·
                        rfl

theorem cell23_2960242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_2960242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960242 prefixEnd_2960242 := by exact prefixLift 2960242
  have htrace : WordTrace (prefixWord ++ tailWord_2960242) baseStart_2960242 baseEnd_2960242 := by
    simpa [prefixWord, tailWord_2960242, baseEnd_2960242] using wordTrace_append hprefix tailTrace_2960242
  have hstable : (prefixWord ++ tailWord_2960242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960242).length < 2 ^ (prefixWord ++ tailWord_2960242).sum := by decide
  have hdescent : baseEnd_2960242 < baseStart_2960242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960265 : List Nat := [1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 4]
def baseStart_2960265 : Nat := 118140960795 + 2960265 * 2 ^ 59
def prefixEnd_2960265 : Nat := 4983230072969 + 3 ^ 40 * 2960265 * 2
def baseEnd_2960265 : Nat := 1520038809681965683273495

theorem tailTrace_2960265 : CollatzResearch.WordTrace tailWord_2960265 prefixEnd_2960265 1520038809681965683273495 := by
  unfold tailWord_2960265
  simp only [CollatzResearch.WordTrace]
  refine ⟨107969734620472952856386249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71979823080315301904257499 107969734620472952856386249)
  ·
    refine ⟨80977300965354714642289687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107969734620472952856386249 80977300965354714642289687)
    ·
      refine ⟨121465951448032071963434531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80977300965354714642289687 121465951448032071963434531)
      ·
        refine ⟨182198927172048107945151797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121465951448032071963434531 182198927172048107945151797)
        ·
          refine ⟨17081149422379510119857981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 182198927172048107945151797 17081149422379510119857981)
          ·
            refine ⟨6405431033392316294946743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17081149422379510119857981 6405431033392316294946743)
            ·
              refine ⟨9608146550088474442420115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405431033392316294946743 9608146550088474442420115)
              ·
                refine ⟨14412219825132711663630173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9608146550088474442420115 14412219825132711663630173)
                ·
                  refine ⟨5404582434424766873861315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14412219825132711663630173 5404582434424766873861315)
                  ·
                    refine ⟨8106873651637150310791973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5404582434424766873861315 8106873651637150310791973)
                    ·
                      refine ⟨1520038809681965683273495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8106873651637150310791973 1520038809681965683273495)
                      ·
                        rfl

theorem cell23_2960265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_2960265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960265 prefixEnd_2960265 := by exact prefixLift 2960265
  have htrace : WordTrace (prefixWord ++ tailWord_2960265) baseStart_2960265 baseEnd_2960265 := by
    simpa [prefixWord, tailWord_2960265, baseEnd_2960265] using wordTrace_append hprefix tailTrace_2960265
  have hstable : (prefixWord ++ tailWord_2960265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960265).length < 2 ^ (prefixWord ++ tailWord_2960265).sum := by decide
  have hdescent : baseEnd_2960265 < baseStart_2960265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960268 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_2960268 : Nat := 118140960795 + 2960268 * 2 ^ 59
def prefixEnd_2960268 : Nat := 4983230072969 + 3 ^ 40 * 2960268 * 2
def baseEnd_2960268 : Nat := 1520040350123929171535981

theorem tailTrace_2960268 : CollatzResearch.WordTrace tailWord_2960268 prefixEnd_2960268 1520040350123929171535981 := by
  unfold tailWord_2960268
  simp only [CollatzResearch.WordTrace]
  refine ⟨53984922019731042184372729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71979896026308056245830305 53984922019731042184372729)
  ·
    refine ⟨40488691514798281638279547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53984922019731042184372729 40488691514798281638279547)
    ·
      refine ⟨60733037272197422457419321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40488691514798281638279547 60733037272197422457419321)
      ·
        refine ⟨45549777954148066843064491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60733037272197422457419321 45549777954148066843064491)
        ·
          refine ⟨68324666931222100264596737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45549777954148066843064491 68324666931222100264596737)
          ·
            refine ⟨51243500198416575198447553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68324666931222100264596737 51243500198416575198447553)
            ·
              refine ⟨38432625148812431398835665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51243500198416575198447553 38432625148812431398835665)
              ·
                refine ⟨28824468861609323549126749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38432625148812431398835665 28824468861609323549126749)
                ·
                  refine ⟨10809175823103496330922531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28824468861609323549126749 10809175823103496330922531)
                  ·
                    refine ⟨16213763734655244496383797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10809175823103496330922531 16213763734655244496383797)
                    ·
                      refine ⟨1520040350123929171535981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16213763734655244496383797 1520040350123929171535981)
                      ·
                        rfl

theorem cell23_2960268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_2960268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960268 prefixEnd_2960268 := by exact prefixLift 2960268
  have htrace : WordTrace (prefixWord ++ tailWord_2960268) baseStart_2960268 baseEnd_2960268 := by
    simpa [prefixWord, tailWord_2960268, baseEnd_2960268] using wordTrace_append hprefix tailTrace_2960268
  have hstable : (prefixWord ++ tailWord_2960268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960268).length < 2 ^ (prefixWord ++ tailWord_2960268).sum := by decide
  have hdescent : baseEnd_2960268 < baseStart_2960268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960292 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 2, 4]
def baseStart_2960292 : Nat := 118140960795 + 2960292 * 2 ^ 59
def prefixEnd_2960292 : Nat := 4983230072969 + 3 ^ 40 * 2960292 * 2
def baseEnd_2960292 : Nat := 506684224553212359211957

theorem tailTrace_2960292 : CollatzResearch.WordTrace tailWord_2960292 prefixEnd_2960292 506684224553212359211957 := by
  unfold tailWord_2960292
  simp only [CollatzResearch.WordTrace]
  refine ⟨53985359695687568233809565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71980479594250090978412753 53985359695687568233809565)
  ·
    refine ⟨20244509885882838087678587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53985359695687568233809565 20244509885882838087678587)
    ·
      refine ⟨30366764828824257131517881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20244509885882838087678587 30366764828824257131517881)
      ·
        refine ⟨22775073621618192848638411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30366764828824257131517881 22775073621618192848638411)
        ·
          refine ⟨34162610432427289272957617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22775073621618192848638411 34162610432427289272957617)
          ·
            refine ⟨25621957824320466954718213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34162610432427289272957617 25621957824320466954718213)
            ·
              refine ⟨4804117092060087554009665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25621957824320466954718213 4804117092060087554009665)
              ·
                refine ⟨3603087819045065665507249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4804117092060087554009665 3603087819045065665507249)
                ·
                  refine ⟨2702315864283799249130437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3603087819045065665507249 2702315864283799249130437)
                  ·
                    refine ⟨506684224553212359211957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2702315864283799249130437 506684224553212359211957)
                    ·
                      rfl

theorem cell23_2960292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_2960292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960292 prefixEnd_2960292 := by exact prefixLift 2960292
  have htrace : WordTrace (prefixWord ++ tailWord_2960292) baseStart_2960292 baseEnd_2960292 := by
    simpa [prefixWord, tailWord_2960292, baseEnd_2960292] using wordTrace_append hprefix tailTrace_2960292
  have hstable : (prefixWord ++ tailWord_2960292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960292).length < 2 ^ (prefixWord ++ tailWord_2960292).sum := by decide
  have hdescent : baseEnd_2960292 < baseStart_2960292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960299 : List Nat := [1, 1, 1, 1, 2, 1, 1, 10, 1, 2, 2]
def baseStart_2960299 : Nat := 118140960795 + 2960299 * 2 ^ 59
def prefixEnd_2960299 : Nat := 4983230072969 + 3 ^ 40 * 2960299 * 2
def baseEnd_2960299 : Nat := 1520056268024218550248339

theorem tailTrace_2960299 : CollatzResearch.WordTrace tailWord_2960299 prefixEnd_2960299 1520056268024218550248339 := by
  unfold tailWord_2960299
  simp only [CollatzResearch.WordTrace]
  refine ⟨107970974702349776663123951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71980649801566517775415967 107970974702349776663123951)
  ·
    refine ⟨161956462053524664994685927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107970974702349776663123951 161956462053524664994685927)
    ·
      refine ⟨242934693080286997492028891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161956462053524664994685927 242934693080286997492028891)
      ·
        refine ⟨364402039620430496238043337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242934693080286997492028891 364402039620430496238043337)
        ·
          refine ⟨273301529715322872178532503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364402039620430496238043337 273301529715322872178532503)
          ·
            refine ⟨409952294572984308267798755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273301529715322872178532503 409952294572984308267798755)
            ·
              refine ⟨614928441859476462401698133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 409952294572984308267798755 614928441859476462401698133)
              ·
                refine ⟨1801548169510184948442475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 614928441859476462401698133 1801548169510184948442475)
                ·
                  refine ⟨2702322254265277422663713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801548169510184948442475 2702322254265277422663713)
                  ·
                    refine ⟨2026741690698958066997785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2702322254265277422663713 2026741690698958066997785)
                    ·
                      refine ⟨1520056268024218550248339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026741690698958066997785 1520056268024218550248339)
                      ·
                        rfl

theorem cell23_2960299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 1, 2, 2].length) (baseStart_2960299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960299 prefixEnd_2960299 := by exact prefixLift 2960299
  have htrace : WordTrace (prefixWord ++ tailWord_2960299) baseStart_2960299 baseEnd_2960299 := by
    simpa [prefixWord, tailWord_2960299, baseEnd_2960299] using wordTrace_append hprefix tailTrace_2960299
  have hstable : (prefixWord ++ tailWord_2960299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960299).length < 2 ^ (prefixWord ++ tailWord_2960299).sum := by decide
  have hdescent : baseEnd_2960299 < baseStart_2960299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960332 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 4, 1, 3]
def baseStart_2960332 : Nat := 118140960795 + 2960332 * 2 ^ 59
def prefixEnd_2960332 : Nat := 4983230072969 + 3 ^ 40 * 2960332 * 2
def baseEnd_2960332 : Nat := 1520073212885816921135687

theorem tailTrace_2960332 : CollatzResearch.WordTrace tailWord_2960332 prefixEnd_2960332 1520073212885816921135687 := by
  unfold tailWord_2960332
  simp only [CollatzResearch.WordTrace]
  refine ⟨53986089155615111649537625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71981452207486815532716833 53986089155615111649537625)
  ·
    refine ⟨40489566866711333737153219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53986089155615111649537625 40489566866711333737153219)
    ·
      refine ⟨60734350300067000605729829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40489566866711333737153219 60734350300067000605729829)
      ·
        refine ⟨11387690681262562613574343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60734350300067000605729829 11387690681262562613574343)
        ·
          refine ⟨17081536021893843920361515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11387690681262562613574343 17081536021893843920361515)
          ·
            refine ⟨25622304032840765880542273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17081536021893843920361515 25622304032840765880542273)
            ·
              refine ⟨19216728024630574410406705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25622304032840765880542273 19216728024630574410406705)
              ·
                refine ⟨14412546018472930807805029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19216728024630574410406705 14412546018472930807805029)
                ·
                  refine ⟨2702352378463674526463443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14412546018472930807805029 2702352378463674526463443)
                  ·
                    refine ⟨4053528567695511789695165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2702352378463674526463443 4053528567695511789695165)
                    ·
                      refine ⟨1520073212885816921135687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4053528567695511789695165 1520073212885816921135687)
                      ·
                        rfl

theorem cell23_2960332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_2960332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960332 prefixEnd_2960332 := by exact prefixLift 2960332
  have htrace : WordTrace (prefixWord ++ tailWord_2960332) baseStart_2960332 baseEnd_2960332 := by
    simpa [prefixWord, tailWord_2960332, baseEnd_2960332] using wordTrace_append hprefix tailTrace_2960332
  have hstable : (prefixWord ++ tailWord_2960332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960332).length < 2 ^ (prefixWord ++ tailWord_2960332).sum := by decide
  have hdescent : baseEnd_2960332 < baseStart_2960332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960333 : List Nat := [1, 6, 3, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_2960333 : Nat := 118140960795 + 2960333 * 2 ^ 59
def prefixEnd_2960333 : Nat := 4983230072969 + 3 ^ 40 * 2960333 * 2
def baseEnd_2960333 : Nat := 1520073726366471417223183

theorem tailTrace_2960333 : CollatzResearch.WordTrace tailWord_2960333 prefixEnd_2960333 1520073726366471417223183 := by
  unfold tailWord_2960333
  simp only [CollatzResearch.WordTrace]
  refine ⟨107972214784226600469861653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71981476522817733646574435 107972214784226600469861653)
  ·
    refine ⟨5061197568010621897024765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107972214784226600469861653 5061197568010621897024765)
    ·
      refine ⟨1897949088003983211384287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5061197568010621897024765 1897949088003983211384287)
      ·
        refine ⟨2846923632005974817076431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1897949088003983211384287 2846923632005974817076431)
        ·
          refine ⟨4270385448008962225614647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2846923632005974817076431 4270385448008962225614647)
          ·
            refine ⟨6405578172013443338421971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4270385448008962225614647 6405578172013443338421971)
            ·
              refine ⟨9608367258020165007632957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405578172013443338421971 9608367258020165007632957)
              ·
                refine ⟨3603137721757561877862359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9608367258020165007632957 3603137721757561877862359)
                ·
                  refine ⟨5404706582636342816793539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603137721757561877862359 5404706582636342816793539)
                  ·
                    refine ⟨8107059873954514225190309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5404706582636342816793539 8107059873954514225190309)
                    ·
                      refine ⟨1520073726366471417223183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8107059873954514225190309 1520073726366471417223183)
                      ·
                        rfl

theorem cell23_2960333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_2960333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960333 prefixEnd_2960333 := by exact prefixLift 2960333
  have htrace : WordTrace (prefixWord ++ tailWord_2960333) baseStart_2960333 baseEnd_2960333 := by
    simpa [prefixWord, tailWord_2960333, baseEnd_2960333] using wordTrace_append hprefix tailTrace_2960333
  have hstable : (prefixWord ++ tailWord_2960333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960333).length < 2 ^ (prefixWord ++ tailWord_2960333).sum := by decide
  have hdescent : baseEnd_2960333 < baseStart_2960333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960349 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_2960349 : Nat := 118140960795 + 2960349 * 2 ^ 59
def prefixEnd_2960349 : Nat := 4983230072969 + 3 ^ 40 * 2960349 * 2
def baseEnd_2960349 : Nat := 1520081942056943354623109

theorem tailTrace_2960349 : CollatzResearch.WordTrace tailWord_2960349 prefixEnd_2960349 1520081942056943354623109 := by
  unfold tailWord_2960349
  simp only [CollatzResearch.WordTrace]
  refine ⟨107972798352168635202444101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71981865568112423468296067 107972798352168635202444101)
  ·
    refine ⟨20244899691031619100458269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107972798352168635202444101 20244899691031619100458269)
    ·
      refine ⟨7591837384136857162671851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20244899691031619100458269 7591837384136857162671851)
      ·
        refine ⟨11387756076205285744007777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7591837384136857162671851 11387756076205285744007777)
        ·
          refine ⟨8540817057153964308005833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11387756076205285744007777 8540817057153964308005833)
          ·
            refine ⟨6405612792865473231004375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8540817057153964308005833 6405612792865473231004375)
            ·
              refine ⟨9608419189298209846506563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405612792865473231004375 9608419189298209846506563)
              ·
                refine ⟨14412628783947314769759845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9608419189298209846506563 14412628783947314769759845)
                ·
                  refine ⟨2702367896990121519329971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14412628783947314769759845 2702367896990121519329971)
                  ·
                    refine ⟨4053551845485182278994957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2702367896990121519329971 4053551845485182278994957)
                    ·
                      refine ⟨1520081942056943354623109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4053551845485182278994957 1520081942056943354623109)
                      ·
                        rfl

theorem cell23_2960349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_2960349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960349 prefixEnd_2960349 := by exact prefixLift 2960349
  have htrace : WordTrace (prefixWord ++ tailWord_2960349) baseStart_2960349 baseEnd_2960349 := by
    simpa [prefixWord, tailWord_2960349, baseEnd_2960349] using wordTrace_append hprefix tailTrace_2960349
  have hstable : (prefixWord ++ tailWord_2960349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960349).length < 2 ^ (prefixWord ++ tailWord_2960349).sum := by decide
  have hdescent : baseEnd_2960349 < baseStart_2960349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960366 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_2960366 : Nat := 118140960795 + 2960366 * 2 ^ 59
def prefixEnd_2960366 : Nat := 4983230072969 + 3 ^ 40 * 2960366 * 2
def baseEnd_2960366 : Nat := 1520090671228069788110531

theorem tailTrace_2960366 : CollatzResearch.WordTrace tailWord_2960366 prefixEnd_2960366 1520090671228069788110531 := by
  unfold tailWord_2960366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13496677299138380888226619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71982278928738031403875301 13496677299138380888226619)
  ·
    refine ⟨20245015948707571332339929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13496677299138380888226619 20245015948707571332339929)
    ·
      refine ⟨15183761961530678499254947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20245015948707571332339929 15183761961530678499254947)
      ·
        refine ⟨22775642942296017748882421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15183761961530678499254947 22775642942296017748882421)
        ·
          refine ⟨2135216525840251663957727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22775642942296017748882421 2135216525840251663957727)
          ·
            refine ⟨3202824788760377495936591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135216525840251663957727 3202824788760377495936591)
            ·
              refine ⟨4804237183140566243904887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3202824788760377495936591 4804237183140566243904887)
              ·
                refine ⟨7206355774710849365857331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4804237183140566243904887 7206355774710849365857331)
                ·
                  refine ⟨10809533662066274048785997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7206355774710849365857331 10809533662066274048785997)
                  ·
                    refine ⟨4053575123274852768294749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10809533662066274048785997 4053575123274852768294749)
                    ·
                      refine ⟨1520090671228069788110531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4053575123274852768294749 1520090671228069788110531)
                      ·
                        rfl

theorem cell23_2960366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_2960366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960366 prefixEnd_2960366 := by exact prefixLift 2960366
  have htrace : WordTrace (prefixWord ++ tailWord_2960366) baseStart_2960366 baseEnd_2960366 := by
    simpa [prefixWord, tailWord_2960366, baseEnd_2960366] using wordTrace_append hprefix tailTrace_2960366
  have hstable : (prefixWord ++ tailWord_2960366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960366).length < 2 ^ (prefixWord ++ tailWord_2960366).sum := by decide
  have hdescent : baseEnd_2960366 < baseStart_2960366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960423 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_2960423 : Nat := 118140960795 + 2960423 * 2 ^ 59
def prefixEnd_2960423 : Nat := 4983230072969 + 3 ^ 40 * 2960423 * 2
def baseEnd_2960423 : Nat := 1520119939625376065097769

theorem tailTrace_2960423 : CollatzResearch.WordTrace tailWord_2960423 prefixEnd_2960423 1520119939625376065097769 := by
  unfold tailWord_2960423
  simp only [CollatzResearch.WordTrace]
  refine ⟨107975497353900545840637923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71983664902600363893758615 107975497353900545840637923)
  ·
    refine ⟨161963246030850818760956885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107975497353900545840637923 161963246030850818760956885)
    ·
      refine ⟨3796013578848066064709927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 161963246030850818760956885 3796013578848066064709927)
      ·
        refine ⟨5694020368272099097064891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3796013578848066064709927 5694020368272099097064891)
        ·
          refine ⟨8541030552408148645597337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5694020368272099097064891 8541030552408148645597337)
          ·
            refine ⟨6405772914306111484198003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8541030552408148645597337 6405772914306111484198003)
            ·
              refine ⟨9608659371459167226297005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6405772914306111484198003 9608659371459167226297005)
              ·
                refine ⟨3603247264297187709861377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9608659371459167226297005 3603247264297187709861377)
                ·
                  refine ⟨2702435448222890782396033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3603247264297187709861377 2702435448222890782396033)
                  ·
                    refine ⟨2026826586167168086797025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2702435448222890782396033 2026826586167168086797025)
                    ·
                      refine ⟨1520119939625376065097769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026826586167168086797025 1520119939625376065097769)
                      ·
                        rfl

theorem cell23_2960423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_2960423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960423 prefixEnd_2960423 := by exact prefixLift 2960423
  have htrace : WordTrace (prefixWord ++ tailWord_2960423) baseStart_2960423 baseEnd_2960423 := by
    simpa [prefixWord, tailWord_2960423, baseEnd_2960423] using wordTrace_append hprefix tailTrace_2960423
  have hstable : (prefixWord ++ tailWord_2960423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960423).length < 2 ^ (prefixWord ++ tailWord_2960423).sum := by decide
  have hdescent : baseEnd_2960423 < baseStart_2960423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960462 : List Nat := [4, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2960462 : Nat := 118140960795 + 2960462 * 2 ^ 59
def prefixEnd_2960462 : Nat := 4983230072969 + 3 ^ 40 * 2960462 * 2
def baseEnd_2960462 : Nat := 1520139965370901412510089

theorem tailTrace_2960462 : CollatzResearch.WordTrace tailWord_2960462 prefixEnd_2960462 1520139965370901412510089 := by
  unfold tailWord_2960462
  simp only [CollatzResearch.WordTrace]
  refine ⟨13497114975094906937663455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71984613200506170334205093 13497114975094906937663455)
  ·
    refine ⟨20245672462642360406495183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13497114975094906937663455 20245672462642360406495183)
    ·
      refine ⟨30368508693963540609742775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20245672462642360406495183 30368508693963540609742775)
      ·
        refine ⟨45552763040945310914614163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30368508693963540609742775 45552763040945310914614163)
        ·
          refine ⟨68329144561417966371921245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45552763040945310914614163 68329144561417966371921245)
          ·
            refine ⟨25623429210531737389470467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68329144561417966371921245 25623429210531737389470467)
            ·
              refine ⟨38435143815797606084205701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25623429210531737389470467 38435143815797606084205701)
              ·
                refine ⟨7206589465462051140788569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38435143815797606084205701 7206589465462051140788569)
                ·
                  refine ⟨5404942099096538355591427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7206589465462051140788569 5404942099096538355591427)
                  ·
                    refine ⟨8107413148644807533387141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5404942099096538355591427 8107413148644807533387141)
                    ·
                      refine ⟨1520139965370901412510089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8107413148644807533387141 1520139965370901412510089)
                      ·
                        rfl

theorem cell23_2960462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2960462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960462 prefixEnd_2960462 := by exact prefixLift 2960462
  have htrace : WordTrace (prefixWord ++ tailWord_2960462) baseStart_2960462 baseEnd_2960462 := by
    simpa [prefixWord, tailWord_2960462, baseEnd_2960462] using wordTrace_append hprefix tailTrace_2960462
  have hstable : (prefixWord ++ tailWord_2960462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960462).length < 2 ^ (prefixWord ++ tailWord_2960462).sum := by decide
  have hdescent : baseEnd_2960462 < baseStart_2960462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960472 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 3, 4]
def baseStart_2960472 : Nat := 118140960795 + 2960472 * 2 ^ 59
def prefixEnd_2960472 : Nat := 4983230072969 + 3 ^ 40 * 2960472 * 2
def baseEnd_2960472 : Nat := 506715033392482124461681

theorem tailTrace_2960472 : CollatzResearch.WordTrace tailWord_2960472 prefixEnd_2960472 506715033392482124461681 := by
  unfold tailWord_2960472
  simp only [CollatzResearch.WordTrace]
  refine ⟨53988642265361513604585835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71984856353815351472781113 53988642265361513604585835)
  ·
    refine ⟨80982963398042270406878753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53988642265361513604585835 80982963398042270406878753)
    ·
      refine ⟨60737222548531702805159065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80982963398042270406878753 60737222548531702805159065)
      ·
        refine ⟨45552916911398777103869299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60737222548531702805159065 45552916911398777103869299)
        ·
          refine ⟨68329375367098165655803949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45552916911398777103869299 68329375367098165655803949)
          ·
            refine ⟨25623515762661812120926481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68329375367098165655803949 25623515762661812120926481)
            ·
              refine ⟨19217636821996359090694861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25623515762661812120926481 19217636821996359090694861)
              ·
                refine ⟨7206613808248634659010573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19217636821996359090694861 7206613808248634659010573)
                ·
                  refine ⟨2702480178093237997128965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7206613808248634659010573 2702480178093237997128965)
                  ·
                    refine ⟨506715033392482124461681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2702480178093237997128965 506715033392482124461681)
                    ·
                      rfl

theorem cell23_2960472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_2960472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960472 prefixEnd_2960472 := by exact prefixLift 2960472
  have htrace : WordTrace (prefixWord ++ tailWord_2960472) baseStart_2960472 baseEnd_2960472 := by
    simpa [prefixWord, tailWord_2960472, baseEnd_2960472] using wordTrace_append hprefix tailTrace_2960472
  have hstable : (prefixWord ++ tailWord_2960472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960472).length < 2 ^ (prefixWord ++ tailWord_2960472).sum := by decide
  have hdescent : baseEnd_2960472 < baseStart_2960472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960502 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_2960502 : Nat := 118140960795 + 2960502 * 2 ^ 59
def prefixEnd_2960502 : Nat := 4983230072969 + 3 ^ 40 * 2960502 * 2
def baseEnd_2960502 : Nat := 168906722733009028445545

theorem tailTrace_2960502 : CollatzResearch.WordTrace tailWord_2960502 prefixEnd_2960502 168906722733009028445545 := by
  unfold tailWord_2960502
  simp only [CollatzResearch.WordTrace]
  refine ⟨6748648670038396395797735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71985585813742894888509173 6748648670038396395797735)
  ·
    refine ⟨10122973005057594593696603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6748648670038396395797735 10122973005057594593696603)
    ·
      refine ⟨15184459507586391890544905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10122973005057594593696603 15184459507586391890544905)
      ·
        refine ⟨11388344630689793917908679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15184459507586391890544905 11388344630689793917908679)
        ·
          refine ⟨17082516946034690876863019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11388344630689793917908679 17082516946034690876863019)
          ·
            refine ⟨25623775419052036315294529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17082516946034690876863019 25623775419052036315294529)
            ·
              refine ⟨19217831564289027236470897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25623775419052036315294529 19217831564289027236470897)
              ·
                refine ⟨14413373673216770427353173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19217831564289027236470897 14413373673216770427353173)
                ·
                  refine ⟨168906722733009028445545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14413373673216770427353173 168906722733009028445545)
                  ·
                    rfl

theorem cell23_2960502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_2960502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960502 prefixEnd_2960502 := by exact prefixLift 2960502
  have htrace : WordTrace (prefixWord ++ tailWord_2960502) baseStart_2960502 baseEnd_2960502 := by
    simpa [prefixWord, tailWord_2960502, baseEnd_2960502] using wordTrace_append hprefix tailTrace_2960502
  have hstable : (prefixWord ++ tailWord_2960502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960502).length < 2 ^ (prefixWord ++ tailWord_2960502).sum := by decide
  have hdescent : baseEnd_2960502 < baseStart_2960502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960549 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_2960549 : Nat := 118140960795 + 2960549 * 2 ^ 59
def prefixEnd_2960549 : Nat := 4983230072969 + 3 ^ 40 * 2960549 * 2
def baseEnd_2960549 : Nat := 506728212729280857374063

theorem tailTrace_2960549 : CollatzResearch.WordTrace tailWord_2960549 prefixEnd_2960549 506728212729280857374063 := by
  unfold tailWord_2960549
  simp only [CollatzResearch.WordTrace]
  refine ⟨107980092951444069359724701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71986728634296046239816467 107980092951444069359724701)
  ·
    refine ⟨40492534856791526009896763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107980092951444069359724701 40492534856791526009896763)
    ·
      refine ⟨60738802285187289014845145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40492534856791526009896763 60738802285187289014845145)
      ·
        refine ⟨45554101713890466761133859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60738802285187289014845145 45554101713890466761133859)
        ·
          refine ⟨68331152570835700141700789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45554101713890466761133859 68331152570835700141700789)
          ·
            refine ⟨6406045553515846888284449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68331152570835700141700789 6406045553515846888284449)
            ·
              refine ⟨4804534165136885166213337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6406045553515846888284449 4804534165136885166213337)
              ·
                refine ⟨3603400623852663874660003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4804534165136885166213337 3603400623852663874660003)
                ·
                  refine ⟨5405100935778995811990005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603400623852663874660003 5405100935778995811990005)
                  ·
                    refine ⟨506728212729280857374063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5405100935778995811990005 506728212729280857374063)
                    ·
                      rfl

theorem cell23_2960549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_2960549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960549 prefixEnd_2960549 := by exact prefixLift 2960549
  have htrace : WordTrace (prefixWord ++ tailWord_2960549) baseStart_2960549 baseEnd_2960549 := by
    simpa [prefixWord, tailWord_2960549, baseEnd_2960549] using wordTrace_append hprefix tailTrace_2960549
  have hstable : (prefixWord ++ tailWord_2960549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960549).length < 2 ^ (prefixWord ++ tailWord_2960549).sum := by decide
  have hdescent : baseEnd_2960549 < baseStart_2960549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960569 : List Nat := [1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 4]
def baseStart_2960569 : Nat := 118140960795 + 2960569 * 2 ^ 59
def prefixEnd_2960569 : Nat := 4983230072969 + 3 ^ 40 * 2960569 * 2
def baseEnd_2960569 : Nat := 1520194907800932493872097

theorem tailTrace_2960569 : CollatzResearch.WordTrace tailWord_2960569 prefixEnd_2960569 1520194907800932493872097 := by
  unfold tailWord_2960569
  simp only [CollatzResearch.WordTrace]
  refine ⟨107980822411371612775452761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71987214940914408516968507 107980822411371612775452761)
  ·
    refine ⟨80985616808528709581589571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107980822411371612775452761 80985616808528709581589571)
    ·
      refine ⟨121478425212793064372384357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80985616808528709581589571 121478425212793064372384357)
      ·
        refine ⟨22777204727398699569822067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121478425212793064372384357 22777204727398699569822067)
        ·
          refine ⟨34165807091098049354733101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22777204727398699569822067 34165807091098049354733101)
          ·
            refine ⟨12812177659161768508024913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34165807091098049354733101 12812177659161768508024913)
            ·
              refine ⟨9609133244371326381018685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12812177659161768508024913 9609133244371326381018685)
              ·
                refine ⟨3603424966639247392882007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9609133244371326381018685 3603424966639247392882007)
                ·
                  refine ⟨5405137449958871089323011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603424966639247392882007 5405137449958871089323011)
                  ·
                    refine ⟨8107706174938306633984517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5405137449958871089323011 8107706174938306633984517)
                    ·
                      refine ⟨1520194907800932493872097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8107706174938306633984517 1520194907800932493872097)
                      ·
                        rfl

theorem cell23_2960569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_2960569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960569 prefixEnd_2960569 := by exact prefixLift 2960569
  have htrace : WordTrace (prefixWord ++ tailWord_2960569) baseStart_2960569 baseEnd_2960569 := by
    simpa [prefixWord, tailWord_2960569, baseEnd_2960569] using wordTrace_append hprefix tailTrace_2960569
  have hstable : (prefixWord ++ tailWord_2960569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960569).length < 2 ^ (prefixWord ++ tailWord_2960569).sum := by decide
  have hdescent : baseEnd_2960569 < baseStart_2960569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960575 : List Nat := [1, 1, 2, 2, 2, 2, 13]
def baseStart_2960575 : Nat := 118140960795 + 2960575 * 2 ^ 59
def prefixEnd_2960575 : Nat := 4983230072969 + 3 ^ 40 * 2960575 * 2
def baseEnd_2960575 : Nat := 18767876403516783585149

theorem tailTrace_2960575 : CollatzResearch.WordTrace tailWord_2960575 prefixEnd_2960575 18767876403516783585149 := by
  unfold tailWord_2960575
  simp only [CollatzResearch.WordTrace]
  refine ⟨107981041249349875800171179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71987360832899917200114119 107981041249349875800171179)
  ·
    refine ⟨161971561874024813700256769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107981041249349875800171179 161971561874024813700256769)
    ·
      refine ⟨121478671405518610275192577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161971561874024813700256769 121478671405518610275192577)
      ·
        refine ⟨91109003554138957706394433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121478671405518610275192577 91109003554138957706394433)
        ·
          refine ⟨68331752665604218279795825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91109003554138957706394433 68331752665604218279795825)
          ·
            refine ⟨51248814499203163709846869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68331752665604218279795825 51248814499203163709846869)
            ·
              refine ⟨18767876403516783585149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 51248814499203163709846869 18767876403516783585149)
              ·
                rfl

theorem cell23_2960575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 13].length) (baseStart_2960575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960575 prefixEnd_2960575 := by exact prefixLift 2960575
  have htrace : WordTrace (prefixWord ++ tailWord_2960575) baseStart_2960575 baseEnd_2960575 := by
    simpa [prefixWord, tailWord_2960575, baseEnd_2960575] using wordTrace_append hprefix tailTrace_2960575
  have hstable : (prefixWord ++ tailWord_2960575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960575).length < 2 ^ (prefixWord ++ tailWord_2960575).sum := by decide
  have hdescent : baseEnd_2960575 < baseStart_2960575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960580 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_2960580 : Nat := 118140960795 + 2960580 * 2 ^ 59
def prefixEnd_2960580 : Nat := 4983230072969 + 3 ^ 40 * 2960580 * 2
def baseEnd_2960580 : Nat := 1520200556088131950834547

theorem tailTrace_2960580 : CollatzResearch.WordTrace tailWord_2960580 prefixEnd_2960580 1520200556088131950834547 := by
  unfold tailWord_2960580
  simp only [CollatzResearch.WordTrace]
  refine ⟨53990611807165880827051597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71987482409554507769402129 53990611807165880827051597)
  ·
    refine ⟨20246479427687205310144349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53990611807165880827051597 20246479427687205310144349)
    ·
      refine ⟨7592429785382701991304131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20246479427687205310144349 7592429785382701991304131)
      ·
        refine ⟨11388644678074052986956197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7592429785382701991304131 11388644678074052986956197)
        ·
          refine ⟨2135370877138884935054287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11388644678074052986956197 2135370877138884935054287)
          ·
            refine ⟨3203056315708327402581431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135370877138884935054287 3203056315708327402581431)
            ·
              refine ⟨4804584473562491103872147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203056315708327402581431 4804584473562491103872147)
              ·
                refine ⟨7206876710343736655808221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4804584473562491103872147 7206876710343736655808221)
                ·
                  refine ⟨2702578766378901245928083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7206876710343736655808221 2702578766378901245928083)
                  ·
                    refine ⟨4053868149568351868892125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2702578766378901245928083 4053868149568351868892125)
                    ·
                      refine ⟨1520200556088131950834547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4053868149568351868892125 1520200556088131950834547)
                      ·
                        rfl

theorem cell23_2960580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_2960580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960580 prefixEnd_2960580 := by exact prefixLift 2960580
  have htrace : WordTrace (prefixWord ++ tailWord_2960580) baseStart_2960580 baseEnd_2960580 := by
    simpa [prefixWord, tailWord_2960580, baseEnd_2960580] using wordTrace_append hprefix tailTrace_2960580
  have hstable : (prefixWord ++ tailWord_2960580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960580).length < 2 ^ (prefixWord ++ tailWord_2960580).sum := by decide
  have hdescent : baseEnd_2960580 < baseStart_2960580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960619 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 3]
def baseStart_2960619 : Nat := 118140960795 + 2960619 * 2 ^ 59
def prefixEnd_2960619 : Nat := 4983230072969 + 3 ^ 40 * 2960619 * 2
def baseEnd_2960619 : Nat := 1520220581833657298246867

theorem tailTrace_2960619 : CollatzResearch.WordTrace tailWord_2960619 prefixEnd_2960619 1520220581833657298246867 := by
  unfold tailWord_2960619
  simp only [CollatzResearch.WordTrace]
  refine ⟨107982646061190471314772911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71988430707460314209848607 107982646061190471314772911)
  ·
    refine ⟨161973969091785706972159367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107982646061190471314772911 161973969091785706972159367)
    ·
      refine ⟨242960953637678560458239051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161973969091785706972159367 242960953637678560458239051)
      ·
        refine ⟨364441430456517840687358577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242960953637678560458239051 364441430456517840687358577)
        ·
          refine ⟨273331072842388380515518933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364441430456517840687358577 273331072842388380515518933)
          ·
            refine ⟨6406197019743477668332475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 273331072842388380515518933 6406197019743477668332475)
            ·
              refine ⟨9609295529615216502498713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6406197019743477668332475 9609295529615216502498713)
              ·
                refine ⟨7206971647211412376874035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9609295529615216502498713 7206971647211412376874035)
                ·
                  refine ⟨10810457470817118565311053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7206971647211412376874035 10810457470817118565311053)
                  ·
                    refine ⟨4053921551556419461991645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10810457470817118565311053 4053921551556419461991645)
                    ·
                      refine ⟨1520220581833657298246867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4053921551556419461991645 1520220581833657298246867)
                      ·
                        rfl

theorem cell23_2960619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 3].length) (baseStart_2960619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960619 prefixEnd_2960619 := by exact prefixLift 2960619
  have htrace : WordTrace (prefixWord ++ tailWord_2960619) baseStart_2960619 baseEnd_2960619 := by
    simpa [prefixWord, tailWord_2960619, baseEnd_2960619] using wordTrace_append hprefix tailTrace_2960619
  have hstable : (prefixWord ++ tailWord_2960619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960619).length < 2 ^ (prefixWord ++ tailWord_2960619).sum := by decide
  have hdescent : baseEnd_2960619 < baseStart_2960619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960623 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 1, 2, 3]
def baseStart_2960623 : Nat := 118140960795 + 2960623 * 2 ^ 59
def prefixEnd_2960623 : Nat := 4983230072969 + 3 ^ 40 * 2960623 * 2
def baseEnd_2960623 : Nat := 1520222635756275282596849

theorem tailTrace_2960623 : CollatzResearch.WordTrace tailWord_2960623 prefixEnd_2960623 1520222635756275282596849 := by
  unfold tailWord_2960623
  simp only [CollatzResearch.WordTrace]
  refine ⟨107982791953175979997918523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71988527968783986665279015 107982791953175979997918523)
  ·
    refine ⟨161974187929763969996877785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107982791953175979997918523 161974187929763969996877785)
    ·
      refine ⟨121480640947322977497658339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161974187929763969996877785 121480640947322977497658339)
      ·
        refine ⟨182220961420984466246487509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121480640947322977497658339 182220961420984466246487509)
        ·
          refine ⟨4270803783304323427652051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 182220961420984466246487509 4270803783304323427652051)
          ·
            refine ⟨6406205674956485141478077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4270803783304323427652051 6406205674956485141478077)
            ·
              refine ⟨2402327128108681928054279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6406205674956485141478077 2402327128108681928054279)
              ·
                refine ⟨3603490692163022892081419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402327128108681928054279 3603490692163022892081419)
                ·
                  refine ⟨5405236038244534338122129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603490692163022892081419 5405236038244534338122129)
                  ·
                    refine ⟨4053927028683400753591597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5405236038244534338122129 4053927028683400753591597)
                    ·
                      refine ⟨1520222635756275282596849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4053927028683400753591597 1520222635756275282596849)
                      ·
                        rfl

theorem cell23_2960623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 2, 3].length) (baseStart_2960623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960623 prefixEnd_2960623 := by exact prefixLift 2960623
  have htrace : WordTrace (prefixWord ++ tailWord_2960623) baseStart_2960623 baseEnd_2960623 := by
    simpa [prefixWord, tailWord_2960623, baseEnd_2960623] using wordTrace_append hprefix tailTrace_2960623
  have hstable : (prefixWord ++ tailWord_2960623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960623).length < 2 ^ (prefixWord ++ tailWord_2960623).sum := by decide
  have hdescent : baseEnd_2960623 < baseStart_2960623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960652 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 1, 8]
def baseStart_2960652 : Nat := 118140960795 + 2960652 * 2 ^ 59
def prefixEnd_2960652 : Nat := 4983230072969 + 3 ^ 40 * 2960652 * 2
def baseEnd_2960652 : Nat := 506745842231751889711405

theorem tailTrace_2960652 : CollatzResearch.WordTrace tailWord_2960652 prefixEnd_2960652 506745842231751889711405 := by
  unfold tailWord_2960652
  simp only [CollatzResearch.WordTrace]
  refine ⟨53991924835035458975362105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71989233113380611967149473 53991924835035458975362105)
  ·
    refine ⟨40493943626276594231521579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53991924835035458975362105 40493943626276594231521579)
    ·
      refine ⟨60740915439414891347282369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40493943626276594231521579 60740915439414891347282369)
      ·
        refine ⟨45555686579561168510461777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60740915439414891347282369 45555686579561168510461777)
        ·
          refine ⟨34166764934670876382846333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45555686579561168510461777 34166764934670876382846333)
          ·
            refine ⟨12812536850501578643567375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34166764934670876382846333 12812536850501578643567375)
            ·
              refine ⟨19218805275752367965351063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12812536850501578643567375 19218805275752367965351063)
              ·
                refine ⟨28828207913628551948026595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19218805275752367965351063 28828207913628551948026595)
                ·
                  refine ⟨43242311870442827922039893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28828207913628551948026595 43242311870442827922039893)
                  ·
                    refine ⟨506745842231751889711405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43242311870442827922039893 506745842231751889711405)
                    ·
                      rfl

theorem cell23_2960652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_2960652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960652 prefixEnd_2960652 := by exact prefixLift 2960652
  have htrace : WordTrace (prefixWord ++ tailWord_2960652) baseStart_2960652 baseEnd_2960652 := by
    simpa [prefixWord, tailWord_2960652, baseEnd_2960652] using wordTrace_append hprefix tailTrace_2960652
  have hstable : (prefixWord ++ tailWord_2960652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960652).length < 2 ^ (prefixWord ++ tailWord_2960652).sum := by decide
  have hdescent : baseEnd_2960652 < baseStart_2960652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960676 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 1, 4, 2]
def baseStart_2960676 : Nat := 118140960795 + 2960676 * 2 ^ 59
def prefixEnd_2960676 : Nat := 4983230072969 + 3 ^ 40 * 2960676 * 2
def baseEnd_2960676 : Nat := 1520249850230963575234105

theorem tailTrace_2960676 : CollatzResearch.WordTrace tailWord_2960676 prefixEnd_2960676 1520249850230963575234105 := by
  unfold tailWord_2960676
  simp only [CollatzResearch.WordTrace]
  refine ⟨53992362510991985024798941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71989816681322646699731921 53992362510991985024798941)
  ·
    refine ⟨20247135941621994384299603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53992362510991985024798941 20247135941621994384299603)
    ·
      refine ⟨30370703912432991576449405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20247135941621994384299603 30370703912432991576449405)
      ·
        refine ⟨11389013967162371841168527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30370703912432991576449405 11389013967162371841168527)
        ·
          refine ⟨17083520950743557761752791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11389013967162371841168527 17083520950743557761752791)
          ·
            refine ⟨25625281426115336642629187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17083520950743557761752791 25625281426115336642629187)
            ·
              refine ⟨38437922139173004963943781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25625281426115336642629187 38437922139173004963943781)
              ·
                refine ⟨7207110401094938430739459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38437922139173004963943781 7207110401094938430739459)
                ·
                  refine ⟨10810665601642407646109189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7207110401094938430739459 10810665601642407646109189)
                  ·
                    refine ⟨2026999800307951433645473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10810665601642407646109189 2026999800307951433645473)
                    ·
                      refine ⟨1520249850230963575234105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2026999800307951433645473 1520249850230963575234105)
                      ·
                        rfl

theorem cell23_2960676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_2960676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960676 prefixEnd_2960676 := by exact prefixLift 2960676
  have htrace : WordTrace (prefixWord ++ tailWord_2960676) baseStart_2960676 baseEnd_2960676 := by
    simpa [prefixWord, tailWord_2960676, baseEnd_2960676] using wordTrace_append hprefix tailTrace_2960676
  have hstable : (prefixWord ++ tailWord_2960676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960676).length < 2 ^ (prefixWord ++ tailWord_2960676).sum := by decide
  have hdescent : baseEnd_2960676 < baseStart_2960676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960680 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_2960680 : Nat := 118140960795 + 2960680 * 2 ^ 59
def prefixEnd_2960680 : Nat := 4983230072969 + 3 ^ 40 * 2960680 * 2
def baseEnd_2960680 : Nat := 1520251904153581559584087

theorem tailTrace_2960680 : CollatzResearch.WordTrace tailWord_2960680 prefixEnd_2960680 1520251904153581559584087 := by
  unfold tailWord_2960680
  simp only [CollatzResearch.WordTrace]
  refine ⟨53992435456984739366371747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71989913942646319155162329 53992435456984739366371747)
  ·
    refine ⟨80988653185477109049557621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53992435456984739366371747 80988653185477109049557621)
    ·
      refine ⟨7592686236138478973396027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80988653185477109049557621 7592686236138478973396027)
      ·
        refine ⟨11389029354207718460094041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7592686236138478973396027 11389029354207718460094041)
        ·
          refine ⟨8541772015655788845070531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11389029354207718460094041 8541772015655788845070531)
          ·
            refine ⟨12812658023483683267605797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8541772015655788845070531 12812658023483683267605797)
            ·
              refine ⟨2402373379403190612676087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12812658023483683267605797 2402373379403190612676087)
              ·
                refine ⟨3603560069104785919014131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402373379403190612676087 3603560069104785919014131)
                ·
                  refine ⟨5405340103657178878521197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603560069104785919014131 5405340103657178878521197)
                  ·
                    refine ⟨2027002538871442079445449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5405340103657178878521197 2027002538871442079445449)
                    ·
                      refine ⟨1520251904153581559584087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027002538871442079445449 1520251904153581559584087)
                      ·
                        rfl

theorem cell23_2960680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_2960680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960680 prefixEnd_2960680 := by exact prefixLift 2960680
  have htrace : WordTrace (prefixWord ++ tailWord_2960680) baseStart_2960680 baseEnd_2960680 := by
    simpa [prefixWord, tailWord_2960680, baseEnd_2960680] using wordTrace_append hprefix tailTrace_2960680
  have hstable : (prefixWord ++ tailWord_2960680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960680).length < 2 ^ (prefixWord ++ tailWord_2960680).sum := by decide
  have hdescent : baseEnd_2960680 < baseStart_2960680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960689 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_2960689 : Nat := 118140960795 + 2960689 * 2 ^ 59
def prefixEnd_2960689 : Nat := 4983230072969 + 3 ^ 40 * 2960689 * 2
def baseEnd_2960689 : Nat := 1520256525479472024371545

theorem tailTrace_2960689 : CollatzResearch.WordTrace tailWord_2960689 prefixEnd_2960689 1520256525479472024371545 := by
  unfold tailWord_2960689
  simp only [CollatzResearch.WordTrace]
  refine ⟨107985199170936873269821121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71990132780624582179880747 107985199170936873269821121)
  ·
    refine ⟨80988899378202654952365841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107985199170936873269821121 80988899378202654952365841)
    ·
      refine ⟨60741674533651991214274381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80988899378202654952365841 60741674533651991214274381)
      ·
        refine ⟨22778127950119496705352893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60741674533651991214274381 22778127950119496705352893)
        ·
          refine ⟨8541797981294811264507335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22778127950119496705352893 8541797981294811264507335)
          ·
            refine ⟨12812696971942216896761003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8541797981294811264507335 12812696971942216896761003)
            ·
              refine ⟨19219045457913325345141505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12812696971942216896761003 19219045457913325345141505)
              ·
                refine ⟨14414284093434994008856129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19219045457913325345141505 14414284093434994008856129)
                ·
                  refine ⟨10810713070076245506642097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14414284093434994008856129 10810713070076245506642097)
                  ·
                    refine ⟨8108034802557184129981573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10810713070076245506642097 8108034802557184129981573)
                    ·
                      refine ⟨1520256525479472024371545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8108034802557184129981573 1520256525479472024371545)
                      ·
                        rfl

theorem cell23_2960689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_2960689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960689 prefixEnd_2960689 := by exact prefixLift 2960689
  have htrace : WordTrace (prefixWord ++ tailWord_2960689) baseStart_2960689 baseEnd_2960689 := by
    simpa [prefixWord, tailWord_2960689, baseEnd_2960689] using wordTrace_append hprefix tailTrace_2960689
  have hstable : (prefixWord ++ tailWord_2960689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960689).length < 2 ^ (prefixWord ++ tailWord_2960689).sum := by decide
  have hdescent : baseEnd_2960689 < baseStart_2960689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960693 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_2960693 : Nat := 118140960795 + 2960693 * 2 ^ 59
def prefixEnd_2960693 : Nat := 4983230072969 + 3 ^ 40 * 2960693 * 2
def baseEnd_2960693 : Nat := 1520258579402090008721527

theorem tailTrace_2960693 : CollatzResearch.WordTrace tailWord_2960693 prefixEnd_2960693 1520258579402090008721527 := by
  unfold tailWord_2960693
  simp only [CollatzResearch.WordTrace]
  refine ⟨107985345062922381952966733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71990230041948254635311155 107985345062922381952966733)
  ·
    refine ⟨40494504398595893232362525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107985345062922381952966733 40494504398595893232362525)
    ·
      refine ⟨15185439149473459962135947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40494504398595893232362525 15185439149473459962135947)
      ·
        refine ⟨22778158724210189943203921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15185439149473459962135947 22778158724210189943203921)
        ·
          refine ⟨17083619043157642457402941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22778158724210189943203921 17083619043157642457402941)
          ·
            refine ⟨6406357141184115921526103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17083619043157642457402941 6406357141184115921526103)
            ·
              refine ⟨9609535711776173882289155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6406357141184115921526103 9609535711776173882289155)
              ·
                refine ⟨14414303567664260823433733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9609535711776173882289155 14414303567664260823433733)
                ·
                  refine ⟨2702681918937048904393825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14414303567664260823433733 2702681918937048904393825)
                  ·
                    refine ⟨2027011439202786678295369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2702681918937048904393825 2027011439202786678295369)
                    ·
                      refine ⟨1520258579402090008721527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027011439202786678295369 1520258579402090008721527)
                      ·
                        rfl

theorem cell23_2960693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_2960693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960693 prefixEnd_2960693 := by exact prefixLift 2960693
  have htrace : WordTrace (prefixWord ++ tailWord_2960693) baseStart_2960693 baseEnd_2960693 := by
    simpa [prefixWord, tailWord_2960693, baseEnd_2960693] using wordTrace_append hprefix tailTrace_2960693
  have hstable : (prefixWord ++ tailWord_2960693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960693).length < 2 ^ (prefixWord ++ tailWord_2960693).sum := by decide
  have hdescent : baseEnd_2960693 < baseStart_2960693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960719 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 3, 7, 2]
def baseStart_2960719 : Nat := 118140960795 + 2960719 * 2 ^ 59
def prefixEnd_2960719 : Nat := 4983230072969 + 3 ^ 40 * 2960719 * 2
def baseEnd_2960719 : Nat := 1520271929899106906996407

theorem tailTrace_2960719 : CollatzResearch.WordTrace tailWord_2960719 prefixEnd_2960719 1520271929899106906996407 := by
  unfold tailWord_2960719
  simp only [CollatzResearch.WordTrace]
  refine ⟨107986293360828188393413211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71990862240552125595608807 107986293360828188393413211)
  ·
    refine ⟨161979440041242282590119817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107986293360828188393413211 161979440041242282590119817)
    ·
      refine ⟨121484580030931711942589863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 161979440041242282590119817 121484580030931711942589863)
      ·
        refine ⟨182226870046397567913884795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121484580030931711942589863 182226870046397567913884795)
        ·
          refine ⟨273340305069596351870827193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182226870046397567913884795 273340305069596351870827193)
          ·
            refine ⟨205005228802197263903120395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273340305069596351870827193 205005228802197263903120395)
            ·
              refine ⟨307507843203295895854680593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205005228802197263903120395 307507843203295895854680593)
              ·
                refine ⟨230630882402471921891010445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307507843203295895854680593 230630882402471921891010445)
                ·
                  refine ⟨86486580900926970709128917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 230630882402471921891010445 86486580900926970709128917)
                  ·
                    refine ⟨2027029239865475875995209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 86486580900926970709128917 2027029239865475875995209)
                    ·
                      refine ⟨1520271929899106906996407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027029239865475875995209 1520271929899106906996407)
                      ·
                        rfl

theorem cell23_2960719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 7, 2].length) (baseStart_2960719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960719 prefixEnd_2960719 := by exact prefixLift 2960719
  have htrace : WordTrace (prefixWord ++ tailWord_2960719) baseStart_2960719 baseEnd_2960719 := by
    simpa [prefixWord, tailWord_2960719, baseEnd_2960719] using wordTrace_append hprefix tailTrace_2960719
  have hstable : (prefixWord ++ tailWord_2960719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960719).length < 2 ^ (prefixWord ++ tailWord_2960719).sum := by decide
  have hdescent : baseEnd_2960719 < baseStart_2960719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960750 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_2960750 : Nat := 118140960795 + 2960750 * 2 ^ 59
def prefixEnd_2960750 : Nat := 4983230072969 + 3 ^ 40 * 2960750 * 2
def baseEnd_2960750 : Nat := 168920871977710698412085

theorem tailTrace_2960750 : CollatzResearch.WordTrace tailWord_2960750 prefixEnd_2960750 168920871977710698412085 := by
  unfold tailWord_2960750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13498428002964485085973963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71991616015810587125194469 13498428002964485085973963)
  ·
    refine ⟨20247642004446727628960945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13498428002964485085973963 20247642004446727628960945)
    ·
      refine ⟨15185731503335045721720709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20247642004446727628960945 15185731503335045721720709)
      ·
        refine ⟨2847324656875321072822633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15185731503335045721720709 2847324656875321072822633)
        ·
          refine ⟨2135493492656490804616975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2847324656875321072822633 2135493492656490804616975)
          ·
            refine ⟨3203240238984736206925463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135493492656490804616975 3203240238984736206925463)
            ·
              refine ⟨4804860358477104310388195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203240238984736206925463 4804860358477104310388195)
              ·
                refine ⟨7207290537715656465582293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4804860358477104310388195 7207290537715656465582293)
                ·
                  refine ⟨168920871977710698412085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7207290537715656465582293 168920871977710698412085)
                  ·
                    rfl

theorem cell23_2960750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_2960750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960750 prefixEnd_2960750 := by exact prefixLift 2960750
  have htrace : WordTrace (prefixWord ++ tailWord_2960750) baseStart_2960750 baseEnd_2960750 := by
    simpa [prefixWord, tailWord_2960750, baseEnd_2960750] using wordTrace_append hprefix tailTrace_2960750
  have hstable : (prefixWord ++ tailWord_2960750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960750).length < 2 ^ (prefixWord ++ tailWord_2960750).sum := by decide
  have hdescent : baseEnd_2960750 < baseStart_2960750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960829 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_2960829 : Nat := 118140960795 + 2960829 * 2 ^ 59
def prefixEnd_2960829 : Nat := 4983230072969 + 3 ^ 40 * 2960829 * 2
def baseEnd_2960829 : Nat := 1520328412771101476620901

theorem tailTrace_2960829 : CollatzResearch.WordTrace tailWord_2960829 prefixEnd_2960829 1520328412771101476620901 := by
  unfold tailWord_2960829
  simp only [CollatzResearch.WordTrace]
  refine ⟨107990305390429677179917541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71993536926953118119945027 107990305390429677179917541)
  ·
    refine ⟨20248182260705564471234539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107990305390429677179917541 20248182260705564471234539)
    ·
      refine ⟨30372273391058346706851809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20248182260705564471234539 30372273391058346706851809)
      ·
        refine ⟨22779205043293760030138857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30372273391058346706851809 22779205043293760030138857)
        ·
          refine ⟨17084403782470320022604143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22779205043293760030138857 17084403782470320022604143)
          ·
            refine ⟨25626605673705480033906215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17084403782470320022604143 25626605673705480033906215)
            ·
              refine ⟨38439908510558220050859323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25626605673705480033906215 38439908510558220050859323)
              ·
                refine ⟨57659862765837330076288985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38439908510558220050859323 57659862765837330076288985)
                ·
                  refine ⟨43244897074377997557216739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57659862765837330076288985 43244897074377997557216739)
                  ·
                    refine ⟨64867345611566996335825109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43244897074377997557216739 64867345611566996335825109)
                    ·
                      refine ⟨1520328412771101476620901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64867345611566996335825109 1520328412771101476620901)
                      ·
                        rfl

theorem cell23_2960829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_2960829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960829 prefixEnd_2960829 := by exact prefixLift 2960829
  have htrace : WordTrace (prefixWord ++ tailWord_2960829) baseStart_2960829 baseEnd_2960829 := by
    simpa [prefixWord, tailWord_2960829, baseEnd_2960829] using wordTrace_append hprefix tailTrace_2960829
  have hstable : (prefixWord ++ tailWord_2960829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960829).length < 2 ^ (prefixWord ++ tailWord_2960829).sum := by decide
  have hdescent : baseEnd_2960829 < baseStart_2960829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960843 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 2, 3, 2]
def baseStart_2960843 : Nat := 118140960795 + 2960843 * 2 ^ 59
def prefixEnd_2960843 : Nat := 4983230072969 + 3 ^ 40 * 2960843 * 2
def baseEnd_2960843 : Nat := 1520335601500264421845837

theorem tailTrace_2960843 : CollatzResearch.WordTrace tailWord_2960843 prefixEnd_2960843 1520335601500264421845837 := by
  unfold tailWord_2960843
  simp only [CollatzResearch.WordTrace]
  refine ⟨107990816012378957570927183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71993877341585971713951455 107990816012378957570927183)
  ·
    refine ⟨161986224018568436356390775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107990816012378957570927183 161986224018568436356390775)
    ·
      refine ⟨242979336027852654534586163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161986224018568436356390775 242979336027852654534586163)
      ·
        refine ⟨364469004041778981801879245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242979336027852654534586163 364469004041778981801879245)
        ·
          refine ⟨136675876515667118175704717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364469004041778981801879245 136675876515667118175704717)
          ·
            refine ⟨51253453693375169315889269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 136675876515667118175704717 51253453693375169315889269)
            ·
              refine ⟨4805011283753922123364619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51253453693375169315889269 4805011283753922123364619)
              ·
                refine ⟨7207516925630883185046929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4805011283753922123364619 7207516925630883185046929)
                ·
                  refine ⟨5405637694223162388785197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7207516925630883185046929 5405637694223162388785197)
                  ·
                    refine ⟨2027114135333685895794449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5405637694223162388785197 2027114135333685895794449)
                    ·
                      refine ⟨1520335601500264421845837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027114135333685895794449 1520335601500264421845837)
                      ·
                        rfl

theorem cell23_2960843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 3, 2].length) (baseStart_2960843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960843 prefixEnd_2960843 := by exact prefixLift 2960843
  have htrace : WordTrace (prefixWord ++ tailWord_2960843) baseStart_2960843 baseEnd_2960843 := by
    simpa [prefixWord, tailWord_2960843, baseEnd_2960843] using wordTrace_append hprefix tailTrace_2960843
  have hstable : (prefixWord ++ tailWord_2960843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960843).length < 2 ^ (prefixWord ++ tailWord_2960843).sum := by decide
  have hdescent : baseEnd_2960843 < baseStart_2960843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960876 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 3]
def baseStart_2960876 : Nat := 118140960795 + 2960876 * 2 ^ 59
def prefixEnd_2960876 : Nat := 4983230072969 + 3 ^ 40 * 2960876 * 2
def baseEnd_2960876 : Nat := 1520352546361862792733185

theorem tailTrace_2960876 : CollatzResearch.WordTrace tailWord_2960876 prefixEnd_2960876 1520352546361862792733185 := by
  unfold tailWord_2960876
  simp only [CollatzResearch.WordTrace]
  refine ⟨53996009810629702103439241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71994679747506269471252321 53996009810629702103439241)
  ·
    refine ⟨40497007357972276577579431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53996009810629702103439241 40497007357972276577579431)
    ·
      refine ⟨60745511036958414866369147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40497007357972276577579431 60745511036958414866369147)
      ·
        refine ⟨91118266555437622299553721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60745511036958414866369147 91118266555437622299553721)
        ·
          refine ⟨68338699916578216724665291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91118266555437622299553721 68338699916578216724665291)
          ·
            refine ⟨102508049874867325086997937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68338699916578216724665291 102508049874867325086997937)
            ·
              refine ⟨76881037406150493815248453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102508049874867325086997937 76881037406150493815248453)
              ·
                refine ⟨14415194513653217590359085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76881037406150493815248453 14415194513653217590359085)
                ·
                  refine ⟨5405697942619956596384657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14415194513653217590359085 5405697942619956596384657)
                  ·
                    refine ⟨4054273456964967447288493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5405697942619956596384657 4054273456964967447288493)
                    ·
                      refine ⟨1520352546361862792733185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4054273456964967447288493 1520352546361862792733185)
                      ·
                        rfl

theorem cell23_2960876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_2960876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960876 prefixEnd_2960876 := by exact prefixLift 2960876
  have htrace : WordTrace (prefixWord ++ tailWord_2960876) baseStart_2960876 baseEnd_2960876 := by
    simpa [prefixWord, tailWord_2960876, baseEnd_2960876] using wordTrace_append hprefix tailTrace_2960876
  have hstable : (prefixWord ++ tailWord_2960876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960876).length < 2 ^ (prefixWord ++ tailWord_2960876).sum := by decide
  have hdescent : baseEnd_2960876 < baseStart_2960876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960893 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_2960893 : Nat := 118140960795 + 2960893 * 2 ^ 59
def prefixEnd_2960893 : Nat := 4983230072969 + 3 ^ 40 * 2960893 * 2
def baseEnd_2960893 : Nat := 1520361275532989226220607

theorem tailTrace_2960893 : CollatzResearch.WordTrace tailWord_2960893 prefixEnd_2960893 1520361275532989226220607 := by
  unfold tailWord_2960893
  simp only [CollatzResearch.WordTrace]
  refine ⟨107992639662197816110247333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71995093108131877406831555 107992639662197816110247333)
  ·
    refine ⟨20248619936662090520671375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107992639662197816110247333 20248619936662090520671375)
    ·
      refine ⟨30372929904993135781007063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20248619936662090520671375 30372929904993135781007063)
      ·
        refine ⟨45559394857489703671510595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30372929904993135781007063 45559394857489703671510595)
        ·
          refine ⟨68339092286234555507265893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45559394857489703671510595 68339092286234555507265893)
          ·
            refine ⟨12813579803668979157612355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68339092286234555507265893 12813579803668979157612355)
            ·
              refine ⟨19220369705503468736418533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12813579803668979157612355 19220369705503468736418533)
              ·
                refine ⟨3603819319781900388078475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19220369705503468736418533 3603819319781900388078475)
                ·
                  refine ⟨5405728979672850582117713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3603819319781900388078475 5405728979672850582117713)
                  ·
                    refine ⟨4054296734754637936588285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5405728979672850582117713 4054296734754637936588285)
                    ·
                      refine ⟨1520361275532989226220607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4054296734754637936588285 1520361275532989226220607)
                      ·
                        rfl

theorem cell23_2960893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_2960893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960893 prefixEnd_2960893 := by exact prefixLift 2960893
  have htrace : WordTrace (prefixWord ++ tailWord_2960893) baseStart_2960893 baseEnd_2960893 := by
    simpa [prefixWord, tailWord_2960893, baseEnd_2960893] using wordTrace_append hprefix tailTrace_2960893
  have hstable : (prefixWord ++ tailWord_2960893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960893).length < 2 ^ (prefixWord ++ tailWord_2960893).sum := by decide
  have hdescent : baseEnd_2960893 < baseStart_2960893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960924 : List Nat := [2, 2, 3, 1, 2, 1, 5, 2, 1, 2, 2]
def baseStart_2960924 : Nat := 118140960795 + 2960924 * 2 ^ 59
def prefixEnd_2960924 : Nat := 4983230072969 + 3 ^ 40 * 2960924 * 2
def baseEnd_2960924 : Nat := 1520377193433278604932965

theorem tailTrace_2960924 : CollatzResearch.WordTrace tailWord_2960924 prefixEnd_2960924 1520377193433278604932965 := by
  unfold tailWord_2960924
  simp only [CollatzResearch.WordTrace]
  refine ⟨53996885162542754202312913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71995846883390338936417217 53996885162542754202312913)
  ·
    refine ⟨40497663871907065651734685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53996885162542754202312913 40497663871907065651734685)
    ·
      refine ⟨15186623951965149619400507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40497663871907065651734685 15186623951965149619400507)
      ·
        refine ⟨22779935927947724429100761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15186623951965149619400507 22779935927947724429100761)
        ·
          refine ⟨17084951945960793321825571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22779935927947724429100761 17084951945960793321825571)
          ·
            refine ⟨25627427918941189982738357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17084951945960793321825571 25627427918941189982738357)
            ·
              refine ⟨2402571367400736560881721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25627427918941189982738357 2402571367400736560881721)
              ·
                refine ⟨1801928525550552420661291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2402571367400736560881721 1801928525550552420661291)
                ·
                  refine ⟨2702892788325828630991937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1801928525550552420661291 2702892788325828630991937)
                  ·
                    refine ⟨2027169591244371473243953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2702892788325828630991937 2027169591244371473243953)
                    ·
                      refine ⟨1520377193433278604932965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027169591244371473243953 1520377193433278604932965)
                      ·
                        rfl

theorem cell23_2960924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_2960924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960924 prefixEnd_2960924 := by exact prefixLift 2960924
  have htrace : WordTrace (prefixWord ++ tailWord_2960924) baseStart_2960924 baseEnd_2960924 := by
    simpa [prefixWord, tailWord_2960924, baseEnd_2960924] using wordTrace_append hprefix tailTrace_2960924
  have hstable : (prefixWord ++ tailWord_2960924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960924).length < 2 ^ (prefixWord ++ tailWord_2960924).sum := by decide
  have hdescent : baseEnd_2960924 < baseStart_2960924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960933 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 3, 3, 2]
def baseStart_2960933 : Nat := 118140960795 + 2960933 * 2 ^ 59
def prefixEnd_2960933 : Nat := 4983230072969 + 3 ^ 40 * 2960933 * 2
def baseEnd_2960933 : Nat := 1520381814759169069720423

theorem tailTrace_2960933 : CollatzResearch.WordTrace tailWord_2960933 prefixEnd_2960933 1520381814759169069720423 := by
  unfold tailWord_2960933
  simp only [CollatzResearch.WordTrace]
  refine ⟨107994098582052902941703453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71996065721368601961135635 107994098582052902941703453)
  ·
    refine ⟨40497786968269838603138795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107994098582052902941703453 40497786968269838603138795)
    ·
      refine ⟨60746680452404757904708193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40497786968269838603138795 60746680452404757904708193)
      ·
        refine ⟨45560010339303568428531145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60746680452404757904708193 45560010339303568428531145)
        ·
          refine ⟨34170007754477676321398359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45560010339303568428531145 34170007754477676321398359)
          ·
            refine ⟨51255011631716514482097539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34170007754477676321398359 51255011631716514482097539)
            ·
              refine ⟨76882517447574771723146309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51255011631716514482097539 76882517447574771723146309)
              ·
                refine ⟨14415472021420269698089933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76882517447574771723146309 14415472021420269698089933)
                ·
                  refine ⟨5405802008032601136783725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14415472021420269698089933 5405802008032601136783725)
                  ·
                    refine ⟨2027175753012225426293897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5405802008032601136783725 2027175753012225426293897)
                    ·
                      refine ⟨1520381814759169069720423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027175753012225426293897 1520381814759169069720423)
                      ·
                        rfl

theorem cell23_2960933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_2960933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960933 prefixEnd_2960933 := by exact prefixLift 2960933
  have htrace : WordTrace (prefixWord ++ tailWord_2960933) baseStart_2960933 baseEnd_2960933 := by
    simpa [prefixWord, tailWord_2960933, baseEnd_2960933] using wordTrace_append hprefix tailTrace_2960933
  have hstable : (prefixWord ++ tailWord_2960933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960933).length < 2 ^ (prefixWord ++ tailWord_2960933).sum := by decide
  have hdescent : baseEnd_2960933 < baseStart_2960933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960976 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_2960976 : Nat := 118140960795 + 2960976 * 2 ^ 59
def prefixEnd_2960976 : Nat := 4983230072969 + 3 ^ 40 * 2960976 * 2
def baseEnd_2960976 : Nat := 1520403894427312401482725

theorem tailTrace_2960976 : CollatzResearch.WordTrace tailWord_2960976 prefixEnd_2960976 1520403894427312401482725 := by
  unfold tailWord_2960976
  simp only [CollatzResearch.WordTrace]
  refine ⟨53997833460448560642759391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71997111280598080857012521 53997833460448560642759391)
  ·
    refine ⟨80996750190672840964139087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53997833460448560642759391 80996750190672840964139087)
    ·
      refine ⟨121495125286009261446208631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80996750190672840964139087 121495125286009261446208631)
      ·
        refine ⟨182242687929013892169312947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121495125286009261446208631 182242687929013892169312947)
        ·
          refine ⟨273364031893520838253969421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182242687929013892169312947 273364031893520838253969421)
          ·
            refine ⟨102511511960070314345238533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273364031893520838253969421 102511511960070314345238533)
            ·
              refine ⟨19220908492513183939732225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102511511960070314345238533 19220908492513183939732225)
              ·
                refine ⟨14415681369384887954799169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19220908492513183939732225 14415681369384887954799169)
                ·
                  refine ⟨10811761027038665966099377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14415681369384887954799169 10811761027038665966099377)
                  ·
                    refine ⟨8108820770278999474574533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10811761027038665966099377 8108820770278999474574533)
                    ·
                      refine ⟨1520403894427312401482725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8108820770278999474574533 1520403894427312401482725)
                      ·
                        rfl

theorem cell23_2960976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_2960976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960976 prefixEnd_2960976 := by exact prefixLift 2960976
  have htrace : WordTrace (prefixWord ++ tailWord_2960976) baseStart_2960976 baseEnd_2960976 := by
    simpa [prefixWord, tailWord_2960976, baseEnd_2960976] using wordTrace_append hprefix tailTrace_2960976
  have hstable : (prefixWord ++ tailWord_2960976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960976).length < 2 ^ (prefixWord ++ tailWord_2960976).sum := by decide
  have hdescent : baseEnd_2960976 < baseStart_2960976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2960997 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 2, 2, 2]
def baseStart_2960997 : Nat := 118140960795 + 2960997 * 2 ^ 59
def prefixEnd_2960997 : Nat := 4983230072969 + 3 ^ 40 * 2960997 * 2
def baseEnd_2960997 : Nat := 1520414677521056819320129

theorem tailTrace_2960997 : CollatzResearch.WordTrace tailWord_2960997 prefixEnd_2960997 1520414677521056819320129 := by
  unfold tailWord_2960997
  simp only [CollatzResearch.WordTrace]
  refine ⟨107996432853821041872033245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71997621902547361248022163 107996432853821041872033245)
  ·
    refine ⟨40498662320182890702012467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107996432853821041872033245 40498662320182890702012467)
    ·
      refine ⟨60747993480274336053018701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40498662320182890702012467 60747993480274336053018701)
      ·
        refine ⟨22780497555102876019882013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60747993480274336053018701 22780497555102876019882013)
        ·
          refine ⟨8542686583163578507455755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22780497555102876019882013 8542686583163578507455755)
          ·
            refine ⟨12814029874745367761183633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8542686583163578507455755 12814029874745367761183633)
            ·
              refine ⟨9610522406059025820887725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12814029874745367761183633 9610522406059025820887725)
              ·
                refine ⟨3603945902272134682832897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9610522406059025820887725 3603945902272134682832897)
                ·
                  refine ⟨2702959426704101012124673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3603945902272134682832897 2702959426704101012124673)
                  ·
                    refine ⟨2027219570028075759093505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2702959426704101012124673 2027219570028075759093505)
                    ·
                      refine ⟨1520414677521056819320129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027219570028075759093505 1520414677521056819320129)
                      ·
                        rfl

theorem cell23_2960997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_2960997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2960997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2960997 prefixEnd_2960997 := by exact prefixLift 2960997
  have htrace : WordTrace (prefixWord ++ tailWord_2960997) baseStart_2960997 baseEnd_2960997 := by
    simpa [prefixWord, tailWord_2960997, baseEnd_2960997] using wordTrace_append hprefix tailTrace_2960997
  have hstable : (prefixWord ++ tailWord_2960997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2960997).length < 2 ^ (prefixWord ++ tailWord_2960997).sum := by decide
  have hdescent : baseEnd_2960997 < baseStart_2960997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2960997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961120 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 3, 1, 3]
def baseStart_2961120 : Nat := 118140960795 + 2961120 * 2 ^ 59
def prefixEnd_2961120 : Nat := 4983230072969 + 3 ^ 40 * 2961120 * 2
def baseEnd_2961120 : Nat := 1520477835641559838082063

theorem tailTrace_2961120 : CollatzResearch.WordTrace tailWord_2961120 prefixEnd_2961120 1520477835641559838082063 := by
  unfold tailWord_2961120
  simp only [CollatzResearch.WordTrace]
  refine ⟨54000459516187716939380407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72000612688250289252507209 54000459516187716939380407)
  ·
    refine ⟨81000689274281575409070611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54000459516187716939380407 81000689274281575409070611)
    ·
      refine ⟨121501033911422363113605917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81000689274281575409070611 121501033911422363113605917)
      ·
        refine ⟨45562887716783386167602219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121501033911422363113605917 45562887716783386167602219)
        ·
          refine ⟨68344331575175079251403329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45562887716783386167602219 68344331575175079251403329)
          ·
            refine ⟨51258248681381309438552497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68344331575175079251403329 51258248681381309438552497)
            ·
              refine ⟨38443686511035982078914373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51258248681381309438552497 38443686511035982078914373)
              ·
                refine ⟨7208191220819246639796445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38443686511035982078914373 7208191220819246639796445)
                ·
                  refine ⟨2703071707807217489923667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7208191220819246639796445 2703071707807217489923667)
                  ·
                    refine ⟨4054607561710826234885501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2703071707807217489923667 4054607561710826234885501)
                    ·
                      refine ⟨1520477835641559838082063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4054607561710826234885501 1520477835641559838082063)
                      ·
                        rfl

theorem cell23_2961120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_2961120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961120 prefixEnd_2961120 := by exact prefixLift 2961120
  have htrace : WordTrace (prefixWord ++ tailWord_2961120) baseStart_2961120 baseEnd_2961120 := by
    simpa [prefixWord, tailWord_2961120, baseEnd_2961120] using wordTrace_append hprefix tailTrace_2961120
  have hstable : (prefixWord ++ tailWord_2961120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961120).length < 2 ^ (prefixWord ++ tailWord_2961120).sum := by decide
  have hdescent : baseEnd_2961120 < baseStart_2961120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961130 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_2961130 : Nat := 118140960795 + 2961130 * 2 ^ 59
def prefixEnd_2961130 : Nat := 4983230072969 + 3 ^ 40 * 2961130 * 2
def baseEnd_2961130 : Nat := 1520482970448104798957017

theorem tailTrace_2961130 : CollatzResearch.WordTrace tailWord_2961130 prefixEnd_2961130 1520482970448104798957017 := by
  unfold tailWord_2961130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27000320940584801396656211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72000855841559470391083229 27000320940584801396656211)
  ·
    refine ⟨40500481410877202094984317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27000320940584801396656211 40500481410877202094984317)
    ·
      refine ⟨15187680529078950785619119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40500481410877202094984317 15187680529078950785619119)
      ·
        refine ⟨22781520793618426178428679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15187680529078950785619119 22781520793618426178428679)
        ·
          refine ⟨34172281190427639267643019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22781520793618426178428679 34172281190427639267643019)
          ·
            refine ⟨51258421785641458901464529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34172281190427639267643019 51258421785641458901464529)
            ·
              refine ⟨38443816339231094176098397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51258421785641458901464529 38443816339231094176098397)
              ·
                refine ⟨14416431127211660316036899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38443816339231094176098397 14416431127211660316036899)
                ·
                  refine ⟨21624646690817490474055349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14416431127211660316036899 21624646690817490474055349)
                  ·
                    refine ⟨2027310627264139731942689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21624646690817490474055349 2027310627264139731942689)
                    ·
                      refine ⟨1520482970448104798957017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027310627264139731942689 1520482970448104798957017)
                      ·
                        rfl

theorem cell23_2961130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_2961130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961130 prefixEnd_2961130 := by exact prefixLift 2961130
  have htrace : WordTrace (prefixWord ++ tailWord_2961130) baseStart_2961130 baseEnd_2961130 := by
    simpa [prefixWord, tailWord_2961130, baseEnd_2961130] using wordTrace_append hprefix tailTrace_2961130
  have hstable : (prefixWord ++ tailWord_2961130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961130).length < 2 ^ (prefixWord ++ tailWord_2961130).sum := by decide
  have hdescent : baseEnd_2961130 < baseStart_2961130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961163 : List Nat := [1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 5]
def baseStart_2961163 : Nat := 118140960795 + 2961163 * 2 ^ 59
def prefixEnd_2961163 : Nat := 4983230072969 + 3 ^ 40 * 2961163 * 2
def baseEnd_2961163 : Nat := 1520499915309703169844365

theorem tailTrace_2961163 : CollatzResearch.WordTrace tailWord_2961163 prefixEnd_2961163 1520499915309703169844365 := by
  unfold tailWord_2961163
  simp only [CollatzResearch.WordTrace]
  refine ⟨108002487371219652222576143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72001658247479768148384095 108002487371219652222576143)
  ·
    refine ⟨162003731056829478333864215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108002487371219652222576143 162003731056829478333864215)
    ·
      refine ⟨243005596585244217500796323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162003731056829478333864215 243005596585244217500796323)
      ·
        refine ⟨364508394877866326251194485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243005596585244217500796323 364508394877866326251194485)
        ·
          refine ⟨34172662019799968086049483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 364508394877866326251194485 34172662019799968086049483)
          ·
            refine ⟨51258993029699952129074225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34172662019799968086049483 51258993029699952129074225)
            ·
              refine ⟨38444244772274964096805669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51258993029699952129074225 38444244772274964096805669)
              ·
                refine ⟨7208295894801555768151063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38444244772274964096805669 7208295894801555768151063)
                ·
                  refine ⟨10812443842202333652226595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7208295894801555768151063 10812443842202333652226595)
                  ·
                    refine ⟨16218665763303500478339893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10812443842202333652226595 16218665763303500478339893)
                    ·
                      refine ⟨1520499915309703169844365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16218665763303500478339893 1520499915309703169844365)
                      ·
                        rfl

theorem cell23_2961163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 1, 5].length) (baseStart_2961163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961163 prefixEnd_2961163 := by exact prefixLift 2961163
  have htrace : WordTrace (prefixWord ++ tailWord_2961163) baseStart_2961163 baseEnd_2961163 := by
    simpa [prefixWord, tailWord_2961163, baseEnd_2961163] using wordTrace_append hprefix tailTrace_2961163
  have hstable : (prefixWord ++ tailWord_2961163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961163).length < 2 ^ (prefixWord ++ tailWord_2961163).sum := by decide
  have hdescent : baseEnd_2961163 < baseStart_2961163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961180 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_2961180 : Nat := 118140960795 + 2961180 * 2 ^ 59
def prefixEnd_2961180 : Nat := 4983230072969 + 3 ^ 40 * 2961180 * 2
def baseEnd_2961180 : Nat := 1520508644480829603331787

theorem tailTrace_2961180 : CollatzResearch.WordTrace tailWord_2961180 prefixEnd_2961180 1520508644480829603331787 := by
  unfold tailWord_2961180
  simp only [CollatzResearch.WordTrace]
  refine ⟨54001553706079032062972497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72002071608105376083963329 54001553706079032062972497)
  ·
    refine ⟨40501165279559274047229373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54001553706079032062972497 40501165279559274047229373)
    ·
      refine ⟨15187936979834727767711015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40501165279559274047229373 15187936979834727767711015)
      ·
        refine ⟨22781905469752091651566523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15187936979834727767711015 22781905469752091651566523)
        ·
          refine ⟨34172858204628137477349785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22781905469752091651566523 34172858204628137477349785)
          ·
            refine ⟨25629643653471103108012339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34172858204628137477349785 25629643653471103108012339)
            ·
              refine ⟨38444465480206654662018509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25629643653471103108012339 38444465480206654662018509)
              ·
                refine ⟨14416674555077495498256941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38444465480206654662018509 14416674555077495498256941)
                ·
                  refine ⟨5406252958154060811846353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14416674555077495498256941 5406252958154060811846353)
                  ·
                    refine ⟨4054689718615545608884765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5406252958154060811846353 4054689718615545608884765)
                    ·
                      refine ⟨1520508644480829603331787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4054689718615545608884765 1520508644480829603331787)
                      ·
                        rfl

theorem cell23_2961180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_2961180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961180 prefixEnd_2961180 := by exact prefixLift 2961180
  have htrace : WordTrace (prefixWord ++ tailWord_2961180) baseStart_2961180 baseEnd_2961180 := by
    simpa [prefixWord, tailWord_2961180, baseEnd_2961180] using wordTrace_append hprefix tailTrace_2961180
  have hstable : (prefixWord ++ tailWord_2961180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961180).length < 2 ^ (prefixWord ++ tailWord_2961180).sum := by decide
  have hdescent : baseEnd_2961180 < baseStart_2961180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961204 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_2961204 : Nat := 118140960795 + 2961204 * 2 ^ 59
def prefixEnd_2961204 : Nat := 4983230072969 + 3 ^ 40 * 2961204 * 2
def baseEnd_2961204 : Nat := 506840322672179169810559

theorem tailTrace_2961204 : CollatzResearch.WordTrace tailWord_2961204 prefixEnd_2961204 506840322672179169810559 := by
  unfold tailWord_2961204
  simp only [CollatzResearch.WordTrace]
  refine ⟨54001991382035558112409333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72002655176047410816545777 54001991382035558112409333)
  ·
    refine ⟨5062686692065833573038375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54001991382035558112409333 5062686692065833573038375)
    ·
      refine ⟨7594030038098750359557563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5062686692065833573038375 7594030038098750359557563)
      ·
        refine ⟨11391045057148125539336345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7594030038098750359557563 11391045057148125539336345)
        ·
          refine ⟨8543283792861094154502259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11391045057148125539336345 8543283792861094154502259)
          ·
            refine ⟨12814925689291641231753389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8543283792861094154502259 12814925689291641231753389)
            ·
              refine ⟨4805597133484365461907521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12814925689291641231753389 4805597133484365461907521)
              ·
                refine ⟨3604197850113274096430641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4805597133484365461907521 3604197850113274096430641)
                ·
                  refine ⟨2703148387584955572322981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3604197850113274096430641 2703148387584955572322981)
                  ·
                    refine ⟨506840322672179169810559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2703148387584955572322981 506840322672179169810559)
                    ·
                      rfl

theorem cell23_2961204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_2961204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961204 prefixEnd_2961204 := by exact prefixLift 2961204
  have htrace : WordTrace (prefixWord ++ tailWord_2961204) baseStart_2961204 baseEnd_2961204 := by
    simpa [prefixWord, tailWord_2961204, baseEnd_2961204] using wordTrace_append hprefix tailTrace_2961204
  have hstable : (prefixWord ++ tailWord_2961204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961204).length < 2 ^ (prefixWord ++ tailWord_2961204).sum := by decide
  have hdescent : baseEnd_2961204 < baseStart_2961204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961278 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_2961278 : Nat := 118140960795 + 2961278 * 2 ^ 59
def prefixEnd_2961278 : Nat := 4983230072969 + 3 ^ 40 * 2961278 * 2
def baseEnd_2961278 : Nat := 1520558965584970219906337

theorem tailTrace_2961278 : CollatzResearch.WordTrace tailWord_2961278 prefixEnd_2961278 1520558965584970219906337 := by
  unfold tailWord_2961278
  simp only [CollatzResearch.WordTrace]
  refine ⟨13500835220725378357876561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72004454510535351242008325 13500835220725378357876561)
  ·
    refine ⟨10125626415544033768407421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13500835220725378357876561 10125626415544033768407421)
    ·
      refine ⟨3797109905829012663152783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10125626415544033768407421 3797109905829012663152783)
      ·
        refine ⟨5695664858743518994729175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3797109905829012663152783 5695664858743518994729175)
        ·
          refine ⟨8543497288115278492093763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5695664858743518994729175 8543497288115278492093763)
          ·
            refine ⟨12815245932172917738140645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8543497288115278492093763 12815245932172917738140645)
            ·
              refine ⟨2402858612282422075901371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12815245932172917738140645 2402858612282422075901371)
              ·
                refine ⟨3604287918423633113852057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402858612282422075901371 3604287918423633113852057)
                ·
                  refine ⟨2703215938817724835389043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3604287918423633113852057 2703215938817724835389043)
                  ·
                    refine ⟨4054823908226587253083565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2703215938817724835389043 4054823908226587253083565)
                    ·
                      refine ⟨1520558965584970219906337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4054823908226587253083565 1520558965584970219906337)
                      ·
                        rfl

theorem cell23_2961278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_2961278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961278 prefixEnd_2961278 := by exact prefixLift 2961278
  have htrace : WordTrace (prefixWord ++ tailWord_2961278) baseStart_2961278 baseEnd_2961278 := by
    simpa [prefixWord, tailWord_2961278, baseEnd_2961278] using wordTrace_append hprefix tailTrace_2961278
  have hstable : (prefixWord ++ tailWord_2961278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961278).length < 2 ^ (prefixWord ++ tailWord_2961278).sum := by decide
  have hdescent : baseEnd_2961278 < baseStart_2961278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961288 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 1, 3, 2]
def baseStart_2961288 : Nat := 118140960795 + 2961288 * 2 ^ 59
def prefixEnd_2961288 : Nat := 4983230072969 + 3 ^ 40 * 2961288 * 2
def baseEnd_2961288 : Nat := 1520564100391515180781291

theorem tailTrace_2961288 : CollatzResearch.WordTrace tailWord_2961288 prefixEnd_2961288 1520564100391515180781291 := by
  unfold tailWord_2961288
  simp only [CollatzResearch.WordTrace]
  refine ⟨54003523247883399285438259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72004697663844532380584345 54003523247883399285438259)
  ·
    refine ⟨81005284871825098928157389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54003523247883399285438259 81005284871825098928157389)
    ·
      refine ⟨30376981826934412098059021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81005284871825098928157389 30376981826934412098059021)
      ·
        refine ⟨11391368185100404536772133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30376981826934412098059021 11391368185100404536772133)
        ·
          refine ⟨2135881534706325850644775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11391368185100404536772133 2135881534706325850644775)
          ·
            refine ⟨3203822302059488775967163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2135881534706325850644775 3203822302059488775967163)
            ·
              refine ⟨4805733453089233163950745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203822302059488775967163 4805733453089233163950745)
              ·
                refine ⟨3604300089816924872963059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4805733453089233163950745 3604300089816924872963059)
                ·
                  refine ⟨5406450134725387309444589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604300089816924872963059 5406450134725387309444589)
                  ·
                    refine ⟨2027418800522020241041721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5406450134725387309444589 2027418800522020241041721)
                    ·
                      refine ⟨1520564100391515180781291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027418800522020241041721 1520564100391515180781291)
                      ·
                        rfl

theorem cell23_2961288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_2961288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961288 prefixEnd_2961288 := by exact prefixLift 2961288
  have htrace : WordTrace (prefixWord ++ tailWord_2961288) baseStart_2961288 baseEnd_2961288 := by
    simpa [prefixWord, tailWord_2961288, baseEnd_2961288] using wordTrace_append hprefix tailTrace_2961288
  have hstable : (prefixWord ++ tailWord_2961288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961288).length < 2 ^ (prefixWord ++ tailWord_2961288).sum := by decide
  have hdescent : baseEnd_2961288 < baseStart_2961288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961323 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 8]
def baseStart_2961323 : Nat := 118140960795 + 2961323 * 2 ^ 59
def prefixEnd_2961323 : Nat := 4983230072969 + 3 ^ 40 * 2961323 * 2
def baseEnd_2961323 : Nat := 1520582072214422543843629

theorem tailTrace_2961323 : CollatzResearch.WordTrace tailWord_2961323 prefixEnd_2961323 1520582072214422543843629 := by
  unfold tailWord_2961323
  simp only [CollatzResearch.WordTrace]
  refine ⟨108008323050639999548400623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72005548700426666365600415 108008323050639999548400623)
  ·
    refine ⟨162012484575959999322600935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108008323050639999548400623 162012484575959999322600935)
    ·
      refine ⟨243018726863939998983901403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162012484575959999322600935 243018726863939998983901403)
      ·
        refine ⟨364528090295909998475852105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243018726863939998983901403 364528090295909998475852105)
        ·
          refine ⟨273396067721932498856889079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364528090295909998475852105 273396067721932498856889079)
          ·
            refine ⟨410094101582898748285333619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273396067721932498856889079 410094101582898748285333619)
            ·
              refine ⟨615141152374348122428000429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410094101582898748285333619 615141152374348122428000429)
              ·
                refine ⟨230677932140380545910500161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 615141152374348122428000429 230677932140380545910500161)
                ·
                  refine ⟨173008449105285409432875121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 230677932140380545910500161 173008449105285409432875121)
                  ·
                    refine ⟨129756336828964057074656341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173008449105285409432875121 129756336828964057074656341)
                    ·
                      refine ⟨1520582072214422543843629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 129756336828964057074656341 1520582072214422543843629)
                      ·
                        rfl

theorem cell23_2961323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 8].length) (baseStart_2961323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961323 prefixEnd_2961323 := by exact prefixLift 2961323
  have htrace : WordTrace (prefixWord ++ tailWord_2961323) baseStart_2961323 baseEnd_2961323 := by
    simpa [prefixWord, tailWord_2961323, baseEnd_2961323] using wordTrace_append hprefix tailTrace_2961323
  have hstable : (prefixWord ++ tailWord_2961323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961323).length < 2 ^ (prefixWord ++ tailWord_2961323).sum := by decide
  have hdescent : baseEnd_2961323 < baseStart_2961323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961377 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_2961377 : Nat := 118140960795 + 2961377 * 2 ^ 59
def prefixEnd_2961377 : Nat := 4983230072969 + 3 ^ 40 * 2961377 * 2
def baseEnd_2961377 : Nat := 1520609800169765332568381

theorem tailTrace_2961377 : CollatzResearch.WordTrace tailWord_2961377 prefixEnd_2961377 1520609800169765332568381 := by
  unfold tailWord_2961377
  simp only [CollatzResearch.WordTrace]
  refine ⟨108010292592444366770866385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72006861728296244513910923 108010292592444366770866385)
  ·
    refine ⟨81007719444333275078149789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108010292592444366770866385 81007719444333275078149789)
    ·
      refine ⟨30377894791624978154306171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81007719444333275078149789 30377894791624978154306171)
      ·
        refine ⟨45566842187437467231459257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30377894791624978154306171 45566842187437467231459257)
        ·
          refine ⟨34175131640578100423594443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45566842187437467231459257 34175131640578100423594443)
          ·
            refine ⟨51262697460867150635391665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34175131640578100423594443 51262697460867150635391665)
            ·
              refine ⟨38447023095650362976543749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51262697460867150635391665 38447023095650362976543749)
              ·
                refine ⟨7208816830434443058101953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38447023095650362976543749 7208816830434443058101953)
                ·
                  refine ⟨5406612622825832293576465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7208816830434443058101953 5406612622825832293576465)
                  ·
                    refine ⟨4054959467119374220182349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5406612622825832293576465 4054959467119374220182349)
                    ·
                      refine ⟨1520609800169765332568381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4054959467119374220182349 1520609800169765332568381)
                      ·
                        rfl

theorem cell23_2961377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_2961377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961377 prefixEnd_2961377 := by exact prefixLift 2961377
  have htrace : WordTrace (prefixWord ++ tailWord_2961377) baseStart_2961377 baseEnd_2961377 := by
    simpa [prefixWord, tailWord_2961377, baseEnd_2961377] using wordTrace_append hprefix tailTrace_2961377
  have hstable : (prefixWord ++ tailWord_2961377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961377).length < 2 ^ (prefixWord ++ tailWord_2961377).sum := by decide
  have hdescent : baseEnd_2961377 < baseStart_2961377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961380 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 8]
def baseStart_2961380 : Nat := 118140960795 + 2961380 * 2 ^ 59
def prefixEnd_2961380 : Nat := 4983230072969 + 3 ^ 40 * 2961380 * 2
def baseEnd_2961380 : Nat := 168956815623525424536763

theorem tailTrace_2961380 : CollatzResearch.WordTrace tailWord_2961380 prefixEnd_2961380 168956815623525424536763 := by
  unfold tailWord_2961380
  simp only [CollatzResearch.WordTrace]
  refine ⟨54005201005716749141612797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72006934674288998855483729 54005201005716749141612797)
  ·
    refine ⟨20251950377143780928104799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54005201005716749141612797 20251950377143780928104799)
    ·
      refine ⟨30377925565715671392157199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20251950377143780928104799 30377925565715671392157199)
      ·
        refine ⟨45566888348573507088235799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30377925565715671392157199 45566888348573507088235799)
        ·
          refine ⟨68350332522860260632353699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45566888348573507088235799 68350332522860260632353699)
          ·
            refine ⟨102525498784290390948530549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68350332522860260632353699 102525498784290390948530549)
            ·
              refine ⟨9611765511027224151424739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102525498784290390948530549 9611765511027224151424739)
              ·
                refine ⟨14417648266540836227137109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9611765511027224151424739 14417648266540836227137109)
                ·
                  refine ⟨168956815623525424536763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14417648266540836227137109 168956815623525424536763)
                  ·
                    rfl

theorem cell23_2961380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_2961380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961380 prefixEnd_2961380 := by exact prefixLift 2961380
  have htrace : WordTrace (prefixWord ++ tailWord_2961380) baseStart_2961380 baseEnd_2961380 := by
    simpa [prefixWord, tailWord_2961380, baseEnd_2961380] using wordTrace_append hprefix tailTrace_2961380
  have hstable : (prefixWord ++ tailWord_2961380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961380).length < 2 ^ (prefixWord ++ tailWord_2961380).sum := by decide
  have hdescent : baseEnd_2961380 < baseStart_2961380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961418 : List Nat := [3, 1, 2, 2, 4, 2, 1, 3, 1, 4]
def baseStart_2961418 : Nat := 118140960795 + 2961418 * 2 ^ 59
def prefixEnd_2961418 : Nat := 4983230072969 + 3 ^ 40 * 2961418 * 2
def baseEnd_2961418 : Nat := 506876950958866557385231

theorem tailTrace_2961418 : CollatzResearch.WordTrace tailWord_2961418 prefixEnd_2961418 506876950958866557385231 := by
  unfold tailWord_2961418
  simp only [CollatzResearch.WordTrace]
  refine ⟨27002946996323957693277227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72007858656863887182072605 27002946996323957693277227)
  ·
    refine ⟨40504420494485936539915841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27002946996323957693277227 40504420494485936539915841)
    ·
      refine ⟨30378315370864452404936881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40504420494485936539915841 30378315370864452404936881)
      ·
        refine ⟨22783736528148339303702661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30378315370864452404936881 22783736528148339303702661)
        ·
          refine ⟨4271950599027813619444249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22783736528148339303702661 4271950599027813619444249)
          ·
            refine ⟨3203962949270860214583187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4271950599027813619444249 3203962949270860214583187)
            ·
              refine ⟨4805944423906290321874781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3203962949270860214583187 4805944423906290321874781)
              ·
                refine ⟨1802229158964858870703043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4805944423906290321874781 1802229158964858870703043)
                ·
                  refine ⟨2703343738447288306054565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802229158964858870703043 2703343738447288306054565)
                  ·
                    refine ⟨506876950958866557385231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2703343738447288306054565 506876950958866557385231)
                    ·
                      rfl

theorem cell23_2961418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_2961418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961418 prefixEnd_2961418 := by exact prefixLift 2961418
  have htrace : WordTrace (prefixWord ++ tailWord_2961418) baseStart_2961418 baseEnd_2961418 := by
    simpa [prefixWord, tailWord_2961418, baseEnd_2961418] using wordTrace_append hprefix tailTrace_2961418
  have hstable : (prefixWord ++ tailWord_2961418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961418).length < 2 ^ (prefixWord ++ tailWord_2961418).sum := by decide
  have hdescent : baseEnd_2961418 < baseStart_2961418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961427 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 1, 5]
def baseStart_2961427 : Nat := 118140960795 + 2961427 * 2 ^ 59
def prefixEnd_2961427 : Nat := 4983230072969 + 3 ^ 40 * 2961427 * 2
def baseEnd_2961427 : Nat := 506878491400830045647717

theorem tailTrace_2961427 : CollatzResearch.WordTrace tailWord_2961427 prefixEnd_2961427 506878491400830045647717 := by
  unfold tailWord_2961427
  simp only [CollatzResearch.WordTrace]
  refine ⟨108012116242263225310186535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72008077494842150206791023 108012116242263225310186535)
  ·
    refine ⟨162018174363394837965279803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108012116242263225310186535 162018174363394837965279803)
    ·
      refine ⟨243027261545092256947919705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162018174363394837965279803 243027261545092256947919705)
      ·
        refine ⟨182270446158819192710939779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243027261545092256947919705 182270446158819192710939779)
        ·
          refine ⟨273405669238228789066409669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182270446158819192710939779 273405669238228789066409669)
          ·
            refine ⟨51263562982167897949951813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 273405669238228789066409669 51263562982167897949951813)
            ·
              refine ⟨9611918059156480865615965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51263562982167897949951813 9611918059156480865615965)
              ·
                refine ⟨3604469272183680324605987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9611918059156480865615965 3604469272183680324605987)
                ·
                  refine ⟨5406703908275520486908981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604469272183680324605987 5406703908275520486908981)
                  ·
                    refine ⟨506878491400830045647717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5406703908275520486908981 506878491400830045647717)
                    ·
                      rfl

theorem cell23_2961427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 1, 5].length) (baseStart_2961427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961427 prefixEnd_2961427 := by exact prefixLift 2961427
  have htrace : WordTrace (prefixWord ++ tailWord_2961427) baseStart_2961427 baseEnd_2961427 := by
    simpa [prefixWord, tailWord_2961427, baseEnd_2961427] using wordTrace_append hprefix tailTrace_2961427
  have hstable : (prefixWord ++ tailWord_2961427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961427).length < 2 ^ (prefixWord ++ tailWord_2961427).sum := by decide
  have hdescent : baseEnd_2961427 < baseStart_2961427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961428 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2961428 : Nat := 118140960795 + 2961428 * 2 ^ 59
def prefixEnd_2961428 : Nat := 4983230072969 + 3 ^ 40 * 2961428 * 2
def baseEnd_2961428 : Nat := 1520635987683144633030647

theorem tailTrace_2961428 : CollatzResearch.WordTrace tailWord_2961428 prefixEnd_2961428 1520635987683144633030647 := by
  unfold tailWord_2961428
  simp only [CollatzResearch.WordTrace]
  refine ⟨54006076357629801240486469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72008101810173068320648625 54006076357629801240486469)
  ·
    refine ⟨10126139317055587732591213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54006076357629801240486469 10126139317055587732591213)
    ·
      refine ⟨3797302243895845399721705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10126139317055587732591213 3797302243895845399721705)
      ·
        refine ⟨2847976682921884049791279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3797302243895845399721705 2847976682921884049791279)
        ·
          refine ⟨4271965024382826074686919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2847976682921884049791279 4271965024382826074686919)
          ·
            refine ⟨6407947536574239112030379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4271965024382826074686919 6407947536574239112030379)
            ·
              refine ⟨9611921304861358668045569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6407947536574239112030379 9611921304861358668045569)
              ·
                refine ⟨7208940978646019001034177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9611921304861358668045569 7208940978646019001034177)
                ·
                  refine ⟨5406705733984514250775633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7208940978646019001034177 5406705733984514250775633)
                  ·
                    refine ⟨4055029300488385688081725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5406705733984514250775633 4055029300488385688081725)
                    ·
                      refine ⟨1520635987683144633030647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055029300488385688081725 1520635987683144633030647)
                      ·
                        rfl

theorem cell23_2961428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2961428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961428 prefixEnd_2961428 := by exact prefixLift 2961428
  have htrace : WordTrace (prefixWord ++ tailWord_2961428) baseStart_2961428 baseEnd_2961428 := by
    simpa [prefixWord, tailWord_2961428, baseEnd_2961428] using wordTrace_append hprefix tailTrace_2961428
  have hstable : (prefixWord ++ tailWord_2961428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961428).length < 2 ^ (prefixWord ++ tailWord_2961428).sum := by decide
  have hdescent : baseEnd_2961428 < baseStart_2961428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961434 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2]
def baseStart_2961434 : Nat := 118140960795 + 2961434 * 2 ^ 59
def prefixEnd_2961434 : Nat := 4983230072969 + 3 ^ 40 * 2961434 * 2
def baseEnd_2961434 : Nat := 1520639068567071609555619

theorem tailTrace_2961434 : CollatzResearch.WordTrace tailWord_2961434 prefixEnd_2961434 1520639068567071609555619 := by
  unfold tailWord_2961434
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003092888309466376422839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72008247702158577003794237 27003092888309466376422839)
  ·
    refine ⟨40504639332464199564634259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27003092888309466376422839 40504639332464199564634259)
    ·
      refine ⟨60756958998696299346951389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40504639332464199564634259 60756958998696299346951389)
      ·
        refine ⟨22783859624511112255106771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60756958998696299346951389 22783859624511112255106771)
        ·
          refine ⟨34175789436766668382660157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22783859624511112255106771 34175789436766668382660157)
          ·
            refine ⟨12815921038787500643497559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34175789436766668382660157 12815921038787500643497559)
            ·
              refine ⟨19223881558181250965246339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12815921038787500643497559 19223881558181250965246339)
              ·
                refine ⟨28835822337271876447869509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19223881558181250965246339 28835822337271876447869509)
                ·
                  refine ⟨5406716688238476833975533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28835822337271876447869509 5406716688238476833975533)
                  ·
                    refine ⟨2027518758089428812740825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5406716688238476833975533 2027518758089428812740825)
                    ·
                      refine ⟨1520639068567071609555619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027518758089428812740825 1520639068567071609555619)
                      ·
                        rfl

theorem cell23_2961434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_2961434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961434 prefixEnd_2961434 := by exact prefixLift 2961434
  have htrace : WordTrace (prefixWord ++ tailWord_2961434) baseStart_2961434 baseEnd_2961434 := by
    simpa [prefixWord, tailWord_2961434, baseEnd_2961434] using wordTrace_append hprefix tailTrace_2961434
  have hstable : (prefixWord ++ tailWord_2961434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961434).length < 2 ^ (prefixWord ++ tailWord_2961434).sum := by decide
  have hdescent : baseEnd_2961434 < baseStart_2961434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961448 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 6]
def baseStart_2961448 : Nat := 118140960795 + 2961448 * 2 ^ 59
def prefixEnd_2961448 : Nat := 4983230072969 + 3 ^ 40 * 2961448 * 2
def baseEnd_2961448 : Nat := 168960695255137172753395

theorem tailTrace_2961448 : CollatzResearch.WordTrace tailWord_2961448 prefixEnd_2961448 168960695255137172753395 := by
  unfold tailWord_2961448
  simp only [CollatzResearch.WordTrace]
  refine ⟨54006441087593572948350499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72008588116791430597800665 54006441087593572948350499)
  ·
    refine ⟨81009661631390359422525749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54006441087593572948350499 81009661631390359422525749)
    ·
      refine ⟨7594655777942846195861789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81009661631390359422525749 7594655777942846195861789)
      ·
        refine ⟨2847995916728567323448171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7594655777942846195861789 2847995916728567323448171)
        ·
          refine ⟨4271993875092850985172257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2847995916728567323448171 4271993875092850985172257)
          ·
            refine ⟨3203995406319638238879193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4271993875092850985172257 3203995406319638238879193)
            ·
              refine ⟨2402996554739728679159395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3203995406319638238879193 2402996554739728679159395)
              ·
                refine ⟨3604494832109593018739093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2402996554739728679159395 3604494832109593018739093)
                ·
                  refine ⟨168960695255137172753395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3604494832109593018739093 168960695255137172753395)
                  ·
                    rfl

theorem cell23_2961448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 6].length) (baseStart_2961448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961448 prefixEnd_2961448 := by exact prefixLift 2961448
  have htrace : WordTrace (prefixWord ++ tailWord_2961448) baseStart_2961448 baseEnd_2961448 := by
    simpa [prefixWord, tailWord_2961448, baseEnd_2961448] using wordTrace_append hprefix tailTrace_2961448
  have hstable : (prefixWord ++ tailWord_2961448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961448).length < 2 ^ (prefixWord ++ tailWord_2961448).sum := by decide
  have hdescent : baseEnd_2961448 < baseStart_2961448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961464 : List Nat := [2, 1, 2, 1, 6, 1, 1, 1, 3, 1, 4]
def baseStart_2961464 : Nat := 118140960795 + 2961464 * 2 ^ 59
def prefixEnd_2961464 : Nat := 4983230072969 + 3 ^ 40 * 2961464 * 2
def baseEnd_2961464 : Nat := 1520654472986706492180481

theorem tailTrace_2961464 : CollatzResearch.WordTrace tailWord_2961464 prefixEnd_2961464 1520654472986706492180481 := by
  unfold tailWord_2961464
  simp only [CollatzResearch.WordTrace]
  refine ⟨54006732871564590314641723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72008977162086120419522297 54006732871564590314641723)
  ·
    refine ⟨81010099307346885471962585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54006732871564590314641723 81010099307346885471962585)
    ·
      refine ⟨60757574480510164103971939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81010099307346885471962585 60757574480510164103971939)
      ·
        refine ⟨91136361720765246155957909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60757574480510164103971939 91136361720765246155957909)
        ·
          refine ⟨4272016955660870913560527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 91136361720765246155957909 4272016955660870913560527)
          ·
            refine ⟨6408025433491306370340791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272016955660870913560527 6408025433491306370340791)
            ·
              refine ⟨9612038150236959555511187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408025433491306370340791 9612038150236959555511187)
              ·
                refine ⟨14418057225355439333266781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9612038150236959555511187 14418057225355439333266781)
                ·
                  refine ⟨5406771459508289749975043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14418057225355439333266781 5406771459508289749975043)
                  ·
                    refine ⟨8110157189262434624962565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5406771459508289749975043 8110157189262434624962565)
                    ·
                      refine ⟨1520654472986706492180481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8110157189262434624962565 1520654472986706492180481)
                      ·
                        rfl

theorem cell23_2961464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_2961464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961464 prefixEnd_2961464 := by exact prefixLift 2961464
  have htrace : WordTrace (prefixWord ++ tailWord_2961464) baseStart_2961464 baseEnd_2961464 := by
    simpa [prefixWord, tailWord_2961464, baseEnd_2961464] using wordTrace_append hprefix tailTrace_2961464
  have hstable : (prefixWord ++ tailWord_2961464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961464).length < 2 ^ (prefixWord ++ tailWord_2961464).sum := by decide
  have hdescent : baseEnd_2961464 < baseStart_2961464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961467 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 3]
def baseStart_2961467 : Nat := 118140960795 + 2961467 * 2 ^ 59
def prefixEnd_2961467 : Nat := 4983230072969 + 3 ^ 40 * 2961467 * 2
def baseEnd_2961467 : Nat := 1520656013428669980442967

theorem tailTrace_2961467 : CollatzResearch.WordTrace tailWord_2961467 prefixEnd_2961467 1520656013428669980442967 := by
  unfold tailWord_2961467
  simp only [CollatzResearch.WordTrace]
  refine ⟨108013575162118312141642655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72009050108078874761095103 108013575162118312141642655)
  ·
    refine ⟨162020362743177468212463983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108013575162118312141642655 162020362743177468212463983)
    ·
      refine ⟨243030544114766202318695975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162020362743177468212463983 243030544114766202318695975)
      ·
        refine ⟨364545816172149303478043963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243030544114766202318695975 364545816172149303478043963)
        ·
          refine ⟨546818724258223955217065945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364545816172149303478043963 546818724258223955217065945)
          ·
            refine ⟨410114043193667966412799459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546818724258223955217065945 410114043193667966412799459)
            ·
              refine ⟨615171064790501949619199189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 410114043193667966412799459 615171064790501949619199189)
              ·
                refine ⟨14418071831027389444199981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 615171064790501949619199189 14418071831027389444199981)
                ·
                  refine ⟨5406776936635271041574993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14418071831027389444199981 5406776936635271041574993)
                  ·
                    refine ⟨4055082702476453281181245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5406776936635271041574993 4055082702476453281181245)
                    ·
                      refine ⟨1520656013428669980442967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055082702476453281181245 1520656013428669980442967)
                      ·
                        rfl

theorem cell23_2961467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 2, 3].length) (baseStart_2961467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961467 prefixEnd_2961467 := by exact prefixLift 2961467
  have htrace : WordTrace (prefixWord ++ tailWord_2961467) baseStart_2961467 baseEnd_2961467 := by
    simpa [prefixWord, tailWord_2961467, baseEnd_2961467] using wordTrace_append hprefix tailTrace_2961467
  have hstable : (prefixWord ++ tailWord_2961467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961467).length < 2 ^ (prefixWord ++ tailWord_2961467).sum := by decide
  have hdescent : baseEnd_2961467 < baseStart_2961467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961478 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_2961478 : Nat := 118140960795 + 2961478 * 2 ^ 59
def prefixEnd_2961478 : Nat := 4983230072969 + 3 ^ 40 * 2961478 * 2
def baseEnd_2961478 : Nat := 506887220571956479135139

theorem tailTrace_2961478 : CollatzResearch.WordTrace tailWord_2961478 prefixEnd_2961478 506887220571956479135139 := by
  unfold tailWord_2961478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375436761408701906884159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72009317576718974013528725 3375436761408701906884159)
  ·
    refine ⟨5063155142113052860326239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3375436761408701906884159 5063155142113052860326239)
    ·
      refine ⟨7594732713169579290489359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5063155142113052860326239 7594732713169579290489359)
      ·
        refine ⟨11392099069754368935734039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7594732713169579290489359 11392099069754368935734039)
        ·
          refine ⟨17088148604631553403601059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11392099069754368935734039 17088148604631553403601059)
          ·
            refine ⟨25632222906947330105401589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17088148604631553403601059 25632222906947330105401589)
            ·
              refine ⟨2403020897526312197381399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25632222906947330105401589 2403020897526312197381399)
              ·
                refine ⟨3604531346289468296072099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403020897526312197381399 3604531346289468296072099)
                ·
                  refine ⟨5406797019434202444108149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604531346289468296072099 5406797019434202444108149)
                  ·
                    refine ⟨506887220571956479135139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5406797019434202444108149 506887220571956479135139)
                    ·
                      rfl

theorem cell23_2961478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_2961478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961478 prefixEnd_2961478 := by exact prefixLift 2961478
  have htrace : WordTrace (prefixWord ++ tailWord_2961478) baseStart_2961478 baseEnd_2961478 := by
    simpa [prefixWord, tailWord_2961478, baseEnd_2961478] using wordTrace_append hprefix tailTrace_2961478
  have hstable : (prefixWord ++ tailWord_2961478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961478).length < 2 ^ (prefixWord ++ tailWord_2961478).sum := by decide
  have hdescent : baseEnd_2961478 < baseStart_2961478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961484 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 1, 2, 3]
def baseStart_2961484 : Nat := 118140960795 + 2961484 * 2 ^ 59
def prefixEnd_2961484 : Nat := 4983230072969 + 3 ^ 40 * 2961484 * 2
def baseEnd_2961484 : Nat := 1520664742599796413930389

theorem tailTrace_2961484 : CollatzResearch.WordTrace tailWord_2961484 prefixEnd_2961484 1520664742599796413930389 := by
  unfold tailWord_2961484
  simp only [CollatzResearch.WordTrace]
  refine ⟨54007097601528362022505753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72009463468704482696674337 54007097601528362022505753)
  ·
    refine ⟨40505323201146271516879315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54007097601528362022505753 40505323201146271516879315)
    ·
      refine ⟨60757984801719407275318973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40505323201146271516879315 60757984801719407275318973)
      ·
        refine ⟨22784244300644777728244615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60757984801719407275318973 22784244300644777728244615)
        ·
          refine ⟨34176366450967166592366923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22784244300644777728244615 34176366450967166592366923)
          ·
            refine ⟨51264549676450749888550385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34176366450967166592366923 51264549676450749888550385)
            ·
              refine ⟨38448412257338062416412789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51264549676450749888550385 38448412257338062416412789)
              ·
                refine ⟨3604538649125443351538699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38448412257338062416412789 3604538649125443351538699)
                ·
                  refine ⟨5406807973688165027308049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604538649125443351538699 5406807973688165027308049)
                  ·
                    refine ⟨4055105980266123770481037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5406807973688165027308049 4055105980266123770481037)
                    ·
                      refine ⟨1520664742599796413930389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055105980266123770481037 1520664742599796413930389)
                      ·
                        rfl

theorem cell23_2961484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_2961484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961484 prefixEnd_2961484 := by exact prefixLift 2961484
  have htrace : WordTrace (prefixWord ++ tailWord_2961484) baseStart_2961484 baseEnd_2961484 := by
    simpa [prefixWord, tailWord_2961484, baseEnd_2961484] using wordTrace_append hprefix tailTrace_2961484
  have hstable : (prefixWord ++ tailWord_2961484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961484).length < 2 ^ (prefixWord ++ tailWord_2961484).sum := by decide
  have hdescent : baseEnd_2961484 < baseStart_2961484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961497 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 3, 3, 3]
def baseStart_2961497 : Nat := 118140960795 + 2961497 * 2 ^ 59
def prefixEnd_2961497 : Nat := 4983230072969 + 3 ^ 40 * 2961497 * 2
def baseEnd_2961497 : Nat := 1520671417848304863067829

theorem tailTrace_2961497 : CollatzResearch.WordTrace tailWord_2961497 prefixEnd_2961497 1520671417848304863067829 := by
  unfold tailWord_2961497
  simp only [CollatzResearch.WordTrace]
  refine ⟨108014669352009627265234745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72009779568006418176823163 108014669352009627265234745)
  ·
    refine ⟨81011002014007220448926059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108014669352009627265234745 81011002014007220448926059)
    ·
      refine ⟨121516503021010830673389089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81011002014007220448926059 121516503021010830673389089)
      ·
        refine ⟨91137377265758123005041817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121516503021010830673389089 91137377265758123005041817)
        ·
          refine ⟨68353032949318592253781363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91137377265758123005041817 68353032949318592253781363)
          ·
            refine ⟨102529549423977888380672045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68353032949318592253781363 102529549423977888380672045)
            ·
              refine ⟨38448581033991708142752017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102529549423977888380672045 38448581033991708142752017)
              ·
                refine ⟨28836435775493781107064013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38448581033991708142752017 28836435775493781107064013)
                ·
                  refine ⟨10813663415810167915149005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28836435775493781107064013 10813663415810167915149005)
                  ·
                    refine ⟨4055123780928812968180877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10813663415810167915149005 4055123780928812968180877)
                    ·
                      refine ⟨1520671417848304863067829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055123780928812968180877 1520671417848304863067829)
                      ·
                        rfl

theorem cell23_2961497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_2961497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961497 prefixEnd_2961497 := by exact prefixLift 2961497
  have htrace : WordTrace (prefixWord ++ tailWord_2961497) baseStart_2961497 baseEnd_2961497 := by
    simpa [prefixWord, tailWord_2961497, baseEnd_2961497] using wordTrace_append hprefix tailTrace_2961497
  have hstable : (prefixWord ++ tailWord_2961497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961497).length < 2 ^ (prefixWord ++ tailWord_2961497).sum := by decide
  have hdescent : baseEnd_2961497 < baseStart_2961497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961498 : List Nat := [3, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2]
def baseStart_2961498 : Nat := 118140960795 + 2961498 * 2 ^ 59
def prefixEnd_2961498 : Nat := 4983230072969 + 3 ^ 40 * 2961498 * 2
def baseEnd_2961498 : Nat := 1520671931328959359155325

theorem tailTrace_2961498 : CollatzResearch.WordTrace tailWord_2961498 prefixEnd_2961498 1520671931328959359155325 := by
  unfold tailWord_2961498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27003676456251501109005287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72009803883337336290680765 27003676456251501109005287)
  ·
    refine ⟨40505514684377251663507931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27003676456251501109005287 40505514684377251663507931)
    ·
      refine ⟨60758272026565877495261897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40505514684377251663507931 60758272026565877495261897)
      ·
        refine ⟨45568704019924408121446423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60758272026565877495261897 45568704019924408121446423)
        ·
          refine ⟨68353056029886612182169635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45568704019924408121446423 68353056029886612182169635)
          ·
            refine ⟨102529584044829918273254453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68353056029886612182169635 102529584044829918273254453)
            ·
              refine ⟨9612148504202804838117605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102529584044829918273254453 9612148504202804838117605)
              ·
                refine ⟨1802277844538025907147051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9612148504202804838117605 1802277844538025907147051)
                ·
                  refine ⟨2703416766807038860720577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802277844538025907147051 2703416766807038860720577)
                  ·
                    refine ⟨2027562575105279145540433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2703416766807038860720577 2027562575105279145540433)
                    ·
                      refine ⟨1520671931328959359155325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027562575105279145540433 1520671931328959359155325)
                      ·
                        rfl

theorem cell23_2961498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_2961498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961498 prefixEnd_2961498 := by exact prefixLift 2961498
  have htrace : WordTrace (prefixWord ++ tailWord_2961498) baseStart_2961498 baseEnd_2961498 := by
    simpa [prefixWord, tailWord_2961498, baseEnd_2961498] using wordTrace_append hprefix tailTrace_2961498
  have hstable : (prefixWord ++ tailWord_2961498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961498).length < 2 ^ (prefixWord ++ tailWord_2961498).sum := by decide
  have hdescent : baseEnd_2961498 < baseStart_2961498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961501 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2961501 : Nat := 118140960795 + 2961501 * 2 ^ 59
def prefixEnd_2961501 : Nat := 4983230072969 + 3 ^ 40 * 2961501 * 2
def baseEnd_2961501 : Nat := 1520673471770922847417811

theorem tailTrace_2961501 : CollatzResearch.WordTrace tailWord_2961501 prefixEnd_2961501 1520673471770922847417811 := by
  unfold tailWord_2961501
  simp only [CollatzResearch.WordTrace]
  refine ⟨108014815243995135948380357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72009876829330090632253571 108014815243995135948380357)
  ·
    refine ⟨20252777858249087990321317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108014815243995135948380357 20252777858249087990321317)
    ·
      refine ⟨3797395848421703998185247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20252777858249087990321317 3797395848421703998185247)
      ·
        refine ⟨5696093772632555997277871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3797395848421703998185247 5696093772632555997277871)
        ·
          refine ⟨8544140658948833995916807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5696093772632555997277871 8544140658948833995916807)
          ·
            refine ⟨12816210988423250993875211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544140658948833995916807 12816210988423250993875211)
            ·
              refine ⟨19224316482634876490812817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12816210988423250993875211 19224316482634876490812817)
              ·
                refine ⟨14418237361976157368109613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19224316482634876490812817 14418237361976157368109613)
                ·
                  refine ⟨5406839010741059013041105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14418237361976157368109613 5406839010741059013041105)
                  ·
                    refine ⟨4055129258055794259780829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5406839010741059013041105 4055129258055794259780829)
                    ·
                      refine ⟨1520673471770922847417811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055129258055794259780829 1520673471770922847417811)
                      ·
                        rfl

theorem cell23_2961501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2961501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961501 prefixEnd_2961501 := by exact prefixLift 2961501
  have htrace : WordTrace (prefixWord ++ tailWord_2961501) baseStart_2961501 baseEnd_2961501 := by
    simpa [prefixWord, tailWord_2961501, baseEnd_2961501] using wordTrace_append hprefix tailTrace_2961501
  have hstable : (prefixWord ++ tailWord_2961501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961501).length < 2 ^ (prefixWord ++ tailWord_2961501).sum := by decide
  have hdescent : baseEnd_2961501 < baseStart_2961501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961517 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2961517 : Nat := 118140960795 + 2961517 * 2 ^ 59
def prefixEnd_2961517 : Nat := 4983230072969 + 3 ^ 40 * 2961517 * 2
def baseEnd_2961517 : Nat := 506893895820464928272579

theorem tailTrace_2961517 : CollatzResearch.WordTrace tailWord_2961517 prefixEnd_2961517 506893895820464928272579 := by
  unfold tailWord_2961517
  simp only [CollatzResearch.WordTrace]
  refine ⟨108015398811937170680962805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72010265874624780453975203 108015398811937170680962805)
  ·
    refine ⟨10126443638619109751340263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108015398811937170680962805 10126443638619109751340263)
    ·
      refine ⟨15189665457928664627010395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10126443638619109751340263 15189665457928664627010395)
      ·
        refine ⟨22784498186892996940515593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15189665457928664627010395 22784498186892996940515593)
        ·
          refine ⟨17088373640169747705386695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22784498186892996940515593 17088373640169747705386695)
          ·
            refine ⟨25632560460254621558080043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17088373640169747705386695 25632560460254621558080043)
            ·
              refine ⟨38448840690381932337120065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25632560460254621558080043 38448840690381932337120065)
              ·
                refine ⟨28836630517786449252840049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38448840690381932337120065 28836630517786449252840049)
                ·
                  refine ⟨21627472888339836939630037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28836630517786449252840049 21627472888339836939630037)
                  ·
                    refine ⟨506893895820464928272579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21627472888339836939630037 506893895820464928272579)
                    ·
                      rfl

theorem cell23_2961517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2961517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961517 prefixEnd_2961517 := by exact prefixLift 2961517
  have htrace : WordTrace (prefixWord ++ tailWord_2961517) baseStart_2961517 baseEnd_2961517 := by
    simpa [prefixWord, tailWord_2961517, baseEnd_2961517] using wordTrace_append hprefix tailTrace_2961517
  have hstable : (prefixWord ++ tailWord_2961517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961517).length < 2 ^ (prefixWord ++ tailWord_2961517).sum := by decide
  have hdescent : baseEnd_2961517 < baseStart_2961517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961575 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_2961575 : Nat := 118140960795 + 2961575 * 2 ^ 59
def prefixEnd_2961575 : Nat := 4983230072969 + 3 ^ 40 * 2961575 * 2
def baseEnd_2961575 : Nat := 1520711469339355557892471

theorem tailTrace_2961575 : CollatzResearch.WordTrace tailWord_2961575 prefixEnd_2961575 1520711469339355557892471 := by
  unfold tailWord_2961575
  simp only [CollatzResearch.WordTrace]
  refine ⟨108017514245727046586574179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72011676163818031057716119 108017514245727046586574179)
  ·
    refine ⟨162026271368590569879861269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108017514245727046586574179 162026271368590569879861269)
    ·
      refine ⟨7594981470402682963118497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 162026271368590569879861269 7594981470402682963118497)
      ·
        refine ⟨5696236102802012222338873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7594981470402682963118497 5696236102802012222338873)
        ·
          refine ⟨4272177077101509166754155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5696236102802012222338873 4272177077101509166754155)
          ·
            refine ⟨6408265615652263750131233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272177077101509166754155 6408265615652263750131233)
            ·
              refine ⟨4806199211739197812598425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6408265615652263750131233 4806199211739197812598425)
              ·
                refine ⟨3604649408804398359448819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806199211739197812598425 3604649408804398359448819)
                ·
                  refine ⟨5406974113206597539173229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604649408804398359448819 5406974113206597539173229)
                  ·
                    refine ⟨2027615292452474077189961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5406974113206597539173229 2027615292452474077189961)
                    ·
                      refine ⟨1520711469339355557892471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027615292452474077189961 1520711469339355557892471)
                      ·
                        rfl

theorem cell23_2961575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_2961575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961575 prefixEnd_2961575 := by exact prefixLift 2961575
  have htrace : WordTrace (prefixWord ++ tailWord_2961575) baseStart_2961575 baseEnd_2961575 := by
    simpa [prefixWord, tailWord_2961575, baseEnd_2961575] using wordTrace_append hprefix tailTrace_2961575
  have hstable : (prefixWord ++ tailWord_2961575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961575).length < 2 ^ (prefixWord ++ tailWord_2961575).sum := by decide
  have hdescent : baseEnd_2961575 < baseStart_2961575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961611 : List Nat := [1, 1, 1, 1, 3, 2, 7, 2, 5]
def baseStart_2961611 : Nat := 118140960795 + 2961611 * 2 ^ 59
def prefixEnd_2961611 : Nat := 4983230072969 + 3 ^ 40 * 2961611 * 2
def baseEnd_2961611 : Nat := 168969994960324157449145

theorem tailTrace_2961611 : CollatzResearch.WordTrace tailWord_2961611 prefixEnd_2961611 168969994960324157449145 := by
  unfold tailWord_2961611
  simp only [CollatzResearch.WordTrace]
  refine ⟨108018827273596624734884687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72012551515731083156589791 108018827273596624734884687)
  ·
    refine ⟨162028240910394937102327031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108018827273596624734884687 162028240910394937102327031)
    ·
      refine ⟨243042361365592405653490547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162028240910394937102327031 243042361365592405653490547)
      ·
        refine ⟨364563542048388608480235821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243042361365592405653490547 364563542048388608480235821)
        ·
          refine ⟨136711328268145728180088433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 364563542048388608480235821 136711328268145728180088433)
          ·
            refine ⟨102533496201109296135066325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136711328268145728180088433 102533496201109296135066325)
            ·
              refine ⟨2403128817213499128165617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 102533496201109296135066325 2403128817213499128165617)
              ·
                refine ⟨1802346612910124346124213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2403128817213499128165617 1802346612910124346124213)
                ·
                  refine ⟨168969994960324157449145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1802346612910124346124213 168969994960324157449145)
                  ·
                    rfl

theorem cell23_2961611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 5].length) (baseStart_2961611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961611 prefixEnd_2961611 := by exact prefixLift 2961611
  have htrace : WordTrace (prefixWord ++ tailWord_2961611) baseStart_2961611 baseEnd_2961611 := by
    simpa [prefixWord, tailWord_2961611, baseEnd_2961611] using wordTrace_append hprefix tailTrace_2961611
  have hstable : (prefixWord ++ tailWord_2961611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961611).length < 2 ^ (prefixWord ++ tailWord_2961611).sum := by decide
  have hdescent : baseEnd_2961611 < baseStart_2961611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961617 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_2961617 : Nat := 118140960795 + 2961617 * 2 ^ 59
def prefixEnd_2961617 : Nat := 4983230072969 + 3 ^ 40 * 2961617 * 2
def baseEnd_2961617 : Nat := 1520733035526844393567277

theorem tailTrace_2961617 : CollatzResearch.WordTrace tailWord_2961617 prefixEnd_2961617 1520733035526844393567277 := by
  unfold tailWord_2961617
  simp only [CollatzResearch.WordTrace]
  refine ⟨108019046111574887759603105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72012697407716591839735403 108019046111574887759603105)
  ·
    refine ⟨81014284583681165819702329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108019046111574887759603105 81014284583681165819702329)
    ·
      refine ⟨60760713437760874364776747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81014284583681165819702329 60760713437760874364776747)
      ·
        refine ⟨91141070156641311547165121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60760713437760874364776747 91141070156641311547165121)
        ·
          refine ⟨68355802617480983660373841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91141070156641311547165121 68355802617480983660373841)
          ·
            refine ⟨51266851963110737745280381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68355802617480983660373841 51266851963110737745280381)
            ·
              refine ⟨19225069486166526654480143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51266851963110737745280381 19225069486166526654480143)
              ·
                refine ⟨28837604229249789981720215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19225069486166526654480143 28837604229249789981720215)
                ·
                  refine ⟨43256406343874684972580323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28837604229249789981720215 43256406343874684972580323)
                  ·
                    refine ⟨64884609515812027458870485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43256406343874684972580323 64884609515812027458870485)
                    ·
                      refine ⟨1520733035526844393567277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64884609515812027458870485 1520733035526844393567277)
                      ·
                        rfl

theorem cell23_2961617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_2961617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961617 prefixEnd_2961617 := by exact prefixLift 2961617
  have htrace : WordTrace (prefixWord ++ tailWord_2961617) baseStart_2961617 baseEnd_2961617 := by
    simpa [prefixWord, tailWord_2961617, baseEnd_2961617] using wordTrace_append hprefix tailTrace_2961617
  have hstable : (prefixWord ++ tailWord_2961617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961617).length < 2 ^ (prefixWord ++ tailWord_2961617).sum := by decide
  have hdescent : baseEnd_2961617 < baseStart_2961617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961622 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_2961622 : Nat := 118140960795 + 2961622 * 2 ^ 59
def prefixEnd_2961622 : Nat := 4983230072969 + 3 ^ 40 * 2961622 * 2
def baseEnd_2961622 : Nat := 1520735602930116874004755

theorem tailTrace_2961622 : CollatzResearch.WordTrace tailWord_2961622 prefixEnd_2961622 1520735602930116874004755 := by
  unfold tailWord_2961622
  simp only [CollatzResearch.WordTrace]
  refine ⟨6751201779784798350845945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72012818984371182409023413 6751201779784798350845945)
  ·
    refine ⟨5063401334838598763134459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6751201779784798350845945 5063401334838598763134459)
    ·
      refine ⟨7595102002257898144701689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5063401334838598763134459 7595102002257898144701689)
      ·
        refine ⟨5696326501693423608526267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7595102002257898144701689 5696326501693423608526267)
        ·
          refine ⟨8544489752540135412789401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5696326501693423608526267 8544489752540135412789401)
          ·
            refine ⟨6408367314405101559592051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8544489752540135412789401 6408367314405101559592051)
            ·
              refine ⟨9612550971607652339388077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408367314405101559592051 9612550971607652339388077)
              ·
                refine ⟨3604706614352869627270529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9612550971607652339388077 3604706614352869627270529)
                ·
                  refine ⟨2703529960764652220452897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3604706614352869627270529 2703529960764652220452897)
                  ·
                    refine ⟨2027647470573489165339673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2703529960764652220452897 2027647470573489165339673)
                    ·
                      refine ⟨1520735602930116874004755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027647470573489165339673 1520735602930116874004755)
                      ·
                        rfl

theorem cell23_2961622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_2961622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961622 prefixEnd_2961622 := by exact prefixLift 2961622
  have htrace : WordTrace (prefixWord ++ tailWord_2961622) baseStart_2961622 baseEnd_2961622 := by
    simpa [prefixWord, tailWord_2961622, baseEnd_2961622] using wordTrace_append hprefix tailTrace_2961622
  have hstable : (prefixWord ++ tailWord_2961622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961622).length < 2 ^ (prefixWord ++ tailWord_2961622).sum := by decide
  have hdescent : baseEnd_2961622 < baseStart_2961622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961698 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_2961698 : Nat := 118140960795 + 2961698 * 2 ^ 59
def prefixEnd_2961698 : Nat := 4983230072969 + 3 ^ 40 * 2961698 * 2
def baseEnd_2961698 : Nat := 1520774627459858576654405

theorem tailTrace_2961698 : CollatzResearch.WordTrace tailWord_2961698 prefixEnd_2961698 1520774627459858576654405 := by
  unfold tailWord_2961698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27005500106070359648325437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72014666949520959062201165 27005500106070359648325437)
  ·
    refine ⟨10127062539776384868122039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27005500106070359648325437 10127062539776384868122039)
    ·
      refine ⟨15190593809664577302183059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10127062539776384868122039 15190593809664577302183059)
      ·
        refine ⟨22785890714496865953274589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15190593809664577302183059 22785890714496865953274589)
        ·
          refine ⟨8544709017936324732477971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22785890714496865953274589 8544709017936324732477971)
          ·
            refine ⟨12817063526904487098716957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544709017936324732477971 12817063526904487098716957)
            ·
              refine ⟨4806398822589182662018859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12817063526904487098716957 4806398822589182662018859)
              ·
                refine ⟨7209598233883773993028289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806398822589182662018859 7209598233883773993028289)
                ·
                  refine ⟨5407198675412830494771217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7209598233883773993028289 5407198675412830494771217)
                  ·
                    refine ⟨4055399006559622871078413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5407198675412830494771217 4055399006559622871078413)
                    ·
                      refine ⟨1520774627459858576654405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055399006559622871078413 1520774627459858576654405)
                      ·
                        rfl

theorem cell23_2961698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_2961698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961698 prefixEnd_2961698 := by exact prefixLift 2961698
  have htrace : WordTrace (prefixWord ++ tailWord_2961698) baseStart_2961698 baseEnd_2961698 := by
    simpa [prefixWord, tailWord_2961698, baseEnd_2961698] using wordTrace_append hprefix tailTrace_2961698
  have hstable : (prefixWord ++ tailWord_2961698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961698).length < 2 ^ (prefixWord ++ tailWord_2961698).sum := by decide
  have hdescent : baseEnd_2961698 < baseStart_2961698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961748 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_2961748 : Nat := 118140960795 + 2961748 * 2 ^ 59
def prefixEnd_2961748 : Nat := 4983230072969 + 3 ^ 40 * 2961748 * 2
def baseEnd_2961748 : Nat := 506933433830861127009725

theorem tailTrace_2961748 : CollatzResearch.WordTrace tailWord_2961748 prefixEnd_2961748 506933433830861127009725 := by
  unfold tailWord_2961748
  simp only [CollatzResearch.WordTrace]
  refine ⟨54011912037050148566310949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72015882716066864755081265 54011912037050148566310949)
  ·
    refine ⟨10127233506946902856183303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54011912037050148566310949 10127233506946902856183303)
    ·
      refine ⟨15190850260420354284274955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10127233506946902856183303 15190850260420354284274955)
      ·
        refine ⟨22786275390630531426412433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15190850260420354284274955 22786275390630531426412433)
        ·
          refine ⟨17089706542972898569809325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22786275390630531426412433 17089706542972898569809325)
          ·
            refine ⟨6408639953614836963678497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17089706542972898569809325 6408639953614836963678497)
            ·
              refine ⟨4806479965211127722758873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6408639953614836963678497 4806479965211127722758873)
              ·
                refine ⟨3604859973908345792069155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806479965211127722758873 3604859973908345792069155)
                ·
                  refine ⟨5407289960862518688103733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604859973908345792069155 5407289960862518688103733)
                  ·
                    refine ⟨506933433830861127009725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5407289960862518688103733 506933433830861127009725)
                    ·
                      rfl

theorem cell23_2961748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_2961748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961748 prefixEnd_2961748 := by exact prefixLift 2961748
  have htrace : WordTrace (prefixWord ++ tailWord_2961748) baseStart_2961748 baseEnd_2961748 := by
    simpa [prefixWord, tailWord_2961748, baseEnd_2961748] using wordTrace_append hprefix tailTrace_2961748
  have hstable : (prefixWord ++ tailWord_2961748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961748).length < 2 ^ (prefixWord ++ tailWord_2961748).sum := by decide
  have hdescent : baseEnd_2961748 < baseStart_2961748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961751 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 2, 6, 2]
def baseStart_2961751 : Nat := 118140960795 + 2961751 * 2 ^ 59
def prefixEnd_2961751 : Nat := 4983230072969 + 3 ^ 40 * 2961751 * 2
def baseEnd_2961751 : Nat := 1520801841934546869291661

theorem tailTrace_2961751 : CollatzResearch.WordTrace tailWord_2961751 prefixEnd_2961751 1520801841934546869291661 := by
  unfold tailWord_2961751
  simp only [CollatzResearch.WordTrace]
  refine ⟨108023933493089428644981107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72015955662059619096654071 108023933493089428644981107)
  ·
    refine ⟨162035900239634142967471661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108023933493089428644981107 162035900239634142967471661)
    ·
      refine ⟨60763462589862803612801873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162035900239634142967471661 60763462589862803612801873)
      ·
        refine ⟨45572596942397102709601405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60763462589862803612801873 45572596942397102709601405)
        ·
          refine ⟨17089723853398913516100527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45572596942397102709601405 17089723853398913516100527)
          ·
            refine ⟨25634585780098370274150791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17089723853398913516100527 25634585780098370274150791)
            ·
              refine ⟨38451878670147555411226187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25634585780098370274150791 38451878670147555411226187)
              ·
                refine ⟨57677818005221333116839281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38451878670147555411226187 57677818005221333116839281)
                ·
                  refine ⟨43258363503915999837629461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57677818005221333116839281 43258363503915999837629461)
                  ·
                    refine ⟨2027735789246062492388881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43258363503915999837629461 2027735789246062492388881)
                    ·
                      refine ⟨1520801841934546869291661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027735789246062492388881 1520801841934546869291661)
                      ·
                        rfl

theorem cell23_2961751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_2961751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961751 prefixEnd_2961751 := by exact prefixLift 2961751
  have htrace : WordTrace (prefixWord ++ tailWord_2961751) baseStart_2961751 baseEnd_2961751 := by
    simpa [prefixWord, tailWord_2961751, baseEnd_2961751] using wordTrace_append hprefix tailTrace_2961751
  have hstable : (prefixWord ++ tailWord_2961751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961751).length < 2 ^ (prefixWord ++ tailWord_2961751).sum := by decide
  have hdescent : baseEnd_2961751 < baseStart_2961751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961754 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_2961754 : Nat := 118140960795 + 2961754 * 2 ^ 59
def prefixEnd_2961754 : Nat := 4983230072969 + 3 ^ 40 * 2961754 * 2
def baseEnd_2961754 : Nat := 1520803382376510357554147

theorem tailTrace_2961754 : CollatzResearch.WordTrace tailWord_2961754 prefixEnd_2961754 1520803382376510357554147 := by
  unfold tailWord_2961754
  simp only [CollatzResearch.WordTrace]
  refine ⟨27006010728019640039335079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72016028608052373438226877 27006010728019640039335079)
  ·
    refine ⟨40509016092029460059002619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27006010728019640039335079 40509016092029460059002619)
    ·
      refine ⟨60763524138044190088503929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40509016092029460059002619 60763524138044190088503929)
      ·
        refine ⟨45572643103533142566377947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60763524138044190088503929 45572643103533142566377947)
        ·
          refine ⟨68358964655299713849566921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45572643103533142566377947 68358964655299713849566921)
          ·
            refine ⟨51269223491474785387175191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68358964655299713849566921 51269223491474785387175191)
            ·
              refine ⟨76903835237212178080762787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51269223491474785387175191 76903835237212178080762787)
              ·
                refine ⟨115355752855818267121144181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76903835237212178080762787 115355752855818267121144181)
                ·
                  refine ⟨10814601830232962542607267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115355752855818267121144181 10814601830232962542607267)
                  ·
                    refine ⟨16221902745349443813910901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10814601830232962542607267 16221902745349443813910901)
                    ·
                      refine ⟨1520803382376510357554147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16221902745349443813910901 1520803382376510357554147)
                      ·
                        rfl

theorem cell23_2961754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_2961754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961754 prefixEnd_2961754 := by exact prefixLift 2961754
  have htrace : WordTrace (prefixWord ++ tailWord_2961754) baseStart_2961754 baseEnd_2961754 := by
    simpa [prefixWord, tailWord_2961754, baseEnd_2961754] using wordTrace_append hprefix tailTrace_2961754
  have hstable : (prefixWord ++ tailWord_2961754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961754).length < 2 ^ (prefixWord ++ tailWord_2961754).sum := by decide
  have hdescent : baseEnd_2961754 < baseStart_2961754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961762 : List Nat := [3, 3, 2, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_2961762 : Nat := 118140960795 + 2961762 * 2 ^ 59
def prefixEnd_2961762 : Nat := 4983230072969 + 3 ^ 40 * 2961762 * 2
def baseEnd_2961762 : Nat := 1520807490221746326254111

theorem tailTrace_2961762 : CollatzResearch.WordTrace tailWord_2961762 prefixEnd_2961762 1520807490221746326254111 := by
  unfold tailWord_2961762
  simp only [CollatzResearch.WordTrace]
  refine ⟨27006083674012394380907885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72016223130699718349087693 27006083674012394380907885)
  ·
    refine ⟨10127281377754647892840457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27006083674012394380907885 10127281377754647892840457)
    ·
      refine ⟨7595461033315985919630343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10127281377754647892840457 7595461033315985919630343)
      ·
        refine ⟨11393191549973978879445515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7595461033315985919630343 11393191549973978879445515)
        ·
          refine ⟨17089787324960968319168273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393191549973978879445515 17089787324960968319168273)
          ·
            refine ⟨12817340493720726239376205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17089787324960968319168273 12817340493720726239376205)
            ·
              refine ⟨4806502685145272339766077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12817340493720726239376205 4806502685145272339766077)
              ·
                refine ⟨1802438506929477127412279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4806502685145272339766077 1802438506929477127412279)
                ·
                  refine ⟨2703657760394215691118419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802438506929477127412279 2703657760394215691118419)
                  ·
                    refine ⟨4055486640591323536677629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2703657760394215691118419 4055486640591323536677629)
                    ·
                      refine ⟨1520807490221746326254111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055486640591323536677629 1520807490221746326254111)
                      ·
                        rfl

theorem cell23_2961762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_2961762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961762 prefixEnd_2961762 := by exact prefixLift 2961762
  have htrace : WordTrace (prefixWord ++ tailWord_2961762) baseStart_2961762 baseEnd_2961762 := by
    simpa [prefixWord, tailWord_2961762, baseEnd_2961762] using wordTrace_append hprefix tailTrace_2961762
  have hstable : (prefixWord ++ tailWord_2961762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961762).length < 2 ^ (prefixWord ++ tailWord_2961762).sum := by decide
  have hdescent : baseEnd_2961762 < baseStart_2961762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961768 : List Nat := [2, 1, 4, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2961768 : Nat := 118140960795 + 2961768 * 2 ^ 59
def prefixEnd_2961768 : Nat := 4983230072969 + 3 ^ 40 * 2961768 * 2
def baseEnd_2961768 : Nat := 1520810571105673302779083

theorem tailTrace_2961768 : CollatzResearch.WordTrace tailWord_2961768 prefixEnd_2961768 1520810571105673302779083 := by
  unfold tailWord_2961768
  simp only [CollatzResearch.WordTrace]
  refine ⟨54012276767013920274174979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72016369022685227032233305 54012276767013920274174979)
  ·
    refine ⟨81018415150520880411262469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54012276767013920274174979 81018415150520880411262469)
    ·
      refine ⟨15190952840722665077111713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81018415150520880411262469 15190952840722665077111713)
      ·
        refine ⟨11393214630541998807833785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15190952840722665077111713 11393214630541998807833785)
        ·
          refine ⟨8544910972906499105875339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11393214630541998807833785 8544910972906499105875339)
          ·
            refine ⟨12817366459359748658813009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544910972906499105875339 12817366459359748658813009)
            ·
              refine ⟨9613024844519811494109757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12817366459359748658813009 9613024844519811494109757)
              ·
                refine ⟨3604884316694929310291159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9613024844519811494109757 3604884316694929310291159)
                ·
                  refine ⟨5407326475042393965436739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604884316694929310291159 5407326475042393965436739)
                  ·
                    refine ⟨8110989712563590948155109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5407326475042393965436739 8110989712563590948155109)
                    ·
                      refine ⟨1520810571105673302779083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8110989712563590948155109 1520810571105673302779083)
                      ·
                        rfl

theorem cell23_2961768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2961768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961768 prefixEnd_2961768 := by exact prefixLift 2961768
  have htrace : WordTrace (prefixWord ++ tailWord_2961768) baseStart_2961768 baseEnd_2961768 := by
    simpa [prefixWord, tailWord_2961768, baseEnd_2961768] using wordTrace_append hprefix tailTrace_2961768
  have hstable : (prefixWord ++ tailWord_2961768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961768).length < 2 ^ (prefixWord ++ tailWord_2961768).sum := by decide
  have hdescent : baseEnd_2961768 < baseStart_2961768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961781 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_2961781 : Nat := 118140960795 + 2961781 * 2 ^ 59
def prefixEnd_2961781 : Nat := 4983230072969 + 3 ^ 40 * 2961781 * 2
def baseEnd_2961781 : Nat := 1520817246354181751916523

theorem tailTrace_2961781 : CollatzResearch.WordTrace tailWord_2961781 prefixEnd_2961781 1520817246354181751916523 := by
  unfold tailWord_2961781
  simp only [CollatzResearch.WordTrace]
  refine ⟨108025027682980743768573197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72016685121987162512382131 108025027682980743768573197)
  ·
    refine ⟨40509385381117778913214949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108025027682980743768573197 40509385381117778913214949)
    ·
      refine ⟨7595509758959583546227803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40509385381117778913214949 7595509758959583546227803)
      ·
        refine ⟨11393264638439375319341705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7595509758959583546227803 11393264638439375319341705)
        ·
          refine ⟨8544948478829531489506279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11393264638439375319341705 8544948478829531489506279)
          ·
            refine ⟨12817422718244297234259419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8544948478829531489506279 12817422718244297234259419)
            ·
              refine ⟨19226134077366445851389129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12817422718244297234259419 19226134077366445851389129)
              ·
                refine ⟨14419600558024834388541847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19226134077366445851389129 14419600558024834388541847)
                ·
                  refine ⟨21629400837037251582812771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14419600558024834388541847 21629400837037251582812771)
                  ·
                    refine ⟨32444101255555877374219157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21629400837037251582812771 32444101255555877374219157)
                    ·
                      refine ⟨1520817246354181751916523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32444101255555877374219157 1520817246354181751916523)
                      ·
                        rfl

theorem cell23_2961781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_2961781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961781 prefixEnd_2961781 := by exact prefixLift 2961781
  have htrace : WordTrace (prefixWord ++ tailWord_2961781) baseStart_2961781 baseEnd_2961781 := by
    simpa [prefixWord, tailWord_2961781, baseEnd_2961781] using wordTrace_append hprefix tailTrace_2961781
  have hstable : (prefixWord ++ tailWord_2961781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961781).length < 2 ^ (prefixWord ++ tailWord_2961781).sum := by decide
  have hdescent : baseEnd_2961781 < baseStart_2961781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961802 : List Nat := [3, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2961802 : Nat := 118140960795 + 2961802 * 2 ^ 59
def prefixEnd_2961802 : Nat := 4983230072969 + 3 ^ 40 * 2961802 * 2
def baseEnd_2961802 : Nat := 1520828029447926169753927

theorem tailTrace_2961802 : CollatzResearch.WordTrace tailWord_2961802 prefixEnd_2961802 1520828029447926169753927 := by
  unfold tailWord_2961802
  simp only [CollatzResearch.WordTrace]
  refine ⟨27006448403976166088771915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72017195743936442903391773 27006448403976166088771915)
  ·
    refine ⟨40509672605964249133157873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27006448403976166088771915 40509672605964249133157873)
    ·
      refine ⟨30382254454473186849868405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40509672605964249133157873 30382254454473186849868405)
      ·
        refine ⟨2848336355106861267175163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30382254454473186849868405 2848336355106861267175163)
        ·
          refine ⟨4272504532660291900762745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2848336355106861267175163 4272504532660291900762745)
          ·
            refine ⟨3204378399495218925572059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4272504532660291900762745 3204378399495218925572059)
            ·
              refine ⟨4806567599242828388358089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204378399495218925572059 4806567599242828388358089)
              ·
                refine ⟨3604925699432121291268567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4806567599242828388358089 3604925699432121291268567)
                ·
                  refine ⟨5407388549148181936902851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3604925699432121291268567 5407388549148181936902851)
                  ·
                    refine ⟨8111082823722272905354277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5407388549148181936902851 8111082823722272905354277)
                    ·
                      refine ⟨1520828029447926169753927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8111082823722272905354277 1520828029447926169753927)
                      ·
                        rfl

theorem cell23_2961802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2961802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961802 prefixEnd_2961802 := by exact prefixLift 2961802
  have htrace : WordTrace (prefixWord ++ tailWord_2961802) baseStart_2961802 baseEnd_2961802 := by
    simpa [prefixWord, tailWord_2961802, baseEnd_2961802] using wordTrace_append hprefix tailTrace_2961802
  have hstable : (prefixWord ++ tailWord_2961802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961802).length < 2 ^ (prefixWord ++ tailWord_2961802).sum := by decide
  have hdescent : baseEnd_2961802 < baseStart_2961802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961818 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3]
def baseStart_2961818 : Nat := 118140960795 + 2961818 * 2 ^ 59
def prefixEnd_2961818 : Nat := 4983230072969 + 3 ^ 40 * 2961818 * 2
def baseEnd_2961818 : Nat := 1520836245138398107153853

theorem tailTrace_2961818 : CollatzResearch.WordTrace tailWord_2961818 prefixEnd_2961818 1520836245138398107153853 := by
  unfold tailWord_2961818
  simp only [CollatzResearch.WordTrace]
  refine ⟨27006594295961674771917527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72017584789231132725113405 27006594295961674771917527)
  ·
    refine ⟨40509891443942512157876291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27006594295961674771917527 40509891443942512157876291)
    ·
      refine ⟨60764837165913768236814437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40509891443942512157876291 60764837165913768236814437)
      ·
        refine ⟨11393406968608831544402707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60764837165913768236814437 11393406968608831544402707)
        ·
          refine ⟨17090110452913247316604061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393406968608831544402707 17090110452913247316604061)
          ·
            refine ⟨6408791419842467743726523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17090110452913247316604061 6408791419842467743726523)
            ·
              refine ⟨9613187129763701615589785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6408791419842467743726523 9613187129763701615589785)
              ·
                refine ⟨7209890347322776211692339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9613187129763701615589785 7209890347322776211692339)
                ·
                  refine ⟨10814835520984164317538509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7209890347322776211692339 10814835520984164317538509)
                  ·
                    refine ⟨4055563320369061619076941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10814835520984164317538509 4055563320369061619076941)
                    ·
                      refine ⟨1520836245138398107153853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055563320369061619076941 1520836245138398107153853)
                      ·
                        rfl

theorem cell23_2961818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_2961818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961818 prefixEnd_2961818 := by exact prefixLift 2961818
  have htrace : WordTrace (prefixWord ++ tailWord_2961818) baseStart_2961818 baseEnd_2961818 := by
    simpa [prefixWord, tailWord_2961818, baseEnd_2961818] using wordTrace_append hprefix tailTrace_2961818
  have hstable : (prefixWord ++ tailWord_2961818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961818).length < 2 ^ (prefixWord ++ tailWord_2961818).sum := by decide
  have hdescent : baseEnd_2961818 < baseStart_2961818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961841 : List Nat := [1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_2961841 : Nat := 118140960795 + 2961841 * 2 ^ 59
def prefixEnd_2961841 : Nat := 4983230072969 + 3 ^ 40 * 2961841 * 2
def baseEnd_2961841 : Nat := 1520848055193451517166247

theorem tailTrace_2961841 : CollatzResearch.WordTrace tailWord_2961841 prefixEnd_2961841 1520848055193451517166247 := by
  unfold tailWord_2961841
  simp only [CollatzResearch.WordTrace]
  refine ⟨108027216062763374015757377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72018144041842249343838251 108027216062763374015757377)
  ·
    refine ⟨81020412047072530511818033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108027216062763374015757377 81020412047072530511818033)
    ·
      refine ⟨60765309035304397883863525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81020412047072530511818033 60765309035304397883863525)
      ·
        refine ⟨11393495444119574603224411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60765309035304397883863525 11393495444119574603224411)
        ·
          refine ⟨17090243166179361904836617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393495444119574603224411 17090243166179361904836617)
          ·
            refine ⟨12817682374634521428627463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17090243166179361904836617 12817682374634521428627463)
            ·
              refine ⟨19226523561951782142941195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12817682374634521428627463 19226523561951782142941195)
              ·
                refine ⟨28839785342927673214411793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19226523561951782142941195 28839785342927673214411793)
                ·
                  refine ⟨21629839007195754910808845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28839785342927673214411793 21629839007195754910808845)
                  ·
                    refine ⟨8111189627698408091553317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21629839007195754910808845 8111189627698408091553317)
                    ·
                      refine ⟨1520848055193451517166247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8111189627698408091553317 1520848055193451517166247)
                      ·
                        rfl

theorem cell23_2961841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_2961841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961841 prefixEnd_2961841 := by exact prefixLift 2961841
  have htrace : WordTrace (prefixWord ++ tailWord_2961841) baseStart_2961841 baseEnd_2961841 := by
    simpa [prefixWord, tailWord_2961841, baseEnd_2961841] using wordTrace_append hprefix tailTrace_2961841
  have hstable : (prefixWord ++ tailWord_2961841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961841).length < 2 ^ (prefixWord ++ tailWord_2961841).sum := by decide
  have hdescent : baseEnd_2961841 < baseStart_2961841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961878 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2961878 : Nat := 118140960795 + 2961878 * 2 ^ 59
def prefixEnd_2961878 : Nat := 4983230072969 + 3 ^ 40 * 2961878 * 2
def baseEnd_2961878 : Nat := 1520867053977667872403577

theorem tailTrace_2961878 : CollatzResearch.WordTrace tailWord_2961878 prefixEnd_2961878 1520867053977667872403577 := by
  unfold tailWord_2961878
  simp only [CollatzResearch.WordTrace]
  refine ⟨6751785347726833083428393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72019043709086219556569525 6751785347726833083428393)
  ·
    refine ⟨5063839010795124812571295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6751785347726833083428393 5063839010795124812571295)
    ·
      refine ⟨7595758516192687218856943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5063839010795124812571295 7595758516192687218856943)
      ·
        refine ⟨11393637774289030828285415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7595758516192687218856943 11393637774289030828285415)
        ·
          refine ⟨17090456661433546242428123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11393637774289030828285415 17090456661433546242428123)
          ·
            refine ⟨25635684992150319363642185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17090456661433546242428123 25635684992150319363642185)
            ·
              refine ⟨19226763744112739522731639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25635684992150319363642185 19226763744112739522731639)
              ·
                refine ⟨28840145616169109284097459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19226763744112739522731639 28840145616169109284097459)
                ·
                  refine ⟨43260218424253663926146189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28840145616169109284097459 43260218424253663926146189)
                  ·
                    refine ⟨16222581909095123972304821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43260218424253663926146189 16222581909095123972304821)
                    ·
                      refine ⟨1520867053977667872403577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16222581909095123972304821 1520867053977667872403577)
                      ·
                        rfl

theorem cell23_2961878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2961878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961878 prefixEnd_2961878 := by exact prefixLift 2961878
  have htrace : WordTrace (prefixWord ++ tailWord_2961878) baseStart_2961878 baseEnd_2961878 := by
    simpa [prefixWord, tailWord_2961878, baseEnd_2961878] using wordTrace_append hprefix tailTrace_2961878
  have hstable : (prefixWord ++ tailWord_2961878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961878).length < 2 ^ (prefixWord ++ tailWord_2961878).sum := by decide
  have hdescent : baseEnd_2961878 < baseStart_2961878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961898 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 7]
def baseStart_2961898 : Nat := 118140960795 + 2961898 * 2 ^ 59
def prefixEnd_2961898 : Nat := 4983230072969 + 3 ^ 40 * 2961898 * 2
def baseEnd_2961898 : Nat := 168986369287861977128165

theorem tailTrace_2961898 : CollatzResearch.WordTrace tailWord_2961898 prefixEnd_2961898 168986369287861977128165 := by
  unfold tailWord_2961898
  simp only [CollatzResearch.WordTrace]
  refine ⟨27007323755889218187645587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72019530015704581833721565 27007323755889218187645587)
  ·
    refine ⟨40510985633833827281468381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27007323755889218187645587 40510985633833827281468381)
    ·
      refine ⟨15191619612687685230550643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40510985633833827281468381 15191619612687685230550643)
      ·
        refine ⟨22787429419031527845825965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15191619612687685230550643 22787429419031527845825965)
        ·
          refine ⟨8545286032136822942184737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22787429419031527845825965 8545286032136822942184737)
          ·
            refine ⟨6408964524102617206638553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8545286032136822942184737 6408964524102617206638553)
            ·
              refine ⟨4806723393076962904978915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6408964524102617206638553 4806723393076962904978915)
              ·
                refine ⟨7210085089615444357468373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806723393076962904978915 7210085089615444357468373)
                ·
                  refine ⟨168986369287861977128165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7210085089615444357468373 168986369287861977128165)
                  ·
                    rfl

theorem cell23_2961898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_2961898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961898 prefixEnd_2961898 := by exact prefixLift 2961898
  have htrace : WordTrace (prefixWord ++ tailWord_2961898) baseStart_2961898 baseEnd_2961898 := by
    simpa [prefixWord, tailWord_2961898, baseEnd_2961898] using wordTrace_append hprefix tailTrace_2961898
  have hstable : (prefixWord ++ tailWord_2961898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961898).length < 2 ^ (prefixWord ++ tailWord_2961898).sum := by decide
  have hdescent : baseEnd_2961898 < baseStart_2961898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961909 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_2961909 : Nat := 118140960795 + 2961909 * 2 ^ 59
def prefixEnd_2961909 : Nat := 4983230072969 + 3 ^ 40 * 2961909 * 2
def baseEnd_2961909 : Nat := 1520882971877957251115935

theorem tailTrace_2961909 : CollatzResearch.WordTrace tailWord_2961909 prefixEnd_2961909 1520882971877957251115935 := by
  unfold tailWord_2961909
  simp only [CollatzResearch.WordTrace]
  refine ⟨108029696226517021629232781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72019797484344681086155187 108029696226517021629232781)
  ·
    refine ⟨40511136084943883110962293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108029696226517021629232781 40511136084943883110962293)
    ·
      refine ⟨3797919007963489041652715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40511136084943883110962293 3797919007963489041652715)
      ·
        refine ⟨5696878511945233562479073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3797919007963489041652715 5696878511945233562479073)
        ·
          refine ⟨4272658883958925171859305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5696878511945233562479073 4272658883958925171859305)
          ·
            refine ⟨3204494162969193878894479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4272658883958925171859305 3204494162969193878894479)
            ·
              refine ⟨4806741244453790818341719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204494162969193878894479 4806741244453790818341719)
              ·
                refine ⟨7210111866680686227512579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4806741244453790818341719 7210111866680686227512579)
                ·
                  refine ⟨10815167800021029341268869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7210111866680686227512579 10815167800021029341268869)
                  ·
                    refine ⟨2027843962503943001487913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10815167800021029341268869 2027843962503943001487913)
                    ·
                      refine ⟨1520882971877957251115935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027843962503943001487913 1520882971877957251115935)
                      ·
                        rfl

theorem cell23_2961909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_2961909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961909 prefixEnd_2961909 := by exact prefixLift 2961909
  have htrace : WordTrace (prefixWord ++ tailWord_2961909) baseStart_2961909 baseEnd_2961909 := by
    simpa [prefixWord, tailWord_2961909, baseEnd_2961909] using wordTrace_append hprefix tailTrace_2961909
  have hstable : (prefixWord ++ tailWord_2961909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961909).length < 2 ^ (prefixWord ++ tailWord_2961909).sum := by decide
  have hdescent : baseEnd_2961909 < baseStart_2961909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961926 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2961926 : Nat := 118140960795 + 2961926 * 2 ^ 59
def prefixEnd_2961926 : Nat := 4983230072969 + 3 ^ 40 * 2961926 * 2
def baseEnd_2961926 : Nat := 1520891701049083684603357

theorem tailTrace_2961926 : CollatzResearch.WordTrace tailWord_2961926 prefixEnd_2961926 1520891701049083684603357 := by
  unfold tailWord_2961926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375947383357982297893801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72020210844970289021734421 3375947383357982297893801)
  ·
    refine ⟨2531960537518486723420351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3375947383357982297893801 2531960537518486723420351)
    ·
      refine ⟨3797940806277730085130527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2531960537518486723420351 3797940806277730085130527)
      ·
        refine ⟨5696911209416595127695791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3797940806277730085130527 5696911209416595127695791)
        ·
          refine ⟨8545366814124892691543687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5696911209416595127695791 8545366814124892691543687)
          ·
            refine ⟨12818050221187339037315531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8545366814124892691543687 12818050221187339037315531)
            ·
              refine ⟨19227075331781008555973297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12818050221187339037315531 19227075331781008555973297)
              ·
                refine ⟨14420306498835756416979973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19227075331781008555973297 14420306498835756416979973)
                ·
                  refine ⟨2703807468531704328183745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14420306498835756416979973 2703807468531704328183745)
                  ·
                    refine ⟨2027855601398778246137809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2703807468531704328183745 2027855601398778246137809)
                    ·
                      refine ⟨1520891701049083684603357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2027855601398778246137809 1520891701049083684603357)
                      ·
                        rfl

theorem cell23_2961926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2961926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961926 prefixEnd_2961926 := by exact prefixLift 2961926
  have htrace : WordTrace (prefixWord ++ tailWord_2961926) baseStart_2961926 baseEnd_2961926 := by
    simpa [prefixWord, tailWord_2961926, baseEnd_2961926] using wordTrace_append hprefix tailTrace_2961926
  have hstable : (prefixWord ++ tailWord_2961926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961926).length < 2 ^ (prefixWord ++ tailWord_2961926).sum := by decide
  have hdescent : baseEnd_2961926 < baseStart_2961926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961948 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2961948 : Nat := 118140960795 + 2961948 * 2 ^ 59
def prefixEnd_2961948 : Nat := 4983230072969 + 3 ^ 40 * 2961948 * 2
def baseEnd_2961948 : Nat := 1520902997623482598528255

theorem tailTrace_2961948 : CollatzResearch.WordTrace tailWord_2961948 prefixEnd_2961948 1520902997623482598528255 := by
  unfold tailWord_2961948
  simp only [CollatzResearch.WordTrace]
  refine ⟨54015559336687865644951249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72020745782250487526601665 54015559336687865644951249)
  ·
    refine ⟨40511669502515899233713437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54015559336687865644951249 40511669502515899233713437)
    ·
      refine ⟨15191876063443462212642539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40511669502515899233713437 15191876063443462212642539)
      ·
        refine ⟨22787814095165193318963809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15191876063443462212642539 22787814095165193318963809)
        ·
          refine ⟨17090860571373894989222857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22787814095165193318963809 17090860571373894989222857)
          ·
            refine ⟨12818145428530421241917143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17090860571373894989222857 12818145428530421241917143)
            ·
              refine ⟨19227218142795631862875715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12818145428530421241917143 19227218142795631862875715)
              ·
                refine ⟨28840827214193447794313573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19227218142795631862875715 28840827214193447794313573)
                ·
                  refine ⟨5407655102661271461433795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28840827214193447794313573 5407655102661271461433795)
                  ·
                    refine ⟨8111482653991907192150693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5407655102661271461433795 8111482653991907192150693)
                    ·
                      refine ⟨1520902997623482598528255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8111482653991907192150693 1520902997623482598528255)
                      ·
                        rfl

theorem cell23_2961948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2961948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961948 prefixEnd_2961948 := by exact prefixLift 2961948
  have htrace : WordTrace (prefixWord ++ tailWord_2961948) baseStart_2961948 baseEnd_2961948 := by
    simpa [prefixWord, tailWord_2961948, baseEnd_2961948] using wordTrace_append hprefix tailTrace_2961948
  have hstable : (prefixWord ++ tailWord_2961948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961948).length < 2 ^ (prefixWord ++ tailWord_2961948).sum := by decide
  have hdescent : baseEnd_2961948 < baseStart_2961948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2961985 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_2961985 : Nat := 118140960795 + 2961985 * 2 ^ 59
def prefixEnd_2961985 : Nat := 4983230072969 + 3 ^ 40 * 2961985 * 2
def baseEnd_2961985 : Nat := 1520921996407698953765585

theorem tailTrace_2961985 : CollatzResearch.WordTrace tailWord_2961985 prefixEnd_2961985 1520921996407698953765585 := by
  unfold tailWord_2961985
  simp only [CollatzResearch.WordTrace]
  refine ⟨108032468174241686608999409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72021645449494457739332939 108032468174241686608999409)
  ·
    refine ⟨81024351130681264956749557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108032468174241686608999409 81024351130681264956749557)
    ·
      refine ⟨7596032918501368589695271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81024351130681264956749557 7596032918501368589695271)
      ·
        refine ⟨11394049377752052884542907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7596032918501368589695271 11394049377752052884542907)
        ·
          refine ⟨17091074066628079326814361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11394049377752052884542907 17091074066628079326814361)
          ·
            refine ⟨12818305549971059495110771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17091074066628079326814361 12818305549971059495110771)
            ·
              refine ⟨19227458324956589242666157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12818305549971059495110771 19227458324956589242666157)
              ·
                refine ⟨7210296871858720965999809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19227458324956589242666157 7210296871858720965999809)
                ·
                  refine ⟨5407722653894040724499857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7210296871858720965999809 5407722653894040724499857)
                  ·
                    refine ⟨4055791990420530543374893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5407722653894040724499857 4055791990420530543374893)
                    ·
                      refine ⟨1520921996407698953765585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055791990420530543374893 1520921996407698953765585)
                      ·
                        rfl

theorem cell23_2961985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_2961985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2961985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2961985 prefixEnd_2961985 := by exact prefixLift 2961985
  have htrace : WordTrace (prefixWord ++ tailWord_2961985) baseStart_2961985 baseEnd_2961985 := by
    simpa [prefixWord, tailWord_2961985, baseEnd_2961985] using wordTrace_append hprefix tailTrace_2961985
  have hstable : (prefixWord ++ tailWord_2961985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2961985).length < 2 ^ (prefixWord ++ tailWord_2961985).sum := by decide
  have hdescent : baseEnd_2961985 < baseStart_2961985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2961985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962032 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 3, 1, 3]
def baseStart_2962032 : Nat := 118140960795 + 2962032 * 2 ^ 59
def prefixEnd_2962032 : Nat := 4983230072969 + 3 ^ 40 * 2962032 * 2
def baseEnd_2962032 : Nat := 1520946129998460269877869

theorem tailTrace_2962032 : CollatzResearch.WordTrace tailWord_2962032 prefixEnd_2962032 1520946129998460269877869 := by
  unfold tailWord_2962032
  simp only [CollatzResearch.WordTrace]
  refine ⟨54017091202535706817980175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72022788270047609090640233 54017091202535706817980175)
  ·
    refine ⟨81025636803803560226970263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54017091202535706817980175 81025636803803560226970263)
    ·
      refine ⟨121538455205705340340455395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81025636803803560226970263 121538455205705340340455395)
      ·
        refine ⟨182307682808558010510683093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121538455205705340340455395 182307682808558010510683093)
        ·
          refine ⟨4272836315825578371344135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 182307682808558010510683093 4272836315825578371344135)
          ·
            refine ⟨6409254473738367557016203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4272836315825578371344135 6409254473738367557016203)
            ·
              refine ⟨9613881710607551335524305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6409254473738367557016203 9613881710607551335524305)
              ·
                refine ⟨7210411282955663501643229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9613881710607551335524305 7210411282955663501643229)
                ·
                  refine ⟨2703904231108373813116211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7210411282955663501643229 2703904231108373813116211)
                  ·
                    refine ⟨4055856346662560719674317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2703904231108373813116211 4055856346662560719674317)
                    ·
                      refine ⟨1520946129998460269877869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055856346662560719674317 1520946129998460269877869)
                      ·
                        rfl

theorem cell23_2962032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3, 1, 3].length) (baseStart_2962032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962032 prefixEnd_2962032 := by exact prefixLift 2962032
  have htrace : WordTrace (prefixWord ++ tailWord_2962032) baseStart_2962032 baseEnd_2962032 := by
    simpa [prefixWord, tailWord_2962032, baseEnd_2962032] using wordTrace_append hprefix tailTrace_2962032
  have hstable : (prefixWord ++ tailWord_2962032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962032).length < 2 ^ (prefixWord ++ tailWord_2962032).sum := by decide
  have hdescent : baseEnd_2962032 < baseStart_2962032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962048 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 1, 6]
def baseStart_2962048 : Nat := 118140960795 + 2962048 * 2 ^ 59
def prefixEnd_2962048 : Nat := 4983230072969 + 3 ^ 40 * 2962048 * 2
def baseEnd_2962048 : Nat := 506984781896310735759265

theorem tailTrace_2962048 : CollatzResearch.WordTrace tailWord_2962048 prefixEnd_2962048 506984781896310735759265 := by
  unfold tailWord_2962048
  simp only [CollatzResearch.WordTrace]
  refine ⟨54017382986506724184271399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72023177315342298912361865 54017382986506724184271399)
  ·
    refine ⟨81026074479760086276407099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54017382986506724184271399 81026074479760086276407099)
    ·
      refine ⟨121539111719640129414610649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81026074479760086276407099 121539111719640129414610649)
      ·
        refine ⟨91154333789730097060957987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121539111719640129414610649 91154333789730097060957987)
        ·
          refine ⟨136731500684595145591436981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91154333789730097060957987 136731500684595145591436981)
          ·
            refine ⟨12818578189180794899197217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 136731500684595145591436981 12818578189180794899197217)
            ·
              refine ⟨9613933641885596174397913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12818578189180794899197217 9613933641885596174397913)
              ·
                refine ⟨7210450231414197130798435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9613933641885596174397913 7210450231414197130798435)
                ·
                  refine ⟨10815675347121295696197653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7210450231414197130798435 10815675347121295696197653)
                  ·
                    refine ⟨506984781896310735759265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10815675347121295696197653 506984781896310735759265)
                    ·
                      rfl

theorem cell23_2962048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 1, 6].length) (baseStart_2962048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962048 prefixEnd_2962048 := by exact prefixLift 2962048
  have htrace : WordTrace (prefixWord ++ tailWord_2962048) baseStart_2962048 baseEnd_2962048 := by
    simpa [prefixWord, tailWord_2962048, baseEnd_2962048] using wordTrace_append hprefix tailTrace_2962048
  have hstable : (prefixWord ++ tailWord_2962048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962048).length < 2 ^ (prefixWord ++ tailWord_2962048).sum := by decide
  have hdescent : baseEnd_2962048 < baseStart_2962048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962049 : List Nat := [1, 2, 4, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_2962049 : Nat := 118140960795 + 2962049 * 2 ^ 59
def prefixEnd_2962049 : Nat := 4983230072969 + 3 ^ 40 * 2962049 * 2
def baseEnd_2962049 : Nat := 1520954859169586703365291

theorem tailTrace_2962049 : CollatzResearch.WordTrace tailWord_2962049 prefixEnd_2962049 1520954859169586703365291 := by
  unfold tailWord_2962049
  simp only [CollatzResearch.WordTrace]
  refine ⟨108034802446009825539329201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72023201630673217026219467 108034802446009825539329201)
  ·
    refine ⟨81026101834507369154496901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108034802446009825539329201 81026101834507369154496901)
    ·
      refine ⟨15192394093970131716468169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81026101834507369154496901 15192394093970131716468169)
      ·
        refine ⟨11394295570477598787351127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15192394093970131716468169 11394295570477598787351127)
        ·
          refine ⟨17091443355716398181026691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11394295570477598787351127 17091443355716398181026691)
          ·
            refine ⟨25637165033574597271540037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17091443355716398181026691 25637165033574597271540037)
            ·
              refine ⟨4806968443795236988413757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25637165033574597271540037 4806968443795236988413757)
              ·
                refine ⟨1802613166423213870655159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4806968443795236988413757 1802613166423213870655159)
                ·
                  refine ⟨2703919749634820805982739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802613166423213870655159 2703919749634820805982739)
                  ·
                    refine ⟨4055879624452231208974109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2703919749634820805982739 4055879624452231208974109)
                    ·
                      refine ⟨1520954859169586703365291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055879624452231208974109 1520954859169586703365291)
                      ·
                        rfl

theorem cell23_2962049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_2962049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962049 prefixEnd_2962049 := by exact prefixLift 2962049
  have htrace : WordTrace (prefixWord ++ tailWord_2962049) baseStart_2962049 baseEnd_2962049 := by
    simpa [prefixWord, tailWord_2962049, baseEnd_2962049] using wordTrace_append hprefix tailTrace_2962049
  have hstable : (prefixWord ++ tailWord_2962049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962049).length < 2 ^ (prefixWord ++ tailWord_2962049).sum := by decide
  have hdescent : baseEnd_2962049 < baseStart_2962049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962052 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 1, 5]
def baseStart_2962052 : Nat := 118140960795 + 2962052 * 2 ^ 59
def prefixEnd_2962052 : Nat := 4983230072969 + 3 ^ 40 * 2962052 * 2
def baseEnd_2962052 : Nat := 506985466537183397209259

theorem tailTrace_2962052 : CollatzResearch.WordTrace tailWord_2962052 prefixEnd_2962052 506985466537183397209259 := by
  unfold tailWord_2962052
  simp only [CollatzResearch.WordTrace]
  refine ⟨54017455932499478525844205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72023274576665971367792273 54017455932499478525844205)
  ·
    refine ⟨20256545974687304447191577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54017455932499478525844205 20256545974687304447191577)
    ·
      refine ⟨15192409481015478335393683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20256545974687304447191577 15192409481015478335393683)
      ·
        refine ⟨22788614221523217503090525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15192409481015478335393683 22788614221523217503090525)
        ·
          refine ⟨8545730333071206563658947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22788614221523217503090525 8545730333071206563658947)
          ·
            refine ⟨12818595499606809845488421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8545730333071206563658947 12818595499606809845488421)
            ·
              refine ⟨2403486656176276846029079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12818595499606809845488421 2403486656176276846029079)
              ·
                refine ⟨3605229984264415269043619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403486656176276846029079 3605229984264415269043619)
                ·
                  refine ⟨5407844976396622903565429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605229984264415269043619 5407844976396622903565429)
                  ·
                    refine ⟨506985466537183397209259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5407844976396622903565429 506985466537183397209259)
                    ·
                      rfl

theorem cell23_2962052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_2962052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962052 prefixEnd_2962052 := by exact prefixLift 2962052
  have htrace : WordTrace (prefixWord ++ tailWord_2962052) baseStart_2962052 baseEnd_2962052 := by
    simpa [prefixWord, tailWord_2962052, baseEnd_2962052] using wordTrace_append hprefix tailTrace_2962052
  have hstable : (prefixWord ++ tailWord_2962052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962052).length < 2 ^ (prefixWord ++ tailWord_2962052).sum := by decide
  have hdescent : baseEnd_2962052 < baseStart_2962052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962055 : List Nat := [1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_2962055 : Nat := 118140960795 + 2962055 * 2 ^ 59
def prefixEnd_2962055 : Nat := 4983230072969 + 3 ^ 40 * 2962055 * 2
def baseEnd_2962055 : Nat := 1520957940053513679890263

theorem tailTrace_2962055 : CollatzResearch.WordTrace tailWord_2962055 prefixEnd_2962055 1520957940053513679890263 := by
  unfold tailWord_2962055
  simp only [CollatzResearch.WordTrace]
  refine ⟨108035021283988088564047619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72023347522658725709365079 108035021283988088564047619)
  ·
    refine ⟨162052531925982132846071429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108035021283988088564047619 162052531925982132846071429)
    ·
      refine ⟨30384849736121649908638393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162052531925982132846071429 30384849736121649908638393)
      ·
        refine ⟨22788637302091237431478795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30384849736121649908638393 22788637302091237431478795)
        ·
          refine ⟨34182955953136856147218193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22788637302091237431478795 34182955953136856147218193)
          ·
            refine ⟨25637216964852642110413645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34182955953136856147218193 25637216964852642110413645)
            ·
              refine ⟨9613956361819740791405117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25637216964852642110413645 9613956361819740791405117)
              ·
                refine ⟨3605233635682402796776919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9613956361819740791405117 3605233635682402796776919)
                ·
                  refine ⟨5407850453523604195165379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605233635682402796776919 5407850453523604195165379)
                  ·
                    refine ⟨8111775680285406292748069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5407850453523604195165379 8111775680285406292748069)
                    ·
                      refine ⟨1520957940053513679890263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8111775680285406292748069 1520957940053513679890263)
                      ·
                        rfl

theorem cell23_2962055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_2962055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962055 prefixEnd_2962055 := by exact prefixLift 2962055
  have htrace : WordTrace (prefixWord ++ tailWord_2962055) baseStart_2962055 baseEnd_2962055 := by
    simpa [prefixWord, tailWord_2962055, baseEnd_2962055] using wordTrace_append hprefix tailTrace_2962055
  have hstable : (prefixWord ++ tailWord_2962055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962055).length < 2 ^ (prefixWord ++ tailWord_2962055).sum := by decide
  have hdescent : baseEnd_2962055 < baseStart_2962055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962095 : List Nat := [1, 1, 2, 1, 2, 7, 2, 7]
def baseStart_2962095 : Nat := 118140960795 + 2962095 * 2 ^ 59
def prefixEnd_2962095 : Nat := 4983230072969 + 3 ^ 40 * 2962095 * 2
def baseEnd_2962095 : Nat := 56332536269618278644077

theorem tailTrace_2962095 : CollatzResearch.WordTrace tailWord_2962095 prefixEnd_2962095 56332536269618278644077 := by
  unfold tailWord_2962095
  simp only [CollatzResearch.WordTrace]
  refine ⟨108036480203843175395503739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72024320135895450263669159 108036480203843175395503739)
  ·
    refine ⟨162054720305764763093255609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108036480203843175395503739 162054720305764763093255609)
    ·
      refine ⟨121541040229323572319941707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162054720305764763093255609 121541040229323572319941707)
      ·
        refine ⟨182311560343985358479912561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121541040229323572319941707 182311560343985358479912561)
        ·
          refine ⟨136733670257989018859934421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182311560343985358479912561 136733670257989018859934421)
          ·
            refine ⟨3204695396671617629529713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 136733670257989018859934421 3204695396671617629529713)
            ·
              refine ⟨2403521547503713222147285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3204695396671617629529713 2403521547503713222147285)
              ·
                refine ⟨56332536269618278644077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2403521547503713222147285 56332536269618278644077)
                ·
                  rfl

theorem cell23_2962095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 7].length) (baseStart_2962095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962095 prefixEnd_2962095 := by exact prefixLift 2962095
  have htrace : WordTrace (prefixWord ++ tailWord_2962095) baseStart_2962095 baseEnd_2962095 := by
    simpa [prefixWord, tailWord_2962095, baseEnd_2962095] using wordTrace_append hprefix tailTrace_2962095
  have hstable : (prefixWord ++ tailWord_2962095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962095).length < 2 ^ (prefixWord ++ tailWord_2962095).sum := by decide
  have hdescent : baseEnd_2962095 < baseStart_2962095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962122 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_2962122 : Nat := 118140960795 + 2962122 * 2 ^ 59
def prefixEnd_2962122 : Nat := 4983230072969 + 3 ^ 40 * 2962122 * 2
def baseEnd_2962122 : Nat := 1520992343257364917752455

theorem tailTrace_2962122 : CollatzResearch.WordTrace tailWord_2962122 prefixEnd_2962122 1520992343257364917752455 := by
  unfold tailWord_2962122
  simp only [CollatzResearch.WordTrace]
  refine ⟨27009366243686339751684155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72024976649830239337824413 27009366243686339751684155)
  ·
    refine ⟨40514049365529509627526233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27009366243686339751684155 40514049365529509627526233)
    ·
      refine ⟨30385537024147132220644675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40514049365529509627526233 30385537024147132220644675)
      ·
        refine ⟨45578305536220698330967013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30385537024147132220644675 45578305536220698330967013)
        ·
          refine ⟨8545932288041380937056315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45578305536220698330967013 8545932288041380937056315)
          ·
            refine ⟨12818898432062071405584473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8545932288041380937056315 12818898432062071405584473)
            ·
              refine ⟨9614173824046553554188355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12818898432062071405584473 9614173824046553554188355)
              ·
                refine ⟨14421260736069830331282533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9614173824046553554188355 14421260736069830331282533)
                ·
                  refine ⟨2703986388013093187115475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14421260736069830331282533 2703986388013093187115475)
                  ·
                    refine ⟨4055979582019639780673213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2703986388013093187115475 4055979582019639780673213)
                    ·
                      refine ⟨1520992343257364917752455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4055979582019639780673213 1520992343257364917752455)
                      ·
                        rfl

theorem cell23_2962122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_2962122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962122 prefixEnd_2962122 := by exact prefixLift 2962122
  have htrace : WordTrace (prefixWord ++ tailWord_2962122) baseStart_2962122 baseEnd_2962122 := by
    simpa [prefixWord, tailWord_2962122, baseEnd_2962122] using wordTrace_append hprefix tailTrace_2962122
  have hstable : (prefixWord ++ tailWord_2962122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962122).length < 2 ^ (prefixWord ++ tailWord_2962122).sum := by decide
  have hdescent : baseEnd_2962122 < baseStart_2962122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962133 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 2, 4]
def baseStart_2962133 : Nat := 118140960795 + 2962133 * 2 ^ 59
def prefixEnd_2962133 : Nat := 4983230072969 + 3 ^ 40 * 2962133 * 2
def baseEnd_2962133 : Nat := 506999330514854791571635

theorem tailTrace_2962133 : CollatzResearch.WordTrace tailWord_2962133 prefixEnd_2962133 506999330514854791571635 := by
  unfold tailWord_2962133
  simp only [CollatzResearch.WordTrace]
  refine ⟨108037866177705507885387053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72025244118470338590258035 108037866177705507885387053)
  ·
    refine ⟨40514199816639565457020145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108037866177705507885387053 40514199816639565457020145)
    ·
      refine ⟨30385649862479674092765109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40514199816639565457020145 30385649862479674092765109)
      ·
        refine ⟨2848654674607469446196729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30385649862479674092765109 2848654674607469446196729)
        ·
          refine ⟨2136491005955602084647547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848654674607469446196729 2136491005955602084647547)
          ·
            refine ⟨3204736508933403126971321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136491005955602084647547 3204736508933403126971321)
            ·
              refine ⟨2403552381700052345228491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3204736508933403126971321 2403552381700052345228491)
              ·
                refine ⟨3605328572550078517842737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403552381700052345228491 3605328572550078517842737)
                ·
                  refine ⟨2703996429412558888382053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3605328572550078517842737 2703996429412558888382053)
                  ·
                    refine ⟨506999330514854791571635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2703996429412558888382053 506999330514854791571635)
                    ·
                      rfl

theorem cell23_2962133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_2962133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962133 prefixEnd_2962133 := by exact prefixLift 2962133
  have htrace : WordTrace (prefixWord ++ tailWord_2962133) baseStart_2962133 baseEnd_2962133 := by
    simpa [prefixWord, tailWord_2962133, baseEnd_2962133] using wordTrace_append hprefix tailTrace_2962133
  have hstable : (prefixWord ++ tailWord_2962133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962133).length < 2 ^ (prefixWord ++ tailWord_2962133).sum := by decide
  have hdescent : baseEnd_2962133 < baseStart_2962133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962138 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_2962138 : Nat := 118140960795 + 2962138 * 2 ^ 59
def prefixEnd_2962138 : Nat := 4983230072969 + 3 ^ 40 * 2962138 * 2
def baseEnd_2962138 : Nat := 507000186315945618384127

theorem tailTrace_2962138 : CollatzResearch.WordTrace tailWord_2962138 prefixEnd_2962138 507000186315945618384127 := by
  unfold tailWord_2962138
  simp only [CollatzResearch.WordTrace]
  refine ⟨27009512135671848434829767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72025365695124929159546045 27009512135671848434829767)
  ·
    refine ⟨40514268203507772652244651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27009512135671848434829767 40514268203507772652244651)
    ·
      refine ⟨60771402305261658978366977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40514268203507772652244651 60771402305261658978366977)
      ·
        refine ⟨45578551728946244233775233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60771402305261658978366977 45578551728946244233775233)
        ·
          refine ⟨34183913796709683175331425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45578551728946244233775233 34183913796709683175331425)
          ·
            refine ⟨25637935347532262381498569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34183913796709683175331425 25637935347532262381498569)
            ·
              refine ⟨19228451510649196786123927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25637935347532262381498569 19228451510649196786123927)
              ·
                refine ⟨28842677265973795179185891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19228451510649196786123927 28842677265973795179185891)
                ·
                  refine ⟨43264015898960692768778837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28842677265973795179185891 43264015898960692768778837)
                  ·
                    refine ⟨507000186315945618384127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43264015898960692768778837 507000186315945618384127)
                    ·
                      rfl

theorem cell23_2962138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_2962138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962138 prefixEnd_2962138 := by exact prefixLift 2962138
  have htrace : WordTrace (prefixWord ++ tailWord_2962138) baseStart_2962138 baseEnd_2962138 := by
    simpa [prefixWord, tailWord_2962138, baseEnd_2962138] using wordTrace_append hprefix tailTrace_2962138
  have hstable : (prefixWord ++ tailWord_2962138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962138).length < 2 ^ (prefixWord ++ tailWord_2962138).sum := by decide
  have hdescent : baseEnd_2962138 < baseStart_2962138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962149 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 1, 3, 2]
def baseStart_2962149 : Nat := 118140960795 + 2962149 * 2 ^ 59
def prefixEnd_2962149 : Nat := 4983230072969 + 3 ^ 40 * 2962149 * 2
def baseEnd_2962149 : Nat := 1521006207235036312114831

theorem tailTrace_2962149 : CollatzResearch.WordTrace tailWord_2962149 prefixEnd_2962149 1521006207235036312114831 := by
  unfold tailWord_2962149
  simp only [CollatzResearch.WordTrace]
  refine ⟨108038449745647542617969501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72025633163765028411979667 108038449745647542617969501)
  ·
    refine ⟨40514418654617828481738563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108038449745647542617969501 40514418654617828481738563)
    ·
      refine ⟨60771627981926742722607845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40514418654617828481738563 60771627981926742722607845)
      ·
        refine ⟨11394680246611264260488971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60771627981926742722607845 11394680246611264260488971)
        ·
          refine ⟨17092020369916896390733457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11394680246611264260488971 17092020369916896390733457)
          ·
            refine ⟨12819015277437672293050093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17092020369916896390733457 12819015277437672293050093)
            ·
              refine ⟨4807130729039127109893785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12819015277437672293050093 4807130729039127109893785)
              ·
                refine ⟨3605348046779345332420339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807130729039127109893785 3605348046779345332420339)
                ·
                  refine ⟨5408022070169017998630509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605348046779345332420339 5408022070169017998630509)
                  ·
                    refine ⟨2028008276313381749486441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5408022070169017998630509 2028008276313381749486441)
                    ·
                      refine ⟨1521006207235036312114831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028008276313381749486441 1521006207235036312114831)
                      ·
                        rfl

theorem cell23_2962149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_2962149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962149 prefixEnd_2962149 := by exact prefixLift 2962149
  have htrace : WordTrace (prefixWord ++ tailWord_2962149) baseStart_2962149 baseEnd_2962149 := by
    simpa [prefixWord, tailWord_2962149, baseEnd_2962149] using wordTrace_append hprefix tailTrace_2962149
  have hstable : (prefixWord ++ tailWord_2962149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962149).length < 2 ^ (prefixWord ++ tailWord_2962149).sum := by decide
  have hdescent : baseEnd_2962149 < baseStart_2962149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962162 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 3, 4, 2]
def baseStart_2962162 : Nat := 118140960795 + 2962162 * 2 ^ 59
def prefixEnd_2962162 : Nat := 4983230072969 + 3 ^ 40 * 2962162 * 2
def baseEnd_2962162 : Nat := 1521012882483544761252271

theorem tailTrace_2962162 : CollatzResearch.WordTrace tailWord_2962162 prefixEnd_2962162 1521012882483544761252271 := by
  unfold tailWord_2962162
  simp only [CollatzResearch.WordTrace]
  refine ⟨27009730973650111459548185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72025949263066963892128493 27009730973650111459548185)
  ·
    refine ⟨20257298230237583594661139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27009730973650111459548185 20257298230237583594661139)
    ·
      refine ⟨30385947345356375391991709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20257298230237583594661139 30385947345356375391991709)
      ·
        refine ⟨11394730254508640771996891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30385947345356375391991709 11394730254508640771996891)
        ·
          refine ⟨17092095381762961157995337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11394730254508640771996891 17092095381762961157995337)
          ·
            refine ⟨12819071536322220868496503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17092095381762961157995337 12819071536322220868496503)
            ·
              refine ⟨19228607304483331302744755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12819071536322220868496503 19228607304483331302744755)
              ·
                refine ⟨28842910956724996954117133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19228607304483331302744755 28842910956724996954117133)
                ·
                  refine ⟨10816091608771873857793925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28842910956724996954117133 10816091608771873857793925)
                  ·
                    refine ⟨2028017176644726348336361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10816091608771873857793925 2028017176644726348336361)
                    ·
                      refine ⟨1521012882483544761252271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028017176644726348336361 1521012882483544761252271)
                      ·
                        rfl

theorem cell23_2962162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_2962162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962162 prefixEnd_2962162 := by exact prefixLift 2962162
  have htrace : WordTrace (prefixWord ++ tailWord_2962162) baseStart_2962162 baseEnd_2962162 := by
    simpa [prefixWord, tailWord_2962162, baseEnd_2962162] using wordTrace_append hprefix tailTrace_2962162
  have hstable : (prefixWord ++ tailWord_2962162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962162).length < 2 ^ (prefixWord ++ tailWord_2962162).sum := by decide
  have hdescent : baseEnd_2962162 < baseStart_2962162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962166 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_2962166 : Nat := 118140960795 + 2962166 * 2 ^ 59
def prefixEnd_2962166 : Nat := 4983230072969 + 3 ^ 40 * 2962166 * 2
def baseEnd_2962166 : Nat := 1521014936406162745602253

theorem tailTrace_2962166 : CollatzResearch.WordTrace tailWord_2962166 prefixEnd_2962166 1521014936406162745602253 := by
  unfold tailWord_2962166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752441861661622157583647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72026046524390636347558901 6752441861661622157583647)
  ·
    refine ⟨10128662792492433236375471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6752441861661622157583647 10128662792492433236375471)
    ·
      refine ⟨15192994188738649854563207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10128662792492433236375471 15192994188738649854563207)
      ·
        refine ⟨22789491283107974781844811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15192994188738649854563207 22789491283107974781844811)
        ·
          refine ⟨34184236924661962172767217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22789491283107974781844811 34184236924661962172767217)
          ·
            refine ⟨25638177693496471629575413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34184236924661962172767217 25638177693496471629575413)
            ·
              refine ⟨2403579158765294215272695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25638177693496471629575413 2403579158765294215272695)
              ·
                refine ⟨3605368738147941322909043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403579158765294215272695 3605368738147941322909043)
                ·
                  refine ⟨5408053107221911984363565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3605368738147941322909043 5408053107221911984363565)
                  ·
                    refine ⟨2028019915208216994136337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5408053107221911984363565 2028019915208216994136337)
                    ·
                      refine ⟨1521014936406162745602253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028019915208216994136337 1521014936406162745602253)
                      ·
                        rfl

theorem cell23_2962166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_2962166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962166 prefixEnd_2962166 := by exact prefixLift 2962166
  have htrace : WordTrace (prefixWord ++ tailWord_2962166) baseStart_2962166 baseEnd_2962166 := by
    simpa [prefixWord, tailWord_2962166, baseEnd_2962166] using wordTrace_append hprefix tailTrace_2962166
  have hstable : (prefixWord ++ tailWord_2962166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962166).length < 2 ^ (prefixWord ++ tailWord_2962166).sum := by decide
  have hdescent : baseEnd_2962166 < baseStart_2962166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962188 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_2962188 : Nat := 118140960795 + 2962188 * 2 ^ 59
def prefixEnd_2962188 : Nat := 4983230072969 + 3 ^ 40 * 2962188 * 2
def baseEnd_2962188 : Nat := 1521026232980561659527151

theorem tailTrace_2962188 : CollatzResearch.WordTrace tailWord_2962188 prefixEnd_2962188 1521026232980561659527151 := by
  unfold tailWord_2962188
  simp only [CollatzResearch.WordTrace]
  refine ⟨54019936096253126139319609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72026581461670834852426145 54019936096253126139319609)
  ·
    refine ⟨40514952072189844604489707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54019936096253126139319609 40514952072189844604489707)
    ·
      refine ⟨60772428108284766906734561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40514952072189844604489707 60772428108284766906734561)
      ·
        refine ⟨45579321081213575180050921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60772428108284766906734561 45579321081213575180050921)
        ·
          refine ⟨34184490810910181385038191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45579321081213575180050921 34184490810910181385038191)
          ·
            refine ⟨51276736216365272077557287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34184490810910181385038191 51276736216365272077557287)
            ·
              refine ⟨76915104324547908116335931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51276736216365272077557287 76915104324547908116335931)
              ·
                refine ⟨115372656486821862174503897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76915104324547908116335931 115372656486821862174503897)
                ·
                  refine ⟨86529492365116396630877923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115372656486821862174503897 86529492365116396630877923)
                  ·
                    refine ⟨129794238547674594946316885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86529492365116396630877923 129794238547674594946316885)
                    ·
                      refine ⟨1521026232980561659527151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 129794238547674594946316885 1521026232980561659527151)
                      ·
                        rfl

theorem cell23_2962188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_2962188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962188 prefixEnd_2962188 := by exact prefixLift 2962188
  have htrace : WordTrace (prefixWord ++ tailWord_2962188) baseStart_2962188 baseEnd_2962188 := by
    simpa [prefixWord, tailWord_2962188, baseEnd_2962188] using wordTrace_append hprefix tailTrace_2962188
  have hstable : (prefixWord ++ tailWord_2962188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962188).length < 2 ^ (prefixWord ++ tailWord_2962188).sum := by decide
  have hdescent : baseEnd_2962188 < baseStart_2962188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962195 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 3]
def baseStart_2962195 : Nat := 118140960795 + 2962195 * 2 ^ 59
def prefixEnd_2962195 : Nat := 4983230072969 + 3 ^ 40 * 2962195 * 2
def baseEnd_2962195 : Nat := 1521029827345143132139619

theorem tailTrace_2962195 : CollatzResearch.WordTrace tailWord_2962195 prefixEnd_2962195 1521029827345143132139619 := by
  unfold tailWord_2962195
  simp only [CollatzResearch.WordTrace]
  refine ⟨108040127503480892474144039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72026751668987261649429359 108040127503480892474144039)
  ·
    refine ⟨162060191255221338711216059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108040127503480892474144039 162060191255221338711216059)
    ·
      refine ⟨243090286882832008066824089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162060191255221338711216059 243090286882832008066824089)
      ·
        refine ⟨182317715162124006050118067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243090286882832008066824089 182317715162124006050118067)
        ·
          refine ⟨273476572743186009075177101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182317715162124006050118067 273476572743186009075177101)
          ·
            refine ⟨102553714778694753403191413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 273476572743186009075177101 102553714778694753403191413)
            ·
              refine ⟨9614410760502633131549195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102553714778694753403191413 9614410760502633131549195)
              ·
                refine ⟨14421616140753949697323793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9614410760502633131549195 14421616140753949697323793)
                ·
                  refine ⟨10816212105565462272992845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14421616140753949697323793 10816212105565462272992845)
                  ·
                    refine ⟨4056079539587048352372317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10816212105565462272992845 4056079539587048352372317)
                    ·
                      refine ⟨1521029827345143132139619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4056079539587048352372317 1521029827345143132139619)
                      ·
                        rfl

theorem cell23_2962195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 3].length) (baseStart_2962195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962195 prefixEnd_2962195 := by exact prefixLift 2962195
  have htrace : WordTrace (prefixWord ++ tailWord_2962195) baseStart_2962195 baseEnd_2962195 := by
    simpa [prefixWord, tailWord_2962195, baseEnd_2962195] using wordTrace_append hprefix tailTrace_2962195
  have hstable : (prefixWord ++ tailWord_2962195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962195).length < 2 ^ (prefixWord ++ tailWord_2962195).sum := by decide
  have hdescent : baseEnd_2962195 < baseStart_2962195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962230 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_2962230 : Nat := 118140960795 + 2962230 * 2 ^ 59
def prefixEnd_2962230 : Nat := 4983230072969 + 3 ^ 40 * 2962230 * 2
def baseEnd_2962230 : Nat := 1521047799168050495201959

theorem tailTrace_2962230 : CollatzResearch.WordTrace tailWord_2962230 prefixEnd_2962230 1521047799168050495201959 := by
  unfold tailWord_2962230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6752587753647130840729259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72027602705569395634445429 6752587753647130840729259)
  ·
    refine ⟨10128881630470696261093889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6752587753647130840729259 10128881630470696261093889)
    ·
      refine ⟨7596661222853022195820417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10128881630470696261093889 7596661222853022195820417)
      ·
        refine ⟨5697495917139766646865313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7596661222853022195820417 5697495917139766646865313)
        ·
          refine ⟨4273121937854824985148985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5697495917139766646865313 4273121937854824985148985)
          ·
            refine ⟨3204841453391118738861739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4273121937854824985148985 3204841453391118738861739)
            ·
              refine ⟨4807262180086678108292609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204841453391118738861739 4807262180086678108292609)
              ·
                refine ⟨3605446635065008581219457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807262180086678108292609 3605446635065008581219457)
                ·
                  refine ⟨2704084976298756435914593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3605446635065008581219457 2704084976298756435914593)
                  ·
                    refine ⟨2028063732224067326935945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2704084976298756435914593 2028063732224067326935945)
                    ·
                      refine ⟨1521047799168050495201959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028063732224067326935945 1521047799168050495201959)
                      ·
                        rfl

theorem cell23_2962230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_2962230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962230 prefixEnd_2962230 := by exact prefixLift 2962230
  have htrace : WordTrace (prefixWord ++ tailWord_2962230) baseStart_2962230 baseEnd_2962230 := by
    simpa [prefixWord, tailWord_2962230, baseEnd_2962230] using wordTrace_append hprefix tailTrace_2962230
  have hstable : (prefixWord ++ tailWord_2962230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962230).length < 2 ^ (prefixWord ++ tailWord_2962230).sum := by decide
  have hdescent : baseEnd_2962230 < baseStart_2962230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962272 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 3]
def baseStart_2962272 : Nat := 118140960795 + 2962272 * 2 ^ 59
def prefixEnd_2962272 : Nat := 4983230072969 + 3 ^ 40 * 2962272 * 2
def baseEnd_2962272 : Nat := 1521069365355539330876765

theorem tailTrace_2962272 : CollatzResearch.WordTrace tailWord_2962272 prefixEnd_2962272 1521069365355539330876765 := by
  unfold tailWord_2962272
  simp only [CollatzResearch.WordTrace]
  refine ⟨54021467962100967312348535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72028623949467956416464713 54021467962100967312348535)
  ·
    refine ⟨81032201943151450968522803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54021467962100967312348535 81032201943151450968522803)
    ·
      refine ⟨121548302914727176452784205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81032201943151450968522803 121548302914727176452784205)
      ·
        refine ⟨45580613593022691169794077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121548302914727176452784205 45580613593022691169794077)
        ·
          refine ⟨17092730097383509188672779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45580613593022691169794077 17092730097383509188672779)
          ·
            refine ⟨25639095146075263783009169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17092730097383509188672779 25639095146075263783009169)
            ·
              refine ⟨19229321359556447837256877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25639095146075263783009169 19229321359556447837256877)
              ·
                refine ⟨7210995509833667938971329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19229321359556447837256877 7210995509833667938971329)
                ·
                  refine ⟨5408246632375250954228497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7210995509833667938971329 5408246632375250954228497)
                  ·
                    refine ⟨4056184974281438215671373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5408246632375250954228497 4056184974281438215671373)
                    ·
                      refine ⟨1521069365355539330876765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4056184974281438215671373 1521069365355539330876765)
                      ·
                        rfl

theorem cell23_2962272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_2962272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962272 prefixEnd_2962272 := by exact prefixLift 2962272
  have htrace : WordTrace (prefixWord ++ tailWord_2962272) baseStart_2962272 baseEnd_2962272 := by
    simpa [prefixWord, tailWord_2962272, baseEnd_2962272] using wordTrace_append hprefix tailTrace_2962272
  have hstable : (prefixWord ++ tailWord_2962272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962272).length < 2 ^ (prefixWord ++ tailWord_2962272).sum := by decide
  have hdescent : baseEnd_2962272 < baseStart_2962272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962275 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 8]
def baseStart_2962275 : Nat := 118140960795 + 2962275 * 2 ^ 59
def prefixEnd_2962275 : Nat := 4983230072969 + 3 ^ 40 * 2962275 * 2
def baseEnd_2962275 : Nat := 169007878421944757682139

theorem tailTrace_2962275 : CollatzResearch.WordTrace tailWord_2962275 prefixEnd_2962275 169007878421944757682139 := by
  unfold tailWord_2962275
  simp only [CollatzResearch.WordTrace]
  refine ⟨108043045343191066137056279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72028696895460710758037519 108043045343191066137056279)
  ·
    refine ⟨162064568014786599205584419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108043045343191066137056279 162064568014786599205584419)
    ·
      refine ⟨243096852022179898808376629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162064568014786599205584419 243096852022179898808376629)
      ·
        refine ⟨22790329877079365513285309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 243096852022179898808376629 22790329877079365513285309)
        ·
          refine ⟨8546373703904762067481991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22790329877079365513285309 8546373703904762067481991)
          ·
            refine ⟨12819560555857143101222987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8546373703904762067481991 12819560555857143101222987)
            ·
              refine ⟨19229340833785714651834481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12819560555857143101222987 19229340833785714651834481)
              ·
                refine ⟨14422005625339285988875861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19229340833785714651834481 14422005625339285988875861)
                ·
                  refine ⟨169007878421944757682139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14422005625339285988875861 169007878421944757682139)
                  ·
                    rfl

theorem cell23_2962275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 8].length) (baseStart_2962275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962275 prefixEnd_2962275 := by exact prefixLift 2962275
  have htrace : WordTrace (prefixWord ++ tailWord_2962275) baseStart_2962275 baseEnd_2962275 := by
    simpa [prefixWord, tailWord_2962275, baseEnd_2962275] using wordTrace_append hprefix tailTrace_2962275
  have hstable : (prefixWord ++ tailWord_2962275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962275).length < 2 ^ (prefixWord ++ tailWord_2962275).sum := by decide
  have hdescent : baseEnd_2962275 < baseStart_2962275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962309 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 6]
def baseStart_2962309 : Nat := 118140960795 + 2962309 * 2 ^ 59
def prefixEnd_2962309 : Nat := 4983230072969 + 3 ^ 40 * 2962309 * 2
def baseEnd_2962309 : Nat := 169009818237750631790455

theorem tailTrace_2962309 : CollatzResearch.WordTrace tailWord_2962309 prefixEnd_2962309 169009818237750631790455 := by
  unfold tailWord_2962309
  simp only [CollatzResearch.WordTrace]
  refine ⟨108044285425067889943793981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72029523616711926629195987 108044285425067889943793981)
  ·
    refine ⟨40516607034400458728922743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108044285425067889943793981 40516607034400458728922743)
    ·
      refine ⟨60774910551600688093384115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40516607034400458728922743 60774910551600688093384115)
      ·
        refine ⟨91162365827401032140076173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60774910551600688093384115 91162365827401032140076173)
        ·
          refine ⟨34185887185275387052528565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91162365827401032140076173 34185887185275387052528565)
          ·
            refine ⟨3204926923619567536174553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34185887185275387052528565 3204926923619567536174553)
            ·
              refine ⟨2403695192714675652130915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3204926923619567536174553 2403695192714675652130915)
              ·
                refine ⟨3605542789072013478196373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2403695192714675652130915 3605542789072013478196373)
                ·
                  refine ⟨169009818237750631790455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3605542789072013478196373 169009818237750631790455)
                  ·
                    rfl

theorem cell23_2962309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_2962309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962309 prefixEnd_2962309 := by exact prefixLift 2962309
  have htrace : WordTrace (prefixWord ++ tailWord_2962309) baseStart_2962309 baseEnd_2962309 := by
    simpa [prefixWord, tailWord_2962309, baseEnd_2962309] using wordTrace_append hprefix tailTrace_2962309
  have hstable : (prefixWord ++ tailWord_2962309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962309).length < 2 ^ (prefixWord ++ tailWord_2962309).sum := by decide
  have hdescent : baseEnd_2962309 < baseStart_2962309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962353 : List Nat := [1, 2, 2, 4, 3, 1, 1, 4, 1, 1, 3]
def baseStart_2962353 : Nat := 118140960795 + 2962353 * 2 ^ 59
def prefixEnd_2962353 : Nat := 4983230072969 + 3 ^ 40 * 2962353 * 2
def baseEnd_2962353 : Nat := 1521110957288553513963893

theorem tailTrace_2962353 : CollatzResearch.WordTrace tailWord_2962353 prefixEnd_2962353 1521110957288553513963893 := by
  unfold tailWord_2962353
  simp only [CollatzResearch.WordTrace]
  refine ⟨108045890236908485458395713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72030593491272323638930475 108045890236908485458395713)
  ·
    refine ⟨81034417677681364093796785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108045890236908485458395713 81034417677681364093796785)
    ·
      refine ⟨60775813258261023070347589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81034417677681364093796785 60775813258261023070347589)
      ·
        refine ⟨11395464985923941825690173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60775813258261023070347589 11395464985923941825690173)
        ·
          refine ⟨4273299369721478184633815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11395464985923941825690173 4273299369721478184633815)
          ·
            refine ⟨6409949054582217276950723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273299369721478184633815 6409949054582217276950723)
            ·
              refine ⟨9614923581873325915426085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6409949054582217276950723 9614923581873325915426085)
              ·
                refine ⟨1802798171601248609142391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9614923581873325915426085 1802798171601248609142391)
                ·
                  refine ⟨2704197257401872913713587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802798171601248609142391 2704197257401872913713587)
                  ·
                    refine ⟨4056295886102809370570381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2704197257401872913713587 4056295886102809370570381)
                    ·
                      refine ⟨1521110957288553513963893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4056295886102809370570381 1521110957288553513963893)
                      ·
                        rfl

theorem cell23_2962353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_2962353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962353 prefixEnd_2962353 := by exact prefixLift 2962353
  have htrace : WordTrace (prefixWord ++ tailWord_2962353) baseStart_2962353 baseEnd_2962353 := by
    simpa [prefixWord, tailWord_2962353, baseEnd_2962353] using wordTrace_append hprefix tailTrace_2962353
  have hstable : (prefixWord ++ tailWord_2962353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962353).length < 2 ^ (prefixWord ++ tailWord_2962353).sum := by decide
  have hdescent : baseEnd_2962353 < baseStart_2962353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962355 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 6]
def baseStart_2962355 : Nat := 118140960795 + 2962355 * 2 ^ 59
def prefixEnd_2962355 : Nat := 4983230072969 + 3 ^ 40 * 2962355 * 2
def baseEnd_2962355 : Nat := 1521111984249862506138883

theorem tailTrace_2962355 : CollatzResearch.WordTrace tailWord_2962355 prefixEnd_2962355 1521111984249862506138883 := by
  unfold tailWord_2962355
  simp only [CollatzResearch.WordTrace]
  refine ⟨108045963182901239799968519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72030642121934159866645679 108045963182901239799968519)
  ·
    refine ⟨162068944774351859699952779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108045963182901239799968519 162068944774351859699952779)
    ·
      refine ⟨243103417161527789549929169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162068944774351859699952779 243103417161527789549929169)
      ·
        refine ⟨182327562871145842162446877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243103417161527789549929169 182327562871145842162446877)
        ·
          refine ⟨68372836076679690810917579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182327562871145842162446877 68372836076679690810917579)
          ·
            refine ⟨102559254115019536216376369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68372836076679690810917579 102559254115019536216376369)
            ·
              refine ⟨76919440586264652162282277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102559254115019536216376369 76919440586264652162282277)
              ·
                refine ⟨14422395109924622280427927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76919440586264652162282277 14422395109924622280427927)
                ·
                  refine ⟨21633592664886933420641891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14422395109924622280427927 21633592664886933420641891)
                  ·
                    refine ⟨32450388997330400130962837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21633592664886933420641891 32450388997330400130962837)
                    ·
                      refine ⟨1521111984249862506138883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32450388997330400130962837 1521111984249862506138883)
                      ·
                        rfl

theorem cell23_2962355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_2962355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962355 prefixEnd_2962355 := by exact prefixLift 2962355
  have htrace : WordTrace (prefixWord ++ tailWord_2962355) baseStart_2962355 baseEnd_2962355 := by
    simpa [prefixWord, tailWord_2962355, baseEnd_2962355] using wordTrace_append hprefix tailTrace_2962355
  have hstable : (prefixWord ++ tailWord_2962355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962355).length < 2 ^ (prefixWord ++ tailWord_2962355).sum := by decide
  have hdescent : baseEnd_2962355 < baseStart_2962355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962362 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3]
def baseStart_2962362 : Nat := 118140960795 + 2962362 * 2 ^ 59
def prefixEnd_2962362 : Nat := 4983230072969 + 3 ^ 40 * 2962362 * 2
def baseEnd_2962362 : Nat := 1521115578614443978751351

theorem tailTrace_2962362 : CollatzResearch.WordTrace tailWord_2962362 prefixEnd_2962362 1521115578614443978751351 := by
  unfold tailWord_2962362
  simp only [CollatzResearch.WordTrace]
  refine ⟨27011554623468969998868335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72030812329250586663648893 27011554623468969998868335)
  ·
    refine ⟨40517331935203454998302503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27011554623468969998868335 40517331935203454998302503)
    ·
      refine ⟨60775997902805182497453755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40517331935203454998302503 60775997902805182497453755)
      ·
        refine ⟨91163996854207773746180633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60775997902805182497453755 91163996854207773746180633)
        ·
          refine ⟨68372997640655830309635475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91163996854207773746180633 68372997640655830309635475)
          ·
            refine ⟨102559496460983745464453213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68372997640655830309635475 102559496460983745464453213)
            ·
              refine ⟨38459811172868904549169955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102559496460983745464453213 38459811172868904549169955)
              ·
                refine ⟨57689716759303356823754933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38459811172868904549169955 57689716759303356823754933)
                ·
                  refine ⟨5408410946184689702227025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57689716759303356823754933 5408410946184689702227025)
                  ·
                    refine ⟨4056308209638517276670269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5408410946184689702227025 4056308209638517276670269)
                    ·
                      refine ⟨1521115578614443978751351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4056308209638517276670269 1521115578614443978751351)
                      ·
                        rfl

theorem cell23_2962362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_2962362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962362 prefixEnd_2962362 := by exact prefixLift 2962362
  have htrace : WordTrace (prefixWord ++ tailWord_2962362) baseStart_2962362 baseEnd_2962362 := by
    simpa [prefixWord, tailWord_2962362, baseEnd_2962362] using wordTrace_append hprefix tailTrace_2962362
  have hstable : (prefixWord ++ tailWord_2962362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962362).length < 2 ^ (prefixWord ++ tailWord_2962362).sum := by decide
  have hdescent : baseEnd_2962362 < baseStart_2962362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962374 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_2962374 : Nat := 118140960795 + 2962374 * 2 ^ 59
def prefixEnd_2962374 : Nat := 4983230072969 + 3 ^ 40 * 2962374 * 2
def baseEnd_2962374 : Nat := 1521121740382297931801297

theorem tailTrace_2962374 : CollatzResearch.WordTrace tailWord_2962374 prefixEnd_2962374 1521121740382297931801297 := by
  unfold tailWord_2962374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3376458005307262688903443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72031104113221604029940117 3376458005307262688903443)
  ·
    refine ⟨5064687007960894033355165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3376458005307262688903443 5064687007960894033355165)
    ·
      refine ⟨1899257627985335262508187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5064687007960894033355165 1899257627985335262508187)
      ·
        refine ⟨2848886441978002893762281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1899257627985335262508187 2848886441978002893762281)
        ·
          refine ⟨2136664831483502170321711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2848886441978002893762281 2136664831483502170321711)
          ·
            refine ⟨3204997247225253255482567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136664831483502170321711 3204997247225253255482567)
            ·
              refine ⟨4807495870837879883223851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3204997247225253255482567 4807495870837879883223851)
              ·
                refine ⟨7211243806256819824835777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4807495870837879883223851 7211243806256819824835777)
                ·
                  refine ⟨5408432854692614868626833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7211243806256819824835777 5408432854692614868626833)
                  ·
                    refine ⟨4056324641019461151470125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5408432854692614868626833 4056324641019461151470125)
                    ·
                      refine ⟨1521121740382297931801297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4056324641019461151470125 1521121740382297931801297)
                      ·
                        rfl

theorem cell23_2962374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_2962374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962374 prefixEnd_2962374 := by exact prefixLift 2962374
  have htrace : WordTrace (prefixWord ++ tailWord_2962374) baseStart_2962374 baseEnd_2962374 := by
    simpa [prefixWord, tailWord_2962374, baseEnd_2962374] using wordTrace_append hprefix tailTrace_2962374
  have hstable : (prefixWord ++ tailWord_2962374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962374).length < 2 ^ (prefixWord ++ tailWord_2962374).sum := by decide
  have hdescent : baseEnd_2962374 < baseStart_2962374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962393 : List Nat := [1, 2, 1, 2, 5, 1, 1, 5, 1, 2, 2]
def baseStart_2962393 : Nat := 118140960795 + 2962393 * 2 ^ 59
def prefixEnd_2962393 : Nat := 4983230072969 + 3 ^ 40 * 2962393 * 2
def baseEnd_2962393 : Nat := 1521131496514733357463709

theorem tailTrace_2962393 : CollatzResearch.WordTrace tailWord_2962393 prefixEnd_2962393 1521131496514733357463709 := by
  unfold tailWord_2962393
  simp only [CollatzResearch.WordTrace]
  refine ⟨108047349156763572289851833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72031566104509048193234555 108047349156763572289851833)
  ·
    refine ⟨81035511867572679217388875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108047349156763572289851833 81035511867572679217388875)
    ·
      refine ⟨121553267801359018826083313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81035511867572679217388875 121553267801359018826083313)
      ·
        refine ⟨91164950851019264119562485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121553267801359018826083313 91164950851019264119562485)
        ·
          refine ⟨8546714142283056011208983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91164950851019264119562485 8546714142283056011208983)
          ·
            refine ⟨12820071213424584016813475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8546714142283056011208983 12820071213424584016813475)
            ·
              refine ⟨19230106820136876025220213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12820071213424584016813475 19230106820136876025220213)
              ·
                refine ⟨1802822514387832127364395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19230106820136876025220213 1802822514387832127364395)
                ·
                  refine ⟨2704233771581748191046593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802822514387832127364395 2704233771581748191046593)
                  ·
                    refine ⟨2028175328686311143284945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2704233771581748191046593 2028175328686311143284945)
                    ·
                      refine ⟨1521131496514733357463709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028175328686311143284945 1521131496514733357463709)
                      ·
                        rfl

theorem cell23_2962393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 1, 2, 2].length) (baseStart_2962393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962393 prefixEnd_2962393 := by exact prefixLift 2962393
  have htrace : WordTrace (prefixWord ++ tailWord_2962393) baseStart_2962393 baseEnd_2962393 := by
    simpa [prefixWord, tailWord_2962393, baseEnd_2962393] using wordTrace_append hprefix tailTrace_2962393
  have hstable : (prefixWord ++ tailWord_2962393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962393).length < 2 ^ (prefixWord ++ tailWord_2962393).sum := by decide
  have hdescent : baseEnd_2962393 < baseStart_2962393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962449 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 1, 4, 2]
def baseStart_2962449 : Nat := 118140960795 + 2962449 * 2 ^ 59
def prefixEnd_2962449 : Nat := 4983230072969 + 3 ^ 40 * 2962449 * 2
def baseEnd_2962449 : Nat := 1521160251431385138363451

theorem tailTrace_2962449 : CollatzResearch.WordTrace tailWord_2962449 prefixEnd_2962449 1521160251431385138363451 := by
  unfold tailWord_2962449
  simp only [CollatzResearch.WordTrace]
  refine ⟨108049391644560693853890401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72032927763040462569260267 108049391644560693853890401)
  ·
    refine ⟨81037043733420520390417801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108049391644560693853890401 81037043733420520390417801)
    ·
      refine ⟨60777782800065390292813351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81037043733420520390417801 60777782800065390292813351)
      ·
        refine ⟨91166674200098085439220027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60777782800065390292813351 91166674200098085439220027)
        ·
          refine ⟨136750011300147128158830041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91166674200098085439220027 136750011300147128158830041)
          ·
            refine ⟨102562508475110346119122531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136750011300147128158830041 102562508475110346119122531)
            ·
              refine ⟨153843762712665519178683797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102562508475110346119122531 153843762712665519178683797)
              ·
                refine ⟨7211426377156196211500803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153843762712665519178683797 7211426377156196211500803)
                ·
                  refine ⟨10817139565734294317251205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7211426377156196211500803 10817139565734294317251205)
                  ·
                    refine ⟨2028213668575180184484601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10817139565734294317251205 2028213668575180184484601)
                    ·
                      refine ⟨1521160251431385138363451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028213668575180184484601 1521160251431385138363451)
                      ·
                        rfl

theorem cell23_2962449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_2962449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962449 prefixEnd_2962449 := by exact prefixLift 2962449
  have htrace : WordTrace (prefixWord ++ tailWord_2962449) baseStart_2962449 baseEnd_2962449 := by
    simpa [prefixWord, tailWord_2962449, baseEnd_2962449] using wordTrace_append hprefix tailTrace_2962449
  have hstable : (prefixWord ++ tailWord_2962449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962449).length < 2 ^ (prefixWord ++ tailWord_2962449).sum := by decide
  have hdescent : baseEnd_2962449 < baseStart_2962449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962532 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 2, 8]
def baseStart_2962532 : Nat := 118140960795 + 2962532 * 2 ^ 59
def prefixEnd_2962532 : Nat := 4983230072969 + 3 ^ 40 * 2962532 * 2
def baseEnd_2962532 : Nat := 507067623441902771208523

theorem tailTrace_2962532 : CollatzResearch.WordTrace tailWord_2962532 prefixEnd_2962532 507067623441902771208523 := by
  unfold tailWord_2962532
  simp only [CollatzResearch.WordTrace]
  refine ⟨54026209451629999514580925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72034945935506666019441233 54026209451629999514580925)
  ·
    refine ⟨20259828544361249817967847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54026209451629999514580925 20259828544361249817967847)
    ·
      refine ⟨30389742816541874726951771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20259828544361249817967847 30389742816541874726951771)
      ·
        refine ⟨45584614224812812090427657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30389742816541874726951771 45584614224812812090427657)
        ·
          refine ⟨34188460668609609067820743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45584614224812812090427657 34188460668609609067820743)
          ·
            refine ⟨51282691002914413601731115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34188460668609609067820743 51282691002914413601731115)
            ·
              refine ⟨76924036504371620402596673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51282691002914413601731115 76924036504371620402596673)
              ·
                refine ⟨57693027378278715301947505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76924036504371620402596673 57693027378278715301947505)
                ·
                  refine ⟨43269770533709036476460629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57693027378278715301947505 43269770533709036476460629)
                  ·
                    refine ⟨507067623441902771208523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43269770533709036476460629 507067623441902771208523)
                    ·
                      rfl

theorem cell23_2962532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_2962532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962532 prefixEnd_2962532 := by exact prefixLift 2962532
  have htrace : WordTrace (prefixWord ++ tailWord_2962532) baseStart_2962532 baseEnd_2962532 := by
    simpa [prefixWord, tailWord_2962532, baseEnd_2962532] using wordTrace_append hprefix tailTrace_2962532
  have hstable : (prefixWord ++ tailWord_2962532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962532).length < 2 ^ (prefixWord ++ tailWord_2962532).sum := by decide
  have hdescent : baseEnd_2962532 < baseStart_2962532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962553 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 2, 5]
def baseStart_2962553 : Nat := 118140960795 + 2962553 * 2 ^ 59
def prefixEnd_2962553 : Nat := 4983230072969 + 3 ^ 40 * 2962553 * 2
def baseEnd_2962553 : Nat := 507071217806484243820991

theorem tailTrace_2962553 : CollatzResearch.WordTrace tailWord_2962553 prefixEnd_2962553 507071217806484243820991 := by
  unfold tailWord_2962553
  simp only [CollatzResearch.WordTrace]
  refine ⟨108053184836183919615676313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72035456557455946410450875 108053184836183919615676313)
  ·
    refine ⟨81039888627137939711757235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108053184836183919615676313 81039888627137939711757235)
    ·
      refine ⟨121559832940706909567635853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81039888627137939711757235 121559832940706909567635853)
      ·
        refine ⟨45584937352765091087863445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121559832940706909567635853 45584937352765091087863445)
        ·
          refine ⟨2136793938410863644743599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45584937352765091087863445 2136793938410863644743599)
          ·
            refine ⟨3205190907616295467115399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2136793938410863644743599 3205190907616295467115399)
            ·
              refine ⟨4807786361424443200673099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205190907616295467115399 4807786361424443200673099)
              ·
                refine ⟨7211679542136664801009649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4807786361424443200673099 7211679542136664801009649)
                ·
                  refine ⟨5408759656602498600757237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7211679542136664801009649 5408759656602498600757237)
                  ·
                    refine ⟨507071217806484243820991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5408759656602498600757237 507071217806484243820991)
                    ·
                      rfl

theorem cell23_2962553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 2, 5].length) (baseStart_2962553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962553 prefixEnd_2962553 := by exact prefixLift 2962553
  have htrace : WordTrace (prefixWord ++ tailWord_2962553) baseStart_2962553 baseEnd_2962553 := by
    simpa [prefixWord, tailWord_2962553, baseEnd_2962553] using wordTrace_append hprefix tailTrace_2962553
  have hstable : (prefixWord ++ tailWord_2962553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962553).length < 2 ^ (prefixWord ++ tailWord_2962553).sum := by decide
  have hdescent : baseEnd_2962553 < baseStart_2962553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962579 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 6]
def baseStart_2962579 : Nat := 118140960795 + 2962579 * 2 ^ 59
def prefixEnd_2962579 : Nat := 4983230072969 + 3 ^ 40 * 2962579 * 2
def baseEnd_2962579 : Nat := 169025222657385514415317

theorem tailTrace_2962579 : CollatzResearch.WordTrace tailWord_2962579 prefixEnd_2962579 169025222657385514415317 := by
  unfold tailWord_2962579
  simp only [CollatzResearch.WordTrace]
  refine ⟨108054133134089726056122791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72036088756059817370748527 108054133134089726056122791)
  ·
    refine ⟨162081199701134589084184187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108054133134089726056122791 162081199701134589084184187)
    ·
      refine ⟨243121799551701883626276281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162081199701134589084184187 243121799551701883626276281)
      ·
        refine ⟨182341349663776412719707211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243121799551701883626276281 182341349663776412719707211)
        ·
          refine ⟨273512024495664619079560817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182341349663776412719707211 273512024495664619079560817)
          ·
            refine ⟨205134018371748464309670613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 273512024495664619079560817 205134018371748464309670613)
            ·
              refine ⟨4807828555587854632257905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 205134018371748464309670613 4807828555587854632257905)
              ·
                refine ⟨3605871416690890974193429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4807828555587854632257905 3605871416690890974193429)
                ·
                  refine ⟨169025222657385514415317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3605871416690890974193429 169025222657385514415317)
                  ·
                    rfl

theorem cell23_2962579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 6].length) (baseStart_2962579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962579 prefixEnd_2962579 := by exact prefixLift 2962579
  have htrace : WordTrace (prefixWord ++ tailWord_2962579) baseStart_2962579 baseEnd_2962579 := by
    simpa [prefixWord, tailWord_2962579, baseEnd_2962579] using wordTrace_append hprefix tailTrace_2962579
  have hstable : (prefixWord ++ tailWord_2962579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962579).length < 2 ^ (prefixWord ++ tailWord_2962579).sum := by decide
  have hdescent : baseEnd_2962579 < baseStart_2962579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962583 : List Nat := [1, 1, 3, 3, 3, 1, 2, 4, 1, 4]
def baseStart_2962583 : Nat := 118140960795 + 2962583 * 2 ^ 59
def prefixEnd_2962583 : Nat := 4983230072969 + 3 ^ 40 * 2962583 * 2
def baseEnd_2962583 : Nat := 507076352613029204695945

theorem tailTrace_2962583 : CollatzResearch.WordTrace tailWord_2962583 prefixEnd_2962583 507076352613029204695945 := by
  unfold tailWord_2962583
  simp only [CollatzResearch.WordTrace]
  refine ⟨108054279026075234739268403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72036186017383489826178935 108054279026075234739268403)
  ·
    refine ⟨162081418539112852108902605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108054279026075234739268403 162081418539112852108902605)
    ·
      refine ⟨60780531952167319540838477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162081418539112852108902605 60780531952167319540838477)
      ·
        refine ⟨22792699482062744827814429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60780531952167319540838477 22792699482062744827814429)
        ·
          refine ⟨8547262305773529310430411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22792699482062744827814429 8547262305773529310430411)
          ·
            refine ⟨12820893458660293965645617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8547262305773529310430411 12820893458660293965645617)
            ·
              refine ⟨9615670093995220474234213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12820893458660293965645617 9615670093995220474234213)
              ·
                refine ⟨1802938142624103838918915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9615670093995220474234213 1802938142624103838918915)
                ·
                  refine ⟨2704407213936155758378373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1802938142624103838918915 2704407213936155758378373)
                  ·
                    refine ⟨507076352613029204695945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2704407213936155758378373 507076352613029204695945)
                    ·
                      rfl

theorem cell23_2962583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_2962583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962583 prefixEnd_2962583 := by exact prefixLift 2962583
  have htrace : WordTrace (prefixWord ++ tailWord_2962583) baseStart_2962583 baseEnd_2962583 := by
    simpa [prefixWord, tailWord_2962583, baseEnd_2962583] using wordTrace_append hprefix tailTrace_2962583
  have hstable : (prefixWord ++ tailWord_2962583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962583).length < 2 ^ (prefixWord ++ tailWord_2962583).sum := by decide
  have hdescent : baseEnd_2962583 < baseStart_2962583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962629 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_2962629 : Nat := 118140960795 + 2962629 * 2 ^ 59
def prefixEnd_2962629 : Nat := 4983230072969 + 3 ^ 40 * 2962629 * 2
def baseEnd_2962629 : Nat := 1521252677949194434112623

theorem tailTrace_2962629 : CollatzResearch.WordTrace tailWord_2962629 prefixEnd_2962629 1521252677949194434112623 := by
  unfold tailWord_2962629
  simp only [CollatzResearch.WordTrace]
  refine ⟨108055956783908584595442941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72037304522605723063628627 108055956783908584595442941)
  ·
    refine ⟨40520983793965719223291103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108055956783908584595442941 40520983793965719223291103)
    ·
      refine ⟨60781475690948578834936655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40520983793965719223291103 60781475690948578834936655)
      ·
        refine ⟨91172213536422868252404983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60781475690948578834936655 91172213536422868252404983)
        ·
          refine ⟨136758320304634302378607475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91172213536422868252404983 136758320304634302378607475)
          ·
            refine ⟨205137480456951453567911213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 136758320304634302378607475 205137480456951453567911213)
            ·
              refine ⟨76926555171356795087966705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 205137480456951453567911213 76926555171356795087966705)
              ·
                refine ⟨57694916378517596315975029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76926555171356795087966705 57694916378517596315975029)
                ·
                  refine ⟨5408898410486024654622659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57694916378517596315975029 5408898410486024654622659)
                  ·
                    refine ⟨8113347615729036981933989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5408898410486024654622659 8113347615729036981933989)
                    ·
                      refine ⟨1521252677949194434112623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8113347615729036981933989 1521252677949194434112623)
                      ·
                        rfl

theorem cell23_2962629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_2962629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962629 prefixEnd_2962629 := by exact prefixLift 2962629
  have htrace : WordTrace (prefixWord ++ tailWord_2962629) baseStart_2962629 baseEnd_2962629 := by
    simpa [prefixWord, tailWord_2962629, baseEnd_2962629] using wordTrace_append hprefix tailTrace_2962629
  have hstable : (prefixWord ++ tailWord_2962629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962629).length < 2 ^ (prefixWord ++ tailWord_2962629).sum := by decide
  have hdescent : baseEnd_2962629 < baseStart_2962629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962649 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 2, 6, 3]
def baseStart_2962649 : Nat := 118140960795 + 2962649 * 2 ^ 59
def prefixEnd_2962649 : Nat := 4983230072969 + 3 ^ 40 * 2962649 * 2
def baseEnd_2962649 : Nat := 1521262947562284355862531

theorem tailTrace_2962649 : CollatzResearch.WordTrace tailWord_2962649 prefixEnd_2962649 1521262947562284355862531 := by
  unfold tailWord_2962649
  simp only [CollatzResearch.WordTrace]
  refine ⟨108056686243836128011171001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72037790829224085340780667 108056686243836128011171001)
  ·
    refine ⟨81042514682877096008378251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108056686243836128011171001 81042514682877096008378251)
    ·
      refine ⟨121563772024315644012567377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81042514682877096008378251 121563772024315644012567377)
      ·
        refine ⟨91172829018236733009425533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121563772024315644012567377 91172829018236733009425533)
        ·
          refine ⟨34189810881838774878534575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91172829018236733009425533 34189810881838774878534575)
          ·
            refine ⟨51284716322758162317801863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34189810881838774878534575 51284716322758162317801863)
            ·
              refine ⟨76927074484137243476702795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51284716322758162317801863 76927074484137243476702795)
              ·
                refine ⟨115390611726205865215054193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76927074484137243476702795 115390611726205865215054193)
                ·
                  refine ⟨86542958794654398911290645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115390611726205865215054193 86542958794654398911290645)
                  ·
                    refine ⟨4056701193499424948966749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 86542958794654398911290645 4056701193499424948966749)
                    ·
                      refine ⟨1521262947562284355862531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4056701193499424948966749 1521262947562284355862531)
                      ·
                        rfl

theorem cell23_2962649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_2962649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962649 prefixEnd_2962649 := by exact prefixLift 2962649
  have htrace : WordTrace (prefixWord ++ tailWord_2962649) baseStart_2962649 baseEnd_2962649 := by
    simpa [prefixWord, tailWord_2962649, baseEnd_2962649] using wordTrace_append hprefix tailTrace_2962649
  have hstable : (prefixWord ++ tailWord_2962649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962649).length < 2 ^ (prefixWord ++ tailWord_2962649).sum := by decide
  have hdescent : baseEnd_2962649 < baseStart_2962649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962663 : List Nat := [1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2962663 : Nat := 118140960795 + 2962663 * 2 ^ 59
def prefixEnd_2962663 : Nat := 4983230072969 + 3 ^ 40 * 2962663 * 2
def baseEnd_2962663 : Nat := 1521270136291447301087467

theorem tailTrace_2962663 : CollatzResearch.WordTrace tailWord_2962663 prefixEnd_2962663 1521270136291447301087467 := by
  unfold tailWord_2962663
  simp only [CollatzResearch.WordTrace]
  refine ⟨108057196865785408402180643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72038131243856938934787095 108057196865785408402180643)
  ·
    refine ⟨162085795298678112603270965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108057196865785408402180643 162085795298678112603270965)
    ·
      refine ⟨15195543309251073056556653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162085795298678112603270965 15195543309251073056556653)
      ·
        refine ⟨5698328740969152396208745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15195543309251073056556653 5698328740969152396208745)
        ·
          refine ⟨4273746555726864297156559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5698328740969152396208745 4273746555726864297156559)
          ·
            refine ⟨6410619833590296445734839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4273746555726864297156559 6410619833590296445734839)
            ·
              refine ⟨9615929750385444668602259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6410619833590296445734839 9615929750385444668602259)
              ·
                refine ⟨14423894625578167002903389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9615929750385444668602259 14423894625578167002903389)
                ·
                  refine ⟨5408960484591812626088771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14423894625578167002903389 5408960484591812626088771)
                  ·
                    refine ⟨8113440726887718939133157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5408960484591812626088771 8113440726887718939133157)
                    ·
                      refine ⟨1521270136291447301087467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8113440726887718939133157 1521270136291447301087467)
                      ·
                        rfl

theorem cell23_2962663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2962663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962663 prefixEnd_2962663 := by exact prefixLift 2962663
  have htrace : WordTrace (prefixWord ++ tailWord_2962663) baseStart_2962663 baseEnd_2962663 := by
    simpa [prefixWord, tailWord_2962663, baseEnd_2962663] using wordTrace_append hprefix tailTrace_2962663
  have hstable : (prefixWord ++ tailWord_2962663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962663).length < 2 ^ (prefixWord ++ tailWord_2962663).sum := by decide
  have hdescent : baseEnd_2962663 < baseStart_2962663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962699 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 2, 7]
def baseStart_2962699 : Nat := 118140960795 + 2962699 * 2 ^ 59
def prefixEnd_2962699 : Nat := 4983230072969 + 3 ^ 40 * 2962699 * 2
def baseEnd_2962699 : Nat := 507096207198336386745767

theorem tailTrace_2962699 : CollatzResearch.WordTrace tailWord_2962699 prefixEnd_2962699 507096207198336386745767 := by
  unfold tailWord_2962699
  simp only [CollatzResearch.WordTrace]
  refine ⟨108058509893654986550491151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72039006595769991033660767 108058509893654986550491151)
  ·
    refine ⟨162087764840482479825736727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108058509893654986550491151 162087764840482479825736727)
    ·
      refine ⟨243131647260723719738605091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162087764840482479825736727 243131647260723719738605091)
      ·
        refine ⟨364697470891085579607907637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243131647260723719738605091 364697470891085579607907637)
        ·
          refine ⟨34190387896039273088241341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 364697470891085579607907637 34190387896039273088241341)
          ·
            refine ⟨12821395461014727408090503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34190387896039273088241341 12821395461014727408090503)
            ·
              refine ⟨19232093191522091112135755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12821395461014727408090503 19232093191522091112135755)
              ·
                refine ⟨28848139787283136668203633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19232093191522091112135755 28848139787283136668203633)
                ·
                  refine ⟨21636104840462352501152725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28848139787283136668203633 21636104840462352501152725)
                  ·
                    refine ⟨507096207198336386745767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21636104840462352501152725 507096207198336386745767)
                    ·
                      rfl

theorem cell23_2962699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 7].length) (baseStart_2962699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962699 prefixEnd_2962699 := by exact prefixLift 2962699
  have htrace : WordTrace (prefixWord ++ tailWord_2962699) baseStart_2962699 baseEnd_2962699 := by
    simpa [prefixWord, tailWord_2962699, baseEnd_2962699] using wordTrace_append hprefix tailTrace_2962699
  have hstable : (prefixWord ++ tailWord_2962699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962699).length < 2 ^ (prefixWord ++ tailWord_2962699).sum := by decide
  have hdescent : baseEnd_2962699 < baseStart_2962699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962709 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_2962709 : Nat := 118140960795 + 2962709 * 2 ^ 59
def prefixEnd_2962709 : Nat := 4983230072969 + 3 ^ 40 * 2962709 * 2
def baseEnd_2962709 : Nat := 1521293756401554121112255

theorem tailTrace_2962709 : CollatzResearch.WordTrace tailWord_2962709 prefixEnd_2962709 1521293756401554121112255 := by
  unfold tailWord_2962709
  simp only [CollatzResearch.WordTrace]
  refine ⟨108058874623618758258355181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72039249749079172172236787 108058874623618758258355181)
  ·
    refine ⟨40522077983857034346883193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108058874623618758258355181 40522077983857034346883193)
    ·
      refine ⟨30391558487892775760162395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40522077983857034346883193 30391558487892775760162395)
      ·
        refine ⟨45587337731839163640243593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30391558487892775760162395 45587337731839163640243593)
        ·
          refine ⟨34190503298879372730182695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45587337731839163640243593 34190503298879372730182695)
          ·
            refine ⟨51285754948319059095274043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34190503298879372730182695 51285754948319059095274043)
            ·
              refine ⟨76928632422478588642911065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51285754948319059095274043 76928632422478588642911065)
              ·
                refine ⟨57696474316858941482183299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76928632422478588642911065 57696474316858941482183299)
                ·
                  refine ⟨86544711475288412223274949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57696474316858941482183299 86544711475288412223274949)
                  ·
                    refine ⟨16227133401616577291864053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86544711475288412223274949 16227133401616577291864053)
                    ·
                      refine ⟨1521293756401554121112255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16227133401616577291864053 1521293756401554121112255)
                      ·
                        rfl

theorem cell23_2962709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_2962709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962709 prefixEnd_2962709 := by exact prefixLift 2962709
  have htrace : WordTrace (prefixWord ++ tailWord_2962709) baseStart_2962709 baseEnd_2962709 := by
    simpa [prefixWord, tailWord_2962709, baseEnd_2962709] using wordTrace_append hprefix tailTrace_2962709
  have hstable : (prefixWord ++ tailWord_2962709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962709).length < 2 ^ (prefixWord ++ tailWord_2962709).sum := by decide
  have hdescent : baseEnd_2962709 < baseStart_2962709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962723 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 3, 3, 2]
def baseStart_2962723 : Nat := 118140960795 + 2962723 * 2 ^ 59
def prefixEnd_2962723 : Nat := 4983230072969 + 3 ^ 40 * 2962723 * 2
def baseEnd_2962723 : Nat := 1521300945130717066337191

theorem tailTrace_2962723 : CollatzResearch.WordTrace tailWord_2962723 prefixEnd_2962723 1521300945130717066337191 := by
  unfold tailWord_2962723
  simp only [CollatzResearch.WordTrace]
  refine ⟨108059385245568038649364823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72039590163712025766243215 108059385245568038649364823)
  ·
    refine ⟨162089077868352057974047235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108059385245568038649364823 162089077868352057974047235)
    ·
      refine ⟨243133616802528086961070853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162089077868352057974047235 243133616802528086961070853)
      ·
        refine ⟨45587553150474016305200785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243133616802528086961070853 45587553150474016305200785)
        ·
          refine ⟨34190664862855512228900589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45587553150474016305200785 34190664862855512228900589)
          ·
            refine ⟨12821499323570817085837721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34190664862855512228900589 12821499323570817085837721)
            ·
              refine ⟨9616124492678112814378291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12821499323570817085837721 9616124492678112814378291)
              ·
                refine ⟨14424186739017169221567437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9616124492678112814378291 14424186739017169221567437)
                ·
                  refine ⟨5409070027131438458087789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14424186739017169221567437 5409070027131438458087789)
                  ·
                    refine ⟨2028401260174289421782921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5409070027131438458087789 2028401260174289421782921)
                    ·
                      refine ⟨1521300945130717066337191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028401260174289421782921 1521300945130717066337191)
                      ·
                        rfl

theorem cell23_2962723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_2962723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962723 prefixEnd_2962723 := by exact prefixLift 2962723
  have htrace : WordTrace (prefixWord ++ tailWord_2962723) baseStart_2962723 baseEnd_2962723 := by
    simpa [prefixWord, tailWord_2962723, baseEnd_2962723] using wordTrace_append hprefix tailTrace_2962723
  have hstable : (prefixWord ++ tailWord_2962723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962723).length < 2 ^ (prefixWord ++ tailWord_2962723).sum := by decide
  have hdescent : baseEnd_2962723 < baseStart_2962723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962766 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2962766 : Nat := 118140960795 + 2962766 * 2 ^ 59
def prefixEnd_2962766 : Nat := 4983230072969 + 3 ^ 40 * 2962766 * 2
def baseEnd_2962766 : Nat := 1521323024798860398099493

theorem tailTrace_2962766 : CollatzResearch.WordTrace tailWord_2962766 prefixEnd_2962766 1521323024798860398099493 := by
  unfold tailWord_2962766
  simp only [CollatzResearch.WordTrace]
  refine ⟨13507619198051532124147519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72040635722941504662120101 13507619198051532124147519)
  ·
    refine ⟨20261428797077298186221279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13507619198051532124147519 20261428797077298186221279)
    ·
      refine ⟨30392143195615947279331919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20261428797077298186221279 30392143195615947279331919)
      ·
        refine ⟨45588214793423920918997879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30392143195615947279331919 45588214793423920918997879)
        ·
          refine ⟨68382322190135881378496819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45588214793423920918997879 68382322190135881378496819)
          ·
            refine ⟨102573483285203822067745229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68382322190135881378496819 102573483285203822067745229)
            ·
              refine ⟨38465056231951433275404461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102573483285203822067745229 38465056231951433275404461)
              ·
                refine ⟨14424396086981787478276673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38465056231951433275404461 14424396086981787478276673)
                ·
                  refine ⟨10818297065236340608707505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14424396086981787478276673 10818297065236340608707505)
                  ·
                    refine ⟨8113722798927255456530629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10818297065236340608707505 8113722798927255456530629)
                    ·
                      refine ⟨1521323024798860398099493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8113722798927255456530629 1521323024798860398099493)
                      ·
                        rfl

theorem cell23_2962766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2962766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962766 prefixEnd_2962766 := by exact prefixLift 2962766
  have htrace : WordTrace (prefixWord ++ tailWord_2962766) baseStart_2962766 baseEnd_2962766 := by
    simpa [prefixWord, tailWord_2962766, baseEnd_2962766] using wordTrace_append hprefix tailTrace_2962766
  have hstable : (prefixWord ++ tailWord_2962766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962766).length < 2 ^ (prefixWord ++ tailWord_2962766).sum := by decide
  have hdescent : baseEnd_2962766 < baseStart_2962766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962813 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 2, 5, 2]
def baseStart_2962813 : Nat := 118140960795 + 2962813 * 2 ^ 59
def prefixEnd_2962813 : Nat := 4983230072969 + 3 ^ 40 * 2962813 * 2
def baseEnd_2962813 : Nat := 1521347158389621714211777

theorem tailTrace_2962813 : CollatzResearch.WordTrace tailWord_2962813 prefixEnd_2962813 1521347158389621714211777 := by
  unfold tailWord_2962813
  simp only [CollatzResearch.WordTrace]
  refine ⟨108062667815241984020141093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72041778543494656013427395 108062667815241984020141093)
  ·
    refine ⟨20261750215357872003776455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108062667815241984020141093 20261750215357872003776455)
    ·
      refine ⟨30392625323036808005664683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20261750215357872003776455 30392625323036808005664683)
      ·
        refine ⟨45588937984555212008497025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30392625323036808005664683 45588937984555212008497025)
        ·
          refine ⟨34191703488416409006372769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45588937984555212008497025 34191703488416409006372769)
          ·
            refine ⟨25643777616312306754779577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34191703488416409006372769 25643777616312306754779577)
            ·
              refine ⟨19232833212234230066084683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25643777616312306754779577 19232833212234230066084683)
              ·
                refine ⟨28849249818351345099127025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19232833212234230066084683 28849249818351345099127025)
                ·
                  refine ⟨21636937363763508824345269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28849249818351345099127025 21636937363763508824345269)
                  ·
                    refine ⟨2028462877852828952282369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21636937363763508824345269 2028462877852828952282369)
                    ·
                      refine ⟨1521347158389621714211777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028462877852828952282369 1521347158389621714211777)
                      ·
                        rfl

theorem cell23_2962813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_2962813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962813 prefixEnd_2962813 := by exact prefixLift 2962813
  have htrace : WordTrace (prefixWord ++ tailWord_2962813) baseStart_2962813 baseEnd_2962813 := by
    simpa [prefixWord, tailWord_2962813, baseEnd_2962813] using wordTrace_append hprefix tailTrace_2962813
  have hstable : (prefixWord ++ tailWord_2962813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962813).length < 2 ^ (prefixWord ++ tailWord_2962813).sum := by decide
  have hdescent : baseEnd_2962813 < baseStart_2962813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962840 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 2, 5]
def baseStart_2962840 : Nat := 118140960795 + 2962840 * 2 ^ 59
def prefixEnd_2962840 : Nat := 4983230072969 + 3 ^ 40 * 2962840 * 2
def baseEnd_2962840 : Nat := 507120340789097702858051

theorem tailTrace_2962840 : CollatzResearch.WordTrace tailWord_2962840 prefixEnd_2962840 507120340789097702858051 := by
  unfold tailWord_2962840
  simp only [CollatzResearch.WordTrace]
  refine ⟨54031826293072083815686987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72042435057429445087582649 54031826293072083815686987)
  ·
    refine ⟨81047739439608125723530481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54031826293072083815686987 81047739439608125723530481)
    ·
      refine ⟨60785804579706094292647861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81047739439608125723530481 60785804579706094292647861)
      ·
        refine ⟨5698669179347446339935737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60785804579706094292647861 5698669179347446339935737)
        ·
          refine ⟨4274001884510584754951803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5698669179347446339935737 4274001884510584754951803)
          ·
            refine ⟨6411002826765877132427705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274001884510584754951803 6411002826765877132427705)
            ·
              refine ⟨4808252120074407849320779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6411002826765877132427705 4808252120074407849320779)
              ·
                refine ⟨7212378180111611773981169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808252120074407849320779 7212378180111611773981169)
                ·
                  refine ⟨5409283635083708830485877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7212378180111611773981169 5409283635083708830485877)
                  ·
                    refine ⟨507120340789097702858051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5409283635083708830485877 507120340789097702858051)
                    ·
                      rfl

theorem cell23_2962840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_2962840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962840 prefixEnd_2962840 := by exact prefixLift 2962840
  have htrace : WordTrace (prefixWord ++ tailWord_2962840) baseStart_2962840 baseEnd_2962840 := by
    simpa [prefixWord, tailWord_2962840, baseEnd_2962840] using wordTrace_append hprefix tailTrace_2962840
  have hstable : (prefixWord ++ tailWord_2962840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962840).length < 2 ^ (prefixWord ++ tailWord_2962840).sum := by decide
  have hdescent : baseEnd_2962840 < baseStart_2962840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962920 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 4, 3, 2]
def baseStart_2962920 : Nat := 118140960795 + 2962920 * 2 ^ 59
def prefixEnd_2962920 : Nat := 4983230072969 + 3 ^ 40 * 2962920 * 2
def baseEnd_2962920 : Nat := 1521402100819652795573785

theorem tailTrace_2962920 : CollatzResearch.WordTrace tailWord_2962920 prefixEnd_2962920 1521402100819652795573785 := by
  unfold tailWord_2962920
  simp only [CollatzResearch.WordTrace]
  refine ⟨54033285212927170647143107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72044380283902894196190809 54033285212927170647143107)
  ·
    refine ⟨81049927819390755970714661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54033285212927170647143107 81049927819390755970714661)
    ·
      refine ⟨15196861466135766744508999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81049927819390755970714661 15196861466135766744508999)
      ·
        refine ⟨22795292199203650116763499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15196861466135766744508999 22795292199203650116763499)
        ·
          refine ⟨34192938298805475175145249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22795292199203650116763499 34192938298805475175145249)
          ·
            refine ⟨25644703724104106381358937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34192938298805475175145249 25644703724104106381358937)
            ·
              refine ⟨19233527793078079786019203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25644703724104106381358937 19233527793078079786019203)
              ·
                refine ⟨28850291689617119679028805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19233527793078079786019203 28850291689617119679028805)
                ·
                  refine ⟨5409429691803209939817901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28850291689617119679028805 5409429691803209939817901)
                  ·
                    refine ⟨2028536134426203727431713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5409429691803209939817901 2028536134426203727431713)
                    ·
                      refine ⟨1521402100819652795573785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028536134426203727431713 1521402100819652795573785)
                      ·
                        rfl

theorem cell23_2962920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_2962920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962920 prefixEnd_2962920 := by exact prefixLift 2962920
  have htrace : WordTrace (prefixWord ++ tailWord_2962920) baseStart_2962920 baseEnd_2962920 := by
    simpa [prefixWord, tailWord_2962920, baseEnd_2962920] using wordTrace_append hprefix tailTrace_2962920
  have hstable : (prefixWord ++ tailWord_2962920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962920).length < 2 ^ (prefixWord ++ tailWord_2962920).sum := by decide
  have hdescent : baseEnd_2962920 < baseStart_2962920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962927 : List Nat := [1, 1, 2, 1, 4, 1, 4, 4, 1, 1, 3]
def baseStart_2962927 : Nat := 118140960795 + 2962927 * 2 ^ 59
def prefixEnd_2962927 : Nat := 4983230072969 + 3 ^ 40 * 2962927 * 2
def baseEnd_2962927 : Nat := 1521405695184234268186253

theorem tailTrace_2962927 : CollatzResearch.WordTrace tailWord_2962927 prefixEnd_2962927 1521405695184234268186253 := by
  unfold tailWord_2962927
  simp only [CollatzResearch.WordTrace]
  refine ⟨108066825736828981489791035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72044550491219320993194023 108066825736828981489791035)
  ·
    refine ⟨162100238605243472234686553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108066825736828981489791035 162100238605243472234686553)
    ·
      refine ⟨121575178953932604176014915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162100238605243472234686553 121575178953932604176014915)
      ·
        refine ⟨182362768430898906264022373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121575178953932604176014915 182362768430898906264022373)
        ·
          refine ⟨34193019080793544924504195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 182362768430898906264022373 34193019080793544924504195)
          ·
            refine ⟨51289528621190317386756293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34193019080793544924504195 51289528621190317386756293)
            ·
              refine ⟨9616786616473184510016805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51289528621190317386756293 9616786616473184510016805)
              ·
                refine ⟨1803147490588722095628151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9616786616473184510016805 1803147490588722095628151)
                ·
                  refine ⟨2704721235883083143442227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1803147490588722095628151 2704721235883083143442227)
                  ·
                    refine ⟨4057081853824624715163341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2704721235883083143442227 4057081853824624715163341)
                    ·
                      refine ⟨1521405695184234268186253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4057081853824624715163341 1521405695184234268186253)
                      ·
                        rfl

theorem cell23_2962927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 1, 1, 3].length) (baseStart_2962927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962927 prefixEnd_2962927 := by exact prefixLift 2962927
  have htrace : WordTrace (prefixWord ++ tailWord_2962927) baseStart_2962927 baseEnd_2962927 := by
    simpa [prefixWord, tailWord_2962927, baseEnd_2962927] using wordTrace_append hprefix tailTrace_2962927
  have hstable : (prefixWord ++ tailWord_2962927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962927).length < 2 ^ (prefixWord ++ tailWord_2962927).sum := by decide
  have hdescent : baseEnd_2962927 < baseStart_2962927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2962990 : List Nat := [4, 1, 3, 1, 2, 2, 2, 8]
def baseStart_2962990 : Nat := 118140960795 + 2962990 * 2 ^ 59
def prefixEnd_2962990 : Nat := 4983230072969 + 3 ^ 40 * 2962990 * 2
def baseEnd_2962990 : Nat := 56349557202424723025869

theorem tailTrace_2962990 : CollatzResearch.WordTrace tailWord_2962990 prefixEnd_2962990 56349557202424723025869 := by
  unfold tailWord_2962990
  simp only [CollatzResearch.WordTrace]
  refine ⟨13508640441950092906166803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72046082357067162166222949 13508640441950092906166803)
  ·
    refine ⟨20262960662925139359250205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13508640441950092906166803 20262960662925139359250205)
    ·
      refine ⟨7598610248596927259718827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20262960662925139359250205 7598610248596927259718827)
      ·
        refine ⟨11397915372895390889578241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7598610248596927259718827 11397915372895390889578241)
        ·
          refine ⟨8548436529671543167183681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11397915372895390889578241 8548436529671543167183681)
          ·
            refine ⟨6411327397253657375387761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8548436529671543167183681 6411327397253657375387761)
            ·
              refine ⟨4808495547940243031540821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6411327397253657375387761 4808495547940243031540821)
              ·
                refine ⟨56349557202424723025869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4808495547940243031540821 56349557202424723025869)
                ·
                  rfl

theorem cell23_2962990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_2962990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2962990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2962990 prefixEnd_2962990 := by exact prefixLift 2962990
  have htrace : WordTrace (prefixWord ++ tailWord_2962990) baseStart_2962990 baseEnd_2962990 := by
    simpa [prefixWord, tailWord_2962990, baseEnd_2962990] using wordTrace_append hprefix tailTrace_2962990
  have hstable : (prefixWord ++ tailWord_2962990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2962990).length < 2 ^ (prefixWord ++ tailWord_2962990).sum := by decide
  have hdescent : baseEnd_2962990 < baseStart_2962990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2962990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963004 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_2963004 : Nat := 118140960795 + 2963004 * 2 ^ 59
def prefixEnd_2963004 : Nat := 4983230072969 + 3 ^ 40 * 2963004 * 2
def baseEnd_2963004 : Nat := 1521445233194630466923399

theorem tailTrace_2963004 : CollatzResearch.WordTrace tailWord_2963004 prefixEnd_2963004 1521445233194630466923399 := by
  unfold tailWord_2963004
  simp only [CollatzResearch.WordTrace]
  refine ⟨54034817078775011820172033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72046422771700015760229377 54034817078775011820172033)
  ·
    refine ⟨40526112809081258865129025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54034817078775011820172033 40526112809081258865129025)
    ·
      refine ⟨30394584606810944148846769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40526112809081258865129025 30394584606810944148846769)
      ·
        refine ⟨22795938455108208111635077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30394584606810944148846769 22795938455108208111635077)
        ·
          refine ⟨4274238460332789020931577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22795938455108208111635077 4274238460332789020931577)
          ·
            refine ⟨3205678845249591765698683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4274238460332789020931577 3205678845249591765698683)
            ·
              refine ⟨4808518267874387648548025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3205678845249591765698683 4808518267874387648548025)
              ·
                refine ⟨3606388700905790736411019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4808518267874387648548025 3606388700905790736411019)
                ·
                  refine ⟨5409583051358686104616529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3606388700905790736411019 5409583051358686104616529)
                  ·
                    refine ⟨4057187288519014578462397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5409583051358686104616529 4057187288519014578462397)
                    ·
                      refine ⟨1521445233194630466923399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4057187288519014578462397 1521445233194630466923399)
                      ·
                        rfl

theorem cell23_2963004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_2963004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963004 prefixEnd_2963004 := by exact prefixLift 2963004
  have htrace : WordTrace (prefixWord ++ tailWord_2963004) baseStart_2963004 baseEnd_2963004 := by
    simpa [prefixWord, tailWord_2963004, baseEnd_2963004] using wordTrace_append hprefix tailTrace_2963004
  have hstable : (prefixWord ++ tailWord_2963004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963004).length < 2 ^ (prefixWord ++ tailWord_2963004).sum := by decide
  have hdescent : baseEnd_2963004 < baseStart_2963004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963014 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2963014 : Nat := 118140960795 + 2963014 * 2 ^ 59
def prefixEnd_2963014 : Nat := 4983230072969 + 3 ^ 40 * 2963014 * 2
def baseEnd_2963014 : Nat := 1521450368001175427798353

theorem tailTrace_2963014 : CollatzResearch.WordTrace tailWord_2963014 prefixEnd_2963014 1521450368001175427798353 := by
  unfold tailWord_2963014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377187465234806104631503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72046665925009196898805397 3377187465234806104631503)
  ·
    refine ⟨5065781197852209156947255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3377187465234806104631503 5065781197852209156947255)
    ·
      refine ⟨7598671796778313735420883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5065781197852209156947255 7598671796778313735420883)
      ·
        refine ⟨11398007695167470603131325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7598671796778313735420883 11398007695167470603131325)
        ·
          refine ⟨4274252885687801476174247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11398007695167470603131325 4274252885687801476174247)
          ·
            refine ⟨6411379328531702214261371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274252885687801476174247 6411379328531702214261371)
            ·
              refine ⟨9617068992797553321392057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6411379328531702214261371 9617068992797553321392057)
              ·
                refine ⟨7212801744598164991044043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9617068992797553321392057 7212801744598164991044043)
                ·
                  refine ⟨10819202616897247486566065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7212801744598164991044043 10819202616897247486566065)
                  ·
                    refine ⟨8114401962672935614924549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10819202616897247486566065 8114401962672935614924549)
                    ·
                      refine ⟨1521450368001175427798353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8114401962672935614924549 1521450368001175427798353)
                      ·
                        rfl

theorem cell23_2963014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2963014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963014 prefixEnd_2963014 := by exact prefixLift 2963014
  have htrace : WordTrace (prefixWord ++ tailWord_2963014) baseStart_2963014 baseEnd_2963014 := by
    simpa [prefixWord, tailWord_2963014, baseEnd_2963014] using wordTrace_append hprefix tailTrace_2963014
  have hstable : (prefixWord ++ tailWord_2963014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963014).length < 2 ^ (prefixWord ++ tailWord_2963014).sum := by decide
  have hdescent : baseEnd_2963014 < baseStart_2963014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963021 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_2963021 : Nat := 118140960795 + 2963021 * 2 ^ 59
def prefixEnd_2963021 : Nat := 4983230072969 + 3 ^ 40 * 2963021 * 2
def baseEnd_2963021 : Nat := 1521453962365756900410821

theorem tailTrace_2963021 : CollatzResearch.WordTrace tailWord_2963021 prefixEnd_2963021 1521453962365756900410821 := by
  unfold tailWord_2963021
  simp only [CollatzResearch.WordTrace]
  refine ⟨108070254198488435543712917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72046836132325623695808611 108070254198488435543712917)
  ·
    refine ⟨5065793165554145416111543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108070254198488435543712917 5065793165554145416111543)
    ·
      refine ⟨7598689748331218124167315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5065793165554145416111543 7598689748331218124167315)
      ·
        refine ⟨11398034622496827186250973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7598689748331218124167315 11398034622496827186250973)
        ·
          refine ⟨4274262983436310194844115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11398034622496827186250973 4274262983436310194844115)
          ·
            refine ⟨6411394475154465292266173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274262983436310194844115 6411394475154465292266173)
            ·
              refine ⟨2404272928182924484599815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6411394475154465292266173 2404272928182924484599815)
              ·
                refine ⟨3606409392274386726899723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404272928182924484599815 3606409392274386726899723)
                ·
                  refine ⟨5409614088411580090349585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3606409392274386726899723 5409614088411580090349585)
                  ·
                    refine ⟨4057210566308685067762189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5409614088411580090349585 4057210566308685067762189)
                    ·
                      refine ⟨1521453962365756900410821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4057210566308685067762189 1521453962365756900410821)
                      ·
                        rfl

theorem cell23_2963021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_2963021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963021 prefixEnd_2963021 := by exact prefixLift 2963021
  have htrace : WordTrace (prefixWord ++ tailWord_2963021) baseStart_2963021 baseEnd_2963021 := by
    simpa [prefixWord, tailWord_2963021, baseEnd_2963021] using wordTrace_append hprefix tailTrace_2963021
  have hstable : (prefixWord ++ tailWord_2963021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963021).length < 2 ^ (prefixWord ++ tailWord_2963021).sum := by decide
  have hdescent : baseEnd_2963021 < baseStart_2963021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963040 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 5, 4, 2]
def baseStart_2963040 : Nat := 118140960795 + 2963040 * 2 ^ 59
def prefixEnd_2963040 : Nat := 4983230072969 + 3 ^ 40 * 2963040 * 2
def baseEnd_2963040 : Nat := 1521463718498192326073233

theorem tailTrace_2963040 : CollatzResearch.WordTrace tailWord_2963040 prefixEnd_2963040 1521463718498192326073233 := by
  unfold tailWord_2963040
  simp only [CollatzResearch.WordTrace]
  refine ⟨54035473592709800894327287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72047298123613067859103049 54035473592709800894327287)
  ·
    refine ⟨81053210389064701341490931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54035473592709800894327287 81053210389064701341490931)
    ·
      refine ⟨121579815583597052012236397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81053210389064701341490931 121579815583597052012236397)
      ·
        refine ⟨45592430843848894504588649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121579815583597052012236397 45592430843848894504588649)
        ·
          refine ⟨34194323132886670878441487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45592430843848894504588649 34194323132886670878441487)
          ·
            refine ⟨51291484699330006317662231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34194323132886670878441487 51291484699330006317662231)
            ·
              refine ⟨76937227048995009476493347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51291484699330006317662231 76937227048995009476493347)
              ·
                refine ⟨115405840573492514214740021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76937227048995009476493347 115405840573492514214740021)
                ·
                  refine ⟨10819297553764923207631877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 115405840573492514214740021 10819297553764923207631877)
                  ·
                    refine ⟨2028618291330923101430977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10819297553764923207631877 2028618291330923101430977)
                    ·
                      refine ⟨1521463718498192326073233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028618291330923101430977 1521463718498192326073233)
                      ·
                        rfl

theorem cell23_2963040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_2963040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963040 prefixEnd_2963040 := by exact prefixLift 2963040
  have htrace : WordTrace (prefixWord ++ tailWord_2963040) baseStart_2963040 baseEnd_2963040 := by
    simpa [prefixWord, tailWord_2963040, baseEnd_2963040] using wordTrace_append hprefix tailTrace_2963040
  have hstable : (prefixWord ++ tailWord_2963040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963040).length < 2 ^ (prefixWord ++ tailWord_2963040).sum := by decide
  have hdescent : baseEnd_2963040 < baseStart_2963040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963050 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_2963050 : Nat := 118140960795 + 2963050 * 2 ^ 59
def prefixEnd_2963050 : Nat := 4983230072969 + 3 ^ 40 * 2963050 * 2
def baseEnd_2963050 : Nat := 507156284434912428982729

theorem tailTrace_2963050 : CollatzResearch.WordTrace tailWord_2963050 prefixEnd_2963050 507156284434912428982729 := by
  unfold tailWord_2963050
  simp only [CollatzResearch.WordTrace]
  refine ⟨27017827978845843374129651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72047541276922248997679069 27017827978845843374129651)
  ·
    refine ⟨40526741968268765061194477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27017827978845843374129651 40526741968268765061194477)
    ·
      refine ⟨15197528238100786897947929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40526741968268765061194477 15197528238100786897947929)
      ·
        refine ⟨11398146178575590173460947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15197528238100786897947929 11398146178575590173460947)
        ·
          refine ⟨17097219267863385260191421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11398146178575590173460947 17097219267863385260191421)
          ·
            refine ⟨6411457225448769472571783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17097219267863385260191421 6411457225448769472571783)
            ·
              refine ⟨9617185838173154208857675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6411457225448769472571783 9617185838173154208857675)
              ·
                refine ⟨14425778757259731313286513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9617185838173154208857675 14425778757259731313286513)
                ·
                  refine ⟨10819334067944798484964885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14425778757259731313286513 10819334067944798484964885)
                  ·
                    refine ⟨507156284434912428982729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10819334067944798484964885 507156284434912428982729)
                    ·
                      rfl

theorem cell23_2963050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_2963050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963050 prefixEnd_2963050 := by exact prefixLift 2963050
  have htrace : WordTrace (prefixWord ++ tailWord_2963050) baseStart_2963050 baseEnd_2963050 := by
    simpa [prefixWord, tailWord_2963050, baseEnd_2963050] using wordTrace_append hprefix tailTrace_2963050
  have hstable : (prefixWord ++ tailWord_2963050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963050).length < 2 ^ (prefixWord ++ tailWord_2963050).sum := by decide
  have hdescent : baseEnd_2963050 < baseStart_2963050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963123 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 2, 8]
def baseStart_2963123 : Nat := 118140960795 + 2963123 * 2 ^ 59
def prefixEnd_2963123 : Nat := 4983230072969 + 3 ^ 40 * 2963123 * 2
def baseEnd_2963123 : Nat := 507168779130838500445117

theorem tailTrace_2963123 : CollatzResearch.WordTrace tailWord_2963123 prefixEnd_2963123 507168779130838500445117 := by
  unfold tailWord_2963123
  simp only [CollatzResearch.WordTrace]
  refine ⟨108073974444118906963926023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72049316296079271309284015 108073974444118906963926023)
  ·
    refine ⟨162110961666178360445889035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108073974444118906963926023 162110961666178360445889035)
    ·
      refine ⟨243166442499267540668833553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162110961666178360445889035 243166442499267540668833553)
      ·
        refine ⟨182374831874450655501625165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243166442499267540668833553 182374831874450655501625165)
        ·
          refine ⟨68390561952918995813109437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182374831874450655501625165 68390561952918995813109437)
          ·
            refine ⟨25646460732344623429916039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68390561952918995813109437 25646460732344623429916039)
            ·
              refine ⟨38469691098516935144874059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25646460732344623429916039 38469691098516935144874059)
              ·
                refine ⟨57704536647775402717311089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38469691098516935144874059 57704536647775402717311089)
                ·
                  refine ⟨43278402485831552037983317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57704536647775402717311089 43278402485831552037983317)
                  ·
                    refine ⟨507168779130838500445117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43278402485831552037983317 507168779130838500445117)
                    ·
                      rfl

theorem cell23_2963123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 8].length) (baseStart_2963123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963123 prefixEnd_2963123 := by exact prefixLift 2963123
  have htrace : WordTrace (prefixWord ++ tailWord_2963123) baseStart_2963123 baseEnd_2963123 := by
    simpa [prefixWord, tailWord_2963123, baseEnd_2963123] using wordTrace_append hprefix tailTrace_2963123
  have hstable : (prefixWord ++ tailWord_2963123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963123).length < 2 ^ (prefixWord ++ tailWord_2963123).sum := by decide
  have hdescent : baseEnd_2963123 < baseStart_2963123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963130 : List Nat := [3, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_2963130 : Nat := 118140960795 + 2963130 * 2 ^ 59
def prefixEnd_2963130 : Nat := 4983230072969 + 3 ^ 40 * 2963130 * 2
def baseEnd_2963130 : Nat := 1521509931757096973947819

theorem tailTrace_2963130 : CollatzResearch.WordTrace tailWord_2963130 prefixEnd_2963130 1521509931757096973947819 := by
  unfold tailWord_2963130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27018557438773386789857711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72049486503395698106287229 27018557438773386789857711)
  ·
    refine ⟨40527836158160080184786567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27018557438773386789857711 40527836158160080184786567)
    ·
      refine ⟨60791754237240120277179851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40527836158160080184786567 60791754237240120277179851)
      ·
        refine ⟨91187631355860180415769777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60791754237240120277179851 91187631355860180415769777)
        ·
          refine ⟨68390723516895135311827333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91187631355860180415769777 68390723516895135311827333)
          ·
            refine ⟨12823260659417837870967625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68390723516895135311827333 12823260659417837870967625)
            ·
              refine ⟨9617445494563378403225719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12823260659417837870967625 9617445494563378403225719)
              ·
                refine ⟨14426168241845067604838579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9617445494563378403225719 14426168241845067604838579)
                ·
                  refine ⟨21639252362767601407257869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14426168241845067604838579 21639252362767601407257869)
                  ·
                    refine ⟨8114719636037850527721701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21639252362767601407257869 8114719636037850527721701)
                    ·
                      refine ⟨1521509931757096973947819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8114719636037850527721701 1521509931757096973947819)
                      ·
                        rfl

theorem cell23_2963130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_2963130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963130 prefixEnd_2963130 := by exact prefixLift 2963130
  have htrace : WordTrace (prefixWord ++ tailWord_2963130) baseStart_2963130 baseEnd_2963130 := by
    simpa [prefixWord, tailWord_2963130, baseEnd_2963130] using wordTrace_append hprefix tailTrace_2963130
  have hstable : (prefixWord ++ tailWord_2963130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963130).length < 2 ^ (prefixWord ++ tailWord_2963130).sum := by decide
  have hdescent : baseEnd_2963130 < baseStart_2963130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963180 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 3]
def baseStart_2963180 : Nat := 118140960795 + 2963180 * 2 ^ 59
def prefixEnd_2963180 : Nat := 4983230072969 + 3 ^ 40 * 2963180 * 2
def baseEnd_2963180 : Nat := 1521535605789821778322589

theorem tailTrace_2963180 : CollatzResearch.WordTrace tailWord_2963180 prefixEnd_2963180 1521535605789821778322589 := by
  unfold tailWord_2963180
  simp only [CollatzResearch.WordTrace]
  refine ⟨54038026702456202849375497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72050702269941603799167329 54038026702456202849375497)
  ·
    refine ⟨40528520026842152137031623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54038026702456202849375497 40528520026842152137031623)
    ·
      refine ⟨60792780040263228205547435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40528520026842152137031623 60792780040263228205547435)
      ·
        refine ⟨91189170060394842308321153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60792780040263228205547435 91189170060394842308321153)
        ·
          refine ⟨68391877545296131731240865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91189170060394842308321153 68391877545296131731240865)
          ·
            refine ⟨51293908158972098798430649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68391877545296131731240865 51293908158972098798430649)
            ·
              refine ⟨38470431119229074098822987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51293908158972098798430649 38470431119229074098822987)
              ·
                refine ⟨57705646678843611148234481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38470431119229074098822987 57705646678843611148234481)
                ·
                  refine ⟨43279235009132708361175861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57705646678843611148234481 43279235009132708361175861)
                  ·
                    refine ⟨4057428282106191408860237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 43279235009132708361175861 4057428282106191408860237)
                    ·
                      refine ⟨1521535605789821778322589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4057428282106191408860237 1521535605789821778322589)
                      ·
                        rfl

theorem cell23_2963180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 3].length) (baseStart_2963180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963180 prefixEnd_2963180 := by exact prefixLift 2963180
  have htrace : WordTrace (prefixWord ++ tailWord_2963180) baseStart_2963180 baseEnd_2963180 := by
    simpa [prefixWord, tailWord_2963180, baseEnd_2963180] using wordTrace_append hprefix tailTrace_2963180
  have hstable : (prefixWord ++ tailWord_2963180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963180).length < 2 ^ (prefixWord ++ tailWord_2963180).sum := by decide
  have hdescent : baseEnd_2963180 < baseStart_2963180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963197 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 7, 1, 3]
def baseStart_2963197 : Nat := 118140960795 + 2963197 * 2 ^ 59
def prefixEnd_2963197 : Nat := 4983230072969 + 3 ^ 40 * 2963197 * 2
def baseEnd_2963197 : Nat := 1521544334960948211810011

theorem tailTrace_2963197 : CollatzResearch.WordTrace tailWord_2963197 prefixEnd_2963197 1521544334960948211810011 := by
  unfold tailWord_2963197
  simp only [CollatzResearch.WordTrace]
  refine ⟨108076673445850817602119845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72051115630567211734746563 108076673445850817602119845)
  ·
    refine ⟨20264376271097028300397471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108076673445850817602119845 20264376271097028300397471)
    ·
      refine ⟨30396564406645542450596207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20264376271097028300397471 30396564406645542450596207)
      ·
        refine ⟨45594846609968313675894311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30396564406645542450596207 45594846609968313675894311)
        ·
          refine ⟨68392269914952470513841467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45594846609968313675894311 68392269914952470513841467)
          ·
            refine ⟨102588404872428705770762201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68392269914952470513841467 102588404872428705770762201)
            ·
              refine ⟨76941303654321529328071651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102588404872428705770762201 76941303654321529328071651)
              ·
                refine ⟨115411955481482293992107477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76941303654321529328071651 115411955481482293992107477)
                ·
                  refine ⟨2704967706597241265440019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 115411955481482293992107477 2704967706597241265440019)
                  ·
                    refine ⟨4057451559895861898160029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2704967706597241265440019 4057451559895861898160029)
                    ·
                      refine ⟨1521544334960948211810011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4057451559895861898160029 1521544334960948211810011)
                      ·
                        rfl

theorem cell23_2963197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_2963197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963197 prefixEnd_2963197 := by exact prefixLift 2963197
  have htrace : WordTrace (prefixWord ++ tailWord_2963197) baseStart_2963197 baseEnd_2963197 := by
    simpa [prefixWord, tailWord_2963197, baseEnd_2963197] using wordTrace_append hprefix tailTrace_2963197
  have hstable : (prefixWord ++ tailWord_2963197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963197).length < 2 ^ (prefixWord ++ tailWord_2963197).sum := by decide
  have hdescent : baseEnd_2963197 < baseStart_2963197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963237 : List Nat := [1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_2963237 : Nat := 118140960795 + 2963237 * 2 ^ 59
def prefixEnd_2963237 : Nat := 4983230072969 + 3 ^ 40 * 2963237 * 2
def baseEnd_2963237 : Nat := 1521564874187128055309827

theorem tailTrace_2963237 : CollatzResearch.WordTrace tailWord_2963237 prefixEnd_2963237 1521564874187128055309827 := by
  unfold tailWord_2963237
  simp only [CollatzResearch.WordTrace]
  refine ⟨108078132365705904433575965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72052088243803936289050643 108078132365705904433575965)
  ·
    refine ⟨40529299637139714162590987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108078132365705904433575965 40529299637139714162590987)
    ·
      refine ⟨60793949455709571243886481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40529299637139714162590987 60793949455709571243886481)
      ·
        refine ⟨45595462091782178432914861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60793949455709571243886481 45595462091782178432914861)
        ·
          refine ⟨17098298284418316912343073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45595462091782178432914861 17098298284418316912343073)
          ·
            refine ⟨12823723713313737684257305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17098298284418316912343073 12823723713313737684257305)
            ·
              refine ⟨9617792784985303263192979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12823723713313737684257305 9617792784985303263192979)
              ·
                refine ⟨14426689177477954894789469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9617792784985303263192979 14426689177477954894789469)
                ·
                  refine ⟨5410008441554233085546051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14426689177477954894789469 5410008441554233085546051)
                  ·
                    refine ⟨8115012662331349628319077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5410008441554233085546051 8115012662331349628319077)
                    ·
                      refine ⟨1521564874187128055309827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8115012662331349628319077 1521564874187128055309827)
                      ·
                        rfl

theorem cell23_2963237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_2963237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963237 prefixEnd_2963237 := by exact prefixLift 2963237
  have htrace : WordTrace (prefixWord ++ tailWord_2963237) baseStart_2963237 baseEnd_2963237 := by
    simpa [prefixWord, tailWord_2963237, baseEnd_2963237] using wordTrace_append hprefix tailTrace_2963237
  have hstable : (prefixWord ++ tailWord_2963237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963237).length < 2 ^ (prefixWord ++ tailWord_2963237).sum := by decide
  have hdescent : baseEnd_2963237 < baseStart_2963237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963251 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 1, 5]
def baseStart_2963251 : Nat := 118140960795 + 2963251 * 2 ^ 59
def prefixEnd_2963251 : Nat := 4983230072969 + 3 ^ 40 * 2963251 * 2
def baseEnd_2963251 : Nat := 507190687638763666844921

theorem tailTrace_2963251 : CollatzResearch.WordTrace tailWord_2963251 prefixEnd_2963251 507190687638763666844921 := by
  unfold tailWord_2963251
  simp only [CollatzResearch.WordTrace]
  refine ⟨108078642987655184824585607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72052428658436789883057071 108078642987655184824585607)
  ·
    refine ⟨162117964481482777236878411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108078642987655184824585607 162117964481482777236878411)
    ·
      refine ⟨243176946722224165855317617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162117964481482777236878411 243176946722224165855317617)
      ·
        refine ⟨182382710041668124391488213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243176946722224165855317617 182382710041668124391488213)
        ·
          refine ⟨4274594766601596665425505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 182382710041668124391488213 4274594766601596665425505)
          ·
            refine ⟨3205946074951197499069129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4274594766601596665425505 3205946074951197499069129)
            ·
              refine ⟨2404459556213398124301847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3205946074951197499069129 2404459556213398124301847)
              ·
                refine ⟨3606689334320097186452771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404459556213398124301847 3606689334320097186452771)
                ·
                  refine ⟨5410034001480145779679157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3606689334320097186452771 5410034001480145779679157)
                  ·
                    refine ⟨507190687638763666844921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5410034001480145779679157 507190687638763666844921)
                    ·
                      rfl

theorem cell23_2963251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 1, 5].length) (baseStart_2963251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963251 prefixEnd_2963251 := by exact prefixLift 2963251
  have htrace : WordTrace (prefixWord ++ tailWord_2963251) baseStart_2963251 baseEnd_2963251 := by
    simpa [prefixWord, tailWord_2963251, baseEnd_2963251] using wordTrace_append hprefix tailTrace_2963251
  have hstable : (prefixWord ++ tailWord_2963251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963251).length < 2 ^ (prefixWord ++ tailWord_2963251).sum := by decide
  have hdescent : baseEnd_2963251 < baseStart_2963251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963281 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 2, 4]
def baseStart_2963281 : Nat := 118140960795 + 2963281 * 2 ^ 59
def prefixEnd_2963281 : Nat := 4983230072969 + 3 ^ 40 * 2963281 * 2
def baseEnd_2963281 : Nat := 507195822445308627719875

theorem tailTrace_2963281 : CollatzResearch.WordTrace tailWord_2963281 prefixEnd_2963281 507195822445308627719875 := by
  unfold tailWord_2963281
  simp only [CollatzResearch.WordTrace]
  refine ⟨108079737177546499948177697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72053158118364333298785131 108079737177546499948177697)
  ·
    refine ⟨81059802883159874961133273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108079737177546499948177697 81059802883159874961133273)
    ·
      refine ⟨60794852162369906220849955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81059802883159874961133273 60794852162369906220849955)
      ·
        refine ⟨91192278243554859331274933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60794852162369906220849955 91192278243554859331274933)
        ·
          refine ⟨8549276085333268062307025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91192278243554859331274933 8549276085333268062307025)
          ·
            refine ⟨6411957063999951046730269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8549276085333268062307025 6411957063999951046730269)
            ·
              refine ⟨2404483898999981642523851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6411957063999951046730269 2404483898999981642523851)
              ·
                refine ⟨3606725848499972463785777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2404483898999981642523851 3606725848499972463785777)
                ·
                  refine ⟨2705044386374979347839333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3606725848499972463785777 2705044386374979347839333)
                  ·
                    refine ⟨507195822445308627719875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2705044386374979347839333 507195822445308627719875)
                    ·
                      rfl

theorem cell23_2963281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_2963281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963281 prefixEnd_2963281 := by exact prefixLift 2963281
  have htrace : WordTrace (prefixWord ++ tailWord_2963281) baseStart_2963281 baseEnd_2963281 := by
    simpa [prefixWord, tailWord_2963281, baseEnd_2963281] using wordTrace_append hprefix tailTrace_2963281
  have hstable : (prefixWord ++ tailWord_2963281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963281).length < 2 ^ (prefixWord ++ tailWord_2963281).sum := by decide
  have hdescent : baseEnd_2963281 < baseStart_2963281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963284 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_2963284 : Nat := 118140960795 + 2963284 * 2 ^ 59
def prefixEnd_2963284 : Nat := 4983230072969 + 3 ^ 40 * 2963284 * 2
def baseEnd_2963284 : Nat := 1521589007777889371422111

theorem tailTrace_2963284 : CollatzResearch.WordTrace tailWord_2963284 prefixEnd_2963284 1521589007777889371422111 := by
  unfold tailWord_2963284
  simp only [CollatzResearch.WordTrace]
  refine ⟨54039923298267815730268453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72053231064357087640357937 54039923298267815730268453)
  ·
    refine ⟨10132485618425215449425335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54039923298267815730268453 10132485618425215449425335)
    ·
      refine ⟨15198728427637823174138003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10132485618425215449425335 15198728427637823174138003)
      ·
        refine ⟨22798092641456734761207005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15198728427637823174138003 22798092641456734761207005)
        ·
          refine ⟨8549284740546275535452627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22798092641456734761207005 8549284740546275535452627)
          ·
            refine ⟨12823927110819413303178941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8549284740546275535452627 12823927110819413303178941)
            ·
              refine ⟨4808972666557279988692103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12823927110819413303178941 4808972666557279988692103)
              ·
                refine ⟨7213458999835919983038155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4808972666557279988692103 7213458999835919983038155)
                ·
                  refine ⟨10820188499753879974557233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7213458999835919983038155 10820188499753879974557233)
                  ·
                    refine ⟨8115141374815409980917925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10820188499753879974557233 8115141374815409980917925)
                    ·
                      refine ⟨1521589007777889371422111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8115141374815409980917925 1521589007777889371422111)
                      ·
                        rfl

theorem cell23_2963284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_2963284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963284 prefixEnd_2963284 := by exact prefixLift 2963284
  have htrace : WordTrace (prefixWord ++ tailWord_2963284) baseStart_2963284 baseEnd_2963284 := by
    simpa [prefixWord, tailWord_2963284, baseEnd_2963284] using wordTrace_append hprefix tailTrace_2963284
  have hstable : (prefixWord ++ tailWord_2963284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963284).length < 2 ^ (prefixWord ++ tailWord_2963284).sum := by decide
  have hdescent : baseEnd_2963284 < baseStart_2963284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963304 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2963304 : Nat := 118140960795 + 2963304 * 2 ^ 59
def prefixEnd_2963304 : Nat := 4983230072969 + 3 ^ 40 * 2963304 * 2
def baseEnd_2963304 : Nat := 1521599277390979293172019

theorem tailTrace_2963304 : CollatzResearch.WordTrace tailWord_2963304 prefixEnd_2963304 1521599277390979293172019 := by
  unfold tailWord_2963304
  simp only [CollatzResearch.WordTrace]
  refine ⟨54040288028231587438132483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72053717370975449917509977 54040288028231587438132483)
  ·
    refine ⟨81060432042347381157198725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54040288028231587438132483 81060432042347381157198725)
    ·
      refine ⟨15198831007940133966974761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81060432042347381157198725 15198831007940133966974761)
      ·
        refine ⟨11399123255955100475231071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15198831007940133966974761 11399123255955100475231071)
        ·
          refine ⟨17098684883932650712846607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11399123255955100475231071 17098684883932650712846607)
          ·
            refine ⟨25648027325898976069269911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17098684883932650712846607 25648027325898976069269911)
            ·
              refine ⟨38472040988848464103904867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25648027325898976069269911 38472040988848464103904867)
              ·
                refine ⟨57708061483272696155857301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38472040988848464103904867 57708061483272696155857301)
                ·
                  refine ⟨2705065382028407632305811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57708061483272696155857301 2705065382028407632305811)
                  ·
                    refine ⟨4057598073042611448458717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2705065382028407632305811 4057598073042611448458717)
                    ·
                      refine ⟨1521599277390979293172019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4057598073042611448458717 1521599277390979293172019)
                      ·
                        rfl

theorem cell23_2963304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2963304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963304 prefixEnd_2963304 := by exact prefixLift 2963304
  have htrace : WordTrace (prefixWord ++ tailWord_2963304) baseStart_2963304 baseEnd_2963304 := by
    simpa [prefixWord, tailWord_2963304, baseEnd_2963304] using wordTrace_append hprefix tailTrace_2963304
  have hstable : (prefixWord ++ tailWord_2963304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963304).length < 2 ^ (prefixWord ++ tailWord_2963304).sum := by decide
  have hdescent : baseEnd_2963304 < baseStart_2963304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963314 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 5, 3, 2]
def baseStart_2963314 : Nat := 118140960795 + 2963314 * 2 ^ 59
def prefixEnd_2963314 : Nat := 4983230072969 + 3 ^ 40 * 2963314 * 2
def baseEnd_2963314 : Nat := 1521604412197524254046973

theorem tailTrace_2963314 : CollatzResearch.WordTrace tailWord_2963314 prefixEnd_2963314 1521604412197524254046973 := by
  unfold tailWord_2963314
  simp only [CollatzResearch.WordTrace]
  refine ⟨27020235196606736646032249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72053960524284631056085997 27020235196606736646032249)
  ·
    refine ⟨20265176397455052484524187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27020235196606736646032249 20265176397455052484524187)
    ·
      refine ⟨30397764596182578726786281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20265176397455052484524187 30397764596182578726786281)
      ·
        refine ⟨22798323447136934045089711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30397764596182578726786281 22798323447136934045089711)
        ·
          refine ⟨34197485170705401067634567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22798323447136934045089711 34197485170705401067634567)
          ·
            refine ⟨51296227756058101601451851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34197485170705401067634567 51296227756058101601451851)
            ·
              refine ⟨76944341634087152402177777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51296227756058101601451851 76944341634087152402177777)
              ·
                refine ⟨57708256225565364301633333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76944341634087152402177777 57708256225565364301633333)
                ·
                  refine ⟨5410149021146752903278125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57708256225565364301633333 5410149021146752903278125)
                  ·
                    refine ⟨2028805882930032338729297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5410149021146752903278125 2028805882930032338729297)
                    ·
                      refine ⟨1521604412197524254046973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028805882930032338729297 1521604412197524254046973)
                      ·
                        rfl

theorem cell23_2963314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_2963314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963314 prefixEnd_2963314 := by exact prefixLift 2963314
  have htrace : WordTrace (prefixWord ++ tailWord_2963314) baseStart_2963314 baseEnd_2963314 := by
    simpa [prefixWord, tailWord_2963314, baseEnd_2963314] using wordTrace_append hprefix tailTrace_2963314
  have hstable : (prefixWord ++ tailWord_2963314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963314).length < 2 ^ (prefixWord ++ tailWord_2963314).sum := by decide
  have hdescent : baseEnd_2963314 < baseStart_2963314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963317 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_2963317 : Nat := 118140960795 + 2963317 * 2 ^ 59
def prefixEnd_2963317 : Nat := 4983230072969 + 3 ^ 40 * 2963317 * 2
def baseEnd_2963317 : Nat := 1521605952639487742309459

theorem tailTrace_2963317 : CollatzResearch.WordTrace tailWord_2963317 prefixEnd_2963317 1521605952639487742309459 := by
  unfold tailWord_2963317
  simp only [CollatzResearch.WordTrace]
  refine ⟨108081050205416078096488205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72054033470277385397658803 108081050205416078096488205)
  ·
    refine ⟨40530393827031029286183077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108081050205416078096488205 40530393827031029286183077)
    ·
      refine ⟨7599448842568317991159327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40530393827031029286183077 7599448842568317991159327)
      ·
        refine ⟨11399173263852476986738991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7599448842568317991159327 11399173263852476986738991)
        ·
          refine ⟨17098759895778715480108487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11399173263852476986738991 17098759895778715480108487)
          ·
            refine ⟨25648139843668073220162731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17098759895778715480108487 25648139843668073220162731)
            ·
              refine ⟨38472209765502109830244097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25648139843668073220162731 38472209765502109830244097)
              ·
                refine ⟨28854157324126582372683073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38472209765502109830244097 28854157324126582372683073)
                ·
                  refine ⟨21640617993094936779512305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28854157324126582372683073 21640617993094936779512305)
                  ·
                    refine ⟨16230463494821202584634229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21640617993094936779512305 16230463494821202584634229)
                    ·
                      refine ⟨1521605952639487742309459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16230463494821202584634229 1521605952639487742309459)
                      ·
                        rfl

theorem cell23_2963317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_2963317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963317 prefixEnd_2963317 := by exact prefixLift 2963317
  have htrace : WordTrace (prefixWord ++ tailWord_2963317) baseStart_2963317 baseEnd_2963317 := by
    simpa [prefixWord, tailWord_2963317, baseEnd_2963317] using wordTrace_append hprefix tailTrace_2963317
  have hstable : (prefixWord ++ tailWord_2963317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963317).length < 2 ^ (prefixWord ++ tailWord_2963317).sum := by decide
  have hdescent : baseEnd_2963317 < baseStart_2963317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963338 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_2963338 : Nat := 118140960795 + 2963338 * 2 ^ 59
def prefixEnd_2963338 : Nat := 4983230072969 + 3 ^ 40 * 2963338 * 2
def baseEnd_2963338 : Nat := 1521616735733232160146863

theorem tailTrace_2963338 : CollatzResearch.WordTrace tailWord_2963338 prefixEnd_2963338 1521616735733232160146863 := by
  unfold tailWord_2963338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27020454034584999670750667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72054544092226665788668445 27020454034584999670750667)
  ·
    refine ⟨40530681051877499506126001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27020454034584999670750667 40530681051877499506126001)
    ·
      refine ⟨30398010788908124629594501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40530681051877499506126001 30398010788908124629594501)
      ·
        refine ⟨5699627022920273368048969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30398010788908124629594501 5699627022920273368048969)
        ·
          refine ⟨4274720267190205026036727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5699627022920273368048969 4274720267190205026036727)
          ·
            refine ⟨6412080400785307539055091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4274720267190205026036727 6412080400785307539055091)
            ·
              refine ⟨9618120601177961308582637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6412080400785307539055091 9618120601177961308582637)
              ·
                refine ⟨3606795225441735490718489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9618120601177961308582637 3606795225441735490718489)
                ·
                  refine ⟨2705096419081301618038867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3606795225441735490718489 2705096419081301618038867)
                  ·
                    refine ⟨4057644628621952427058301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2705096419081301618038867 4057644628621952427058301)
                    ·
                      refine ⟨1521616735733232160146863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4057644628621952427058301 1521616735733232160146863)
                      ·
                        rfl

theorem cell23_2963338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_2963338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963338 prefixEnd_2963338 := by exact prefixLift 2963338
  have htrace : WordTrace (prefixWord ++ tailWord_2963338) baseStart_2963338 baseEnd_2963338 := by
    simpa [prefixWord, tailWord_2963338, baseEnd_2963338] using wordTrace_append hprefix tailTrace_2963338
  have hstable : (prefixWord ++ tailWord_2963338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963338).length < 2 ^ (prefixWord ++ tailWord_2963338).sum := by decide
  have hdescent : baseEnd_2963338 < baseStart_2963338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963348 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_2963348 : Nat := 118140960795 + 2963348 * 2 ^ 59
def prefixEnd_2963348 : Nat := 4983230072969 + 3 ^ 40 * 2963348 * 2
def baseEnd_2963348 : Nat := 1521621870539777121021817

theorem tailTrace_2963348 : CollatzResearch.WordTrace tailWord_2963348 prefixEnd_2963348 1521621870539777121021817 := by
  unfold tailWord_2963348
  simp only [CollatzResearch.WordTrace]
  refine ⟨54041090434151885195433349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72054787245535846927244465 54041090434151885195433349)
  ·
    refine ⟨10132704456403478474143753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54041090434151885195433349 10132704456403478474143753)
    ·
      refine ⟨7599528342302608855607815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10132704456403478474143753 7599528342302608855607815)
      ·
        refine ⟨11399292513453913283411723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7599528342302608855607815 11399292513453913283411723)
        ·
          refine ⟨17098938770180869925117585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11399292513453913283411723 17098938770180869925117585)
          ·
            refine ⟨12824204077635652443838189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17098938770180869925117585 12824204077635652443838189)
            ·
              refine ⟨4809076529113369666439321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12824204077635652443838189 4809076529113369666439321)
              ·
                refine ⟨3606807396835027249829491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4809076529113369666439321 3606807396835027249829491)
                ·
                  refine ⟨5410211095252540874744237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3606807396835027249829491 5410211095252540874744237)
                  ·
                    refine ⟨2028829160719702828029089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5410211095252540874744237 2028829160719702828029089)
                    ·
                      refine ⟨1521621870539777121021817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2028829160719702828029089 1521621870539777121021817)
                      ·
                        rfl

theorem cell23_2963348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_2963348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963348 prefixEnd_2963348 := by exact prefixLift 2963348
  have htrace : WordTrace (prefixWord ++ tailWord_2963348) baseStart_2963348 baseEnd_2963348 := by
    simpa [prefixWord, tailWord_2963348, baseEnd_2963348] using wordTrace_append hprefix tailTrace_2963348
  have hstable : (prefixWord ++ tailWord_2963348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963348).length < 2 ^ (prefixWord ++ tailWord_2963348).sum := by decide
  have hdescent : baseEnd_2963348 < baseStart_2963348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963384 : List Nat := [2, 1, 2, 1, 2, 3, 3, 4, 5]
def baseStart_2963384 : Nat := 118140960795 + 2963384 * 2 ^ 59
def prefixEnd_2963384 : Nat := 4983230072969 + 3 ^ 40 * 2963384 * 2
def baseEnd_2963384 : Nat := 169071150649259886685739

theorem tailTrace_2963384 : CollatzResearch.WordTrace tailWord_2963384 prefixEnd_2963384 169071150649259886685739 := by
  unfold tailWord_2963384
  simp only [CollatzResearch.WordTrace]
  refine ⟨54041746948086674269588603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72055662597448899026118137 54041746948086674269588603)
  ·
    refine ⟨81062620422130011404382905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54041746948086674269588603 81062620422130011404382905)
    ·
      refine ⟨60796965316597508553287179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81062620422130011404382905 60796965316597508553287179)
      ·
        refine ⟨91195447974896262829930769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60796965316597508553287179 91195447974896262829930769)
        ·
          refine ⟨68396585981172197122448077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91195447974896262829930769 68396585981172197122448077)
          ·
            refine ⟨25648719742939573920918029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68396585981172197122448077 25648719742939573920918029)
            ·
              refine ⟨9618269903602340220344261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25648719742939573920918029 9618269903602340220344261)
              ·
                refine ⟨1803425606925438791314549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9618269903602340220344261 1803425606925438791314549)
                ·
                  refine ⟨169071150649259886685739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1803425606925438791314549 169071150649259886685739)
                  ·
                    rfl

theorem cell23_2963384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 5].length) (baseStart_2963384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963384 prefixEnd_2963384 := by exact prefixLift 2963384
  have htrace : WordTrace (prefixWord ++ tailWord_2963384) baseStart_2963384 baseEnd_2963384 := by
    simpa [prefixWord, tailWord_2963384, baseEnd_2963384] using wordTrace_append hprefix tailTrace_2963384
  have hstable : (prefixWord ++ tailWord_2963384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963384).length < 2 ^ (prefixWord ++ tailWord_2963384).sum := by decide
  have hdescent : baseEnd_2963384 < baseStart_2963384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963434 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_2963434 : Nat := 118140960795 + 2963434 * 2 ^ 59
def prefixEnd_2963434 : Nat := 4983230072969 + 3 ^ 40 * 2963434 * 2
def baseEnd_2963434 : Nat := 1521666029876063784546421

theorem tailTrace_2963434 : CollatzResearch.WordTrace tailWord_2963434 prefixEnd_2963434 1521666029876063784546421 := by
  unfold tailWord_2963434
  simp only [CollatzResearch.WordTrace]
  refine ⟨27021329386498051769624339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72056878363994804718998237 27021329386498051769624339)
  ·
    refine ⟨40531994079747077654436509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27021329386498051769624339 40531994079747077654436509)
    ·
      refine ⟨15199497779905154120413691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40531994079747077654436509 15199497779905154120413691)
      ·
        refine ⟨22799246669857731180620537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15199497779905154120413691 22799246669857731180620537)
        ·
          refine ⟨17099435002393298385465403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22799246669857731180620537 17099435002393298385465403)
          ·
            refine ⟨25649152503589947578198105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17099435002393298385465403 25649152503589947578198105)
            ·
              refine ⟨19236864377692460683648579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25649152503589947578198105 19236864377692460683648579)
              ·
                refine ⟨28855296566538691025472869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19236864377692460683648579 28855296566538691025472869)
                ·
                  refine ⟨5410368106226004567276163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28855296566538691025472869 5410368106226004567276163)
                  ·
                    refine ⟨8115552159339006850914245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5410368106226004567276163 8115552159339006850914245)
                    ·
                      refine ⟨1521666029876063784546421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8115552159339006850914245 1521666029876063784546421)
                      ·
                        rfl

theorem cell23_2963434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_2963434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963434 prefixEnd_2963434 := by exact prefixLift 2963434
  have htrace : WordTrace (prefixWord ++ tailWord_2963434) baseStart_2963434 baseEnd_2963434 := by
    simpa [prefixWord, tailWord_2963434, baseEnd_2963434] using wordTrace_append hprefix tailTrace_2963434
  have hstable : (prefixWord ++ tailWord_2963434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963434).length < 2 ^ (prefixWord ++ tailWord_2963434).sum := by decide
  have hdescent : baseEnd_2963434 < baseStart_2963434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963469 : List Nat := [1, 7, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2963469 : Nat := 118140960795 + 2963469 * 2 ^ 59
def prefixEnd_2963469 : Nat := 4983230072969 + 3 ^ 40 * 2963469 * 2
def baseEnd_2963469 : Nat := 169076000188774571956529

theorem tailTrace_2963469 : CollatzResearch.WordTrace tailWord_2963469 prefixEnd_2963469 169076000188774571956529 := by
  unfold tailWord_2963469
  simp only [CollatzResearch.WordTrace]
  refine ⟨108086594100865408056021461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72057729400576938704014307 108086594100865408056021461)
  ·
    refine ⟨2533279549239033001313003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 108086594100865408056021461 2533279549239033001313003)
    ·
      refine ⟨3799919323858549501969505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2533279549239033001313003 3799919323858549501969505)
      ·
        refine ⟨2849939492893912126477129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3799919323858549501969505 2849939492893912126477129)
        ·
          refine ⟨2137454619670434094857847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2849939492893912126477129 2137454619670434094857847)
          ·
            refine ⟨3206181929505651142286771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2137454619670434094857847 3206181929505651142286771)
            ·
              refine ⟨4809272894258476713430157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206181929505651142286771 4809272894258476713430157)
              ·
                refine ⟨1803477335346928767536309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4809272894258476713430157 1803477335346928767536309)
                ·
                  refine ⟨169076000188774571956529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1803477335346928767536309 169076000188774571956529)
                  ·
                    rfl

theorem cell23_2963469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2963469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963469 prefixEnd_2963469 := by exact prefixLift 2963469
  have htrace : WordTrace (prefixWord ++ tailWord_2963469) baseStart_2963469 baseEnd_2963469 := by
    simpa [prefixWord, tailWord_2963469, baseEnd_2963469] using wordTrace_append hprefix tailTrace_2963469
  have hstable : (prefixWord ++ tailWord_2963469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963469).length < 2 ^ (prefixWord ++ tailWord_2963469).sum := by decide
  have hdescent : baseEnd_2963469 < baseStart_2963469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2963495 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2963495 : Nat := 118140960795 + 2963495 * 2 ^ 59
def prefixEnd_2963495 : Nat := 4983230072969 + 3 ^ 40 * 2963495 * 2
def baseEnd_2963495 : Nat := 507232450731996015294547

theorem tailTrace_2963495 : CollatzResearch.WordTrace tailWord_2963495 prefixEnd_2963495 507232450731996015294547 := by
  unfold tailWord_2963495
  simp only [CollatzResearch.WordTrace]
  refine ⟨108087542398771214496467939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72058361599180809664311959 108087542398771214496467939)
  ·
    refine ⟨162131313598156821744701909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108087542398771214496467939 162131313598156821744701909)
    ·
      refine ⟨3799952662456800509641451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 162131313598156821744701909 3799952662456800509641451)
      ·
        refine ⟨5699928993685200764462177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3799952662456800509641451 5699928993685200764462177)
        ·
          refine ⟨4274946745263900573346633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5699928993685200764462177 4274946745263900573346633)
          ·
            refine ⟨3206210058947925430009975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4274946745263900573346633 3206210058947925430009975)
            ·
              refine ⟨4809315088421888145014963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3206210058947925430009975 4809315088421888145014963)
              ·
                refine ⟨7213972632632832217522445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4809315088421888145014963 7213972632632832217522445)
                ·
                  refine ⟨2705239737237312081570917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7213972632632832217522445 2705239737237312081570917)
                  ·
                    refine ⟨507232450731996015294547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2705239737237312081570917 507232450731996015294547)
                    ·
                      rfl

theorem cell23_2963495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2963495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2963495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2963495 prefixEnd_2963495 := by exact prefixLift 2963495
  have htrace : WordTrace (prefixWord ++ tailWord_2963495) baseStart_2963495 baseEnd_2963495 := by
    simpa [prefixWord, tailWord_2963495, baseEnd_2963495] using wordTrace_append hprefix tailTrace_2963495
  have hstable : (prefixWord ++ tailWord_2963495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2963495).length < 2 ^ (prefixWord ++ tailWord_2963495).sum := by decide
  have hdescent : baseEnd_2963495 < baseStart_2963495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2963495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
