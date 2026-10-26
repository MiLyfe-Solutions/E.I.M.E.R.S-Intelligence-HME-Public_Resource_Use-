import V185TrunkScan23Chunk0013

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_82123 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 3]
def baseStart_82123 : Nat := 118140960795 + 82123 * 2 ^ 59
def prefixEnd_82123 : Nat := 4983230072969 + 3 ^ 40 * 82123 * 2
def baseEnd_82123 : Nat := 42168571789287427084829

theorem tailTrace_82123 : CollatzResearch.WordTrace tailWord_82123 prefixEnd_82123 42168571789287427084829 := by
  unfold tailWord_82123
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995271881489871336883023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1996847920993247557922015 2995271881489871336883023)
  ·
    refine ⟨4492907822234807005324535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2995271881489871336883023 4492907822234807005324535)
    ·
      refine ⟨6739361733352210507986803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4492907822234807005324535 6739361733352210507986803)
      ·
        refine ⟨10109042600028315761980205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6739361733352210507986803 10109042600028315761980205)
        ·
          refine ⟨3790890975010618410742577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10109042600028315761980205 3790890975010618410742577)
          ·
            refine ⟨2843168231257963808056933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3790890975010618410742577 2843168231257963808056933)
            ·
              refine ⟨533094043360868214010675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2843168231257963808056933 533094043360868214010675)
              ·
                refine ⟨799641065041302321016013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533094043360868214010675 799641065041302321016013)
                ·
                  refine ⟨299865399390488370381005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799641065041302321016013 299865399390488370381005)
                  ·
                    refine ⟨112449524771433138892877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 299865399390488370381005 112449524771433138892877)
                    ·
                      refine ⟨42168571789287427084829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 112449524771433138892877 42168571789287427084829)
                      ·
                        rfl

theorem cell23_82123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 3].length) (baseStart_82123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82123 prefixEnd_82123 := by exact prefixLift 82123
  have htrace : WordTrace (prefixWord ++ tailWord_82123) baseStart_82123 baseEnd_82123 := by
    simpa [prefixWord, tailWord_82123, baseEnd_82123] using wordTrace_append hprefix tailTrace_82123
  have hstable : (prefixWord ++ tailWord_82123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82123).length < 2 ^ (prefixWord ++ tailWord_82123).sum := by decide
  have hdescent : baseEnd_82123 < baseStart_82123 := by decide
  rcases family_descends (prefixWord ++ tailWord_82123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82141 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_82141 : Nat := 118140960795 + 82141 * 2 ^ 59
def prefixEnd_82141 : Nat := 4983230072969 + 3 ^ 40 * 82141 * 2
def baseEnd_82141 : Nat := 42177814441068356659747

theorem tailTrace_82141 : CollatzResearch.WordTrace tailWord_82141 prefixEnd_82141 42177814441068356659747 := by
  unfold tailWord_82141
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995928395424660411038277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1997285596949773607358851 2995928395424660411038277)
  ·
    refine ⟨561736574142123827069677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2995928395424660411038277 561736574142123827069677)
    ·
      refine ⟨210651215303296435151129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 561736574142123827069677 210651215303296435151129)
      ·
        refine ⟨157988411477472326363347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210651215303296435151129 157988411477472326363347)
        ·
          refine ⟨236982617216208489545021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157988411477472326363347 236982617216208489545021)
          ·
            refine ⟨88868481456078183579383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236982617216208489545021 88868481456078183579383)
            ·
              refine ⟨133302722184117275369075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88868481456078183579383 133302722184117275369075)
              ·
                refine ⟨199954083276175913053613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133302722184117275369075 199954083276175913053613)
                ·
                  refine ⟨74982781228565967395105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199954083276175913053613 74982781228565967395105)
                  ·
                    refine ⟨56237085921424475546329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74982781228565967395105 56237085921424475546329)
                    ·
                      refine ⟨42177814441068356659747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56237085921424475546329 42177814441068356659747)
                      ·
                        rfl

theorem cell23_82141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_82141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82141 prefixEnd_82141 := by exact prefixLift 82141
  have htrace : WordTrace (prefixWord ++ tailWord_82141) baseStart_82141 baseEnd_82141 := by
    simpa [prefixWord, tailWord_82141, baseEnd_82141] using wordTrace_append hprefix tailTrace_82141
  have hstable : (prefixWord ++ tailWord_82141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82141).length < 2 ^ (prefixWord ++ tailWord_82141).sum := by decide
  have hdescent : baseEnd_82141 < baseStart_82141 := by decide
  rcases family_descends (prefixWord ++ tailWord_82141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82197 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 4, 2, 2]
def baseStart_82197 : Nat := 118140960795 + 82197 * 2 ^ 59
def prefixEnd_82197 : Nat := 4983230072969 + 3 ^ 40 * 82197 * 2
def baseEnd_82197 : Nat := 42206569357720137559489

theorem tailTrace_82197 : CollatzResearch.WordTrace tailWord_82197 prefixEnd_82197 42206569357720137559489 := by
  unfold tailWord_82197
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997970883221781975076845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1998647255481187983384563 2997970883221781975076845)
  ·
    refine ⟨1124239081208168240653817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2997970883221781975076845 1124239081208168240653817)
    ·
      refine ⟨843179310906126180490363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1124239081208168240653817 843179310906126180490363)
      ·
        refine ⟨1264768966359189270735545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843179310906126180490363 1264768966359189270735545)
        ·
          refine ⟨948576724769391953051659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1264768966359189270735545 948576724769391953051659)
          ·
            refine ⟨1422865087154087929577489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948576724769391953051659 1422865087154087929577489)
            ·
              refine ⟨1067148815365565947183117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422865087154087929577489 1067148815365565947183117)
              ·
                refine ⟨400180805762087230193669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1067148815365565947183117 400180805762087230193669)
                ·
                  refine ⟨75033901080391355661313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400180805762087230193669 75033901080391355661313)
                  ·
                    refine ⟨56275425810293516745985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75033901080391355661313 56275425810293516745985)
                    ·
                      refine ⟨42206569357720137559489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56275425810293516745985 42206569357720137559489)
                      ·
                        rfl

theorem cell23_82197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_82197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82197 prefixEnd_82197 := by exact prefixLift 82197
  have htrace : WordTrace (prefixWord ++ tailWord_82197) baseStart_82197 baseEnd_82197 := by
    simpa [prefixWord, tailWord_82197, baseEnd_82197] using wordTrace_append hprefix tailTrace_82197
  have hstable : (prefixWord ++ tailWord_82197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82197).length < 2 ^ (prefixWord ++ tailWord_82197).sum := by decide
  have hdescent : baseEnd_82197 < baseStart_82197 := by decide
  rcases family_descends (prefixWord ++ tailWord_82197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82210 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_82210 : Nat := 118140960795 + 82210 * 2 ^ 59
def prefixEnd_82210 : Nat := 4983230072969 + 3 ^ 40 * 82210 * 2
def baseEnd_82210 : Nat := 42213244606228586696929

theorem tailTrace_82210 : CollatzResearch.WordTrace tailWord_82210 prefixEnd_82210 42213244606228586696929 := by
  unfold tailWord_82210
  simp only [CollatzResearch.WordTrace]
  refine ⟨749611258043671298825021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1998963354783123463533389 749611258043671298825021)
  ·
    refine ⟨281104221766376737059383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 749611258043671298825021 281104221766376737059383)
    ·
      refine ⟨421656332649565105589075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281104221766376737059383 421656332649565105589075)
      ·
        refine ⟨632484498974347658383613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421656332649565105589075 632484498974347658383613)
        ·
          refine ⟨237181687115380371893855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 632484498974347658383613 237181687115380371893855)
          ·
            refine ⟨355772530673070557840783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237181687115380371893855 355772530673070557840783)
            ·
              refine ⟨533658796009605836761175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355772530673070557840783 533658796009605836761175)
              ·
                refine ⟨800488194014408755141763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533658796009605836761175 800488194014408755141763)
                ·
                  refine ⟨1200732291021613132712645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800488194014408755141763 1200732291021613132712645)
                  ·
                    refine ⟨225137304566552462383621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1200732291021613132712645 225137304566552462383621)
                    ·
                      refine ⟨42213244606228586696929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 225137304566552462383621 42213244606228586696929)
                      ·
                        rfl

theorem cell23_82210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_82210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82210 prefixEnd_82210 := by exact prefixLift 82210
  have htrace : WordTrace (prefixWord ++ tailWord_82210) baseStart_82210 baseEnd_82210 := by
    simpa [prefixWord, tailWord_82210, baseEnd_82210] using wordTrace_append hprefix tailTrace_82210
  have hstable : (prefixWord ++ tailWord_82210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82210).length < 2 ^ (prefixWord ++ tailWord_82210).sum := by decide
  have hdescent : baseEnd_82210 < baseStart_82210 := by decide
  rcases family_descends (prefixWord ++ tailWord_82210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82240 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 1, 7, 2]
def baseStart_82240 : Nat := 118140960795 + 82240 * 2 ^ 59
def prefixEnd_82240 : Nat := 4983230072969 + 3 ^ 40 * 82240 * 2
def baseEnd_82240 : Nat := 42228649025863469321791

theorem tailTrace_82240 : CollatzResearch.WordTrace tailWord_82240 prefixEnd_82240 42228649025863469321791 := by
  unfold tailWord_82240
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499769611033000159446087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1999692814710666879261449 1499769611033000159446087)
  ·
    refine ⟨2249654416549500239169131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1499769611033000159446087 2249654416549500239169131)
    ·
      refine ⟨3374481624824250358753697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2249654416549500239169131 3374481624824250358753697)
      ·
        refine ⟨2530861218618187769065273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3374481624824250358753697 2530861218618187769065273)
        ·
          refine ⟨1898145913963640826798955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2530861218618187769065273 1898145913963640826798955)
          ·
            refine ⟨2847218870945461240198433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898145913963640826798955 2847218870945461240198433)
            ·
              refine ⟨2135414153209095930148825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2847218870945461240198433 2135414153209095930148825)
              ·
                refine ⟨1601560614906821947611619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135414153209095930148825 1601560614906821947611619)
                ·
                  refine ⟨2402340922360232921417429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601560614906821947611619 2402340922360232921417429)
                  ·
                    refine ⟨56304865367817959095721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2402340922360232921417429 56304865367817959095721)
                    ·
                      refine ⟨42228649025863469321791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56304865367817959095721 42228649025863469321791)
                      ·
                        rfl

theorem cell23_82240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_82240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82240 prefixEnd_82240 := by exact prefixLift 82240
  have htrace : WordTrace (prefixWord ++ tailWord_82240) baseStart_82240 baseEnd_82240 := by
    simpa [prefixWord, tailWord_82240, baseEnd_82240] using wordTrace_append hprefix tailTrace_82240
  have hstable : (prefixWord ++ tailWord_82240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82240).length < 2 ^ (prefixWord ++ tailWord_82240).sum := by decide
  have hdescent : baseEnd_82240 < baseStart_82240 := by decide
  rcases family_descends (prefixWord ++ tailWord_82240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82243 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 5]
def baseStart_82243 : Nat := 118140960795 + 82243 * 2 ^ 59
def prefixEnd_82243 : Nat := 4983230072969 + 3 ^ 40 * 82243 * 2
def baseEnd_82243 : Nat := 42230189467826957584277

theorem tailTrace_82243 : CollatzResearch.WordTrace tailWord_82243 prefixEnd_82243 42230189467826957584277 := by
  unfold tailWord_82243
  simp only [CollatzResearch.WordTrace]
  refine ⟨2999648641055131831251383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1999765760703421220834255 2999648641055131831251383)
  ·
    refine ⟨4499472961582697746877075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2999648641055131831251383 4499472961582697746877075)
    ·
      refine ⟨6749209442374046620315613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4499472961582697746877075 6749209442374046620315613)
      ·
        refine ⟨2530953540890267482618355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6749209442374046620315613 2530953540890267482618355)
        ·
          refine ⟨3796430311335401223927533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2530953540890267482618355 3796430311335401223927533)
          ·
            refine ⟨1423661366750775458972825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3796430311335401223927533 1423661366750775458972825)
            ·
              refine ⟨1067746025063081594229619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1423661366750775458972825 1067746025063081594229619)
              ·
                refine ⟨1601619037594622391344429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067746025063081594229619 1601619037594622391344429)
                ·
                  refine ⟨600607139097983396754161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1601619037594622391344429 600607139097983396754161)
                  ·
                    refine ⟨450455354323487547565621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 600607139097983396754161 450455354323487547565621)
                    ·
                      refine ⟨42230189467826957584277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 450455354323487547565621 42230189467826957584277)
                      ·
                        rfl

theorem cell23_82243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_82243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82243 prefixEnd_82243 := by exact prefixLift 82243
  have htrace : WordTrace (prefixWord ++ tailWord_82243) baseStart_82243 baseEnd_82243 := by
    simpa [prefixWord, tailWord_82243, baseEnd_82243] using wordTrace_append hprefix tailTrace_82243
  have hstable : (prefixWord ++ tailWord_82243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82243).length < 2 ^ (prefixWord ++ tailWord_82243).sum := by decide
  have hdescent : baseEnd_82243 < baseStart_82243 := by decide
  rcases family_descends (prefixWord ++ tailWord_82243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82283 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 6]
def baseStart_82283 : Nat := 118140960795 + 82283 * 2 ^ 59
def prefixEnd_82283 : Nat := 4983230072969 + 3 ^ 40 * 82283 * 2
def baseEnd_82283 : Nat := 42250728694006801084093

theorem tailTrace_82283 : CollatzResearch.WordTrace tailWord_82283 prefixEnd_82283 42250728694006801084093 := by
  unfold tailWord_82283
  simp only [CollatzResearch.WordTrace]
  refine ⟨3001107560910218662707503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2000738373940145775138335 3001107560910218662707503)
  ·
    refine ⟨4501661341365327994061255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3001107560910218662707503 4501661341365327994061255)
    ·
      refine ⟨6752492012047991991091883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4501661341365327994061255 6752492012047991991091883)
      ·
        refine ⟨10128738018071987986637825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6752492012047991991091883 10128738018071987986637825)
        ·
          refine ⟨7596553513553990989978369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10128738018071987986637825 7596553513553990989978369)
          ·
            refine ⟨5697415135165493242483777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7596553513553990989978369 5697415135165493242483777)
            ·
              refine ⟨4273061351374119931862833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5697415135165493242483777 4273061351374119931862833)
              ·
                refine ⟨3204796013530589948897125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4273061351374119931862833 3204796013530589948897125)
                ·
                  refine ⟨600899252536985615418211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3204796013530589948897125 600899252536985615418211)
                  ·
                    refine ⟨901348878805478423127317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 600899252536985615418211 901348878805478423127317)
                    ·
                      refine ⟨42250728694006801084093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 901348878805478423127317 42250728694006801084093)
                      ·
                        rfl

theorem cell23_82283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 6].length) (baseStart_82283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82283 prefixEnd_82283 := by exact prefixLift 82283
  have htrace : WordTrace (prefixWord ++ tailWord_82283) baseStart_82283 baseEnd_82283 := by
    simpa [prefixWord, tailWord_82283, baseEnd_82283] using wordTrace_append hprefix tailTrace_82283
  have hstable : (prefixWord ++ tailWord_82283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82283).length < 2 ^ (prefixWord ++ tailWord_82283).sum := by decide
  have hdescent : baseEnd_82283 < baseStart_82283 := by decide
  rcases family_descends (prefixWord ++ tailWord_82283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82327 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 6]
def baseStart_82327 : Nat := 118140960795 + 82327 * 2 ^ 59
def prefixEnd_82327 : Nat := 4983230072969 + 3 ^ 40 * 82327 * 2
def baseEnd_82327 : Nat := 4697035760311625437099

theorem tailTrace_82327 : CollatzResearch.WordTrace tailWord_82327 prefixEnd_82327 4697035760311625437099 := by
  unfold tailWord_82327
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002712372750814177309235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2001808248500542784872823 3002712372750814177309235)
  ·
    refine ⟨4504068559126221265963853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3002712372750814177309235 4504068559126221265963853)
    ·
      refine ⟨1689025709672332974736445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4504068559126221265963853 1689025709672332974736445)
      ·
        refine ⟨633384641127124865526167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1689025709672332974736445 633384641127124865526167)
        ·
          refine ⟨950076961690687298289251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633384641127124865526167 950076961690687298289251)
          ·
            refine ⟨1425115442536030947433877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950076961690687298289251 1425115442536030947433877)
            ·
              refine ⟨66802286368876450660963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1425115442536030947433877 66802286368876450660963)
              ·
                refine ⟨100203429553314675991445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66802286368876450660963 100203429553314675991445)
                ·
                  refine ⟨4697035760311625437099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100203429553314675991445 4697035760311625437099)
                  ·
                    rfl

theorem cell23_82327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 6].length) (baseStart_82327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82327 prefixEnd_82327 := by exact prefixLift 82327
  have htrace : WordTrace (prefixWord ++ tailWord_82327) baseStart_82327 baseEnd_82327 := by
    simpa [prefixWord, tailWord_82327, baseEnd_82327] using wordTrace_append hprefix tailTrace_82327
  have hstable : (prefixWord ++ tailWord_82327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82327).length < 2 ^ (prefixWord ++ tailWord_82327).sum := by decide
  have hdescent : baseEnd_82327 < baseStart_82327 := by decide
  rcases family_descends (prefixWord ++ tailWord_82327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82407 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_82407 : Nat := 118140960795 + 82407 * 2 ^ 59
def prefixEnd_82407 : Nat := 4983230072969 + 3 ^ 40 * 82407 * 2
def baseEnd_82407 : Nat := 42314400295164315933523

theorem tailTrace_82407 : CollatzResearch.WordTrace tailWord_82407 prefixEnd_82407 42314400295164315933523 := by
  unfold tailWord_82407
  simp only [CollatzResearch.WordTrace]
  refine ⟨3005630212460987840221475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2003753474973991893480983 3005630212460987840221475)
  ·
    refine ⟨4508445318691481760332213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3005630212460987840221475 4508445318691481760332213)
    ·
      refine ⟨422666748627326415031145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4508445318691481760332213 422666748627326415031145)
      ·
        refine ⟨317000061470494811273359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422666748627326415031145 317000061470494811273359)
        ·
          refine ⟨475500092205742216910039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317000061470494811273359 475500092205742216910039)
          ·
            refine ⟨713250138308613325365059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475500092205742216910039 713250138308613325365059)
            ·
              refine ⟨1069875207462919988047589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713250138308613325365059 1069875207462919988047589)
              ·
                refine ⟨200601601399297497758923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1069875207462919988047589 200601601399297497758923)
                ·
                  refine ⟨300902402098946246638385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200601601399297497758923 300902402098946246638385)
                  ·
                    refine ⟨225676801574209684978789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 300902402098946246638385 225676801574209684978789)
                    ·
                      refine ⟨42314400295164315933523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 225676801574209684978789 42314400295164315933523)
                      ·
                        rfl

theorem cell23_82407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_82407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82407 prefixEnd_82407 := by exact prefixLift 82407
  have htrace : WordTrace (prefixWord ++ tailWord_82407) baseStart_82407 baseEnd_82407 := by
    simpa [prefixWord, tailWord_82407, baseEnd_82407] using wordTrace_append hprefix tailTrace_82407
  have hstable : (prefixWord ++ tailWord_82407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82407).length < 2 ^ (prefixWord ++ tailWord_82407).sum := by decide
  have hdescent : baseEnd_82407 < baseStart_82407 := by decide
  rcases family_descends (prefixWord ++ tailWord_82407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82421 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 4, 4]
def baseStart_82421 : Nat := 118140960795 + 82421 * 2 ^ 59
def prefixEnd_82421 : Nat := 4983230072969 + 3 ^ 40 * 82421 * 2
def baseEnd_82421 : Nat := 14107196341442420386153

theorem tailTrace_82421 : CollatzResearch.WordTrace tailWord_82421 prefixEnd_82421 14107196341442420386153 := by
  unfold tailWord_82421
  simp only [CollatzResearch.WordTrace]
  refine ⟨3006140834410268231231117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2004093889606845487487411 3006140834410268231231117)
  ·
    refine ⟨1127302812903850586711669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3006140834410268231231117 1127302812903850586711669)
    ·
      refine ⟨105684638709735992504219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1127302812903850586711669 105684638709735992504219)
      ·
        refine ⟨158526958064603988756329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105684638709735992504219 158526958064603988756329)
        ·
          refine ⟨118895218548452991567247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158526958064603988756329 118895218548452991567247)
          ·
            refine ⟨178342827822679487350871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118895218548452991567247 178342827822679487350871)
            ·
              refine ⟨267514241734019231026307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178342827822679487350871 267514241734019231026307)
              ·
                refine ⟨401271362601028846539461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267514241734019231026307 401271362601028846539461)
                ·
                  refine ⟨75238380487692908726149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 401271362601028846539461 75238380487692908726149)
                  ·
                    refine ⟨14107196341442420386153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75238380487692908726149 14107196341442420386153)
                    ·
                      rfl

theorem cell23_82421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_82421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82421 prefixEnd_82421 := by exact prefixLift 82421
  have htrace : WordTrace (prefixWord ++ tailWord_82421) baseStart_82421 baseEnd_82421 := by
    simpa [prefixWord, tailWord_82421, baseEnd_82421] using wordTrace_append hprefix tailTrace_82421
  have hstable : (prefixWord ++ tailWord_82421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82421).length < 2 ^ (prefixWord ++ tailWord_82421).sum := by decide
  have hdescent : baseEnd_82421 < baseStart_82421 := by decide
  rcases family_descends (prefixWord ++ tailWord_82421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82438 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_82438 : Nat := 118140960795 + 82438 * 2 ^ 59
def prefixEnd_82438 : Nat := 4983230072969 + 3 ^ 40 * 82438 * 2
def baseEnd_82438 : Nat := 14110106065151231548627

theorem tailTrace_82438 : CollatzResearch.WordTrace tailWord_82438 prefixEnd_82438 14110106065151231548627 := by
  unfold tailWord_82438
  simp only [CollatzResearch.WordTrace]
  refine ⟨93961277354646254206249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2004507250232453423066645 93961277354646254206249)
  ·
    refine ⟨70470958015984690654687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93961277354646254206249 70470958015984690654687)
    ·
      refine ⟨105706437023977035982031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70470958015984690654687 105706437023977035982031)
      ·
        refine ⟨158559655535965553973047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105706437023977035982031 158559655535965553973047)
        ·
          refine ⟨237839483303948330959571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158559655535965553973047 237839483303948330959571)
          ·
            refine ⟨356759224955922496439357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237839483303948330959571 356759224955922496439357)
            ·
              refine ⟨133784709358470936164759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 356759224955922496439357 133784709358470936164759)
              ·
                refine ⟨200677064037706404247139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133784709358470936164759 200677064037706404247139)
                ·
                  refine ⟨301015596056559606370709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200677064037706404247139 301015596056559606370709)
                  ·
                    refine ⟨14110106065151231548627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 301015596056559606370709 14110106065151231548627)
                    ·
                      rfl

theorem cell23_82438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_82438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82438 prefixEnd_82438 := by exact prefixLift 82438
  have htrace : WordTrace (prefixWord ++ tailWord_82438) baseStart_82438 baseEnd_82438 := by
    simpa [prefixWord, tailWord_82438, baseEnd_82438] using wordTrace_append hprefix tailTrace_82438
  have hstable : (prefixWord ++ tailWord_82438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82438).length < 2 ^ (prefixWord ++ tailWord_82438).sum := by decide
  have hdescent : baseEnd_82438 < baseStart_82438 := by decide
  rcases family_descends (prefixWord ++ tailWord_82438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82444 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 1, 3, 3]
def baseStart_82444 : Nat := 118140960795 + 82444 * 2 ^ 59
def prefixEnd_82444 : Nat := 4983230072969 + 3 ^ 40 * 82444 * 2
def baseEnd_82444 : Nat := 42333399079380671170853

theorem tailTrace_82444 : CollatzResearch.WordTrace tailWord_82444 prefixEnd_82444 42333399079380671170853 := by
  unfold tailWord_82444
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503489856663471579659193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2004653142217962106212257 1503489856663471579659193)
  ·
    refine ⟨1127617392497603684744395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1503489856663471579659193 1127617392497603684744395)
    ·
      refine ⟨1691426088746405527116593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127617392497603684744395 1691426088746405527116593)
      ·
        refine ⟨1268569566559804145337445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1691426088746405527116593 1268569566559804145337445)
        ·
          refine ⟨237856793729963277250771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1268569566559804145337445 237856793729963277250771)
          ·
            refine ⟨356785190594944915876157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237856793729963277250771 356785190594944915876157)
            ·
              refine ⟨133794446473104343453559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 356785190594944915876157 133794446473104343453559)
              ·
                refine ⟨200691669709656515180339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133794446473104343453559 200691669709656515180339)
                ·
                  refine ⟨301037504564484772770509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200691669709656515180339 301037504564484772770509)
                  ·
                    refine ⟨112889064211681789788941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 301037504564484772770509 112889064211681789788941)
                    ·
                      refine ⟨42333399079380671170853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 112889064211681789788941 42333399079380671170853)
                      ·
                        rfl

theorem cell23_82444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_82444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82444 prefixEnd_82444 := by exact prefixLift 82444
  have htrace : WordTrace (prefixWord ++ tailWord_82444) baseStart_82444 baseEnd_82444 := by
    simpa [prefixWord, tailWord_82444, baseEnd_82444] using wordTrace_append hprefix tailTrace_82444
  have hstable : (prefixWord ++ tailWord_82444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82444).length < 2 ^ (prefixWord ++ tailWord_82444).sum := by decide
  have hdescent : baseEnd_82444 < baseStart_82444 := by decide
  rcases family_descends (prefixWord ++ tailWord_82444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82445 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_82445 : Nat := 118140960795 + 82445 * 2 ^ 59
def prefixEnd_82445 : Nat := 4983230072969 + 3 ^ 40 * 82445 * 2
def baseEnd_82445 : Nat := 42333912560035167258349

theorem tailTrace_82445 : CollatzResearch.WordTrace tailWord_82445 prefixEnd_82445 42333912560035167258349 := by
  unfold tailWord_82445
  simp only [CollatzResearch.WordTrace]
  refine ⟨3007016186323320330104789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2004677457548880220069859 3007016186323320330104789)
  ·
    refine ⟨70476941866952820236831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3007016186323320330104789 70476941866952820236831)
    ·
      refine ⟨105715412800429230355247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70476941866952820236831 105715412800429230355247)
      ·
        refine ⟨158573119200643845532871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105715412800429230355247 158573119200643845532871)
        ·
          refine ⟨237859678800965768299307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158573119200643845532871 237859678800965768299307)
          ·
            refine ⟨356789518201448652448961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237859678800965768299307 356789518201448652448961)
            ·
              refine ⟨267592138651086489336721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 356789518201448652448961 267592138651086489336721)
              ·
                refine ⟨200694103988314867002541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267592138651086489336721 200694103988314867002541)
                ·
                  refine ⟨75260288995618075125953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200694103988314867002541 75260288995618075125953)
                  ·
                    refine ⟨56445216746713556344465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75260288995618075125953 56445216746713556344465)
                    ·
                      refine ⟨42333912560035167258349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56445216746713556344465 42333912560035167258349)
                      ·
                        rfl

theorem cell23_82445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_82445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82445 prefixEnd_82445 := by exact prefixLift 82445
  have htrace : WordTrace (prefixWord ++ tailWord_82445) baseStart_82445 baseEnd_82445 := by
    simpa [prefixWord, tailWord_82445, baseEnd_82445] using wordTrace_append hprefix tailTrace_82445
  have hstable : (prefixWord ++ tailWord_82445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82445).length < 2 ^ (prefixWord ++ tailWord_82445).sum := by decide
  have hdescent : baseEnd_82445 < baseStart_82445 := by decide
  rcases family_descends (prefixWord ++ tailWord_82445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82487 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 3]
def baseStart_82487 : Nat := 118140960795 + 82487 * 2 ^ 59
def prefixEnd_82487 : Nat := 4983230072969 + 3 ^ 40 * 82487 * 2
def baseEnd_82487 : Nat := 42355478747524002933155

theorem tailTrace_82487 : CollatzResearch.WordTrace tailWord_82487 prefixEnd_82487 42355478747524002933155 := by
  unfold tailWord_82487
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008548052171161503133715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2005698701447441002089143 3008548052171161503133715)
  ·
    refine ⟨4512822078256742254700573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3008548052171161503133715 4512822078256742254700573)
    ·
      refine ⟨1692308279346278345512715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4512822078256742254700573 1692308279346278345512715)
      ·
        refine ⟨2538462419019417518269073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692308279346278345512715 2538462419019417518269073)
        ·
          refine ⟨1903846814264563138701805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2538462419019417518269073 1903846814264563138701805)
          ·
            refine ⟨713942555349211177013177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1903846814264563138701805 713942555349211177013177)
            ·
              refine ⟨535456916511908382759883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713942555349211177013177 535456916511908382759883)
              ·
                refine ⟨803185374767862574139825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535456916511908382759883 803185374767862574139825)
                ·
                  refine ⟨602389031075896930604869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 803185374767862574139825 602389031075896930604869)
                  ·
                    refine ⟨112947943326730674488413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 602389031075896930604869 112947943326730674488413)
                    ·
                      refine ⟨42355478747524002933155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 112947943326730674488413 42355478747524002933155)
                      ·
                        rfl

theorem cell23_82487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_82487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82487 prefixEnd_82487 := by exact prefixLift 82487
  have htrace : WordTrace (prefixWord ++ tailWord_82487) baseStart_82487 baseEnd_82487 := by
    simpa [prefixWord, tailWord_82487, baseEnd_82487] using wordTrace_append hprefix tailTrace_82487
  have hstable : (prefixWord ++ tailWord_82487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82487).length < 2 ^ (prefixWord ++ tailWord_82487).sum := by decide
  have hdescent : baseEnd_82487 < baseStart_82487 := by decide
  rcases family_descends (prefixWord ++ tailWord_82487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82541 : List Nat := [1, 5, 1, 1, 3, 2, 1, 4, 5]
def baseStart_82541 : Nat := 118140960795 + 82541 * 2 ^ 59
def prefixEnd_82541 : Nat := 4983230072969 + 3 ^ 40 * 82541 * 2
def baseEnd_82541 : Nat := 4709245189207421295323

theorem tailTrace_82541 : CollatzResearch.WordTrace tailWord_82541 prefixEnd_82541 4709245189207421295323 := by
  unfold tailWord_82541
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010517593975528725599477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2007011729317019150399651 3010517593975528725599477)
  ·
    refine ⟨282236024435205818024951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3010517593975528725599477 282236024435205818024951)
    ·
      refine ⟨423354036652808727037427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282236024435205818024951 423354036652808727037427)
      ·
        refine ⟨635031054979213090556141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423354036652808727037427 635031054979213090556141)
        ·
          refine ⟨238136645617204908958553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 635031054979213090556141 238136645617204908958553)
          ·
            refine ⟨178602484212903681718915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238136645617204908958553 178602484212903681718915)
            ·
              refine ⟨267903726319355522578373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178602484212903681718915 267903726319355522578373)
              ·
                refine ⟨50231948684879160483445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 267903726319355522578373 50231948684879160483445)
                ·
                  refine ⟨4709245189207421295323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50231948684879160483445 4709245189207421295323)
                  ·
                    rfl

theorem cell23_82541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_82541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82541 prefixEnd_82541 := by exact prefixLift 82541
  have htrace : WordTrace (prefixWord ++ tailWord_82541) baseStart_82541 baseEnd_82541 := by
    simpa [prefixWord, tailWord_82541, baseEnd_82541] using wordTrace_append hprefix tailTrace_82541
  have hstable : (prefixWord ++ tailWord_82541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82541).length < 2 ^ (prefixWord ++ tailWord_82541).sum := by decide
  have hdescent : baseEnd_82541 < baseStart_82541 := by decide
  rcases family_descends (prefixWord ++ tailWord_82541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82574 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_82574 : Nat := 118140960795 + 82574 * 2 ^ 59
def prefixEnd_82574 : Nat := 4983230072969 + 3 ^ 40 * 82574 * 2
def baseEnd_82574 : Nat := 42400151564465162545255

theorem tailTrace_82574 : CollatzResearch.WordTrace tailWord_82574 prefixEnd_82574 42400151564465162545255 := by
  unfold tailWord_82574
  simp only [CollatzResearch.WordTrace]
  refine ⟨376465150356996920193847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2007814135237316907700517 376465150356996920193847)
  ·
    refine ⟨564697725535495380290771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 376465150356996920193847 564697725535495380290771)
    ·
      refine ⟨847046588303243070436157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 564697725535495380290771 847046588303243070436157)
      ·
        refine ⟨317642470613716151413559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 847046588303243070436157 317642470613716151413559)
        ·
          refine ⟨476463705920574227120339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317642470613716151413559 476463705920574227120339)
          ·
            refine ⟨714695558880861340680509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476463705920574227120339 714695558880861340680509)
            ·
              refine ⟨268010834580323002755191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 714695558880861340680509 268010834580323002755191)
              ·
                refine ⟨402016251870484504132787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268010834580323002755191 402016251870484504132787)
                ·
                  refine ⟨603024377805726756199181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402016251870484504132787 603024377805726756199181)
                  ·
                    refine ⟨226134141677147533574693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 603024377805726756199181 226134141677147533574693)
                    ·
                      refine ⟨42400151564465162545255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 226134141677147533574693 42400151564465162545255)
                      ·
                        rfl

theorem cell23_82574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_82574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82574 prefixEnd_82574 := by exact prefixLift 82574
  have htrace : WordTrace (prefixWord ++ tailWord_82574) baseStart_82574 baseEnd_82574 := by
    simpa [prefixWord, tailWord_82574, baseEnd_82574] using wordTrace_append hprefix tailTrace_82574
  have hstable : (prefixWord ++ tailWord_82574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82574).length < 2 ^ (prefixWord ++ tailWord_82574).sum := by decide
  have hdescent : baseEnd_82574 < baseStart_82574 := by decide
  rcases family_descends (prefixWord ++ tailWord_82574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82584 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 5, 4]
def baseStart_82584 : Nat := 118140960795 + 82584 * 2 ^ 59
def prefixEnd_82584 : Nat := 4983230072969 + 3 ^ 40 * 82584 * 2
def baseEnd_82584 : Nat := 14135095457003374473403

theorem tailTrace_82584 : CollatzResearch.WordTrace tailWord_82584 prefixEnd_82584 14135095457003374473403 := by
  unfold tailWord_82584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1506042966409873534707403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2008057288546498046276537 1506042966409873534707403)
  ·
    refine ⟨2259064449614810302061105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1506042966409873534707403 2259064449614810302061105)
    ·
      refine ⟨1694298337211107726545829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2259064449614810302061105 1694298337211107726545829)
      ·
        refine ⟨317680938227082698727343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1694298337211107726545829 317680938227082698727343)
        ·
          refine ⟨476521407340624048091015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317680938227082698727343 476521407340624048091015)
          ·
            refine ⟨714782111010936072136523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476521407340624048091015 714782111010936072136523)
            ·
              refine ⟨1072173166516404108204785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714782111010936072136523 1072173166516404108204785)
              ·
                refine ⟨804129874887303081153589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072173166516404108204785 804129874887303081153589)
                ·
                  refine ⟨75387175770684663858149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 804129874887303081153589 75387175770684663858149)
                  ·
                    refine ⟨14135095457003374473403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75387175770684663858149 14135095457003374473403)
                    ·
                      rfl

theorem cell23_82584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_82584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82584 prefixEnd_82584 := by exact prefixLift 82584
  have htrace : WordTrace (prefixWord ++ tailWord_82584) baseStart_82584 baseEnd_82584 := by
    simpa [prefixWord, tailWord_82584, baseEnd_82584] using wordTrace_append hprefix tailTrace_82584
  have hstable : (prefixWord ++ tailWord_82584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82584).length < 2 ^ (prefixWord ++ tailWord_82584).sum := by decide
  have hdescent : baseEnd_82584 < baseStart_82584 := by decide
  rcases family_descends (prefixWord ++ tailWord_82584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82617 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_82617 : Nat := 118140960795 + 82617 * 2 ^ 59
def prefixEnd_82617 : Nat := 4983230072969 + 3 ^ 40 * 82617 * 2
def baseEnd_82617 : Nat := 42422231232608494307557

theorem tailTrace_82617 : CollatzResearch.WordTrace tailWord_82617 prefixEnd_82617 42422231232608494307557 := by
  unfold tailWord_82617
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013289541700193705366105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2008859694466795803577403 3013289541700193705366105)
  ·
    refine ⟨2259967156275145279024579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3013289541700193705366105 2259967156275145279024579)
    ·
      refine ⟨3389950734412717918536869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2259967156275145279024579 3389950734412717918536869)
      ·
        refine ⟨635615762702384609725663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3389950734412717918536869 635615762702384609725663)
        ·
          refine ⟨953423644053576914588495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635615762702384609725663 953423644053576914588495)
          ·
            refine ⟨1430135466080365371882743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953423644053576914588495 1430135466080365371882743)
            ·
              refine ⟨2145203199120548057824115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430135466080365371882743 2145203199120548057824115)
              ·
                refine ⟨3217804798680822086736173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145203199120548057824115 3217804798680822086736173)
                ·
                  refine ⟨1206676799505308282526065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3217804798680822086736173 1206676799505308282526065)
                  ·
                    refine ⟨905007599628981211894549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1206676799505308282526065 905007599628981211894549)
                    ·
                      refine ⟨42422231232608494307557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 905007599628981211894549 42422231232608494307557)
                      ·
                        rfl

theorem cell23_82617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_82617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82617 prefixEnd_82617 := by exact prefixLift 82617
  have htrace : WordTrace (prefixWord ++ tailWord_82617) baseStart_82617 baseEnd_82617 := by
    simpa [prefixWord, tailWord_82617, baseEnd_82617] using wordTrace_append hprefix tailTrace_82617
  have hstable : (prefixWord ++ tailWord_82617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82617).length < 2 ^ (prefixWord ++ tailWord_82617).sum := by decide
  have hdescent : baseEnd_82617 < baseStart_82617 := by decide
  rcases family_descends (prefixWord ++ tailWord_82617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82652 : List Nat := [2, 2, 5, 1, 1, 2, 3, 2, 1, 4]
def baseStart_82652 : Nat := 118140960795 + 82652 * 2 ^ 59
def prefixEnd_82652 : Nat := 4983230072969 + 3 ^ 40 * 82652 * 2
def baseEnd_82652 : Nat := 14146734351838619123299

theorem tailTrace_82652 : CollatzResearch.WordTrace tailWord_82652 prefixEnd_82652 14146734351838619123299 := by
  unfold tailWord_82652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507283048286697341445105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2009710731048929788593473 1507283048286697341445105)
  ·
    refine ⟨1130462286215023006083829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1507283048286697341445105 1130462286215023006083829)
    ·
      refine ⟨105980839332658406820359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1130462286215023006083829 105980839332658406820359)
      ·
        refine ⟨158971258998987610230539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105980839332658406820359 158971258998987610230539)
        ·
          refine ⟨238456888498481415345809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158971258998987610230539 238456888498481415345809)
          ·
            refine ⟨178842666373861061509357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238456888498481415345809 178842666373861061509357)
            ·
              refine ⟨67065999890197898066009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178842666373861061509357 67065999890197898066009)
              ·
                refine ⟨50299499917648423549507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67065999890197898066009 50299499917648423549507)
                ·
                  refine ⟨75449249876472635324261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50299499917648423549507 75449249876472635324261)
                  ·
                    refine ⟨14146734351838619123299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75449249876472635324261 14146734351838619123299)
                    ·
                      rfl

theorem cell23_82652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_82652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82652 prefixEnd_82652 := by exact prefixLift 82652
  have htrace : WordTrace (prefixWord ++ tailWord_82652) baseStart_82652 baseEnd_82652 := by
    simpa [prefixWord, tailWord_82652, baseEnd_82652] using wordTrace_append hprefix tailTrace_82652
  have hstable : (prefixWord ++ tailWord_82652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82652).length < 2 ^ (prefixWord ++ tailWord_82652).sum := by decide
  have hdescent : baseEnd_82652 < baseStart_82652 := by decide
  rcases family_descends (prefixWord ++ tailWord_82652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82698 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4]
def baseStart_82698 : Nat := 118140960795 + 82698 * 2 ^ 59
def prefixEnd_82698 : Nat := 4983230072969 + 3 ^ 40 * 82698 * 2
def baseEnd_82698 : Nat := 42463823165622677394685

theorem tailTrace_82698 : CollatzResearch.WordTrace tailWord_82698 prefixEnd_82698 42463823165622677394685 := by
  unfold tailWord_82698
  simp only [CollatzResearch.WordTrace]
  refine ⟨754060963601686134766187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2010829236271163026043165 754060963601686134766187)
  ·
    refine ⟨1131091445402529202149281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 754060963601686134766187 1131091445402529202149281)
    ·
      refine ⟨848318584051896901611961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1131091445402529202149281 848318584051896901611961)
      ·
        refine ⟨636238938038922676208971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 848318584051896901611961 636238938038922676208971)
        ·
          refine ⟨954358407058384014313457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636238938038922676208971 954358407058384014313457)
          ·
            refine ⟨715768805293788010735093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954358407058384014313457 715768805293788010735093)
            ·
              refine ⟨67103325496292626006415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 715768805293788010735093 67103325496292626006415)
              ·
                refine ⟨100654988244438939009623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67103325496292626006415 100654988244438939009623)
                ·
                  refine ⟨150982482366658408514435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100654988244438939009623 150982482366658408514435)
                  ·
                    refine ⟨226473723549987612771653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150982482366658408514435 226473723549987612771653)
                    ·
                      refine ⟨42463823165622677394685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 226473723549987612771653 42463823165622677394685)
                      ·
                        rfl

theorem cell23_82698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_82698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82698 prefixEnd_82698 := by exact prefixLift 82698
  have htrace : WordTrace (prefixWord ++ tailWord_82698) baseStart_82698 baseEnd_82698 := by
    simpa [prefixWord, tailWord_82698, baseEnd_82698] using wordTrace_append hprefix tailTrace_82698
  have hstable : (prefixWord ++ tailWord_82698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82698).length < 2 ^ (prefixWord ++ tailWord_82698).sum := by decide
  have hdescent : baseEnd_82698 < baseStart_82698 := by decide
  rcases family_descends (prefixWord ++ tailWord_82698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82744 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_82744 : Nat := 118140960795 + 82744 * 2 ^ 59
def prefixEnd_82744 : Nat := 4983230072969 + 3 ^ 40 * 82744 * 2
def baseEnd_82744 : Nat := 42487443275729497419473

theorem tailTrace_82744 : CollatzResearch.WordTrace tailWord_82744 prefixEnd_82744 42487443275729497419473 := by
  unfold tailWord_82744
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508960806120047197619643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2011947741493396263492857 1508960806120047197619643)
  ·
    refine ⟨2263441209180070796429465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1508960806120047197619643 2263441209180070796429465)
    ·
      refine ⟨1697580906885053097322099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2263441209180070796429465 1697580906885053097322099)
      ·
        refine ⟨2546371360327579645983149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1697580906885053097322099 2546371360327579645983149)
        ·
          refine ⟨954889260122842367243681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2546371360327579645983149 954889260122842367243681)
          ·
            refine ⟨716166945092131775432761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954889260122842367243681 716166945092131775432761)
            ·
              refine ⟨537125208819098831574571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716166945092131775432761 537125208819098831574571)
              ·
                refine ⟨805687813228648247361857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537125208819098831574571 805687813228648247361857)
                ·
                  refine ⟨604265859921486185521393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 805687813228648247361857 604265859921486185521393)
                  ·
                    refine ⟨453199394941114639141045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 604265859921486185521393 453199394941114639141045)
                    ·
                      refine ⟨42487443275729497419473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 453199394941114639141045 42487443275729497419473)
                      ·
                        rfl

theorem cell23_82744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_82744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82744 prefixEnd_82744 := by exact prefixLift 82744
  have htrace : WordTrace (prefixWord ++ tailWord_82744) baseStart_82744 baseEnd_82744 := by
    simpa [prefixWord, tailWord_82744, baseEnd_82744] using wordTrace_append hprefix tailTrace_82744
  have hstable : (prefixWord ++ tailWord_82744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82744).length < 2 ^ (prefixWord ++ tailWord_82744).sum := by decide
  have hdescent : baseEnd_82744 < baseStart_82744 := by decide
  rcases family_descends (prefixWord ++ tailWord_82744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82749 : List Nat := [1, 4, 1, 4, 2, 1, 2, 3, 1, 2, 2]
def baseStart_82749 : Nat := 118140960795 + 82749 * 2 ^ 59
def prefixEnd_82749 : Nat := 4983230072969 + 3 ^ 40 * 82749 * 2
def baseEnd_82749 : Nat := 42490010679001977856951

theorem tailTrace_82749 : CollatzResearch.WordTrace tailWord_82749 prefixEnd_82749 42490010679001977856951 := by
  unfold tailWord_82749
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018103977221980249171301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2012069318147986832780867 3018103977221980249171301)
  ·
    refine ⟨565894495729121296719619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3018103977221980249171301 565894495729121296719619)
    ·
      refine ⟨848841743593681945079429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565894495729121296719619 848841743593681945079429)
      ·
        refine ⟨159157826923815364702393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 848841743593681945079429 159157826923815364702393)
        ·
          refine ⟨119368370192861523526795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159157826923815364702393 119368370192861523526795)
          ·
            refine ⟨179052555289292285290193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119368370192861523526795 179052555289292285290193)
            ·
              refine ⟨134289416466969213967645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179052555289292285290193 134289416466969213967645)
              ·
                refine ⟨50358531175113455237867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134289416466969213967645 50358531175113455237867)
                ·
                  refine ⟨75537796762670182856801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50358531175113455237867 75537796762670182856801)
                  ·
                    refine ⟨56653347572002637142601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75537796762670182856801 56653347572002637142601)
                    ·
                      refine ⟨42490010679001977856951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56653347572002637142601 42490010679001977856951)
                      ·
                        rfl

theorem cell23_82749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_82749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82749 prefixEnd_82749 := by exact prefixLift 82749
  have htrace : WordTrace (prefixWord ++ tailWord_82749) baseStart_82749 baseEnd_82749 := by
    simpa [prefixWord, tailWord_82749, baseEnd_82749] using wordTrace_append hprefix tailTrace_82749
  have hstable : (prefixWord ++ tailWord_82749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82749).length < 2 ^ (prefixWord ++ tailWord_82749).sum := by decide
  have hdescent : baseEnd_82749 < baseStart_82749 := by decide
  rcases family_descends (prefixWord ++ tailWord_82749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82771 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 3, 4, 2]
def baseStart_82771 : Nat := 118140960795 + 82771 * 2 ^ 59
def prefixEnd_82771 : Nat := 4983230072969 + 3 ^ 40 * 82771 * 2
def baseEnd_82771 : Nat := 42501307253400891781849

theorem tailTrace_82771 : CollatzResearch.WordTrace tailWord_82771 prefixEnd_82771 42501307253400891781849 := by
  unfold tailWord_82771
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018906383142278006472167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2012604255428185337648111 3018906383142278006472167)
  ·
    refine ⟨4528359574713417009708251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3018906383142278006472167 4528359574713417009708251)
    ·
      refine ⟨6792539362070125514562377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4528359574713417009708251 6792539362070125514562377)
      ·
        refine ⟨5094404521552594135921783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6792539362070125514562377 5094404521552594135921783)
        ·
          refine ⟨7641606782328891203882675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5094404521552594135921783 7641606782328891203882675)
          ·
            refine ⟨11462410173493336805824013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7641606782328891203882675 11462410173493336805824013)
            ·
              refine ⟨4298403815060001302184005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11462410173493336805824013 4298403815060001302184005)
              ·
                refine ⟨805950715323750244159501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4298403815060001302184005 805950715323750244159501)
                ·
                  refine ⟨302231518246406341559813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805950715323750244159501 302231518246406341559813)
                  ·
                    refine ⟨56668409671201189042465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 302231518246406341559813 56668409671201189042465)
                    ·
                      refine ⟨42501307253400891781849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56668409671201189042465 42501307253400891781849)
                      ·
                        rfl

theorem cell23_82771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 4, 2].length) (baseStart_82771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82771 prefixEnd_82771 := by exact prefixLift 82771
  have htrace : WordTrace (prefixWord ++ tailWord_82771) baseStart_82771 baseEnd_82771 := by
    simpa [prefixWord, tailWord_82771, baseEnd_82771] using wordTrace_append hprefix tailTrace_82771
  have hstable : (prefixWord ++ tailWord_82771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82771).length < 2 ^ (prefixWord ++ tailWord_82771).sum := by decide
  have hdescent : baseEnd_82771 < baseStart_82771 := by decide
  rcases family_descends (prefixWord ++ tailWord_82771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82805 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_82805 : Nat := 118140960795 + 82805 * 2 ^ 59
def prefixEnd_82805 : Nat := 4983230072969 + 3 ^ 40 * 82805 * 2
def baseEnd_82805 : Nat := 42518765595653758756693

theorem tailTrace_82805 : CollatzResearch.WordTrace tailWord_82805 prefixEnd_82805 42518765595653758756693 := by
  unfold tailWord_82805
  simp only [CollatzResearch.WordTrace]
  refine ⟨3020146465019101813209869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2013430976679401208806579 3020146465019101813209869)
  ·
    refine ⟨1132554924382163179953701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3020146465019101813209869 1132554924382163179953701)
    ·
      refine ⟨212354048321655596241319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1132554924382163179953701 212354048321655596241319)
      ·
        refine ⟨318531072482483394361979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212354048321655596241319 318531072482483394361979)
        ·
          refine ⟨477796608723725091542969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318531072482483394361979 477796608723725091542969)
          ·
            refine ⟨358347456542793818657227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477796608723725091542969 358347456542793818657227)
            ·
              refine ⟨537521184814190727985841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358347456542793818657227 537521184814190727985841)
              ·
                refine ⟨403140888610643045989381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537521184814190727985841 403140888610643045989381)
                ·
                  refine ⟨75588916614495571123009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403140888610643045989381 75588916614495571123009)
                  ·
                    refine ⟨56691687460871678342257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75588916614495571123009 56691687460871678342257)
                    ·
                      refine ⟨42518765595653758756693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56691687460871678342257 42518765595653758756693)
                      ·
                        rfl

theorem cell23_82805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_82805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82805 prefixEnd_82805 := by exact prefixLift 82805
  have htrace : WordTrace (prefixWord ++ tailWord_82805) baseStart_82805 baseEnd_82805 := by
    simpa [prefixWord, tailWord_82805, baseEnd_82805] using wordTrace_append hprefix tailTrace_82805
  have hstable : (prefixWord ++ tailWord_82805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82805).length < 2 ^ (prefixWord ++ tailWord_82805).sum := by decide
  have hdescent : baseEnd_82805 < baseStart_82805 := by decide
  rcases family_descends (prefixWord ++ tailWord_82805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82864 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_82864 : Nat := 118140960795 + 82864 * 2 ^ 59
def prefixEnd_82864 : Nat := 4983230072969 + 3 ^ 40 * 82864 * 2
def baseEnd_82864 : Nat := 42549060954269027918921

theorem tailTrace_82864 : CollatzResearch.WordTrace tailWord_82864 prefixEnd_82864 42549060954269027918921 := by
  unfold tailWord_82864
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511149185902677444803823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2014865581203569926405097 1511149185902677444803823)
  ·
    refine ⟨2266723778854016167205735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1511149185902677444803823 2266723778854016167205735)
    ·
      refine ⟨3400085668281024250808603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266723778854016167205735 3400085668281024250808603)
      ·
        refine ⟨5100128502421536376212905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400085668281024250808603 5100128502421536376212905)
        ·
          refine ⟨3825096376816152282159679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5100128502421536376212905 3825096376816152282159679)
          ·
            refine ⟨5737644565224228423239519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3825096376816152282159679 5737644565224228423239519)
            ·
              refine ⟨8606466847836342634859279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737644565224228423239519 8606466847836342634859279)
              ·
                refine ⟨12909700271754513952288919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8606466847836342634859279 12909700271754513952288919)
                ·
                  refine ⟨19364550407631770928433379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12909700271754513952288919 19364550407631770928433379)
                  ·
                    refine ⟨29046825611447656392650069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19364550407631770928433379 29046825611447656392650069)
                    ·
                      refine ⟨42549060954269027918921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 29046825611447656392650069 42549060954269027918921)
                      ·
                        rfl

theorem cell23_82864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_82864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82864 prefixEnd_82864 := by exact prefixLift 82864
  have htrace : WordTrace (prefixWord ++ tailWord_82864) baseStart_82864 baseEnd_82864 := by
    simpa [prefixWord, tailWord_82864, baseEnd_82864] using wordTrace_append hprefix tailTrace_82864
  have hstable : (prefixWord ++ tailWord_82864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82864).length < 2 ^ (prefixWord ++ tailWord_82864).sum := by decide
  have hdescent : baseEnd_82864 < baseStart_82864 := by decide
  rcases family_descends (prefixWord ++ tailWord_82864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82878 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_82878 : Nat := 118140960795 + 82878 * 2 ^ 59
def prefixEnd_82878 : Nat := 4983230072969 + 3 ^ 40 * 82878 * 2
def baseEnd_82878 : Nat := 42556249683431973143857

theorem tailTrace_82878 : CollatzResearch.WordTrace tailWord_82878 prefixEnd_82878 42556249683431973143857 := by
  unfold tailWord_82878
  simp only [CollatzResearch.WordTrace]
  refine ⟨377851124219329410077161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2015205995836423520411525 377851124219329410077161)
  ·
    refine ⟨283388343164497057557871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 377851124219329410077161 283388343164497057557871)
    ·
      refine ⟨425082514746745586336807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283388343164497057557871 425082514746745586336807)
      ·
        refine ⟨637623772120118379505211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425082514746745586336807 637623772120118379505211)
        ·
          refine ⟨956435658180177569257817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637623772120118379505211 956435658180177569257817)
          ·
            refine ⟨717326743635133176943363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 956435658180177569257817 717326743635133176943363)
            ·
              refine ⟨1075990115452699765415045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717326743635133176943363 1075990115452699765415045)
              ·
                refine ⟨201748146647381206015321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1075990115452699765415045 201748146647381206015321)
                ·
                  refine ⟨151311109985535904511491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 201748146647381206015321 151311109985535904511491)
                  ·
                    refine ⟨226966664978303856767237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 151311109985535904511491 226966664978303856767237)
                    ·
                      refine ⟨42556249683431973143857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 226966664978303856767237 42556249683431973143857)
                      ·
                        rfl

theorem cell23_82878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_82878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82878 prefixEnd_82878 := by exact prefixLift 82878
  have htrace : WordTrace (prefixWord ++ tailWord_82878) baseStart_82878 baseEnd_82878 := by
    simpa [prefixWord, tailWord_82878, baseEnd_82878] using wordTrace_append hprefix tailTrace_82878
  have hstable : (prefixWord ++ tailWord_82878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82878).length < 2 ^ (prefixWord ++ tailWord_82878).sum := by decide
  have hdescent : baseEnd_82878 < baseStart_82878 := by decide
  rcases family_descends (prefixWord ++ tailWord_82878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82922 : List Nat := [3, 1, 3, 1, 2, 3, 2, 3, 1, 4]
def baseStart_82922 : Nat := 118140960795 + 82922 * 2 ^ 59
def prefixEnd_82922 : Nat := 4983230072969 + 3 ^ 40 * 82922 * 2
def baseEnd_82922 : Nat := 14192947610743266997885

theorem tailTrace_82922 : CollatzResearch.WordTrace tailWord_82922 prefixEnd_82922 14192947610743266997885 := by
  unfold tailWord_82922
  simp only [CollatzResearch.WordTrace]
  refine ⟨756103451398807698804755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2016275870396820530146013 756103451398807698804755)
  ·
    refine ⟨1134155177098211548207133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 756103451398807698804755 1134155177098211548207133)
    ·
      refine ⟨425308191411829330577675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1134155177098211548207133 425308191411829330577675)
      ·
        refine ⟨637962287117743995866513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425308191411829330577675 637962287117743995866513)
        ·
          refine ⟨478471715338307996899885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637962287117743995866513 478471715338307996899885)
          ·
            refine ⟨179426893251865498837457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 478471715338307996899885 179426893251865498837457)
            ·
              refine ⟨134570169938899124128093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179426893251865498837457 134570169938899124128093)
              ·
                refine ⟨50463813727087171548035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134570169938899124128093 50463813727087171548035)
                ·
                  refine ⟨75695720590630757322053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50463813727087171548035 75695720590630757322053)
                  ·
                    refine ⟨14192947610743266997885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75695720590630757322053 14192947610743266997885)
                    ·
                      rfl

theorem cell23_82922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_82922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82922 prefixEnd_82922 := by exact prefixLift 82922
  have htrace : WordTrace (prefixWord ++ tailWord_82922) baseStart_82922 baseEnd_82922 := by
    simpa [prefixWord, tailWord_82922, baseEnd_82922] using wordTrace_append hprefix tailTrace_82922
  have hstable : (prefixWord ++ tailWord_82922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82922).length < 2 ^ (prefixWord ++ tailWord_82922).sum := by decide
  have hdescent : baseEnd_82922 < baseStart_82922 := by decide
  rcases family_descends (prefixWord ++ tailWord_82922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82928 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 7, 1, 3]
def baseStart_82928 : Nat := 118140960795 + 82928 * 2 ^ 59
def prefixEnd_82928 : Nat := 4983230072969 + 3 ^ 40 * 82928 * 2
def baseEnd_82928 : Nat := 42581923716156777518627

theorem tailTrace_82928 : CollatzResearch.WordTrace tailWord_82928 prefixEnd_82928 42581923716156777518627 := by
  unfold tailWord_82928
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512316321786746909968719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2016421762382329213291625 1512316321786746909968719)
  ·
    refine ⟨2268474482680120364953079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1512316321786746909968719 2268474482680120364953079)
    ·
      refine ⟨3402711724020180547429619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2268474482680120364953079 3402711724020180547429619)
      ·
        refine ⟨5104067586030270821144429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3402711724020180547429619 5104067586030270821144429)
        ·
          refine ⟨1914025344761351557929161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5104067586030270821144429 1914025344761351557929161)
          ·
            refine ⟨1435519008571013668446871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1914025344761351557929161 1435519008571013668446871)
            ·
              refine ⟨2153278512856520502670307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435519008571013668446871 2153278512856520502670307)
              ·
                refine ⟨3229917769284780754005461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2153278512856520502670307 3229917769284780754005461)
                ·
                  refine ⟨75701197717612048922003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3229917769284780754005461 75701197717612048922003)
                  ·
                    refine ⟨113551796576418073383005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75701197717612048922003 113551796576418073383005)
                    ·
                      refine ⟨42581923716156777518627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 113551796576418073383005 42581923716156777518627)
                      ·
                        rfl

theorem cell23_82928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 7, 1, 3].length) (baseStart_82928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82928 prefixEnd_82928 := by exact prefixLift 82928
  have htrace : WordTrace (prefixWord ++ tailWord_82928) baseStart_82928 baseEnd_82928 := by
    simpa [prefixWord, tailWord_82928, baseEnd_82928] using wordTrace_append hprefix tailTrace_82928
  have hstable : (prefixWord ++ tailWord_82928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82928).length < 2 ^ (prefixWord ++ tailWord_82928).sum := by decide
  have hdescent : baseEnd_82928 < baseStart_82928 := by decide
  rcases family_descends (prefixWord ++ tailWord_82928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82945 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_82945 : Nat := 118140960795 + 82945 * 2 ^ 59
def prefixEnd_82945 : Nat := 4983230072969 + 3 ^ 40 * 82945 * 2
def baseEnd_82945 : Nat := 42590652887283211006049

theorem tailTrace_82945 : CollatzResearch.WordTrace tailWord_82945 prefixEnd_82945 42590652887283211006049 := by
  unfold tailWord_82945
  simp only [CollatzResearch.WordTrace]
  refine ⟨3025252684511905723306289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2016835123007937148870859 3025252684511905723306289)
  ·
    refine ⟨2268939513383929292479717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3025252684511905723306289 2268939513383929292479717)
    ·
      refine ⟨425426158759486742339947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2268939513383929292479717 425426158759486742339947)
      ·
        refine ⟨638139238139230113509921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425426158759486742339947 638139238139230113509921)
        ·
          refine ⟨478604428604422585132441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638139238139230113509921 478604428604422585132441)
          ·
            refine ⟨358953321453316938849331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478604428604422585132441 358953321453316938849331)
            ·
              refine ⟨538429982179975408273997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358953321453316938849331 538429982179975408273997)
              ·
                refine ⟨201911243317490778102749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 538429982179975408273997 201911243317490778102749)
                ·
                  refine ⟨75716716244059041788531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201911243317490778102749 75716716244059041788531)
                  ·
                    refine ⟨113575074366088562682797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75716716244059041788531 113575074366088562682797)
                    ·
                      refine ⟨42590652887283211006049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 113575074366088562682797 42590652887283211006049)
                      ·
                        rfl

theorem cell23_82945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_82945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82945 prefixEnd_82945 := by exact prefixLift 82945
  have htrace : WordTrace (prefixWord ++ tailWord_82945) baseStart_82945 baseEnd_82945 := by
    simpa [prefixWord, tailWord_82945, baseEnd_82945] using wordTrace_append hprefix tailTrace_82945
  have hstable : (prefixWord ++ tailWord_82945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82945).length < 2 ^ (prefixWord ++ tailWord_82945).sum := by decide
  have hdescent : baseEnd_82945 < baseStart_82945 := by decide
  rcases family_descends (prefixWord ++ tailWord_82945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82965 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_82965 : Nat := 118140960795 + 82965 * 2 ^ 59
def prefixEnd_82965 : Nat := 4983230072969 + 3 ^ 40 * 82965 * 2
def baseEnd_82965 : Nat := 14200307500124377585319

theorem tailTrace_82965 : CollatzResearch.WordTrace tailWord_82965 prefixEnd_82965 14200307500124377585319 := by
  unfold tailWord_82965
  simp only [CollatzResearch.WordTrace]
  refine ⟨3025982144439449139034349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2017321429626299426022899 3025982144439449139034349)
  ·
    refine ⟨1134743304164793427137881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3025982144439449139034349 1134743304164793427137881)
    ·
      refine ⟨851057478123595070353411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1134743304164793427137881 851057478123595070353411)
      ·
        refine ⟨1276586217185392605530117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851057478123595070353411 1276586217185392605530117)
        ·
          refine ⟨239359915722261113536897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1276586217185392605530117 239359915722261113536897)
          ·
            refine ⟨179519936791695835152673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239359915722261113536897 179519936791695835152673)
            ·
              refine ⟨134639952593771876364505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179519936791695835152673 134639952593771876364505)
              ·
                refine ⟨100979964445328907273379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134639952593771876364505 100979964445328907273379)
                ·
                  refine ⟨151469946667993360910069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100979964445328907273379 151469946667993360910069)
                  ·
                    refine ⟨14200307500124377585319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 151469946667993360910069 14200307500124377585319)
                    ·
                      rfl

theorem cell23_82965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_82965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82965 prefixEnd_82965 := by exact prefixLift 82965
  have htrace : WordTrace (prefixWord ++ tailWord_82965) baseStart_82965 baseEnd_82965 := by
    simpa [prefixWord, tailWord_82965, baseEnd_82965] using wordTrace_append hprefix tailTrace_82965
  have hstable : (prefixWord ++ tailWord_82965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82965).length < 2 ^ (prefixWord ++ tailWord_82965).sum := by decide
  have hdescent : baseEnd_82965 < baseStart_82965 := by decide
  rcases family_descends (prefixWord ++ tailWord_82965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82979 : List Nat := [1, 1, 1, 4, 3, 4, 1, 3, 1, 1, 3]
def baseStart_82979 : Nat := 118140960795 + 82979 * 2 ^ 59
def prefixEnd_82979 : Nat := 4983230072969 + 3 ^ 40 * 82979 * 2
def baseEnd_82979 : Nat := 42608111229536077980893

theorem tailTrace_82979 : CollatzResearch.WordTrace tailWord_82979 prefixEnd_82979 42608111229536077980893 := by
  unfold tailWord_82979
  simp only [CollatzResearch.WordTrace]
  refine ⟨3026492766388729530043991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2017661844259153020029327 3026492766388729530043991)
  ·
    refine ⟨4539739149583094295065987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3026492766388729530043991 4539739149583094295065987)
    ·
      refine ⟨6809608724374641442598981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4539739149583094295065987 6809608724374641442598981)
      ·
        refine ⟨1276801635820245270487309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6809608724374641442598981 1276801635820245270487309)
        ·
          refine ⟨478800613432591976432741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1276801635820245270487309 478800613432591976432741)
          ·
            refine ⟨89775115018610995581139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 478800613432591976432741 89775115018610995581139)
            ·
              refine ⟨134662672527916493371709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89775115018610995581139 134662672527916493371709)
              ·
                refine ⟨50498502197968685014391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134662672527916493371709 50498502197968685014391)
                ·
                  refine ⟨75747753296953027521587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50498502197968685014391 75747753296953027521587)
                  ·
                    refine ⟨113621629945429541282381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75747753296953027521587 113621629945429541282381)
                    ·
                      refine ⟨42608111229536077980893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 113621629945429541282381 42608111229536077980893)
                      ·
                        rfl

theorem cell23_82979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_82979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82979 prefixEnd_82979 := by exact prefixLift 82979
  have htrace : WordTrace (prefixWord ++ tailWord_82979) baseStart_82979 baseEnd_82979 := by
    simpa [prefixWord, tailWord_82979, baseEnd_82979] using wordTrace_append hprefix tailTrace_82979
  have hstable : (prefixWord ++ tailWord_82979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82979).length < 2 ^ (prefixWord ++ tailWord_82979).sum := by decide
  have hdescent : baseEnd_82979 < baseStart_82979 := by decide
  rcases family_descends (prefixWord ++ tailWord_82979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82988 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 5]
def baseStart_82988 : Nat := 118140960795 + 82988 * 2 ^ 59
def prefixEnd_82988 : Nat := 4983230072969 + 3 ^ 40 * 82988 * 2
def baseEnd_82988 : Nat := 42612732555426542768351

theorem tailTrace_82988 : CollatzResearch.WordTrace tailWord_82988 prefixEnd_82988 42612732555426542768351 := by
  unfold tailWord_82988
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513410511678062033560809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2017880682237416044747745 1513410511678062033560809)
  ·
    refine ⟨1135057883758546525170607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1513410511678062033560809 1135057883758546525170607)
    ·
      refine ⟨1702586825637819787755911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1135057883758546525170607 1702586825637819787755911)
      ·
        refine ⟨2553880238456729681633867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702586825637819787755911 2553880238456729681633867)
        ·
          refine ⟨3830820357685094522450801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2553880238456729681633867 3830820357685094522450801)
          ·
            refine ⟨2873115268263820891838101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3830820357685094522450801 2873115268263820891838101)
            ·
              refine ⟨134677278199866604304911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2873115268263820891838101 134677278199866604304911)
              ·
                refine ⟨202015917299799906457367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134677278199866604304911 202015917299799906457367)
                ·
                  refine ⟨303023875949699859686051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 202015917299799906457367 303023875949699859686051)
                  ·
                    refine ⟨454535813924549789529077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 303023875949699859686051 454535813924549789529077)
                    ·
                      refine ⟨42612732555426542768351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 454535813924549789529077 42612732555426542768351)
                      ·
                        rfl

theorem cell23_82988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_82988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_82988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_82988 prefixEnd_82988 := by exact prefixLift 82988
  have htrace : WordTrace (prefixWord ++ tailWord_82988) baseStart_82988 baseEnd_82988 := by
    simpa [prefixWord, tailWord_82988, baseEnd_82988] using wordTrace_append hprefix tailTrace_82988
  have hstable : (prefixWord ++ tailWord_82988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82988).length < 2 ^ (prefixWord ++ tailWord_82988).sum := by decide
  have hdescent : baseEnd_82988 < baseStart_82988 := by decide
  rcases family_descends (prefixWord ++ tailWord_82988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83002 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2]
def baseStart_83002 : Nat := 118140960795 + 83002 * 2 ^ 59
def prefixEnd_83002 : Nat := 4983230072969 + 3 ^ 40 * 83002 * 2
def baseEnd_83002 : Nat := 42619921284589487993287

theorem tailTrace_83002 : CollatzResearch.WordTrace tailWord_83002 prefixEnd_83002 42619921284589487993287 := by
  unfold tailWord_83002
  simp only [CollatzResearch.WordTrace]
  refine ⟨756832911326351114532815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2018221096870269638754173 756832911326351114532815)
  ·
    refine ⟨1135249366989526671799223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 756832911326351114532815 1135249366989526671799223)
    ·
      refine ⟨1702874050484290007698835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1135249366989526671799223 1702874050484290007698835)
      ·
        refine ⟨2554311075726435011548253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702874050484290007698835 2554311075726435011548253)
        ·
          refine ⟨957866653397413129330595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2554311075726435011548253 957866653397413129330595)
          ·
            refine ⟨1436799980096119693995893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957866653397413129330595 1436799980096119693995893)
            ·
              refine ⟨134699998134011221312115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1436799980096119693995893 134699998134011221312115)
              ·
                refine ⟨202049997201016831968173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134699998134011221312115 202049997201016831968173)
                ·
                  refine ⟨75768748950381311988065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202049997201016831968173 75768748950381311988065)
                  ·
                    refine ⟨56826561712785983991049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75768748950381311988065 56826561712785983991049)
                    ·
                      refine ⟨42619921284589487993287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56826561712785983991049 42619921284589487993287)
                      ·
                        rfl

theorem cell23_83002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_83002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83002 prefixEnd_83002 := by exact prefixLift 83002
  have htrace : WordTrace (prefixWord ++ tailWord_83002) baseStart_83002 baseEnd_83002 := by
    simpa [prefixWord, tailWord_83002, baseEnd_83002] using wordTrace_append hprefix tailTrace_83002
  have hstable : (prefixWord ++ tailWord_83002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83002).length < 2 ^ (prefixWord ++ tailWord_83002).sum := by decide
  have hdescent : baseEnd_83002 < baseStart_83002 := by decide
  rcases family_descends (prefixWord ++ tailWord_83002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83011 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 6]
def baseStart_83011 : Nat := 118140960795 + 83011 * 2 ^ 59
def prefixEnd_83011 : Nat := 4983230072969 + 3 ^ 40 * 83011 * 2
def baseEnd_83011 : Nat := 42624542610479952780745

theorem tailTrace_83011 : CollatzResearch.WordTrace tailWord_83011 prefixEnd_83011 42624542610479952780745 := by
  unfold tailWord_83011
  simp only [CollatzResearch.WordTrace]
  refine ⟨3027659902272798995208887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2018439934848532663472591 3027659902272798995208887)
  ·
    refine ⟨4541489853409198492813331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3027659902272798995208887 4541489853409198492813331)
    ·
      refine ⟨6812234780113797739219997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4541489853409198492813331 6812234780113797739219997)
      ·
        refine ⟨2554588042542674152207499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6812234780113797739219997 2554588042542674152207499)
        ·
          refine ⟨3831882063814011228311249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554588042542674152207499 3831882063814011228311249)
          ·
            refine ⟨2873911547860508421233437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3831882063814011228311249 2873911547860508421233437)
            ·
              refine ⟨1077716830447690657962539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2873911547860508421233437 1077716830447690657962539)
              ·
                refine ⟨1616575245671535986943809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1077716830447690657962539 1616575245671535986943809)
                ·
                  refine ⟨1212431434253651990207857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1616575245671535986943809 1212431434253651990207857)
                  ·
                    refine ⟨909323575690238992655893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1212431434253651990207857 909323575690238992655893)
                    ·
                      refine ⟨42624542610479952780745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 909323575690238992655893 42624542610479952780745)
                      ·
                        rfl

theorem cell23_83011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_83011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83011 prefixEnd_83011 := by exact prefixLift 83011
  have htrace : WordTrace (prefixWord ++ tailWord_83011) baseStart_83011 baseEnd_83011 := by
    simpa [prefixWord, tailWord_83011, baseEnd_83011] using wordTrace_append hprefix tailTrace_83011
  have hstable : (prefixWord ++ tailWord_83011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83011).length < 2 ^ (prefixWord ++ tailWord_83011).sum := by decide
  have hdescent : baseEnd_83011 < baseStart_83011 := by decide
  rcases family_descends (prefixWord ++ tailWord_83011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83051 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 5, 8]
def baseStart_83051 : Nat := 118140960795 + 83051 * 2 ^ 59
def prefixEnd_83051 : Nat := 4983230072969 + 3 ^ 40 * 83051 * 2
def baseEnd_83051 : Nat := 14215027278886598760187

theorem tailTrace_83051 : CollatzResearch.WordTrace tailWord_83051 prefixEnd_83051 14215027278886598760187 := by
  unfold tailWord_83051
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029118822127885826665007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2019412548085257217776671 3029118822127885826665007)
  ·
    refine ⟨4543678233191828739997511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3029118822127885826665007 4543678233191828739997511)
    ·
      refine ⟨6815517349787743109996267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4543678233191828739997511 6815517349787743109996267)
      ·
        refine ⟨10223276024681614664994401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6815517349787743109996267 10223276024681614664994401)
        ·
          refine ⟨7667457018511210998745801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10223276024681614664994401 7667457018511210998745801)
          ·
            refine ⟨5750592763883408249059351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7667457018511210998745801 5750592763883408249059351)
            ·
              refine ⟨8625889145825112373589027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750592763883408249059351 8625889145825112373589027)
              ·
                refine ⟨12938833718737668560383541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8625889145825112373589027 12938833718737668560383541)
                ·
                  refine ⟨1213015661131656427535957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12938833718737668560383541 1213015661131656427535957)
                  ·
                    refine ⟨14215027278886598760187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1213015661131656427535957 14215027278886598760187)
                    ·
                      rfl

theorem cell23_83051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 8].length) (baseStart_83051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83051 prefixEnd_83051 := by exact prefixLift 83051
  have htrace : WordTrace (prefixWord ++ tailWord_83051) baseStart_83051 baseEnd_83051 := by
    simpa [prefixWord, tailWord_83051, baseEnd_83051] using wordTrace_append hprefix tailTrace_83051
  have hstable : (prefixWord ++ tailWord_83051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83051).length < 2 ^ (prefixWord ++ tailWord_83051).sum := by decide
  have hdescent : baseEnd_83051 < baseStart_83051 := by decide
  rcases family_descends (prefixWord ++ tailWord_83051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83052 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 3]
def baseStart_83052 : Nat := 118140960795 + 83052 * 2 ^ 59
def prefixEnd_83052 : Nat := 4983230072969 + 3 ^ 40 * 83052 * 2
def baseEnd_83052 : Nat := 42645595317314292368057

theorem tailTrace_83052 : CollatzResearch.WordTrace tailWord_83052 prefixEnd_83052 42645595317314292368057 := by
  unfold tailWord_83052
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514577647562131498725705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2019436863416175331634273 1514577647562131498725705)
  ·
    refine ⟨1135933235671598624044279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1514577647562131498725705 1135933235671598624044279)
    ·
      refine ⟨1703899853507397936066419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1135933235671598624044279 1703899853507397936066419)
      ·
        refine ⟨2555849780261096904099629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703899853507397936066419 2555849780261096904099629)
        ·
          refine ⟨958443667597911339037361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2555849780261096904099629 958443667597911339037361)
          ·
            refine ⟨718832750698433504278021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958443667597911339037361 718832750698433504278021)
            ·
              refine ⟨134781140755956282052129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 718832750698433504278021 134781140755956282052129)
              ·
                refine ⟨101085855566967211539097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134781140755956282052129 101085855566967211539097)
                ·
                  refine ⟨75814391675225408654323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101085855566967211539097 75814391675225408654323)
                  ·
                    refine ⟨113721587512838112981485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75814391675225408654323 113721587512838112981485)
                    ·
                      refine ⟨42645595317314292368057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 113721587512838112981485 42645595317314292368057)
                      ·
                        rfl

theorem cell23_83052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_83052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83052 prefixEnd_83052 := by exact prefixLift 83052
  have htrace : WordTrace (prefixWord ++ tailWord_83052) baseStart_83052 baseEnd_83052 := by
    simpa [prefixWord, tailWord_83052, baseEnd_83052] using wordTrace_append hprefix tailTrace_83052
  have hstable : (prefixWord ++ tailWord_83052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83052).length < 2 ^ (prefixWord ++ tailWord_83052).sum := by decide
  have hdescent : baseEnd_83052 < baseStart_83052 := by decide
  rcases family_descends (prefixWord ++ tailWord_83052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83053 : List Nat := [1, 5, 1, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_83053 : Nat := 118140960795 + 83053 * 2 ^ 59
def prefixEnd_83053 : Nat := 4983230072969 + 3 ^ 40 * 83053 * 2
def baseEnd_83053 : Nat := 42646108797968788455553

theorem tailTrace_83053 : CollatzResearch.WordTrace tailWord_83053 prefixEnd_83053 42646108797968788455553 := by
  unfold tailWord_83053
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029191768120640168237813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2019461178747093445491875 3029191768120640168237813)
  ·
    refine ⟨283986728261310015772295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3029191768120640168237813 283986728261310015772295)
    ·
      refine ⟨425980092391965023658443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283986728261310015772295 425980092391965023658443)
      ·
        refine ⟨638970138587947535487665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425980092391965023658443 638970138587947535487665)
        ·
          refine ⟨479227603940960651615749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638970138587947535487665 479227603940960651615749)
          ·
            refine ⟨89855175738930122177953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 479227603940960651615749 89855175738930122177953)
            ·
              refine ⟨67391381804197591633465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89855175738930122177953 67391381804197591633465)
              ·
                refine ⟨50543536353148193725099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67391381804197591633465 50543536353148193725099)
                ·
                  refine ⟨75815304529722290587649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50543536353148193725099 75815304529722290587649)
                  ·
                    refine ⟨56861478397291717940737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75815304529722290587649 56861478397291717940737)
                    ·
                      refine ⟨42646108797968788455553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56861478397291717940737 42646108797968788455553)
                      ·
                        rfl

theorem cell23_83053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_83053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83053 prefixEnd_83053 := by exact prefixLift 83053
  have htrace : WordTrace (prefixWord ++ tailWord_83053) baseStart_83053 baseEnd_83053 := by
    simpa [prefixWord, tailWord_83053, baseEnd_83053] using wordTrace_append hprefix tailTrace_83053
  have hstable : (prefixWord ++ tailWord_83053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83053).length < 2 ^ (prefixWord ++ tailWord_83053).sum := by decide
  have hdescent : baseEnd_83053 < baseStart_83053 := by decide
  rcases family_descends (prefixWord ++ tailWord_83053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83058 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_83058 : Nat := 118140960795 + 83058 * 2 ^ 59
def prefixEnd_83058 : Nat := 4983230072969 + 3 ^ 40 * 83058 * 2
def baseEnd_83058 : Nat := 42648676201241268893029

theorem tailTrace_83058 : CollatzResearch.WordTrace tailWord_83058 prefixEnd_83058 42648676201241268893029 := by
  unfold tailWord_83058
  simp only [CollatzResearch.WordTrace]
  refine ⟨757343533275631505542457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2019582755401684014779885 757343533275631505542457)
  ·
    refine ⟨568007649956723629156843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 757343533275631505542457 568007649956723629156843)
    ·
      refine ⟨852011474935085443735265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568007649956723629156843 852011474935085443735265)
      ·
        refine ⟨639008606201314082801449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 852011474935085443735265 639008606201314082801449)
        ·
          refine ⟨479256454650985562101087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 639008606201314082801449 479256454650985562101087)
          ·
            refine ⟨718884681976478343151631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479256454650985562101087 718884681976478343151631)
            ·
              refine ⟨1078327022964717514727447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718884681976478343151631 1078327022964717514727447)
              ·
                refine ⟨1617490534447076272091171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078327022964717514727447 1617490534447076272091171)
                ·
                  refine ⟨2426235801670614408136757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1617490534447076272091171 2426235801670614408136757)
                  ·
                    refine ⟨227459606406620100762821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2426235801670614408136757 227459606406620100762821)
                    ·
                      refine ⟨42648676201241268893029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 227459606406620100762821 42648676201241268893029)
                      ·
                        rfl

theorem cell23_83058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_83058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83058 prefixEnd_83058 := by exact prefixLift 83058
  have htrace : WordTrace (prefixWord ++ tailWord_83058) baseStart_83058 baseEnd_83058 := by
    simpa [prefixWord, tailWord_83058, baseEnd_83058] using wordTrace_append hprefix tailTrace_83058
  have hstable : (prefixWord ++ tailWord_83058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83058).length < 2 ^ (prefixWord ++ tailWord_83058).sum := by decide
  have hdescent : baseEnd_83058 < baseStart_83058 := by decide
  rcases family_descends (prefixWord ++ tailWord_83058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83062 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_83062 : Nat := 118140960795 + 83062 * 2 ^ 59
def prefixEnd_83062 : Nat := 4983230072969 + 3 ^ 40 * 83062 * 2
def baseEnd_83062 : Nat := 42650730123859253243011

theorem tailTrace_83062 : CollatzResearch.WordTrace tailWord_83062 prefixEnd_83062 42650730123859253243011 := by
  unfold tailWord_83062
  simp only [CollatzResearch.WordTrace]
  refine ⟨189345001568002169082215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2019680016725356470210293 189345001568002169082215)
  ·
    refine ⟨284017502352003253623323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189345001568002169082215 284017502352003253623323)
    ·
      refine ⟨426026253528004880434985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284017502352003253623323 426026253528004880434985)
      ·
        refine ⟨319519690146003660326239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 426026253528004880434985 319519690146003660326239)
        ·
          refine ⟨479279535219005490489359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319519690146003660326239 479279535219005490489359)
          ·
            refine ⟨718919302828508235734039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479279535219005490489359 718919302828508235734039)
            ·
              refine ⟨1078378954242762353601059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718919302828508235734039 1078378954242762353601059)
              ·
                refine ⟨1617568431364143530401589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1078378954242762353601059 1617568431364143530401589)
                ·
                  refine ⟨151647040440388455975149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1617568431364143530401589 151647040440388455975149)
                  ·
                    refine ⟨56867640165145670990681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151647040440388455975149 56867640165145670990681)
                    ·
                      refine ⟨42650730123859253243011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56867640165145670990681 42650730123859253243011)
                      ·
                        rfl

theorem cell23_83062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_83062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83062 prefixEnd_83062 := by exact prefixLift 83062
  have htrace : WordTrace (prefixWord ++ tailWord_83062) baseStart_83062 baseEnd_83062 := by
    simpa [prefixWord, tailWord_83062, baseEnd_83062] using wordTrace_append hprefix tailTrace_83062
  have hstable : (prefixWord ++ tailWord_83062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83062).length < 2 ^ (prefixWord ++ tailWord_83062).sum := by decide
  have hdescent : baseEnd_83062 < baseStart_83062 := by decide
  rcases family_descends (prefixWord ++ tailWord_83062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83068 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_83068 : Nat := 118140960795 + 83068 * 2 ^ 59
def prefixEnd_83068 : Nat := 4983230072969 + 3 ^ 40 * 83068 * 2
def baseEnd_83068 : Nat := 14217937002595409922661

theorem tailTrace_83068 : CollatzResearch.WordTrace tailWord_83068 prefixEnd_83068 14217937002595409922661 := by
  unfold tailWord_83068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514869431533148865016929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2019825908710865153355905 1514869431533148865016929)
  ·
    refine ⟨1136152073649861648762697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1514869431533148865016929 1136152073649861648762697)
    ·
      refine ⟨852114055237396236572023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1136152073649861648762697 852114055237396236572023)
      ·
        refine ⟨1278171082856094354858035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 852114055237396236572023 1278171082856094354858035)
        ·
          refine ⟨1917256624284141532287053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278171082856094354858035 1917256624284141532287053)
          ·
            refine ⟨718971234106553074607645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1917256624284141532287053 718971234106553074607645)
            ·
              refine ⟨269614212789957402977867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 718971234106553074607645 269614212789957402977867)
              ·
                refine ⟨404421319184936104466801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269614212789957402977867 404421319184936104466801)
                ·
                  refine ⟨303315989388702078350101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404421319184936104466801 303315989388702078350101)
                  ·
                    refine ⟨14217937002595409922661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 303315989388702078350101 14217937002595409922661)
                    ·
                      rfl

theorem cell23_83068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_83068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83068 prefixEnd_83068 := by exact prefixLift 83068
  have htrace : WordTrace (prefixWord ++ tailWord_83068) baseStart_83068 baseEnd_83068 := by
    simpa [prefixWord, tailWord_83068, baseEnd_83068] using wordTrace_append hprefix tailTrace_83068
  have hstable : (prefixWord ++ tailWord_83068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83068).length < 2 ^ (prefixWord ++ tailWord_83068).sum := by decide
  have hdescent : baseEnd_83068 < baseStart_83068 := by decide
  rcases family_descends (prefixWord ++ tailWord_83068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83096 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 1, 3, 2]
def baseStart_83096 : Nat := 118140960795 + 83096 * 2 ^ 59
def prefixEnd_83096 : Nat := 4983230072969 + 3 ^ 40 * 83096 * 2
def baseEnd_83096 : Nat := 42668188466112120217855

theorem tailTrace_83096 : CollatzResearch.WordTrace tailWord_83096 prefixEnd_83096 42668188466112120217855 := by
  unfold tailWord_83096
  simp only [CollatzResearch.WordTrace]
  refine ⟨1515380053482429256026571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2020506737976572341368761 1515380053482429256026571)
  ·
    refine ⟨2273070080223643884039857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1515380053482429256026571 2273070080223643884039857)
    ·
      refine ⟨1704802560167732913029893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2273070080223643884039857 1704802560167732913029893)
      ·
        refine ⟨319650480031449921193105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1704802560167732913029893 319650480031449921193105)
        ·
          refine ⟨239737860023587440894829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319650480031449921193105 239737860023587440894829)
          ·
            refine ⟨89901697508845290335561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239737860023587440894829 89901697508845290335561)
            ·
              refine ⟨67426273131633967751671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89901697508845290335561 67426273131633967751671)
              ·
                refine ⟨101139409697450951627507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67426273131633967751671 101139409697450951627507)
                ·
                  refine ⟨151709114546176427441261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101139409697450951627507 151709114546176427441261)
                  ·
                    refine ⟨56890917954816160290473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 151709114546176427441261 56890917954816160290473)
                    ·
                      refine ⟨42668188466112120217855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56890917954816160290473 42668188466112120217855)
                      ·
                        rfl

theorem cell23_83096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_83096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83096 prefixEnd_83096 := by exact prefixLift 83096
  have htrace : WordTrace (prefixWord ++ tailWord_83096) baseStart_83096 baseEnd_83096 := by
    simpa [prefixWord, tailWord_83096, baseEnd_83096] using wordTrace_append hprefix tailTrace_83096
  have hstable : (prefixWord ++ tailWord_83096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83096).length < 2 ^ (prefixWord ++ tailWord_83096).sum := by decide
  have hdescent : baseEnd_83096 < baseStart_83096 := by decide
  rcases family_descends (prefixWord ++ tailWord_83096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83109 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 2, 2, 2]
def baseStart_83109 : Nat := 118140960795 + 83109 * 2 ^ 59
def prefixEnd_83109 : Nat := 4983230072969 + 3 ^ 40 * 83109 * 2
def baseEnd_83109 : Nat := 42674863714620569355295

theorem tailTrace_83109 : CollatzResearch.WordTrace tailWord_83109 prefixEnd_83109 42674863714620569355295 := by
  unfold tailWord_83109
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031234255917761732276381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2020822837278507821517587 3031234255917761732276381)
  ·
    refine ⟨1136712845969160649603643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3031234255917761732276381 1136712845969160649603643)
    ·
      refine ⟨1705069268953740974405465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1136712845969160649603643 1705069268953740974405465)
      ·
        refine ⟨1278801951715305730804099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1705069268953740974405465 1278801951715305730804099)
        ·
          refine ⟨1918202927572958596206149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278801951715305730804099 1918202927572958596206149)
          ·
            refine ⟨359663048919929736788653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1918202927572958596206149 359663048919929736788653)
            ·
              refine ⟨134873643344973651295745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359663048919929736788653 134873643344973651295745)
              ·
                refine ⟨101155232508730238471809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134873643344973651295745 101155232508730238471809)
                ·
                  refine ⟨75866424381547678853857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101155232508730238471809 75866424381547678853857)
                  ·
                    refine ⟨56899818286160759140393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75866424381547678853857 56899818286160759140393)
                    ·
                      refine ⟨42674863714620569355295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56899818286160759140393 42674863714620569355295)
                      ·
                        rfl

theorem cell23_83109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_83109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83109 prefixEnd_83109 := by exact prefixLift 83109
  have htrace : WordTrace (prefixWord ++ tailWord_83109) baseStart_83109 baseEnd_83109 := by
    simpa [prefixWord, tailWord_83109, baseEnd_83109] using wordTrace_append hprefix tailTrace_83109
  have hstable : (prefixWord ++ tailWord_83109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83109).length < 2 ^ (prefixWord ++ tailWord_83109).sum := by decide
  have hdescent : baseEnd_83109 < baseStart_83109 := by decide
  rcases family_descends (prefixWord ++ tailWord_83109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83128 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 6, 5]
def baseStart_83128 : Nat := 118140960795 + 83128 * 2 ^ 59
def prefixEnd_83128 : Nat := 4983230072969 + 3 ^ 40 * 83128 * 2
def baseEnd_83128 : Nat := 14228206615685331672569

theorem tailTrace_83128 : CollatzResearch.WordTrace tailWord_83128 prefixEnd_83128 14228206615685331672569 := by
  unfold tailWord_83128
  simp only [CollatzResearch.WordTrace]
  refine ⟨1515963621424463988609019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2021284828565951984812025 1515963621424463988609019)
  ·
    refine ⟨2273945432136695982913529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1515963621424463988609019 2273945432136695982913529)
    ·
      refine ⟨1705459074102521987185147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2273945432136695982913529 1705459074102521987185147)
      ·
        refine ⟨2558188611153782980777721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705459074102521987185147 2558188611153782980777721)
        ·
          refine ⟨1918641458365337235583291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2558188611153782980777721 1918641458365337235583291)
          ·
            refine ⟨2877962187548005853374937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918641458365337235583291 2877962187548005853374937)
            ·
              refine ⟨2158471640661004390031203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877962187548005853374937 2158471640661004390031203)
              ·
                refine ⟨3237707460991506585046805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2158471640661004390031203 3237707460991506585046805)
                ·
                  refine ⟨151767537233976871174069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3237707460991506585046805 151767537233976871174069)
                  ·
                    refine ⟨14228206615685331672569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 151767537233976871174069 14228206615685331672569)
                    ·
                      rfl

theorem cell23_83128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_83128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83128 prefixEnd_83128 := by exact prefixLift 83128
  have htrace : WordTrace (prefixWord ++ tailWord_83128) baseStart_83128 baseEnd_83128 := by
    simpa [prefixWord, tailWord_83128, baseEnd_83128] using wordTrace_append hprefix tailTrace_83128
  have hstable : (prefixWord ++ tailWord_83128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83128).length < 2 ^ (prefixWord ++ tailWord_83128).sum := by decide
  have hdescent : baseEnd_83128 < baseStart_83128 := by decide
  rcases family_descends (prefixWord ++ tailWord_83128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83135 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 2, 5, 2]
def baseStart_83135 : Nat := 118140960795 + 83135 * 2 ^ 59
def prefixEnd_83135 : Nat := 4983230072969 + 3 ^ 40 * 83135 * 2
def baseEnd_83135 : Nat := 42688214211637467630175

theorem tailTrace_83135 : CollatzResearch.WordTrace tailWord_83135 prefixEnd_83135 42688214211637467630175 := by
  unfold tailWord_83135
  simp only [CollatzResearch.WordTrace]
  refine ⟨3032182553823568172722859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2021455035882378781815239 3032182553823568172722859)
  ·
    refine ⟨4548273830735352259084289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3032182553823568172722859 4548273830735352259084289)
    ·
      refine ⟨3411205373051514194313217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4548273830735352259084289 3411205373051514194313217)
      ·
        refine ⟨2558404029788635645734913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3411205373051514194313217 2558404029788635645734913)
        ·
          refine ⟨1918803022341476734301185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2558404029788635645734913 1918803022341476734301185)
          ·
            refine ⟨1439102266756107550725889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1918803022341476734301185 1439102266756107550725889)
            ·
              refine ⟨1079326700067080663044417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439102266756107550725889 1079326700067080663044417)
              ·
                refine ⟨809495025050310497283313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1079326700067080663044417 809495025050310497283313)
                ·
                  refine ⟨607121268787732872962485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 809495025050310497283313 607121268787732872962485)
                  ·
                    refine ⟨56917618948849956840233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 607121268787732872962485 56917618948849956840233)
                    ·
                      refine ⟨42688214211637467630175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56917618948849956840233 42688214211637467630175)
                      ·
                        rfl

theorem cell23_83135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_83135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83135 prefixEnd_83135 := by exact prefixLift 83135
  have htrace : WordTrace (prefixWord ++ tailWord_83135) baseStart_83135 baseEnd_83135 := by
    simpa [prefixWord, tailWord_83135, baseEnd_83135] using wordTrace_append hprefix tailTrace_83135
  have hstable : (prefixWord ++ tailWord_83135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83135).length < 2 ^ (prefixWord ++ tailWord_83135).sum := by decide
  have hdescent : baseEnd_83135 < baseStart_83135 := by decide
  rcases family_descends (prefixWord ++ tailWord_83135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83182 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_83182 : Nat := 118140960795 + 83182 * 2 ^ 59
def prefixEnd_83182 : Nat := 4983230072969 + 3 ^ 40 * 83182 * 2
def baseEnd_83182 : Nat := 42712347802398783742459

theorem tailTrace_83182 : CollatzResearch.WordTrace tailWord_83182 prefixEnd_83182 42712347802398783742459 := by
  unfold tailWord_83182
  simp only [CollatzResearch.WordTrace]
  refine ⟨379237098081661899960475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2022597856435530133122533 379237098081661899960475)
  ·
    refine ⟨568855647122492849940713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 379237098081661899960475 568855647122492849940713)
    ·
      refine ⟨426641735341869637455535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 568855647122492849940713 426641735341869637455535)
      ·
        refine ⟨639962603012804456183303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426641735341869637455535 639962603012804456183303)
        ·
          refine ⟨959943904519206684274955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639962603012804456183303 959943904519206684274955)
          ·
            refine ⟨1439915856778810026412433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959943904519206684274955 1439915856778810026412433)
            ·
              refine ⟨1079936892584107519809325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439915856778810026412433 1079936892584107519809325)
              ·
                refine ⟨404976334719040319928497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1079936892584107519809325 404976334719040319928497)
                ·
                  refine ⟨303732251039280239946373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 404976334719040319928497 303732251039280239946373)
                  ·
                    refine ⟨56949797069865044989945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 303732251039280239946373 56949797069865044989945)
                    ·
                      refine ⟨42712347802398783742459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 56949797069865044989945 42712347802398783742459)
                      ·
                        rfl

theorem cell23_83182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_83182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83182 prefixEnd_83182 := by exact prefixLift 83182
  have htrace : WordTrace (prefixWord ++ tailWord_83182) baseStart_83182 baseEnd_83182 := by
    simpa [prefixWord, tailWord_83182, baseEnd_83182] using wordTrace_append hprefix tailTrace_83182
  have hstable : (prefixWord ++ tailWord_83182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83182).length < 2 ^ (prefixWord ++ tailWord_83182).sum := by decide
  have hdescent : baseEnd_83182 < baseStart_83182 := by decide
  rcases family_descends (prefixWord ++ tailWord_83182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83185 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 6, 2, 3]
def baseStart_83185 : Nat := 118140960795 + 83185 * 2 ^ 59
def prefixEnd_83185 : Nat := 4983230072969 + 3 ^ 40 * 83185 * 2
def baseEnd_83185 : Nat := 42713888244362272004945

theorem tailTrace_83185 : CollatzResearch.WordTrace tailWord_83185 prefixEnd_83185 42713888244362272004945 := by
  unfold tailWord_83185
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034006203642426712043009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2022670802428284474695339 3034006203642426712043009)
  ·
    refine ⟨2275504652731820034032257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3034006203642426712043009 2275504652731820034032257)
    ·
      refine ⟨1706628489548865025524193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2275504652731820034032257 1706628489548865025524193)
      ·
        refine ⟨1279971367161648769143145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1706628489548865025524193 1279971367161648769143145)
        ·
          refine ⟨959978525371236576857359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1279971367161648769143145 959978525371236576857359)
          ·
            refine ⟨1439967788056854865286039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 959978525371236576857359 1439967788056854865286039)
            ·
              refine ⟨2159951682085282297929059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1439967788056854865286039 2159951682085282297929059)
              ·
                refine ⟨3239927523127923446893589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2159951682085282297929059 3239927523127923446893589)
                ·
                  refine ⟨151871602646621411573137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3239927523127923446893589 151871602646621411573137)
                  ·
                    refine ⟨113903701984966058679853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 151871602646621411573137 113903701984966058679853)
                    ·
                      refine ⟨42713888244362272004945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 113903701984966058679853 42713888244362272004945)
                      ·
                        rfl

theorem cell23_83185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_83185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83185 prefixEnd_83185 := by exact prefixLift 83185
  have htrace : WordTrace (prefixWord ++ tailWord_83185) baseStart_83185 baseEnd_83185 := by
    simpa [prefixWord, tailWord_83185, baseEnd_83185] using wordTrace_append hprefix tailTrace_83185
  have hstable : (prefixWord ++ tailWord_83185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83185).length < 2 ^ (prefixWord ++ tailWord_83185).sum := by decide
  have hdescent : baseEnd_83185 < baseStart_83185 := by decide
  rcases family_descends (prefixWord ++ tailWord_83185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83226 : List Nat := [3, 1, 1, 3, 3, 1, 4, 2, 1, 4]
def baseStart_83226 : Nat := 118140960795 + 83226 * 2 ^ 59
def prefixEnd_83226 : Nat := 4983230072969 + 3 ^ 40 * 83226 * 2
def baseEnd_83226 : Nat := 14244980317065537197419

theorem tailTrace_83226 : CollatzResearch.WordTrace tailWord_83226 prefixEnd_83226 14244980317065537197419 := by
  unfold tailWord_83226
  simp only [CollatzResearch.WordTrace]
  refine ⟨758875399123472678571383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2023667730995927142857021 758875399123472678571383)
  ·
    refine ⟨1138313098685209017857075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 758875399123472678571383 1138313098685209017857075)
    ·
      refine ⟨1707469648027813526785613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138313098685209017857075 1707469648027813526785613)
      ·
        refine ⟨640301118010430072544605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1707469648027813526785613 640301118010430072544605)
        ·
          refine ⟨240112919253911277204227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 640301118010430072544605 240112919253911277204227)
          ·
            refine ⟨360169378880866915806341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240112919253911277204227 360169378880866915806341)
            ·
              refine ⟨67531758540162546713689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 360169378880866915806341 67531758540162546713689)
              ·
                refine ⟨50648818905121910035267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67531758540162546713689 50648818905121910035267)
                ·
                  refine ⟨75973228357682865052901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50648818905121910035267 75973228357682865052901)
                  ·
                    refine ⟨14244980317065537197419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75973228357682865052901 14244980317065537197419)
                    ·
                      rfl

theorem cell23_83226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_83226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83226 prefixEnd_83226 := by exact prefixLift 83226
  have htrace : WordTrace (prefixWord ++ tailWord_83226) baseStart_83226 baseEnd_83226 := by
    simpa [prefixWord, tailWord_83226, baseEnd_83226] using wordTrace_append hprefix tailTrace_83226
  have hstable : (prefixWord ++ tailWord_83226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83226).length < 2 ^ (prefixWord ++ tailWord_83226).sum := by decide
  have hdescent : baseEnd_83226 < baseStart_83226 := by decide
  rcases family_descends (prefixWord ++ tailWord_83226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83235 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 3, 5]
def baseStart_83235 : Nat := 118140960795 + 83235 * 2 ^ 59
def prefixEnd_83235 : Nat := 4983230072969 + 3 ^ 40 * 83235 * 2
def baseEnd_83235 : Nat := 14246520759029025459905

theorem tailTrace_83235 : CollatzResearch.WordTrace tailWord_83235 prefixEnd_83235 14246520759029025459905 := by
  unfold tailWord_83235
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035829853461285251363159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2023886568974190167575439 3035829853461285251363159)
  ·
    refine ⟨4553744780191927877044739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3035829853461285251363159 4553744780191927877044739)
    ·
      refine ⟨6830617170287891815567109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4553744780191927877044739 6830617170287891815567109)
      ·
        refine ⟨1280740719428979715418833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6830617170287891815567109 1280740719428979715418833)
        ·
          refine ⟨960555539571734786564125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1280740719428979715418833 960555539571734786564125)
          ·
            refine ⟨360208327339400544961547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 960555539571734786564125 360208327339400544961547)
            ·
              refine ⟨540312491009100817442321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360208327339400544961547 540312491009100817442321)
              ·
                refine ⟨405234368256825613081741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540312491009100817442321 405234368256825613081741)
                ·
                  refine ⟨151962888096309604905653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405234368256825613081741 151962888096309604905653)
                  ·
                    refine ⟨14246520759029025459905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 151962888096309604905653 14246520759029025459905)
                    ·
                      rfl

theorem cell23_83235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 3, 5].length) (baseStart_83235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83235 prefixEnd_83235 := by exact prefixLift 83235
  have htrace : WordTrace (prefixWord ++ tailWord_83235) baseStart_83235 baseEnd_83235 := by
    simpa [prefixWord, tailWord_83235, baseEnd_83235] using wordTrace_append hprefix tailTrace_83235
  have hstable : (prefixWord ++ tailWord_83235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83235).length < 2 ^ (prefixWord ++ tailWord_83235).sum := by decide
  have hdescent : baseEnd_83235 < baseStart_83235 := by decide
  rcases family_descends (prefixWord ++ tailWord_83235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83249 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 3, 1, 3]
def baseStart_83249 : Nat := 118140960795 + 83249 * 2 ^ 59
def prefixEnd_83249 : Nat := 4983230072969 + 3 ^ 40 * 83249 * 2
def baseEnd_83249 : Nat := 42746751006250021604651

theorem tailTrace_83249 : CollatzResearch.WordTrace tailWord_83249 prefixEnd_83249 42746751006250021604651 := by
  unfold tailWord_83249
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036340475410565642372801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2024226983607043761581867 3036340475410565642372801)
  ·
    refine ⟨2277255356557924231779601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3036340475410565642372801 2277255356557924231779601)
    ·
      refine ⟨1707941517418443173834701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2277255356557924231779601 1707941517418443173834701)
      ·
        refine ⟨640478069031916190188013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1707941517418443173834701 640478069031916190188013)
        ·
          refine ⟨240179275886968571320505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 640478069031916190188013 240179275886968571320505)
          ·
            refine ⟨180134456915226428490379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240179275886968571320505 180134456915226428490379)
            ·
              refine ⟨270201685372839642735569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180134456915226428490379 270201685372839642735569)
              ·
                refine ⟨202651264029629732051677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270201685372839642735569 202651264029629732051677)
                ·
                  refine ⟨75994224011111149519379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202651264029629732051677 75994224011111149519379)
                  ·
                    refine ⟨113991336016666724279069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75994224011111149519379 113991336016666724279069)
                    ·
                      refine ⟨42746751006250021604651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 113991336016666724279069 42746751006250021604651)
                      ·
                        rfl

theorem cell23_83249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_83249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83249 prefixEnd_83249 := by exact prefixLift 83249
  have htrace : WordTrace (prefixWord ++ tailWord_83249) baseStart_83249 baseEnd_83249 := by
    simpa [prefixWord, tailWord_83249, baseEnd_83249] using wordTrace_append hprefix tailTrace_83249
  have hstable : (prefixWord ++ tailWord_83249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83249).length < 2 ^ (prefixWord ++ tailWord_83249).sum := by decide
  have hdescent : baseEnd_83249 < baseStart_83249 := by decide
  rcases family_descends (prefixWord ++ tailWord_83249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83252 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_83252 : Nat := 118140960795 + 83252 * 2 ^ 59
def prefixEnd_83252 : Nat := 4983230072969 + 3 ^ 40 * 83252 * 2
def baseEnd_83252 : Nat := 14249430482737836622379

theorem tailTrace_83252 : CollatzResearch.WordTrace tailWord_83252 prefixEnd_83252 14249430482737836622379 := by
  unfold tailWord_83252
  simp only [CollatzResearch.WordTrace]
  refine ⟨1518224947199848577366005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2024299929599798103154673 1518224947199848577366005)
  ·
    refine ⟨142333588799985804128063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1518224947199848577366005 142333588799985804128063)
    ·
      refine ⟨213500383199978706192095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142333588799985804128063 213500383199978706192095)
      ·
        refine ⟨320250574799968059288143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213500383199978706192095 320250574799968059288143)
        ·
          refine ⟨480375862199952088932215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320250574799968059288143 480375862199952088932215)
          ·
            refine ⟨720563793299928133398323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480375862199952088932215 720563793299928133398323)
            ·
              refine ⟨1080845689949892200097485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720563793299928133398323 1080845689949892200097485)
              ·
                refine ⟨405317133731209575036557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1080845689949892200097485 405317133731209575036557)
                ·
                  refine ⟨151993925149203590638709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 405317133731209575036557 151993925149203590638709)
                  ·
                    refine ⟨14249430482737836622379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 151993925149203590638709 14249430482737836622379)
                    ·
                      rfl

theorem cell23_83252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_83252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83252 prefixEnd_83252 := by exact prefixLift 83252
  have htrace : WordTrace (prefixWord ++ tailWord_83252) baseStart_83252 baseEnd_83252 := by
    simpa [prefixWord, tailWord_83252, baseEnd_83252] using wordTrace_append hprefix tailTrace_83252
  have hstable : (prefixWord ++ tailWord_83252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83252).length < 2 ^ (prefixWord ++ tailWord_83252).sum := by decide
  have hdescent : baseEnd_83252 < baseStart_83252 := by decide
  rcases family_descends (prefixWord ++ tailWord_83252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83289 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2]
def baseStart_83289 : Nat := 118140960795 + 83289 * 2 ^ 59
def prefixEnd_83289 : Nat := 4983230072969 + 3 ^ 40 * 83289 * 2
def baseEnd_83289 : Nat := 42767290232429865104467

theorem tailTrace_83289 : CollatzResearch.WordTrace tailWord_83289 prefixEnd_83289 42767290232429865104467 := by
  unfold tailWord_83289
  simp only [CollatzResearch.WordTrace]
  refine ⟨3037799395265652473828921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2025199596843768315885947 3037799395265652473828921)
  ·
    refine ⟨2278349546449239355371691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3037799395265652473828921 2278349546449239355371691)
    ·
      refine ⟨3417524319673859033057537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2278349546449239355371691 3417524319673859033057537)
      ·
        refine ⟨2563143239755394274793153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3417524319673859033057537 2563143239755394274793153)
        ·
          refine ⟨1922357429816545706094865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2563143239755394274793153 1922357429816545706094865)
          ·
            refine ⟨1441768072362409279571149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1922357429816545706094865 1441768072362409279571149)
            ·
              refine ⟨540663027135903479839181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1441768072362409279571149 540663027135903479839181)
              ·
                refine ⟨202748635175963804939693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 540663027135903479839181 202748635175963804939693)
                ·
                  refine ⟨76030738190986426852385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202748635175963804939693 76030738190986426852385)
                  ·
                    refine ⟨57023053643239820139289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76030738190986426852385 57023053643239820139289)
                    ·
                      refine ⟨42767290232429865104467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57023053643239820139289 42767290232429865104467)
                      ·
                        rfl

theorem cell23_83289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 2, 2].length) (baseStart_83289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83289 prefixEnd_83289 := by exact prefixLift 83289
  have htrace : WordTrace (prefixWord ++ tailWord_83289) baseStart_83289 baseEnd_83289 := by
    simpa [prefixWord, tailWord_83289, baseEnd_83289] using wordTrace_append hprefix tailTrace_83289
  have hstable : (prefixWord ++ tailWord_83289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83289).length < 2 ^ (prefixWord ++ tailWord_83289).sum := by decide
  have hdescent : baseEnd_83289 < baseStart_83289 := by decide
  rcases family_descends (prefixWord ++ tailWord_83289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83306 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_83306 : Nat := 118140960795 + 83306 * 2 ^ 59
def prefixEnd_83306 : Nat := 4983230072969 + 3 ^ 40 * 83306 * 2
def baseEnd_83306 : Nat := 42776019403556298591889

theorem tailTrace_83306 : CollatzResearch.WordTrace tailWord_83306 prefixEnd_83306 42776019403556298591889 := by
  unfold tailWord_83306
  simp only [CollatzResearch.WordTrace]
  refine ⟨759604859051016094299443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2025612957469376251465181 759604859051016094299443)
  ·
    refine ⟨1139407288576524141449165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 759604859051016094299443 1139407288576524141449165)
    ·
      refine ⟨427277733216196553043437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1139407288576524141449165 427277733216196553043437)
      ·
        refine ⟨160229149956073707391289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 427277733216196553043437 160229149956073707391289)
        ·
          refine ⟨120171862467055280543467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160229149956073707391289 120171862467055280543467)
          ·
            refine ⟨180257793700582920815201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120171862467055280543467 180257793700582920815201)
            ·
              refine ⟨135193345275437190611401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180257793700582920815201 135193345275437190611401)
              ·
                refine ⟨101395008956577892958551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135193345275437190611401 101395008956577892958551)
                ·
                  refine ⟨152092513434866839437827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101395008956577892958551 152092513434866839437827)
                  ·
                    refine ⟨228138770152300259156741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 152092513434866839437827 228138770152300259156741)
                    ·
                      refine ⟨42776019403556298591889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 228138770152300259156741 42776019403556298591889)
                      ·
                        rfl

theorem cell23_83306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_83306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83306 prefixEnd_83306 := by exact prefixLift 83306
  have htrace : WordTrace (prefixWord ++ tailWord_83306) baseStart_83306 baseEnd_83306 := by
    simpa [prefixWord, tailWord_83306, baseEnd_83306] using wordTrace_append hprefix tailTrace_83306
  have hstable : (prefixWord ++ tailWord_83306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83306).length < 2 ^ (prefixWord ++ tailWord_83306).sum := by decide
  have hdescent : baseEnd_83306 < baseStart_83306 := by decide
  rcases family_descends (prefixWord ++ tailWord_83306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83309 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_83309 : Nat := 118140960795 + 83309 * 2 ^ 59
def prefixEnd_83309 : Nat := 4983230072969 + 3 ^ 40 * 83309 * 2
def baseEnd_83309 : Nat := 42777559845519786854375

theorem tailTrace_83309 : CollatzResearch.WordTrace tailWord_83309 prefixEnd_83309 42777559845519786854375 := by
  unfold tailWord_83309
  simp only [CollatzResearch.WordTrace]
  refine ⟨3038528855193195889556981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2025685903462130593037987 3038528855193195889556981)
  ·
    refine ⟨284862080174362114645967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3038528855193195889556981 284862080174362114645967)
    ·
      refine ⟨427293120261543171968951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284862080174362114645967 427293120261543171968951)
      ·
        refine ⟨640939680392314757953427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427293120261543171968951 640939680392314757953427)
        ·
          refine ⟨961409520588472136930141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640939680392314757953427 961409520588472136930141)
          ·
            refine ⟨360528570220677051348803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 961409520588472136930141 360528570220677051348803)
            ·
              refine ⟨540792855331015577023205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360528570220677051348803 540792855331015577023205)
              ·
                refine ⟨101398660374565420691851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540792855331015577023205 101398660374565420691851)
                ·
                  refine ⟨152097990561848131037777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101398660374565420691851 152097990561848131037777)
                  ·
                    refine ⟨114073492921386098278333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152097990561848131037777 114073492921386098278333)
                    ·
                      refine ⟨42777559845519786854375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 114073492921386098278333 42777559845519786854375)
                      ·
                        rfl

theorem cell23_83309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_83309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83309 prefixEnd_83309 := by exact prefixLift 83309
  have htrace : WordTrace (prefixWord ++ tailWord_83309) baseStart_83309 baseEnd_83309 := by
    simpa [prefixWord, tailWord_83309, baseEnd_83309] using wordTrace_append hprefix tailTrace_83309
  have hstable : (prefixWord ++ tailWord_83309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83309).length < 2 ^ (prefixWord ++ tailWord_83309).sum := by decide
  have hdescent : baseEnd_83309 < baseStart_83309 := by decide
  rcases family_descends (prefixWord ++ tailWord_83309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83329 : List Nat := [1, 2, 4, 3, 3, 1, 9]
def baseStart_83329 : Nat := 118140960795 + 83329 * 2 ^ 59
def prefixEnd_83329 : Nat := 4983230072969 + 3 ^ 40 * 83329 * 2
def baseEnd_83329 : Nat := 528244808130984056843

theorem tailTrace_83329 : CollatzResearch.WordTrace tailWord_83329 prefixEnd_83329 528244808130984056843 := by
  unfold tailWord_83329
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039258315120739305285041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2026172210080492870190027 3039258315120739305285041)
  ·
    refine ⟨2279443736340554478963781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3039258315120739305285041 2279443736340554478963781)
    ·
      refine ⟨427395700563853964805709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2279443736340554478963781 427395700563853964805709)
      ·
        refine ⟨160273387711445236802141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 427395700563853964805709 160273387711445236802141)
        ·
          refine ⟨60102520391791963800803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160273387711445236802141 60102520391791963800803)
          ·
            refine ⟨90153780587687945701205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60102520391791963800803 90153780587687945701205)
            ·
              refine ⟨528244808130984056843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 90153780587687945701205 528244808130984056843)
              ·
                rfl

theorem cell23_83329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 9].length) (baseStart_83329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83329 prefixEnd_83329 := by exact prefixLift 83329
  have htrace : WordTrace (prefixWord ++ tailWord_83329) baseStart_83329 baseEnd_83329 := by
    simpa [prefixWord, tailWord_83329, baseEnd_83329] using wordTrace_append hprefix tailTrace_83329
  have hstable : (prefixWord ++ tailWord_83329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83329).length < 2 ^ (prefixWord ++ tailWord_83329).sum := by decide
  have hdescent : baseEnd_83329 < baseStart_83329 := by decide
  rcases family_descends (prefixWord ++ tailWord_83329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83339 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 2, 1, 3]
def baseStart_83339 : Nat := 118140960795 + 83339 * 2 ^ 59
def prefixEnd_83339 : Nat := 4983230072969 + 3 ^ 40 * 83339 * 2
def baseEnd_83339 : Nat := 42792964265154669479237

theorem tailTrace_83339 : CollatzResearch.WordTrace tailWord_83339 prefixEnd_83339 42792964265154669479237 := by
  unfold tailWord_83339
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039623045084511013149071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2026415363389674008766047 3039623045084511013149071)
  ·
    refine ⟨4559434567626766519723607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3039623045084511013149071 4559434567626766519723607)
    ·
      refine ⟨6839151851440149779585411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4559434567626766519723607 6839151851440149779585411)
      ·
        refine ⟨10258727777160224669378117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6839151851440149779585411 10258727777160224669378117)
        ·
          refine ⟨1923511458217542125508397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10258727777160224669378117 1923511458217542125508397)
          ·
            refine ⟨721316796831578297065649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1923511458217542125508397 721316796831578297065649)
            ·
              refine ⟨540987597623683722799237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 721316796831578297065649 540987597623683722799237)
              ·
                refine ⟨101435174554440698024857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540987597623683722799237 101435174554440698024857)
                ·
                  refine ⟨76076380915830523518643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101435174554440698024857 76076380915830523518643)
                  ·
                    refine ⟨114114571373745785277965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76076380915830523518643 114114571373745785277965)
                    ·
                      refine ⟨42792964265154669479237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 114114571373745785277965 42792964265154669479237)
                      ·
                        rfl

theorem cell23_83339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 1, 3].length) (baseStart_83339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83339 prefixEnd_83339 := by exact prefixLift 83339
  have htrace : WordTrace (prefixWord ++ tailWord_83339) baseStart_83339 baseEnd_83339 := by
    simpa [prefixWord, tailWord_83339, baseEnd_83339] using wordTrace_append hprefix tailTrace_83339
  have hstable : (prefixWord ++ tailWord_83339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83339).length < 2 ^ (prefixWord ++ tailWord_83339).sum := by decide
  have hdescent : baseEnd_83339 < baseStart_83339 := by decide
  rcases family_descends (prefixWord ++ tailWord_83339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83345 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_83345 : Nat := 118140960795 + 83345 * 2 ^ 59
def prefixEnd_83345 : Nat := 4983230072969 + 3 ^ 40 * 83345 * 2
def baseEnd_83345 : Nat := 42796045149081646004209

theorem tailTrace_83345 : CollatzResearch.WordTrace tailWord_83345 prefixEnd_83345 42796045149081646004209 := by
  unfold tailWord_83345
  simp only [CollatzResearch.WordTrace]
  refine ⟨3039841883062774037867489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2026561255375182691911659 3039841883062774037867489)
  ·
    refine ⟨2279881412297080528400617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3039841883062774037867489 2279881412297080528400617)
    ·
      refine ⟨1709911059222810396300463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2279881412297080528400617 1709911059222810396300463)
      ·
        refine ⟨2564866588834215594450695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1709911059222810396300463 2564866588834215594450695)
        ·
          refine ⟨3847299883251323391676043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564866588834215594450695 3847299883251323391676043)
          ·
            refine ⟨5770949824876985087514065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3847299883251323391676043 5770949824876985087514065)
            ·
              refine ⟨4328212368657738815635549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5770949824876985087514065 4328212368657738815635549)
              ·
                refine ⟨1623079638246652055863331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4328212368657738815635549 1623079638246652055863331)
                ·
                  refine ⟨2434619457369978083794997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1623079638246652055863331 2434619457369978083794997)
                  ·
                    refine ⟨228245574128435445355781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2434619457369978083794997 228245574128435445355781)
                    ·
                      refine ⟨42796045149081646004209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 228245574128435445355781 42796045149081646004209)
                      ·
                        rfl

theorem cell23_83345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_83345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83345 prefixEnd_83345 := by exact prefixLift 83345
  have htrace : WordTrace (prefixWord ++ tailWord_83345) baseStart_83345 baseEnd_83345 := by
    simpa [prefixWord, tailWord_83345, baseEnd_83345] using wordTrace_append hprefix tailTrace_83345
  have hstable : (prefixWord ++ tailWord_83345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83345).length < 2 ^ (prefixWord ++ tailWord_83345).sum := by decide
  have hdescent : baseEnd_83345 < baseStart_83345 := by decide
  rcases family_descends (prefixWord ++ tailWord_83345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83379 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 6, 2, 2]
def baseStart_83379 : Nat := 118140960795 + 83379 * 2 ^ 59
def prefixEnd_83379 : Nat := 4983230072969 + 3 ^ 40 * 83379 * 2
def baseEnd_83379 : Nat := 42813503491334512979053

theorem tailTrace_83379 : CollatzResearch.WordTrace tailWord_83379 prefixEnd_83379 42813503491334512979053 := by
  unfold tailWord_83379
  simp only [CollatzResearch.WordTrace]
  refine ⟨3041081964939597844605191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2027387976626398563070127 3041081964939597844605191)
  ·
    refine ⟨4561622947409396766907787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3041081964939597844605191 4561622947409396766907787)
    ·
      refine ⟨6842434421114095150361681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4561622947409396766907787 6842434421114095150361681)
      ·
        refine ⟨5131825815835571362771261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6842434421114095150361681 5131825815835571362771261)
        ·
          refine ⟨1924434680938339261039223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5131825815835571362771261 1924434680938339261039223)
          ·
            refine ⟨2886652021407508891558835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924434680938339261039223 2886652021407508891558835)
            ·
              refine ⟨4329978032111263337338253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2886652021407508891558835 4329978032111263337338253)
              ·
                refine ⟨1623741762041723751501845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4329978032111263337338253 1623741762041723751501845)
                ·
                  refine ⟨76112895095705800851649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1623741762041723751501845 76112895095705800851649)
                  ·
                    refine ⟨57084671321779350638737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76112895095705800851649 57084671321779350638737)
                    ·
                      refine ⟨42813503491334512979053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57084671321779350638737 42813503491334512979053)
                      ·
                        rfl

theorem cell23_83379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 2, 2].length) (baseStart_83379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83379 prefixEnd_83379 := by exact prefixLift 83379
  have htrace : WordTrace (prefixWord ++ tailWord_83379) baseStart_83379 baseEnd_83379 := by
    simpa [prefixWord, tailWord_83379, baseEnd_83379] using wordTrace_append hprefix tailTrace_83379
  have hstable : (prefixWord ++ tailWord_83379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83379).length < 2 ^ (prefixWord ++ tailWord_83379).sum := by decide
  have hdescent : baseEnd_83379 < baseStart_83379 := by decide
  rcases family_descends (prefixWord ++ tailWord_83379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83395 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 7]
def baseStart_83395 : Nat := 118140960795 + 83395 * 2 ^ 59
def prefixEnd_83395 : Nat := 4983230072969 + 3 ^ 40 * 83395 * 2
def baseEnd_83395 : Nat := 42821719181806450378979

theorem tailTrace_83395 : CollatzResearch.WordTrace tailWord_83395 prefixEnd_83395 42821719181806450378979 := by
  unfold tailWord_83395
  simp only [CollatzResearch.WordTrace]
  refine ⟨3041665532881632577187639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2027777021921088384791759 3041665532881632577187639)
  ·
    refine ⟨4562498299322448865781459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3041665532881632577187639 4562498299322448865781459)
    ·
      refine ⟨6843747448983673298672189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4562498299322448865781459 6843747448983673298672189)
      ·
        refine ⟨2566405293368877487002071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6843747448983673298672189 2566405293368877487002071)
        ·
          refine ⟨3849607940053316230503107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566405293368877487002071 3849607940053316230503107)
          ·
            refine ⟨5774411910079974345754661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3849607940053316230503107 5774411910079974345754661)
            ·
              refine ⟨1082702233139995189828999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5774411910079974345754661 1082702233139995189828999)
              ·
                refine ⟨1624053349709992784743499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1082702233139995189828999 1624053349709992784743499)
                ·
                  refine ⟨2436080024564989177115249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1624053349709992784743499 2436080024564989177115249)
                  ·
                    refine ⟨1827060018423741882836437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2436080024564989177115249 1827060018423741882836437)
                    ·
                      refine ⟨42821719181806450378979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1827060018423741882836437 42821719181806450378979)
                      ·
                        rfl

theorem cell23_83395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_83395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83395 prefixEnd_83395 := by exact prefixLift 83395
  have htrace : WordTrace (prefixWord ++ tailWord_83395) baseStart_83395 baseEnd_83395 := by
    simpa [prefixWord, tailWord_83395, baseEnd_83395] using wordTrace_append hprefix tailTrace_83395
  have hstable : (prefixWord ++ tailWord_83395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83395).length < 2 ^ (prefixWord ++ tailWord_83395).sum := by decide
  have hdescent : baseEnd_83395 < baseStart_83395 := by decide
  rcases family_descends (prefixWord ++ tailWord_83395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83432 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 1, 7]
def baseStart_83432 : Nat := 118140960795 + 83432 * 2 ^ 59
def prefixEnd_83432 : Nat := 4983230072969 + 3 ^ 40 * 83432 * 2
def baseEnd_83432 : Nat := 14280239322007601872103

theorem tailTrace_83432 : CollatzResearch.WordTrace tailWord_83432 prefixEnd_83432 14280239322007601872103 := by
  unfold tailWord_83432
  simp only [CollatzResearch.WordTrace]
  refine ⟨1521507516873793948142275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2028676689165058597523033 1521507516873793948142275)
  ·
    refine ⟨2282261275310690922213413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1521507516873793948142275 2282261275310690922213413)
    ·
      refine ⟨427923989120754547915015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2282261275310690922213413 427923989120754547915015)
      ·
        refine ⟨641885983681131821872523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427923989120754547915015 641885983681131821872523)
        ·
          refine ⟨962828975521697732808785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641885983681131821872523 962828975521697732808785)
          ·
            refine ⟨722121731641273299606589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 962828975521697732808785 722121731641273299606589)
            ·
              refine ⟨270795649365477487352471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722121731641273299606589 270795649365477487352471)
              ·
                refine ⟨406193474048216231028707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270795649365477487352471 406193474048216231028707)
                ·
                  refine ⟨609290211072324346543061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406193474048216231028707 609290211072324346543061)
                  ·
                    refine ⟨14280239322007601872103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 609290211072324346543061 14280239322007601872103)
                    ·
                      rfl

theorem cell23_83432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_83432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83432 prefixEnd_83432 := by exact prefixLift 83432
  have htrace : WordTrace (prefixWord ++ tailWord_83432) baseStart_83432 baseEnd_83432 := by
    simpa [prefixWord, tailWord_83432, baseEnd_83432] using wordTrace_append hprefix tailTrace_83432
  have hstable : (prefixWord ++ tailWord_83432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83432).length < 2 ^ (prefixWord ++ tailWord_83432).sum := by decide
  have hdescent : baseEnd_83432 < baseStart_83432 := by decide
  rcases family_descends (prefixWord ++ tailWord_83432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83482 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_83482 : Nat := 118140960795 + 83482 * 2 ^ 59
def prefixEnd_83482 : Nat := 4983230072969 + 3 ^ 40 * 83482 * 2
def baseEnd_83482 : Nat := 42866391998747609991079

theorem tailTrace_83482 : CollatzResearch.WordTrace tailWord_83482 prefixEnd_83482 42866391998747609991079 := by
  unfold tailWord_83482
  simp only [CollatzResearch.WordTrace]
  refine ⟨761209670891611608901175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2029892455710964290403133 761209670891611608901175)
  ·
    refine ⟨1141814506337417413351763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 761209670891611608901175 1141814506337417413351763)
    ·
      refine ⟨1712721759506126120027645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141814506337417413351763 1712721759506126120027645)
      ·
        refine ⟨642270659814797295010367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1712721759506126120027645 642270659814797295010367)
        ·
          refine ⟨963405989722195942515551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642270659814797295010367 963405989722195942515551)
          ·
            refine ⟨1445108984583293913773327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963405989722195942515551 1445108984583293913773327)
            ·
              refine ⟨2167663476874940870659991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1445108984583293913773327 2167663476874940870659991)
              ·
                refine ⟨3251495215312411305989987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2167663476874940870659991 3251495215312411305989987)
                ·
                  refine ⟨4877242822968616958984981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3251495215312411305989987 4877242822968616958984981)
                  ·
                    refine ⟨228620757326653919952421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4877242822968616958984981 228620757326653919952421)
                    ·
                      refine ⟨42866391998747609991079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 228620757326653919952421 42866391998747609991079)
                      ·
                        rfl

theorem cell23_83482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_83482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83482 prefixEnd_83482 := by exact prefixLift 83482
  have htrace : WordTrace (prefixWord ++ tailWord_83482) baseStart_83482 baseEnd_83482 := by
    simpa [prefixWord, tailWord_83482, baseEnd_83482] using wordTrace_append hprefix tailTrace_83482
  have hstable : (prefixWord ++ tailWord_83482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83482).length < 2 ^ (prefixWord ++ tailWord_83482).sum := by decide
  have hdescent : baseEnd_83482 < baseStart_83482 := by decide
  rcases family_descends (prefixWord ++ tailWord_83482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83489 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_83489 : Nat := 118140960795 + 83489 * 2 ^ 59
def prefixEnd_83489 : Nat := 4983230072969 + 3 ^ 40 * 83489 * 2
def baseEnd_83489 : Nat := 42869986363329082603547

theorem tailTrace_83489 : CollatzResearch.WordTrace tailWord_83489 prefixEnd_83489 42869986363329082603547 := by
  unfold tailWord_83489
  simp only [CollatzResearch.WordTrace]
  refine ⟨3045093994541086631109521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2030062663027391087406347 3045093994541086631109521)
  ·
    refine ⟨2283820495905814973332141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3045093994541086631109521 2283820495905814973332141)
    ·
      refine ⟨856432685964680614999553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2283820495905814973332141 856432685964680614999553)
      ·
        refine ⟨642324514473510461249665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 856432685964680614999553 642324514473510461249665)
        ·
          refine ⟨481743385855132845937249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 642324514473510461249665 481743385855132845937249)
          ·
            refine ⟨361307539391349634452937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481743385855132845937249 361307539391349634452937)
            ·
              refine ⟨270980654543512225839703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361307539391349634452937 270980654543512225839703)
              ·
                refine ⟨406470981815268338759555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270980654543512225839703 406470981815268338759555)
                ·
                  refine ⟨609706472722902508139333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 406470981815268338759555 609706472722902508139333)
                  ·
                    refine ⟨114319963635544220276125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 609706472722902508139333 114319963635544220276125)
                    ·
                      refine ⟨42869986363329082603547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 114319963635544220276125 42869986363329082603547)
                      ·
                        rfl

theorem cell23_83489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_83489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83489 prefixEnd_83489 := by exact prefixLift 83489
  have htrace : WordTrace (prefixWord ++ tailWord_83489) baseStart_83489 baseEnd_83489 := by
    simpa [prefixWord, tailWord_83489, baseEnd_83489] using wordTrace_append hprefix tailTrace_83489
  have hstable : (prefixWord ++ tailWord_83489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83489).length < 2 ^ (prefixWord ++ tailWord_83489).sum := by decide
  have hdescent : baseEnd_83489 < baseStart_83489 := by decide
  rcases family_descends (prefixWord ++ tailWord_83489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83529 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 3, 5, 2]
def baseStart_83529 : Nat := 118140960795 + 83529 * 2 ^ 59
def prefixEnd_83529 : Nat := 4983230072969 + 3 ^ 40 * 83529 * 2
def baseEnd_83529 : Nat := 42890525589508926103363

theorem tailTrace_83529 : CollatzResearch.WordTrace tailWord_83529 prefixEnd_83529 42890525589508926103363 := by
  unfold tailWord_83529
  simp only [CollatzResearch.WordTrace]
  refine ⟨3046552914396173462565641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2031035276264115641710427 3046552914396173462565641)
  ·
    refine ⟨2284914685797130096924231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3046552914396173462565641 2284914685797130096924231)
    ·
      refine ⟨3427372028695695145386347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2284914685797130096924231 3427372028695695145386347)
      ·
        refine ⟨5141058043043542718079521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3427372028695695145386347 5141058043043542718079521)
        ·
          refine ⟨3855793532282657038559641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5141058043043542718079521 3855793532282657038559641)
          ·
            refine ⟨2891845149211992778919731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3855793532282657038559641 2891845149211992778919731)
            ·
              refine ⟨4337767723817989168379597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2891845149211992778919731 4337767723817989168379597)
              ·
                refine ⟨1626662896431745938142349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4337767723817989168379597 1626662896431745938142349)
                ·
                  refine ⟨609998586161904726803381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1626662896431745938142349 609998586161904726803381)
                  ·
                    refine ⟨57187367452678568137817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 609998586161904726803381 57187367452678568137817)
                    ·
                      refine ⟨42890525589508926103363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57187367452678568137817 42890525589508926103363)
                      ·
                        rfl

theorem cell23_83529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 5, 2].length) (baseStart_83529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83529 prefixEnd_83529 := by exact prefixLift 83529
  have htrace : WordTrace (prefixWord ++ tailWord_83529) baseStart_83529 baseEnd_83529 := by
    simpa [prefixWord, tailWord_83529, baseEnd_83529] using wordTrace_append hprefix tailTrace_83529
  have hstable : (prefixWord ++ tailWord_83529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83529).length < 2 ^ (prefixWord ++ tailWord_83529).sum := by decide
  have hdescent : baseEnd_83529 < baseStart_83529 := by decide
  rcases family_descends (prefixWord ++ tailWord_83529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83553 : List Nat := [1, 2, 3, 1, 1, 3, 2, 5, 1, 1, 3]
def baseStart_83553 : Nat := 118140960795 + 83553 * 2 ^ 59
def prefixEnd_83553 : Nat := 4983230072969 + 3 ^ 40 * 83553 * 2
def baseEnd_83553 : Nat := 42902849125216832203253

theorem tailTrace_83553 : CollatzResearch.WordTrace tailWord_83553 prefixEnd_83553 42902849125216832203253 := by
  unfold tailWord_83553
  simp only [CollatzResearch.WordTrace]
  refine ⟨3047428266309225561439313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2031618844206150374292875 3047428266309225561439313)
  ·
    refine ⟨2285571199731919171079485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3047428266309225561439313 2285571199731919171079485)
    ·
      refine ⟨857089199899469689154807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2285571199731919171079485 857089199899469689154807)
      ·
        refine ⟨1285633799849204533732211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857089199899469689154807 1285633799849204533732211)
        ·
          refine ⟨1928450699773806800598317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285633799849204533732211 1928450699773806800598317)
          ·
            refine ⟨723169012415177550224369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1928450699773806800598317 723169012415177550224369)
            ·
              refine ⟨542376759311383162668277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 723169012415177550224369 542376759311383162668277)
              ·
                refine ⟨50847821185442171500151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 542376759311383162668277 50847821185442171500151)
                ·
                  refine ⟨76271731778163257250227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50847821185442171500151 76271731778163257250227)
                  ·
                    refine ⟨114407597667244885875341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76271731778163257250227 114407597667244885875341)
                    ·
                      refine ⟨42902849125216832203253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 114407597667244885875341 42902849125216832203253)
                      ·
                        rfl

theorem cell23_83553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_83553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83553 prefixEnd_83553 := by exact prefixLift 83553
  have htrace : WordTrace (prefixWord ++ tailWord_83553) baseStart_83553 baseEnd_83553 := by
    simpa [prefixWord, tailWord_83553, baseEnd_83553] using wordTrace_append hprefix tailTrace_83553
  have hstable : (prefixWord ++ tailWord_83553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83553).length < 2 ^ (prefixWord ++ tailWord_83553).sum := by decide
  have hdescent : baseEnd_83553 < baseStart_83553 := by decide
  rcases family_descends (prefixWord ++ tailWord_83553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83569 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 4, 4]
def baseStart_83569 : Nat := 118140960795 + 83569 * 2 ^ 59
def prefixEnd_83569 : Nat := 4983230072969 + 3 ^ 40 * 83569 * 2
def baseEnd_83569 : Nat := 14303688271896256534393

theorem tailTrace_83569 : CollatzResearch.WordTrace tailWord_83569 prefixEnd_83569 14303688271896256534393 := by
  unfold tailWord_83569
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048011834251260294021761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2032007889500840196014507 3048011834251260294021761)
  ·
    refine ⟨2286008875688445220516321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3048011834251260294021761 2286008875688445220516321)
    ·
      refine ⟨1714506656766333915387241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2286008875688445220516321 1714506656766333915387241)
      ·
        refine ⟨1285879992574750436540431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1714506656766333915387241 1285879992574750436540431)
        ·
          refine ⟨1928819988862125654810647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1285879992574750436540431 1928819988862125654810647)
          ·
            refine ⟨2893229983293188482215971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1928819988862125654810647 2893229983293188482215971)
            ·
              refine ⟨4339844974939782723323957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2893229983293188482215971 4339844974939782723323957)
              ·
                refine ⟨406860466400604630311621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4339844974939782723323957 406860466400604630311621)
                ·
                  refine ⟨76286337450113368183429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406860466400604630311621 76286337450113368183429)
                  ·
                    refine ⟨14303688271896256534393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 76286337450113368183429 14303688271896256534393)
                    ·
                      rfl

theorem cell23_83569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_83569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83569 prefixEnd_83569 := by exact prefixLift 83569
  have htrace : WordTrace (prefixWord ++ tailWord_83569) baseStart_83569 baseEnd_83569 := by
    simpa [prefixWord, tailWord_83569, baseEnd_83569] using wordTrace_append hprefix tailTrace_83569
  have hstable : (prefixWord ++ tailWord_83569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83569).length < 2 ^ (prefixWord ++ tailWord_83569).sum := by decide
  have hdescent : baseEnd_83569 < baseStart_83569 := by decide
  rcases family_descends (prefixWord ++ tailWord_83569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83570 : List Nat := [3, 2, 1, 2, 3, 2, 1, 4, 1, 1, 3]
def baseStart_83570 : Nat := 118140960795 + 83570 * 2 ^ 59
def prefixEnd_83570 : Nat := 4983230072969 + 3 ^ 40 * 83570 * 2
def baseEnd_83570 : Nat := 42911578296343265690675

theorem tailTrace_83570 : CollatzResearch.WordTrace tailWord_83570 prefixEnd_83570 42911578296343265690675 := by
  unfold tailWord_83570
  simp only [CollatzResearch.WordTrace]
  refine ⟨762012076811909366202041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2032032204831758309872109 762012076811909366202041)
  ·
    refine ⟨571509057608932024651531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 762012076811909366202041 571509057608932024651531)
    ·
      refine ⟨857263586413398036977297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571509057608932024651531 857263586413398036977297)
      ·
        refine ⟨642947689810048527732973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 857263586413398036977297 642947689810048527732973)
        ·
          refine ⟨241105383678768197899865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 642947689810048527732973 241105383678768197899865)
          ·
            refine ⟨180829037759076148424899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241105383678768197899865 180829037759076148424899)
            ·
              refine ⟨271243556638614222637349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180829037759076148424899 271243556638614222637349)
              ·
                refine ⟨50858166869740166744503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 271243556638614222637349 50858166869740166744503)
                ·
                  refine ⟨76287250304610250116755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50858166869740166744503 76287250304610250116755)
                  ·
                    refine ⟨114430875456915375175133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76287250304610250116755 114430875456915375175133)
                    ·
                      refine ⟨42911578296343265690675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 114430875456915375175133 42911578296343265690675)
                      ·
                        rfl

theorem cell23_83570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_83570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83570 prefixEnd_83570 := by exact prefixLift 83570
  have htrace : WordTrace (prefixWord ++ tailWord_83570) baseStart_83570 baseEnd_83570 := by
    simpa [prefixWord, tailWord_83570, baseEnd_83570] using wordTrace_append hprefix tailTrace_83570
  have hstable : (prefixWord ++ tailWord_83570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83570).length < 2 ^ (prefixWord ++ tailWord_83570).sum := by decide
  have hdescent : baseEnd_83570 < baseStart_83570 := by decide
  rcases family_descends (prefixWord ++ tailWord_83570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83579 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 3]
def baseStart_83579 : Nat := 118140960795 + 83579 * 2 ^ 59
def prefixEnd_83579 : Nat := 4983230072969 + 3 ^ 40 * 83579 * 2
def baseEnd_83579 : Nat := 42916199622233730478133

theorem tailTrace_83579 : CollatzResearch.WordTrace tailWord_83579 prefixEnd_83579 42916199622233730478133 := by
  unfold tailWord_83579
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048376564215032001885791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2032251042810021334590527 3048376564215032001885791)
  ·
    refine ⟨4572564846322548002828687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3048376564215032001885791 4572564846322548002828687)
    ·
      refine ⟨6858847269483822004243031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4572564846322548002828687 6858847269483822004243031)
      ·
        refine ⟨10288270904225733006364547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6858847269483822004243031 10288270904225733006364547)
        ·
          refine ⟨15432406356338599509546821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10288270904225733006364547 15432406356338599509546821)
          ·
            refine ⟨2893576191813487408040029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15432406356338599509546821 2893576191813487408040029)
            ·
              refine ⟨1085091071930057778015011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2893576191813487408040029 1085091071930057778015011)
              ·
                refine ⟨1627636607895086667022517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1085091071930057778015011 1627636607895086667022517)
                ·
                  refine ⟨152590931990164375033361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1627636607895086667022517 152590931990164375033361)
                  ·
                    refine ⟨114443198992623281275021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152590931990164375033361 114443198992623281275021)
                    ·
                      refine ⟨42916199622233730478133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 114443198992623281275021 42916199622233730478133)
                      ·
                        rfl

theorem cell23_83579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 3].length) (baseStart_83579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83579 prefixEnd_83579 := by exact prefixLift 83579
  have htrace : WordTrace (prefixWord ++ tailWord_83579) baseStart_83579 baseEnd_83579 := by
    simpa [prefixWord, tailWord_83579, baseEnd_83579] using wordTrace_append hprefix tailTrace_83579
  have hstable : (prefixWord ++ tailWord_83579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83579).length < 2 ^ (prefixWord ++ tailWord_83579).sum := by decide
  have hdescent : baseEnd_83579 < baseStart_83579 := by decide
  rcases family_descends (prefixWord ++ tailWord_83579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83596 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 1, 2, 3]
def baseStart_83596 : Nat := 118140960795 + 83596 * 2 ^ 59
def prefixEnd_83596 : Nat := 4983230072969 + 3 ^ 40 * 83596 * 2
def baseEnd_83596 : Nat := 42924928793360163965555

theorem tailTrace_83596 : CollatzResearch.WordTrace tailWord_83596 prefixEnd_83596 42924928793360163965555 := by
  unfold tailWord_83596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1524498302576721952627321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2032664403435629270169761 1524498302576721952627321)
  ·
    refine ⟨1143373726932541464470491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1524498302576721952627321 1143373726932541464470491)
    ·
      refine ⟨1715060590398812196705737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1143373726932541464470491 1715060590398812196705737)
      ·
        refine ⟨1286295442799109147529303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1715060590398812196705737 1286295442799109147529303)
        ·
          refine ⟨1929443164198663721293955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286295442799109147529303 1929443164198663721293955)
          ·
            refine ⟨2894164746297995581940933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1929443164198663721293955 2894164746297995581940933)
            ·
              refine ⟨542655889930874171613925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2894164746297995581940933 542655889930874171613925)
              ·
                refine ⟨101747979362038907177611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 542655889930874171613925 101747979362038907177611)
                ·
                  refine ⟨152621969043058360766417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101747979362038907177611 152621969043058360766417)
                  ·
                    refine ⟨114466476782293770574813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 152621969043058360766417 114466476782293770574813)
                    ·
                      refine ⟨42924928793360163965555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 114466476782293770574813 42924928793360163965555)
                      ·
                        rfl

theorem cell23_83596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_83596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83596 prefixEnd_83596 := by exact prefixLift 83596
  have htrace : WordTrace (prefixWord ++ tailWord_83596) baseStart_83596 baseEnd_83596 := by
    simpa [prefixWord, tailWord_83596, baseEnd_83596] using wordTrace_append hprefix tailTrace_83596
  have hstable : (prefixWord ++ tailWord_83596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83596).length < 2 ^ (prefixWord ++ tailWord_83596).sum := by decide
  have hdescent : baseEnd_83596 < baseStart_83596 := by decide
  rcases family_descends (prefixWord ++ tailWord_83596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83609 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 3, 3, 3]
def baseStart_83609 : Nat := 118140960795 + 83609 * 2 ^ 59
def prefixEnd_83609 : Nat := 4983230072969 + 3 ^ 40 * 83609 * 2
def baseEnd_83609 : Nat := 42931604041868613102995

theorem tailTrace_83609 : CollatzResearch.WordTrace tailWord_83609 prefixEnd_83609 42931604041868613102995 := by
  unfold tailWord_83609
  simp only [CollatzResearch.WordTrace]
  refine ⟨3049470754106347125477881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2032980502737564750318587 3049470754106347125477881)
  ·
    refine ⟨2287103065579760344108411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3049470754106347125477881 2287103065579760344108411)
    ·
      refine ⟨3430654598369640516162617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2287103065579760344108411 3430654598369640516162617)
      ·
        refine ⟨2572990948777230387121963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3430654598369640516162617 2572990948777230387121963)
        ·
          refine ⟨3859486423165845580682945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2572990948777230387121963 3859486423165845580682945)
          ·
            refine ⟨2894614817374384185512209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3859486423165845580682945 2894614817374384185512209)
            ·
              refine ⟨2170961113030788139134157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2894614817374384185512209 2170961113030788139134157)
              ·
                refine ⟨814110417386545552175309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2170961113030788139134157 814110417386545552175309)
                ·
                  refine ⟨305291406519954582065741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 814110417386545552175309 305291406519954582065741)
                  ·
                    refine ⟨114484277444982968274653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 305291406519954582065741 114484277444982968274653)
                    ·
                      refine ⟨42931604041868613102995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 114484277444982968274653 42931604041868613102995)
                      ·
                        rfl

theorem cell23_83609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_83609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83609 prefixEnd_83609 := by exact prefixLift 83609
  have htrace : WordTrace (prefixWord ++ tailWord_83609) baseStart_83609 baseEnd_83609 := by
    simpa [prefixWord, tailWord_83609, baseEnd_83609] using wordTrace_append hprefix tailTrace_83609
  have hstable : (prefixWord ++ tailWord_83609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83609).length < 2 ^ (prefixWord ++ tailWord_83609).sum := by decide
  have hdescent : baseEnd_83609 < baseStart_83609 := by decide
  rcases family_descends (prefixWord ++ tailWord_83609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83650 : List Nat := [3, 5, 1, 2, 1, 1, 1, 9]
def baseStart_83650 : Nat := 118140960795 + 83650 * 2 ^ 59
def prefixEnd_83650 : Nat := 4983230072969 + 3 ^ 40 * 83650 * 2
def baseEnd_83650 : Nat := 1590839138840850099641

theorem tailTrace_83650 : CollatzResearch.WordTrace tailWord_83650 prefixEnd_83650 1590839138840850099641 := by
  unfold tailWord_83650
  simp only [CollatzResearch.WordTrace]
  refine ⟨762741536739452781930101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2033977431305207418480269 762741536739452781930101)
  ·
    refine ⟨71507019069323698305947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 762741536739452781930101 71507019069323698305947)
    ·
      refine ⟨107260528603985547458921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71507019069323698305947 107260528603985547458921)
      ·
        refine ⟨80445396452989160594191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107260528603985547458921 80445396452989160594191)
        ·
          refine ⟨120668094679483740891287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80445396452989160594191 120668094679483740891287)
          ·
            refine ⟨181002142019225611336931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120668094679483740891287 181002142019225611336931)
            ·
              refine ⟨271503213028838417005397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181002142019225611336931 271503213028838417005397)
              ·
                refine ⟨1590839138840850099641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 271503213028838417005397 1590839138840850099641)
                ·
                  rfl

theorem cell23_83650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 9].length) (baseStart_83650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83650 prefixEnd_83650 := by exact prefixLift 83650
  have htrace : WordTrace (prefixWord ++ tailWord_83650) baseStart_83650 baseEnd_83650 := by
    simpa [prefixWord, tailWord_83650, baseEnd_83650] using wordTrace_append hprefix tailTrace_83650
  have hstable : (prefixWord ++ tailWord_83650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83650).length < 2 ^ (prefixWord ++ tailWord_83650).sum := by decide
  have hdescent : baseEnd_83650 < baseStart_83650 := by decide
  rcases family_descends (prefixWord ++ tailWord_83650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83661 : List Nat := [1, 6, 2, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_83661 : Nat := 118140960795 + 83661 * 2 ^ 59
def prefixEnd_83661 : Nat := 4983230072969 + 3 ^ 40 * 83661 * 2
def baseEnd_83661 : Nat := 42958305035902409652757

theorem tailTrace_83661 : CollatzResearch.WordTrace tailWord_83661 prefixEnd_83661 42958305035902409652757 := by
  unfold tailWord_83661
  simp only [CollatzResearch.WordTrace]
  refine ⟨3051367349917960006370837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2034244899945306670913891 3051367349917960006370837)
  ·
    refine ⟨143032844527404375298633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3051367349917960006370837 143032844527404375298633)
    ·
      refine ⟨107274633395553281473975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143032844527404375298633 107274633395553281473975)
      ·
        refine ⟨160911950093329922210963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107274633395553281473975 160911950093329922210963)
        ·
          refine ⟨241367925139994883316445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160911950093329922210963 241367925139994883316445)
          ·
            refine ⟨90512971927498081243667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 241367925139994883316445 90512971927498081243667)
            ·
              refine ⟨135769457891247121865501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90512971927498081243667 135769457891247121865501)
              ·
                refine ⟨50913546709217670699563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135769457891247121865501 50913546709217670699563)
                ·
                  refine ⟨76370320063826506049345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50913546709217670699563 76370320063826506049345)
                  ·
                    refine ⟨57277740047869879537009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76370320063826506049345 57277740047869879537009)
                    ·
                      refine ⟨42958305035902409652757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57277740047869879537009 42958305035902409652757)
                      ·
                        rfl

theorem cell23_83661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_83661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83661 prefixEnd_83661 := by exact prefixLift 83661
  have htrace : WordTrace (prefixWord ++ tailWord_83661) baseStart_83661 baseEnd_83661 := by
    simpa [prefixWord, tailWord_83661, baseEnd_83661] using wordTrace_append hprefix tailTrace_83661
  have hstable : (prefixWord ++ tailWord_83661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83661).length < 2 ^ (prefixWord ++ tailWord_83661).sum := by decide
  have hdescent : baseEnd_83661 < baseStart_83661 := by decide
  rcases family_descends (prefixWord ++ tailWord_83661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83736 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 2, 5]
def baseStart_83736 : Nat := 118140960795 + 83736 * 2 ^ 59
def prefixEnd_83736 : Nat := 4983230072969 + 3 ^ 40 * 83736 * 2
def baseEnd_83736 : Nat := 14332272028329872071637

theorem tailTrace_83736 : CollatzResearch.WordTrace tailWord_83736 prefixEnd_83736 14332272028329872071637 := by
  unfold tailWord_83736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1527051412323123907675531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2036068549764165210234041 1527051412323123907675531)
  ·
    refine ⟨2290577118484685861513297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1527051412323123907675531 2290577118484685861513297)
    ·
      refine ⟨1717932838863514396134973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2290577118484685861513297 1717932838863514396134973)
      ·
        refine ⟨644224814573817898550615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1717932838863514396134973 644224814573817898550615)
        ·
          refine ⟨966337221860726847825923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644224814573817898550615 966337221860726847825923)
          ·
            refine ⟨1449505832791090271738885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966337221860726847825923 1449505832791090271738885)
            ·
              refine ⟨271782343648329425951041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1449505832791090271738885 271782343648329425951041)
              ·
                refine ⟨203836757736247069463281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271782343648329425951041 203836757736247069463281)
                ·
                  refine ⟨152877568302185302097461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 203836757736247069463281 152877568302185302097461)
                  ·
                    refine ⟨14332272028329872071637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 152877568302185302097461 14332272028329872071637)
                    ·
                      rfl

theorem cell23_83736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_83736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83736 prefixEnd_83736 := by exact prefixLift 83736
  have htrace : WordTrace (prefixWord ++ tailWord_83736) baseStart_83736 baseEnd_83736 := by
    simpa [prefixWord, tailWord_83736, baseEnd_83736] using wordTrace_append hprefix tailTrace_83736
  have hstable : (prefixWord ++ tailWord_83736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83736).length < 2 ^ (prefixWord ++ tailWord_83736).sum := by decide
  have hdescent : baseEnd_83736 < baseStart_83736 := by decide
  rcases family_descends (prefixWord ++ tailWord_83736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83746 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_83746 : Nat := 118140960795 + 83746 * 2 ^ 59
def prefixEnd_83746 : Nat := 4983230072969 + 3 ^ 40 * 83746 * 2
def baseEnd_83746 : Nat := 43001950891534577089865

theorem tailTrace_83746 : CollatzResearch.WordTrace tailWord_83746 prefixEnd_83746 43001950891534577089865 := by
  unfold tailWord_83746
  simp only [CollatzResearch.WordTrace]
  refine ⟨763616888652504880803773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2036311703073346348810061 763616888652504880803773)
  ·
    refine ⟨286356333244689330301415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 763616888652504880803773 286356333244689330301415)
    ·
      refine ⟨429534499867033995452123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286356333244689330301415 429534499867033995452123)
      ·
        refine ⟨644301749800550993178185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429534499867033995452123 644301749800550993178185)
        ·
          refine ⟨483226312350413244883639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644301749800550993178185 483226312350413244883639)
          ·
            refine ⟨724839468525619867325459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483226312350413244883639 724839468525619867325459)
            ·
              refine ⟨1087259202788429800988189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724839468525619867325459 1087259202788429800988189)
              ·
                refine ⟨407722201045661175370571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1087259202788429800988189 407722201045661175370571)
                ·
                  refine ⟨611583301568491763055857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407722201045661175370571 611583301568491763055857)
                  ·
                    refine ⟨458687476176368822291893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 611583301568491763055857 458687476176368822291893)
                    ·
                      refine ⟨43001950891534577089865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 458687476176368822291893 43001950891534577089865)
                      ·
                        rfl

theorem cell23_83746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_83746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83746 prefixEnd_83746 := by exact prefixLift 83746
  have htrace : WordTrace (prefixWord ++ tailWord_83746) baseStart_83746 baseEnd_83746 := by
    simpa [prefixWord, tailWord_83746, baseEnd_83746] using wordTrace_append hprefix tailTrace_83746
  have hstable : (prefixWord ++ tailWord_83746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83746).length < 2 ^ (prefixWord ++ tailWord_83746).sum := by decide
  have hdescent : baseEnd_83746 < baseStart_83746 := by decide
  rcases family_descends (prefixWord ++ tailWord_83746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83759 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_83759 : Nat := 118140960795 + 83759 * 2 ^ 59
def prefixEnd_83759 : Nat := 4983230072969 + 3 ^ 40 * 83759 * 2
def baseEnd_83759 : Nat := 43008626140043026227305

theorem tailTrace_83759 : CollatzResearch.WordTrace tailWord_83759 prefixEnd_83759 43008626140043026227305 := by
  unfold tailWord_83759
  simp only [CollatzResearch.WordTrace]
  refine ⟨3054941703562922743438331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2036627802375281828958887 3054941703562922743438331)
  ·
    refine ⟨4582412555344384115157497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3054941703562922743438331 4582412555344384115157497)
    ·
      refine ⟨3436809416508288086368123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4582412555344384115157497 3436809416508288086368123)
      ·
        refine ⟨5155214124762432129552185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3436809416508288086368123 5155214124762432129552185)
        ·
          refine ⟨3866410593571824097164139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5155214124762432129552185 3866410593571824097164139)
          ·
            refine ⟨5799615890357736145746209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3866410593571824097164139 5799615890357736145746209)
            ·
              refine ⟨4349711917768302109309657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5799615890357736145746209 4349711917768302109309657)
              ·
                refine ⟨3262283938326226581982243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4349711917768302109309657 3262283938326226581982243)
                ·
                  refine ⟨4893425907489339872973365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3262283938326226581982243 4893425907489339872973365)
                  ·
                    refine ⟨458758678827125613091253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4893425907489339872973365 458758678827125613091253)
                    ·
                      refine ⟨43008626140043026227305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 458758678827125613091253 43008626140043026227305)
                      ·
                        rfl

theorem cell23_83759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_83759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83759 prefixEnd_83759 := by exact prefixLift 83759
  have htrace : WordTrace (prefixWord ++ tailWord_83759) baseStart_83759 baseEnd_83759 := by
    simpa [prefixWord, tailWord_83759, baseEnd_83759] using wordTrace_append hprefix tailTrace_83759
  have hstable : (prefixWord ++ tailWord_83759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83759).length < 2 ^ (prefixWord ++ tailWord_83759).sum := by decide
  have hdescent : baseEnd_83759 < baseStart_83759 := by decide
  rcases family_descends (prefixWord ++ tailWord_83759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83773 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_83773 : Nat := 118140960795 + 83773 * 2 ^ 59
def prefixEnd_83773 : Nat := 4983230072969 + 3 ^ 40 * 83773 * 2
def baseEnd_83773 : Nat := 43015814869205971452241

theorem tailTrace_83773 : CollatzResearch.WordTrace tailWord_83773 prefixEnd_83773 43015814869205971452241 := by
  unfold tailWord_83773
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055452325512203134447973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2036968217008135422965315 3055452325512203134447973)
  ·
    refine ⟨572897311033538087708995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3055452325512203134447973 572897311033538087708995)
    ·
      refine ⟨859345966550307131563493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 572897311033538087708995 859345966550307131563493)
      ·
        refine ⟨161127368728182587168155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 859345966550307131563493 161127368728182587168155)
        ·
          refine ⟨241691053092273880752233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161127368728182587168155 241691053092273880752233)
          ·
            refine ⟨181268289819205410564175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241691053092273880752233 181268289819205410564175)
            ·
              refine ⟨271902434728808115846263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181268289819205410564175 271902434728808115846263)
              ·
                refine ⟨407853652093212173769395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271902434728808115846263 407853652093212173769395)
                ·
                  refine ⟨611780478139818260654093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 407853652093212173769395 611780478139818260654093)
                  ·
                    refine ⟨229417679302431847745285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 611780478139818260654093 229417679302431847745285)
                    ·
                      refine ⟨43015814869205971452241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 229417679302431847745285 43015814869205971452241)
                      ·
                        rfl

theorem cell23_83773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_83773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83773 prefixEnd_83773 := by exact prefixLift 83773
  have htrace : WordTrace (prefixWord ++ tailWord_83773) baseStart_83773 baseEnd_83773 := by
    simpa [prefixWord, tailWord_83773, baseEnd_83773] using wordTrace_append hprefix tailTrace_83773
  have hstable : (prefixWord ++ tailWord_83773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83773).length < 2 ^ (prefixWord ++ tailWord_83773).sum := by decide
  have hdescent : baseEnd_83773 < baseStart_83773 := by decide
  rcases family_descends (prefixWord ++ tailWord_83773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83816 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_83816 : Nat := 118140960795 + 83816 * 2 ^ 59
def prefixEnd_83816 : Nat := 4983230072969 + 3 ^ 40 * 83816 * 2
def baseEnd_83816 : Nat := 43037894537349303214543

theorem tailTrace_83816 : CollatzResearch.WordTrace tailWord_83816 prefixEnd_83816 43037894537349303214543 := by
  unfold tailWord_83816
  simp only [CollatzResearch.WordTrace]
  refine ⟨1528510332178210739131651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2038013776237614318842201 1528510332178210739131651)
  ·
    refine ⟨2292765498267316108697477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1528510332178210739131651 2292765498267316108697477)
    ·
      refine ⟨429893530925121770380777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2292765498267316108697477 429893530925121770380777)
      ·
        refine ⟨322420148193841327785583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429893530925121770380777 322420148193841327785583)
        ·
          refine ⟨483630222290761991678375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322420148193841327785583 483630222290761991678375)
          ·
            refine ⟨725445333436142987517563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483630222290761991678375 725445333436142987517563)
            ·
              refine ⟨1088168000154214481276345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725445333436142987517563 1088168000154214481276345)
              ·
                refine ⟨816126000115660860957259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1088168000154214481276345 816126000115660860957259)
                ·
                  refine ⟨1224189000173491291435889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 816126000115660860957259 1224189000173491291435889)
                  ·
                    refine ⟨918141750130118468576917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1224189000173491291435889 918141750130118468576917)
                    ·
                      refine ⟨43037894537349303214543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 918141750130118468576917 43037894537349303214543)
                      ·
                        rfl

theorem cell23_83816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_83816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83816 prefixEnd_83816 := by exact prefixLift 83816
  have htrace : WordTrace (prefixWord ++ tailWord_83816) baseStart_83816 baseEnd_83816 := by
    simpa [prefixWord, tailWord_83816, baseEnd_83816] using wordTrace_append hprefix tailTrace_83816
  have hstable : (prefixWord ++ tailWord_83816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83816).length < 2 ^ (prefixWord ++ tailWord_83816).sum := by decide
  have hdescent : baseEnd_83816 < baseStart_83816 := by decide
  rcases family_descends (prefixWord ++ tailWord_83816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83833 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 1, 5, 2]
def baseStart_83833 : Nat := 118140960795 + 83833 * 2 ^ 59
def prefixEnd_83833 : Nat := 4983230072969 + 3 ^ 40 * 83833 * 2
def baseEnd_83833 : Nat := 43046623708475736701965

theorem tailTrace_83833 : CollatzResearch.WordTrace tailWord_83833 prefixEnd_83833 43046623708475736701965 := by
  unfold tailWord_83833
  simp only [CollatzResearch.WordTrace]
  refine ⟨3057640705294833381632153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2038427136863222254421435 3057640705294833381632153)
  ·
    refine ⟨2293230528971125036224115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3057640705294833381632153 2293230528971125036224115)
    ·
      refine ⟨3439845793456687554336173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2293230528971125036224115 3439845793456687554336173)
      ·
        refine ⟨1289942172546257832876065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3439845793456687554336173 1289942172546257832876065)
        ·
          refine ⟨967456629409693374657049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1289942172546257832876065 967456629409693374657049)
          ·
            refine ⟨725592472057270030992787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 967456629409693374657049 725592472057270030992787)
            ·
              refine ⟨1088388708085905046489181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725592472057270030992787 1088388708085905046489181)
              ·
                refine ⟨408145765532214392433443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1088388708085905046489181 408145765532214392433443)
                ·
                  refine ⟨612218648298321588650165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 408145765532214392433443 612218648298321588650165)
                  ·
                    refine ⟨57395498277967648935953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 612218648298321588650165 57395498277967648935953)
                    ·
                      refine ⟨43046623708475736701965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57395498277967648935953 43046623708475736701965)
                      ·
                        rfl

theorem cell23_83833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_83833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83833 prefixEnd_83833 := by exact prefixLift 83833
  have htrace : WordTrace (prefixWord ++ tailWord_83833) baseStart_83833 baseEnd_83833 := by
    simpa [prefixWord, tailWord_83833, baseEnd_83833] using wordTrace_append hprefix tailTrace_83833
  have hstable : (prefixWord ++ tailWord_83833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83833).length < 2 ^ (prefixWord ++ tailWord_83833).sum := by decide
  have hdescent : baseEnd_83833 < baseStart_83833 := by decide
  rcases family_descends (prefixWord ++ tailWord_83833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83843 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 1, 5]
def baseStart_83843 : Nat := 118140960795 + 83843 * 2 ^ 59
def prefixEnd_83843 : Nat := 4983230072969 + 3 ^ 40 * 83843 * 2
def baseEnd_83843 : Nat := 14350586171673565858973

theorem tailTrace_83843 : CollatzResearch.WordTrace tailWord_83843 prefixEnd_83843 14350586171673565858973 := by
  unfold tailWord_83843
  simp only [CollatzResearch.WordTrace]
  refine ⟨3058005435258605089496183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2038670290172403392997455 3058005435258605089496183)
  ·
    refine ⟨4587008152887907634244275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3058005435258605089496183 4587008152887907634244275)
    ·
      refine ⟨6880512229331861451366413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4587008152887907634244275 6880512229331861451366413)
      ·
        refine ⟨2580192085999448044262405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6880512229331861451366413 2580192085999448044262405)
        ·
          refine ⟨483786016124896508299201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2580192085999448044262405 483786016124896508299201)
          ·
            refine ⟨362839512093672381224401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483786016124896508299201 362839512093672381224401)
            ·
              refine ⟨272129634070254285918301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362839512093672381224401 272129634070254285918301)
              ·
                refine ⟨102048612776345357219363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272129634070254285918301 102048612776345357219363)
                ·
                  refine ⟨153072919164518035829045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102048612776345357219363 153072919164518035829045)
                  ·
                    refine ⟨14350586171673565858973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 153072919164518035829045 14350586171673565858973)
                    ·
                      rfl

theorem cell23_83843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 1, 5].length) (baseStart_83843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83843 prefixEnd_83843 := by exact prefixLift 83843
  have htrace : WordTrace (prefixWord ++ tailWord_83843) baseStart_83843 baseEnd_83843 := by
    simpa [prefixWord, tailWord_83843, baseEnd_83843] using wordTrace_append hprefix tailTrace_83843
  have hstable : (prefixWord ++ tailWord_83843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83843).length < 2 ^ (prefixWord ++ tailWord_83843).sum := by decide
  have hdescent : baseEnd_83843 < baseStart_83843 := by decide
  rcases family_descends (prefixWord ++ tailWord_83843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83864 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 6]
def baseStart_83864 : Nat := 118140960795 + 83864 * 2 ^ 59
def prefixEnd_83864 : Nat := 4983230072969 + 3 ^ 40 * 83864 * 2
def baseEnd_83864 : Nat := 4784726845418346157147

theorem tailTrace_83864 : CollatzResearch.WordTrace tailWord_83864 prefixEnd_83864 4784726845418346157147 := by
  unfold tailWord_83864
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529385684091262838005323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2039180912121683784007097 1529385684091262838005323)
  ·
    refine ⟨2294078526136894257007985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1529385684091262838005323 2294078526136894257007985)
    ·
      refine ⟨1720558894602670692755989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2294078526136894257007985 1720558894602670692755989)
      ·
        refine ⟨80651198184500188722937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1720558894602670692755989 80651198184500188722937)
        ·
          refine ⟨60488398638375141542203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80651198184500188722937 60488398638375141542203)
          ·
            refine ⟨90732597957562712313305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60488398638375141542203 90732597957562712313305)
            ·
              refine ⟨68049448468172034234979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90732597957562712313305 68049448468172034234979)
              ·
                refine ⟨102074172702258051352469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68049448468172034234979 102074172702258051352469)
                ·
                  refine ⟨4784726845418346157147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102074172702258051352469 4784726845418346157147)
                  ·
                    rfl

theorem cell23_83864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 6].length) (baseStart_83864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83864 prefixEnd_83864 := by exact prefixLift 83864
  have htrace : WordTrace (prefixWord ++ tailWord_83864) baseStart_83864 baseEnd_83864 := by
    simpa [prefixWord, tailWord_83864, baseEnd_83864] using wordTrace_append hprefix tailTrace_83864
  have hstable : (prefixWord ++ tailWord_83864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83864).length < 2 ^ (prefixWord ++ tailWord_83864).sum := by decide
  have hdescent : baseEnd_83864 < baseStart_83864 := by decide
  rcases family_descends (prefixWord ++ tailWord_83864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83893 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_83893 : Nat := 118140960795 + 83893 * 2 ^ 59
def prefixEnd_83893 : Nat := 4983230072969 + 3 ^ 40 * 83893 * 2
def baseEnd_83893 : Nat := 43077432547745501951689

theorem tailTrace_83893 : CollatzResearch.WordTrace tailWord_83893 prefixEnd_83893 43077432547745501951689 := by
  unfold tailWord_83893
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059829085077463628816333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2039886056718309085877555 3059829085077463628816333)
  ·
    refine ⟨1147435906904048860806125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3059829085077463628816333 1147435906904048860806125)
    ·
      refine ⟨430288465089018322802297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1147435906904048860806125 430288465089018322802297)
      ·
        refine ⟨322716348816763742101723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 430288465089018322802297 322716348816763742101723)
        ·
          refine ⟨484074523225145613152585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322716348816763742101723 484074523225145613152585)
          ·
            refine ⟨363055892418859209864439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484074523225145613152585 363055892418859209864439)
            ·
              refine ⟨544583838628288814796659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363055892418859209864439 544583838628288814796659)
              ·
                refine ⟨816875757942433222194989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 544583838628288814796659 816875757942433222194989)
                ·
                  refine ⟨306328409228412458323121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 816875757942433222194989 306328409228412458323121)
                  ·
                    refine ⟨229746306921309343742341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 306328409228412458323121 229746306921309343742341)
                    ·
                      refine ⟨43077432547745501951689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 229746306921309343742341 43077432547745501951689)
                      ·
                        rfl

theorem cell23_83893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_83893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83893 prefixEnd_83893 := by exact prefixLift 83893
  have htrace : WordTrace (prefixWord ++ tailWord_83893) baseStart_83893 baseEnd_83893 := by
    simpa [prefixWord, tailWord_83893, baseEnd_83893] using wordTrace_append hprefix tailTrace_83893
  have hstable : (prefixWord ++ tailWord_83893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83893).length < 2 ^ (prefixWord ++ tailWord_83893).sum := by decide
  have hdescent : baseEnd_83893 < baseStart_83893 := by decide
  rcases family_descends (prefixWord ++ tailWord_83893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83940 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 3, 3, 2]
def baseStart_83940 : Nat := 118140960795 + 83940 * 2 ^ 59
def prefixEnd_83940 : Nat := 4983230072969 + 3 ^ 40 * 83940 * 2
def baseEnd_83940 : Nat := 43101566138506818063973

theorem tailTrace_83940 : CollatzResearch.WordTrace tailWord_83940 prefixEnd_83940 43101566138506818063973 := by
  unfold tailWord_83940
  simp only [CollatzResearch.WordTrace]
  refine ⟨1530771657953595327888637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2041028877271460437184849 1530771657953595327888637)
  ·
    refine ⟨574039371732598247958239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1530771657953595327888637 574039371732598247958239)
    ·
      refine ⟨861059057598897371937359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574039371732598247958239 861059057598897371937359)
      ·
        refine ⟨1291588586398346057906039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 861059057598897371937359 1291588586398346057906039)
        ·
          refine ⟨1937382879597519086859059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1291588586398346057906039 1937382879597519086859059)
          ·
            refine ⟨2906074319396278630288589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937382879597519086859059 2906074319396278630288589)
            ·
              refine ⟨1089777869773604486358221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2906074319396278630288589 1089777869773604486358221)
              ·
                refine ⟨408666701165101682384333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1089777869773604486358221 408666701165101682384333)
                ·
                  refine ⟨153250012936913130894125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 408666701165101682384333 153250012936913130894125)
                  ·
                    refine ⟨57468754851342424085297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153250012936913130894125 57468754851342424085297)
                    ·
                      refine ⟨43101566138506818063973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57468754851342424085297 43101566138506818063973)
                      ·
                        rfl

theorem cell23_83940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_83940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83940 prefixEnd_83940 := by exact prefixLift 83940
  have htrace : WordTrace (prefixWord ++ tailWord_83940) baseStart_83940 baseEnd_83940 := by
    simpa [prefixWord, tailWord_83940, baseEnd_83940] using wordTrace_append hprefix tailTrace_83940
  have hstable : (prefixWord ++ tailWord_83940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83940).length < 2 ^ (prefixWord ++ tailWord_83940).sum := by decide
  have hdescent : baseEnd_83940 < baseStart_83940 := by decide
  rcases family_descends (prefixWord ++ tailWord_83940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83987 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 2, 2, 2]
def baseStart_83987 : Nat := 118140960795 + 83987 * 2 ^ 59
def prefixEnd_83987 : Nat := 4983230072969 + 3 ^ 40 * 83987 * 2
def baseEnd_83987 : Nat := 43125699729268134176257

theorem tailTrace_83987 : CollatzResearch.WordTrace tailWord_83987 prefixEnd_83987 43125699729268134176257 := by
  unfold tailWord_83987
  simp only [CollatzResearch.WordTrace]
  refine ⟨3063257546736917682738215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2042171697824611788492143 3063257546736917682738215)
  ·
    refine ⟨4594886320105376524107323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3063257546736917682738215 4594886320105376524107323)
    ·
      refine ⟨6892329480158064786160985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4594886320105376524107323 6892329480158064786160985)
      ·
        refine ⟨5169247110118548589620739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6892329480158064786160985 5169247110118548589620739)
        ·
          refine ⟨7753870665177822884431109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5169247110118548589620739 7753870665177822884431109)
          ·
            refine ⟨1453850749720841790830833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7753870665177822884431109 1453850749720841790830833)
            ·
              refine ⟨1090388062290631343123125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1453850749720841790830833 1090388062290631343123125)
              ·
                refine ⟨102223880839746688417793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1090388062290631343123125 102223880839746688417793)
                ·
                  refine ⟨76667910629810016313345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102223880839746688417793 76667910629810016313345)
                  ·
                    refine ⟨57500932972357512235009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76667910629810016313345 57500932972357512235009)
                    ·
                      refine ⟨43125699729268134176257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57500932972357512235009 43125699729268134176257)
                      ·
                        rfl

theorem cell23_83987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 2, 2].length) (baseStart_83987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_83987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_83987 prefixEnd_83987 := by exact prefixLift 83987
  have htrace : WordTrace (prefixWord ++ tailWord_83987) baseStart_83987 baseEnd_83987 := by
    simpa [prefixWord, tailWord_83987, baseEnd_83987] using wordTrace_append hprefix tailTrace_83987
  have hstable : (prefixWord ++ tailWord_83987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83987).length < 2 ^ (prefixWord ++ tailWord_83987).sum := by decide
  have hdescent : baseEnd_83987 < baseStart_83987 := by decide
  rcases family_descends (prefixWord ++ tailWord_83987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84007 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_84007 : Nat := 118140960795 + 84007 * 2 ^ 59
def prefixEnd_84007 : Nat := 4983230072969 + 3 ^ 40 * 84007 * 2
def baseEnd_84007 : Nat := 43135969342358055926165

theorem tailTrace_84007 : CollatzResearch.WordTrace tailWord_84007 prefixEnd_84007 43135969342358055926165 := by
  unfold tailWord_84007
  simp only [CollatzResearch.WordTrace]
  refine ⟨3063987006664461098466275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2042658004442974065644183 3063987006664461098466275)
  ·
    refine ⟨4595980509996691647699413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3063987006664461098466275 4595980509996691647699413)
    ·
      refine ⟨107718293203047460492955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4595980509996691647699413 107718293203047460492955)
      ·
        refine ⟨161577439804571190739433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107718293203047460492955 161577439804571190739433)
        ·
          refine ⟨121183079853428393054575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161577439804571190739433 121183079853428393054575)
          ·
            refine ⟨181774619780142589581863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121183079853428393054575 181774619780142589581863)
            ·
              refine ⟨272661929670213884372795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181774619780142589581863 272661929670213884372795)
              ·
                refine ⟨408992894505320826559193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272661929670213884372795 408992894505320826559193)
                ·
                  refine ⟨306744670878990619919395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 408992894505320826559193 306744670878990619919395)
                  ·
                    refine ⟨460117006318485929879093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 306744670878990619919395 460117006318485929879093)
                    ·
                      refine ⟨43135969342358055926165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 460117006318485929879093 43135969342358055926165)
                      ·
                        rfl

theorem cell23_84007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_84007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84007 prefixEnd_84007 := by exact prefixLift 84007
  have htrace : WordTrace (prefixWord ++ tailWord_84007) baseStart_84007 baseEnd_84007 := by
    simpa [prefixWord, tailWord_84007, baseEnd_84007] using wordTrace_append hprefix tailTrace_84007
  have hstable : (prefixWord ++ tailWord_84007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84007).length < 2 ^ (prefixWord ++ tailWord_84007).sum := by decide
  have hdescent : baseEnd_84007 < baseStart_84007 := by decide
  rcases family_descends (prefixWord ++ tailWord_84007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84023 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 4, 5]
def baseStart_84023 : Nat := 118140960795 + 84023 * 2 ^ 59
def prefixEnd_84023 : Nat := 4983230072969 + 3 ^ 40 * 84023 * 2
def baseEnd_84023 : Nat := 14381395010943331108697

theorem tailTrace_84023 : CollatzResearch.WordTrace tailWord_84023 prefixEnd_84023 14381395010943331108697 := by
  unfold tailWord_84023
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064570574606495831048723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2043047049737663887365815 3064570574606495831048723)
  ·
    refine ⟨4596855861909743746573085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3064570574606495831048723 4596855861909743746573085)
    ·
      refine ⟨1723820948216153904964907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4596855861909743746573085 1723820948216153904964907)
      ·
        refine ⟨2585731422324230857447361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1723820948216153904964907 2585731422324230857447361)
        ·
          refine ⟨1939298566743173143085521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2585731422324230857447361 1939298566743173143085521)
          ·
            refine ⟨1454473925057379857314141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1939298566743173143085521 1454473925057379857314141)
            ·
              refine ⟨545427721896517446492803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1454473925057379857314141 545427721896517446492803)
              ·
                refine ⟨818141582844776169739205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545427721896517446492803 818141582844776169739205)
                ·
                  refine ⟨153401546783395531826101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 818141582844776169739205 153401546783395531826101)
                  ·
                    refine ⟨14381395010943331108697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 153401546783395531826101 14381395010943331108697)
                    ·
                      rfl

theorem cell23_84023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_84023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84023 prefixEnd_84023 := by exact prefixLift 84023
  have htrace : WordTrace (prefixWord ++ tailWord_84023) baseStart_84023 baseEnd_84023 := by
    simpa [prefixWord, tailWord_84023, baseEnd_84023] using wordTrace_append hprefix tailTrace_84023
  have hstable : (prefixWord ++ tailWord_84023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84023).length < 2 ^ (prefixWord ++ tailWord_84023).sum := by decide
  have hdescent : baseEnd_84023 < baseStart_84023 := by decide
  rcases family_descends (prefixWord ++ tailWord_84023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84073 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_84073 : Nat := 118140960795 + 84073 * 2 ^ 59
def prefixEnd_84073 : Nat := 4983230072969 + 3 ^ 40 * 84073 * 2
def baseEnd_84073 : Nat := 43169859065554797700861

theorem tailTrace_84073 : CollatzResearch.WordTrace tailWord_84073 prefixEnd_84073 43169859065554797700861 := by
  unfold tailWord_84073
  simp only [CollatzResearch.WordTrace]
  refine ⟨3066394224425354370368873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2044262816283569580245915 3066394224425354370368873)
  ·
    refine ⟨2299795668319015777776655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3066394224425354370368873 2299795668319015777776655)
    ·
      refine ⟨3449693502478523666664983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299795668319015777776655 3449693502478523666664983)
      ·
        refine ⟨5174540253717785499997475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3449693502478523666664983 5174540253717785499997475)
        ·
          refine ⟨7761810380576678249996213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5174540253717785499997475 7761810380576678249996213)
          ·
            refine ⟨727669723179063585937145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7761810380576678249996213 727669723179063585937145)
            ·
              refine ⟨545752292384297689452859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727669723179063585937145 545752292384297689452859)
              ·
                refine ⟨818628438576446534179289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 545752292384297689452859 818628438576446534179289)
                ·
                  refine ⟨613971328932334900634467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 818628438576446534179289 613971328932334900634467)
                  ·
                    refine ⟨920956993398502350951701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 613971328932334900634467 920956993398502350951701)
                    ·
                      refine ⟨43169859065554797700861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 920956993398502350951701 43169859065554797700861)
                      ·
                        rfl

theorem cell23_84073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_84073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84073 prefixEnd_84073 := by exact prefixLift 84073
  have htrace : WordTrace (prefixWord ++ tailWord_84073) baseStart_84073 baseEnd_84073 := by
    simpa [prefixWord, tailWord_84073, baseEnd_84073] using wordTrace_append hprefix tailTrace_84073
  have hstable : (prefixWord ++ tailWord_84073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84073).length < 2 ^ (prefixWord ++ tailWord_84073).sum := by decide
  have hdescent : baseEnd_84073 < baseStart_84073 := by decide
  rcases family_descends (prefixWord ++ tailWord_84073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84077 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_84077 : Nat := 118140960795 + 84077 * 2 ^ 59
def prefixEnd_84077 : Nat := 4983230072969 + 3 ^ 40 * 84077 * 2
def baseEnd_84077 : Nat := 43171912988172782050843

theorem tailTrace_84077 : CollatzResearch.WordTrace tailWord_84077 prefixEnd_84077 43171912988172782050843 := by
  unfold tailWord_84077
  simp only [CollatzResearch.WordTrace]
  refine ⟨3066540116410863053514485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2044360077607242035676323 3066540116410863053514485)
  ·
    refine ⟨287488135913518411266983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3066540116410863053514485 287488135913518411266983)
    ·
      refine ⟨431232203870277616900475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 287488135913518411266983 431232203870277616900475)
      ·
        refine ⟨646848305805416425350713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431232203870277616900475 646848305805416425350713)
        ·
          refine ⟨485136229354062319013035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646848305805416425350713 485136229354062319013035)
          ·
            refine ⟨727704344031093478519553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485136229354062319013035 727704344031093478519553)
            ·
              refine ⟨545778258023320108889665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727704344031093478519553 545778258023320108889665)
              ·
                refine ⟨409333693517490081667249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545778258023320108889665 409333693517490081667249)
                ·
                  refine ⟨307000270138117561250437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 409333693517490081667249 307000270138117561250437)
                  ·
                    refine ⟨57562550650897042734457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 307000270138117561250437 57562550650897042734457)
                    ·
                      refine ⟨43171912988172782050843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57562550650897042734457 43171912988172782050843)
                      ·
                        rfl

theorem cell23_84077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_84077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84077 prefixEnd_84077 := by exact prefixLift 84077
  have htrace : WordTrace (prefixWord ++ tailWord_84077) baseStart_84077 baseEnd_84077 := by
    simpa [prefixWord, tailWord_84077, baseEnd_84077] using wordTrace_append hprefix tailTrace_84077
  have hstable : (prefixWord ++ tailWord_84077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84077).length < 2 ^ (prefixWord ++ tailWord_84077).sum := by decide
  have hdescent : baseEnd_84077 < baseStart_84077 := by decide
  rcases family_descends (prefixWord ++ tailWord_84077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84100 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 6]
def baseStart_84100 : Nat := 118140960795 + 84100 * 2 ^ 59
def prefixEnd_84100 : Nat := 4983230072969 + 3 ^ 40 * 84100 * 2
def baseEnd_84100 : Nat := 4798191449247354673693

theorem tailTrace_84100 : CollatzResearch.WordTrace tailWord_84100 prefixEnd_84100 4798191449247354673693 := by
  unfold tailWord_84100
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533689497663768990800877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2044919330218358654401169 1533689497663768990800877)
  ·
    refine ⟨575133561623913371550329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1533689497663768990800877 575133561623913371550329)
    ·
      refine ⟨431350171217935028662747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 575133561623913371550329 431350171217935028662747)
      ·
        refine ⟨647025256826902542994121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431350171217935028662747 647025256826902542994121)
        ·
          refine ⟨485268942620176907245591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 647025256826902542994121 485268942620176907245591)
          ·
            refine ⟨727903413930265360868387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485268942620176907245591 727903413930265360868387)
            ·
              refine ⟨1091855120895398041302581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727903413930265360868387 1091855120895398041302581)
              ·
                refine ⟨102361417583943566372117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1091855120895398041302581 102361417583943566372117)
                ·
                  refine ⟨4798191449247354673693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102361417583943566372117 4798191449247354673693)
                  ·
                    rfl

theorem cell23_84100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_84100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84100 prefixEnd_84100 := by exact prefixLift 84100
  have htrace : WordTrace (prefixWord ++ tailWord_84100) baseStart_84100 baseEnd_84100 := by
    simpa [prefixWord, tailWord_84100, baseEnd_84100] using wordTrace_append hprefix tailTrace_84100
  have hstable : (prefixWord ++ tailWord_84100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84100).length < 2 ^ (prefixWord ++ tailWord_84100).sum := by decide
  have hdescent : baseEnd_84100 < baseStart_84100 := by decide
  rcases family_descends (prefixWord ++ tailWord_84100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84164 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_84164 : Nat := 118140960795 + 84164 * 2 ^ 59
def prefixEnd_84164 : Nat := 4983230072969 + 3 ^ 40 * 84164 * 2
def baseEnd_84164 : Nat := 14405528601704647220981

theorem tailTrace_84164 : CollatzResearch.WordTrace tailWord_84164 prefixEnd_84164 14405528601704647220981 := by
  unfold tailWord_84164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1534856633547838455965773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2046475511397117941287697 1534856633547838455965773)
  ·
    refine ⟨575571237580439420987165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1534856633547838455965773 575571237580439420987165)
    ·
      refine ⟨215839214092664782870187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 575571237580439420987165 215839214092664782870187)
      ·
        refine ⟨323758821138997174305281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215839214092664782870187 323758821138997174305281)
        ·
          refine ⟨242819115854247880728961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323758821138997174305281 242819115854247880728961)
          ·
            refine ⟨182114336890685910546721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242819115854247880728961 182114336890685910546721)
            ·
              refine ⟨136585752668014432910041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182114336890685910546721 136585752668014432910041)
              ·
                refine ⟨102439314501010824682531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136585752668014432910041 102439314501010824682531)
                ·
                  refine ⟨153658971751516237023797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102439314501010824682531 153658971751516237023797)
                  ·
                    refine ⟨14405528601704647220981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 153658971751516237023797 14405528601704647220981)
                    ·
                      rfl

theorem cell23_84164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_84164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84164 prefixEnd_84164 := by exact prefixLift 84164
  have htrace : WordTrace (prefixWord ++ tailWord_84164) baseStart_84164 baseEnd_84164 := by
    simpa [prefixWord, tailWord_84164, baseEnd_84164] using wordTrace_append hprefix tailTrace_84164
  have hstable : (prefixWord ++ tailWord_84164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84164).length < 2 ^ (prefixWord ++ tailWord_84164).sum := by decide
  have hdescent : baseEnd_84164 < baseStart_84164 := by decide
  rcases family_descends (prefixWord ++ tailWord_84164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84170 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_84170 : Nat := 118140960795 + 84170 * 2 ^ 59
def prefixEnd_84170 : Nat := 4983230072969 + 3 ^ 40 * 84170 * 2
def baseEnd_84170 : Nat := 43219666689040918187915

theorem tailTrace_84170 : CollatzResearch.WordTrace tailWord_84170 prefixEnd_84170 43219666689040918187915 := by
  unfold tailWord_84170
  simp only [CollatzResearch.WordTrace]
  refine ⟨767483026268484984162491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2046621403382626624433309 767483026268484984162491)
  ·
    refine ⟨1151224539402727476243737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767483026268484984162491 1151224539402727476243737)
    ·
      refine ⟨863418404552045607182803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1151224539402727476243737 863418404552045607182803)
      ·
        refine ⟨1295127606828068410774205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 863418404552045607182803 1295127606828068410774205)
        ·
          refine ⟨485672852560525654040327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1295127606828068410774205 485672852560525654040327)
          ·
            refine ⟨728509278840788481060491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485672852560525654040327 728509278840788481060491)
            ·
              refine ⟨1092763918261182721590737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 728509278840788481060491 1092763918261182721590737)
              ·
                refine ⟨819572938695887041193053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092763918261182721590737 819572938695887041193053)
                ·
                  refine ⟨307339852010957640447395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 819572938695887041193053 307339852010957640447395)
                  ·
                    refine ⟨461009778016436460671093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 307339852010957640447395 461009778016436460671093)
                    ·
                      refine ⟨43219666689040918187915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 461009778016436460671093 43219666689040918187915)
                      ·
                        rfl

theorem cell23_84170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_84170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84170 prefixEnd_84170 := by exact prefixLift 84170
  have htrace : WordTrace (prefixWord ++ tailWord_84170) baseStart_84170 baseEnd_84170 := by
    simpa [prefixWord, tailWord_84170, baseEnd_84170] using wordTrace_append hprefix tailTrace_84170
  have hstable : (prefixWord ++ tailWord_84170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84170).length < 2 ^ (prefixWord ++ tailWord_84170).sum := by decide
  have hdescent : baseEnd_84170 < baseStart_84170 := by decide
  rcases family_descends (prefixWord ++ tailWord_84170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84178 : List Nat := [3, 2, 2, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_84178 : Nat := 118140960795 + 84178 * 2 ^ 59
def prefixEnd_84178 : Nat := 4983230072969 + 3 ^ 40 * 84178 * 2
def baseEnd_84178 : Nat := 43223774534276886887879

theorem tailTrace_84178 : CollatzResearch.WordTrace tailWord_84178 prefixEnd_84178 43223774534276886887879 := by
  unfold tailWord_84178
  simp only [CollatzResearch.WordTrace]
  refine ⟨767555972261239325735297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2046815926029971535294125 767555972261239325735297)
  ·
    refine ⟨575666979195929494301473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 767555972261239325735297 575666979195929494301473)
    ·
      refine ⟨431750234396947120726105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 575666979195929494301473 431750234396947120726105)
      ·
        refine ⟨323812675797710340544579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431750234396947120726105 323812675797710340544579)
        ·
          refine ⟨485719013696565510816869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323812675797710340544579 485719013696565510816869)
          ·
            refine ⟨91072315068106033278163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 485719013696565510816869 91072315068106033278163)
            ·
              refine ⟨136608472602159049917245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91072315068106033278163 136608472602159049917245)
              ·
                refine ⟨51228177225809643718967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136608472602159049917245 51228177225809643718967)
                ·
                  refine ⟨76842265838714465578451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51228177225809643718967 76842265838714465578451)
                  ·
                    refine ⟨115263398758071698367677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76842265838714465578451 115263398758071698367677)
                    ·
                      refine ⟨43223774534276886887879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 115263398758071698367677 43223774534276886887879)
                      ·
                        rfl

theorem cell23_84178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_84178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84178 prefixEnd_84178 := by exact prefixLift 84178
  have htrace : WordTrace (prefixWord ++ tailWord_84178) baseStart_84178 baseEnd_84178 := by
    simpa [prefixWord, tailWord_84178, baseEnd_84178] using wordTrace_append hprefix tailTrace_84178
  have hstable : (prefixWord ++ tailWord_84178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84178).length < 2 ^ (prefixWord ++ tailWord_84178).sum := by decide
  have hdescent : baseEnd_84178 < baseStart_84178 := by decide
  rcases family_descends (prefixWord ++ tailWord_84178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84188 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_84188 : Nat := 118140960795 + 84188 * 2 ^ 59
def prefixEnd_84188 : Nat := 4983230072969 + 3 ^ 40 * 84188 * 2
def baseEnd_84188 : Nat := 43228909340821847762833

theorem tailTrace_84188 : CollatzResearch.WordTrace tailWord_84188 prefixEnd_84188 43228909340821847762833 := by
  unfold tailWord_84188
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535294309504364505402609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2047059079339152673870145 1535294309504364505402609)
  ·
    refine ⟨1151470732128273379051957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1535294309504364505402609 1151470732128273379051957)
    ·
      refine ⟨107950381137025629286121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1151470732128273379051957 107950381137025629286121)
      ·
        refine ⟨80962785852769221964591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107950381137025629286121 80962785852769221964591)
        ·
          refine ⟨121444178779153832946887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80962785852769221964591 121444178779153832946887)
          ·
            refine ⟨182166268168730749420331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121444178779153832946887 182166268168730749420331)
            ·
              refine ⟨273249402253096124130497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182166268168730749420331 273249402253096124130497)
              ·
                refine ⟨204937051689822093097873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273249402253096124130497 204937051689822093097873)
                ·
                  refine ⟨153702788767366569823405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 204937051689822093097873 153702788767366569823405)
                  ·
                    refine ⟨57638545787762463683777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 153702788767366569823405 57638545787762463683777)
                    ·
                      refine ⟨43228909340821847762833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57638545787762463683777 43228909340821847762833)
                      ·
                        rfl

theorem cell23_84188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_84188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84188 prefixEnd_84188 := by exact prefixLift 84188
  have htrace : WordTrace (prefixWord ++ tailWord_84188) baseStart_84188 baseEnd_84188 := by
    simpa [prefixWord, tailWord_84188, baseEnd_84188] using wordTrace_append hprefix tailTrace_84188
  have hstable : (prefixWord ++ tailWord_84188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84188).length < 2 ^ (prefixWord ++ tailWord_84188).sum := by decide
  have hdescent : baseEnd_84188 < baseStart_84188 := by decide
  rcases family_descends (prefixWord ++ tailWord_84188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84195 : List Nat := [1, 1, 1, 8, 1, 1, 3, 2, 1, 1, 3]
def baseStart_84195 : Nat := 118140960795 + 84195 * 2 ^ 59
def prefixEnd_84195 : Nat := 4983230072969 + 3 ^ 40 * 84195 * 2
def baseEnd_84195 : Nat := 43232503705403320375301

theorem tailTrace_84195 : CollatzResearch.WordTrace tailWord_84195 prefixEnd_84195 43232503705403320375301 := by
  unfold tailWord_84195
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070843929983369206310039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2047229286655579470873359 3070843929983369206310039)
  ·
    refine ⟨4606265894975053809465059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3070843929983369206310039 4606265894975053809465059)
    ·
      refine ⟨6909398842462580714197589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4606265894975053809465059 6909398842462580714197589)
      ·
        refine ⟨80969517685108367744503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 6909398842462580714197589 80969517685108367744503)
        ·
          refine ⟨121454276527662551616755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80969517685108367744503 121454276527662551616755)
          ·
            refine ⟨182181414791493827425133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121454276527662551616755 182181414791493827425133)
            ·
              refine ⟨68318030546810185284425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182181414791493827425133 68318030546810185284425)
              ·
                refine ⟨51238522910107638963319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68318030546810185284425 51238522910107638963319)
                ·
                  refine ⟨76857784365161458444979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51238522910107638963319 76857784365161458444979)
                  ·
                    refine ⟨115286676547742187667469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76857784365161458444979 115286676547742187667469)
                    ·
                      refine ⟨43232503705403320375301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 115286676547742187667469 43232503705403320375301)
                      ·
                        rfl

theorem cell23_84195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_84195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84195 prefixEnd_84195 := by exact prefixLift 84195
  have htrace : WordTrace (prefixWord ++ tailWord_84195) baseStart_84195 baseEnd_84195 := by
    simpa [prefixWord, tailWord_84195, baseEnd_84195] using wordTrace_append hprefix tailTrace_84195
  have hstable : (prefixWord ++ tailWord_84195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84195).length < 2 ^ (prefixWord ++ tailWord_84195).sum := by decide
  have hdescent : baseEnd_84195 < baseStart_84195 := by decide
  rcases family_descends (prefixWord ++ tailWord_84195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84217 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 6, 1, 3]
def baseStart_84217 : Nat := 118140960795 + 84217 * 2 ^ 59
def prefixEnd_84217 : Nat := 4983230072969 + 3 ^ 40 * 84217 * 2
def baseEnd_84217 : Nat := 43243800279802234300199

theorem tailTrace_84217 : CollatzResearch.WordTrace tailWord_84217 prefixEnd_84217 43243800279802234300199 := by
  unfold tailWord_84217
  simp only [CollatzResearch.WordTrace]
  refine ⟨3071646335903666963610905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2047764223935777975740603 3071646335903666963610905)
  ·
    refine ⟨2303734751927750222708179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3071646335903666963610905 2303734751927750222708179)
    ·
      refine ⟨3455602127891625334062269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2303734751927750222708179 3455602127891625334062269)
      ·
        refine ⟨1295850797959359500273351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3455602127891625334062269 1295850797959359500273351)
        ·
          refine ⟨1943776196939039250410027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1295850797959359500273351 1943776196939039250410027)
          ·
            refine ⟨2915664295408558875615041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1943776196939039250410027 2915664295408558875615041)
            ·
              refine ⟨2186748221556419156711281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2915664295408558875615041 2186748221556419156711281)
              ·
                refine ⟨1640061166167314367533461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2186748221556419156711281 1640061166167314367533461)
                ·
                  refine ⟨76877867164092860978131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1640061166167314367533461 76877867164092860978131)
                  ·
                    refine ⟨115316800746139291467197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76877867164092860978131 115316800746139291467197)
                    ·
                      refine ⟨43243800279802234300199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 115316800746139291467197 43243800279802234300199)
                      ·
                        rfl

theorem cell23_84217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_84217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84217 prefixEnd_84217 := by exact prefixLift 84217
  have htrace : WordTrace (prefixWord ++ tailWord_84217) baseStart_84217 baseEnd_84217 := by
    simpa [prefixWord, tailWord_84217, baseEnd_84217] using wordTrace_append hprefix tailTrace_84217
  have hstable : (prefixWord ++ tailWord_84217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84217).length < 2 ^ (prefixWord ++ tailWord_84217).sum := by decide
  have hdescent : baseEnd_84217 < baseStart_84217 := by decide
  rcases family_descends (prefixWord ++ tailWord_84217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84254 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_84254 : Nat := 118140960795 + 84254 * 2 ^ 59
def prefixEnd_84254 : Nat := 4983230072969 + 3 ^ 40 * 84254 * 2
def baseEnd_84254 : Nat := 14420933021339529845843

theorem tailTrace_84254 : CollatzResearch.WordTrace tailWord_84254 prefixEnd_84254 14420933021339529845843 := by
  unfold tailWord_84254
  simp only [CollatzResearch.WordTrace]
  refine ⟨384124479596202785338477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2048663891179748188471877 384124479596202785338477)
  ·
    refine ⟨144046679848576044501929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 384124479596202785338477 144046679848576044501929)
    ·
      refine ⟨108035009886432033376447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144046679848576044501929 108035009886432033376447)
      ·
        refine ⟨162052514829648050064671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108035009886432033376447 162052514829648050064671)
        ·
          refine ⟨243078772244472075097007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162052514829648050064671 243078772244472075097007)
          ·
            refine ⟨364618158366708112645511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243078772244472075097007 364618158366708112645511)
            ·
              refine ⟨546927237550062168968267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364618158366708112645511 546927237550062168968267)
              ·
                refine ⟨820390856325093253452401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546927237550062168968267 820390856325093253452401)
                ·
                  refine ⟨615293142243819940089301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 820390856325093253452401 615293142243819940089301)
                  ·
                    refine ⟨14420933021339529845843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 615293142243819940089301 14420933021339529845843)
                    ·
                      rfl

theorem cell23_84254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_84254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84254 prefixEnd_84254 := by exact prefixLift 84254
  have htrace : WordTrace (prefixWord ++ tailWord_84254) baseStart_84254 baseEnd_84254 := by
    simpa [prefixWord, tailWord_84254, baseEnd_84254] using wordTrace_append hprefix tailTrace_84254
  have hstable : (prefixWord ++ tailWord_84254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84254).length < 2 ^ (prefixWord ++ tailWord_84254).sum := by decide
  have hdescent : baseEnd_84254 < baseStart_84254 := by decide
  rcases family_descends (prefixWord ++ tailWord_84254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84277 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_84277 : Nat := 118140960795 + 84277 * 2 ^ 59
def prefixEnd_84277 : Nat := 4983230072969 + 3 ^ 40 * 84277 * 2
def baseEnd_84277 : Nat := 43274609119071999549923

theorem tailTrace_84277 : CollatzResearch.WordTrace tailWord_84277 prefixEnd_84277 43274609119071999549923 := by
  unfold tailWord_84277
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073834715686297210795085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2049223143790864807196723 3073834715686297210795085)
  ·
    refine ⟨1152688018382361454048157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3073834715686297210795085 1152688018382361454048157)
    ·
      refine ⟨432258006893385545268059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1152688018382361454048157 432258006893385545268059)
      ·
        refine ⟨648387010340078317902089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432258006893385545268059 648387010340078317902089)
        ·
          refine ⟨486290257755058738426567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648387010340078317902089 486290257755058738426567)
          ·
            refine ⟨729435386632588107639851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486290257755058738426567 729435386632588107639851)
            ·
              refine ⟨1094153079948882161459777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 729435386632588107639851 1094153079948882161459777)
              ·
                refine ⟨820614809961661621094833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1094153079948882161459777 820614809961661621094833)
                ·
                  refine ⟨615461107471246215821125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 820614809961661621094833 615461107471246215821125)
                  ·
                    refine ⟨115398957650858665466461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 615461107471246215821125 115398957650858665466461)
                    ·
                      refine ⟨43274609119071999549923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 115398957650858665466461 43274609119071999549923)
                      ·
                        rfl

theorem cell23_84277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_84277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84277 prefixEnd_84277 := by exact prefixLift 84277
  have htrace : WordTrace (prefixWord ++ tailWord_84277) baseStart_84277 baseEnd_84277 := by
    simpa [prefixWord, tailWord_84277, baseEnd_84277] using wordTrace_append hprefix tailTrace_84277
  have hstable : (prefixWord ++ tailWord_84277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84277).length < 2 ^ (prefixWord ++ tailWord_84277).sum := by decide
  have hdescent : baseEnd_84277 < baseStart_84277 := by decide
  rcases family_descends (prefixWord ++ tailWord_84277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84280 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 9]
def baseStart_84280 : Nat := 118140960795 + 84280 * 2 ^ 59
def prefixEnd_84280 : Nat := 4983230072969 + 3 ^ 40 * 84280 * 2
def baseEnd_84280 : Nat := 4808461062337276423601

theorem tailTrace_84280 : CollatzResearch.WordTrace tailWord_84280 prefixEnd_84280 4808461062337276423601 := by
  unfold tailWord_84280
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536972067337714361577147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2049296089783619148769529 1536972067337714361577147)
  ·
    refine ⟨2305458101006571542365721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1536972067337714361577147 2305458101006571542365721)
    ·
      refine ⟨1729093575754928656774291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2305458101006571542365721 1729093575754928656774291)
      ·
        refine ⟨2593640363632392985161437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1729093575754928656774291 2593640363632392985161437)
        ·
          refine ⟨972615136362147369435539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2593640363632392985161437 972615136362147369435539)
          ·
            refine ⟨1458922704543221054153309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972615136362147369435539 1458922704543221054153309)
            ·
              refine ⟨547096014203707895307491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1458922704543221054153309 547096014203707895307491)
              ·
                refine ⟨820644021305561842961237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547096014203707895307491 820644021305561842961237)
                ·
                  refine ⟨4808461062337276423601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 820644021305561842961237 4808461062337276423601)
                  ·
                    rfl

theorem cell23_84280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 9].length) (baseStart_84280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84280 prefixEnd_84280 := by exact prefixLift 84280
  have htrace : WordTrace (prefixWord ++ tailWord_84280) baseStart_84280 baseEnd_84280 := by
    simpa [prefixWord, tailWord_84280, baseEnd_84280] using wordTrace_append hprefix tailTrace_84280
  have hstable : (prefixWord ++ tailWord_84280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84280).length < 2 ^ (prefixWord ++ tailWord_84280).sum := by decide
  have hdescent : baseEnd_84280 < baseStart_84280 := by decide
  rcases family_descends (prefixWord ++ tailWord_84280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84308 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_84308 : Nat := 118140960795 + 84308 * 2 ^ 59
def prefixEnd_84308 : Nat := 4983230072969 + 3 ^ 40 * 84308 * 2
def baseEnd_84308 : Nat := 43290527019361378262281

theorem tailTrace_84308 : CollatzResearch.WordTrace tailWord_84308 prefixEnd_84308 43290527019361378262281 := by
  unfold tailWord_84308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537482689286994752586789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2049976919049326336782385 1537482689286994752586789)
  ·
    refine ⟨288278004241311516110023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1537482689286994752586789 288278004241311516110023)
    ·
      refine ⟨432417006361967274165035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 288278004241311516110023 432417006361967274165035)
      ·
        refine ⟨648625509542950911247553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432417006361967274165035 648625509542950911247553)
        ·
          refine ⟨486469132157213183435665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648625509542950911247553 486469132157213183435665)
          ·
            refine ⟨364851849117909887576749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 486469132157213183435665 364851849117909887576749)
            ·
              refine ⟨136819443419216207841281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364851849117909887576749 136819443419216207841281)
              ·
                refine ⟨102614582564412155880961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136819443419216207841281 102614582564412155880961)
                ·
                  refine ⟨76960936923309116910721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102614582564412155880961 76960936923309116910721)
                  ·
                    refine ⟨57720702692481837683041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76960936923309116910721 57720702692481837683041)
                    ·
                      refine ⟨43290527019361378262281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57720702692481837683041 43290527019361378262281)
                      ·
                        rfl

theorem cell23_84308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_84308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84308 prefixEnd_84308 := by exact prefixLift 84308
  have htrace : WordTrace (prefixWord ++ tailWord_84308) baseStart_84308 baseEnd_84308 := by
    simpa [prefixWord, tailWord_84308, baseEnd_84308] using wordTrace_append hprefix tailTrace_84308
  have hstable : (prefixWord ++ tailWord_84308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84308).length < 2 ^ (prefixWord ++ tailWord_84308).sum := by decide
  have hdescent : baseEnd_84308 < baseStart_84308 := by decide
  rcases family_descends (prefixWord ++ tailWord_84308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84327 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 1, 7]
def baseStart_84327 : Nat := 118140960795 + 84327 * 2 ^ 59
def prefixEnd_84327 : Nat := 4983230072969 + 3 ^ 40 * 84327 * 2
def baseEnd_84327 : Nat := 14433427717265601308231

theorem tailTrace_84327 : CollatzResearch.WordTrace tailWord_84327 prefixEnd_84327 14433427717265601308231 := by
  unfold tailWord_84327
  simp only [CollatzResearch.WordTrace]
  refine ⟨3075658365505155750115235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2050438910336770500076823 3075658365505155750115235)
  ·
    refine ⟨4613487548257733625172853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3075658365505155750115235 4613487548257733625172853)
    ·
      refine ⟨432514457649162527359955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4613487548257733625172853 432514457649162527359955)
      ·
        refine ⟨648771686473743791039933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432514457649162527359955 648771686473743791039933)
        ·
          refine ⟨243289382427653921639975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 648771686473743791039933 243289382427653921639975)
          ·
            refine ⟨364934073641480882459963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243289382427653921639975 364934073641480882459963)
            ·
              refine ⟨547401110462221323689945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364934073641480882459963 547401110462221323689945)
              ·
                refine ⟨410550832846665992767459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547401110462221323689945 410550832846665992767459)
                ·
                  refine ⟨615826249269998989151189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410550832846665992767459 615826249269998989151189)
                  ·
                    refine ⟨14433427717265601308231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 615826249269998989151189 14433427717265601308231)
                    ·
                      rfl

theorem cell23_84327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_84327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84327 prefixEnd_84327 := by exact prefixLift 84327
  have htrace : WordTrace (prefixWord ++ tailWord_84327) baseStart_84327 baseEnd_84327 := by
    simpa [prefixWord, tailWord_84327, baseEnd_84327] using wordTrace_append hprefix tailTrace_84327
  have hstable : (prefixWord ++ tailWord_84327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84327).length < 2 ^ (prefixWord ++ tailWord_84327).sum := by decide
  have hdescent : baseEnd_84327 < baseStart_84327 := by decide
  rcases family_descends (prefixWord ++ tailWord_84327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84347 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 4]
def baseStart_84347 : Nat := 118140960795 + 84347 * 2 ^ 59
def prefixEnd_84347 : Nat := 4983230072969 + 3 ^ 40 * 84347 * 2
def baseEnd_84347 : Nat := 43310552764886725674601

theorem tailTrace_84347 : CollatzResearch.WordTrace tailWord_84347 prefixEnd_84347 43310552764886725674601 := by
  unfold tailWord_84347
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076387825432699165843295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2050925216955132777228863 3076387825432699165843295)
  ·
    refine ⟨4614581738149048748764943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3076387825432699165843295 4614581738149048748764943)
    ·
      refine ⟨6921872607223573123147415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4614581738149048748764943 6921872607223573123147415)
      ·
        refine ⟨10382808910835359684721123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6921872607223573123147415 10382808910835359684721123)
        ·
          refine ⟨15574213366253039527081685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10382808910835359684721123 15574213366253039527081685)
          ·
            refine ⟨365020625771555613915977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15574213366253039527081685 365020625771555613915977)
            ·
              refine ⟨273765469328666710436983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365020625771555613915977 273765469328666710436983)
              ·
                refine ⟨410648203993000065655475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273765469328666710436983 410648203993000065655475)
                ·
                  refine ⟨615972305989500098483213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 410648203993000065655475 615972305989500098483213)
                  ·
                    refine ⟨230989614746062536931205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 615972305989500098483213 230989614746062536931205)
                    ·
                      refine ⟨43310552764886725674601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 230989614746062536931205 43310552764886725674601)
                      ·
                        rfl

theorem cell23_84347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 4].length) (baseStart_84347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84347 prefixEnd_84347 := by exact prefixLift 84347
  have htrace : WordTrace (prefixWord ++ tailWord_84347) baseStart_84347 baseEnd_84347 := by
    simpa [prefixWord, tailWord_84347, baseEnd_84347] using wordTrace_append hprefix tailTrace_84347
  have hstable : (prefixWord ++ tailWord_84347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84347).length < 2 ^ (prefixWord ++ tailWord_84347).sum := by decide
  have hdescent : baseEnd_84347 < baseStart_84347 := by decide
  rcases family_descends (prefixWord ++ tailWord_84347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84364 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_84364 : Nat := 118140960795 + 84364 * 2 ^ 59
def prefixEnd_84364 : Nat := 4983230072969 + 3 ^ 40 * 84364 * 2
def baseEnd_84364 : Nat := 43319281936013159162023

theorem tailTrace_84364 : CollatzResearch.WordTrace tailWord_84364 prefixEnd_84364 43319281936013159162023 := by
  unfold tailWord_84364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1538503933185555534606073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2051338577580740712808097 1538503933185555534606073)
  ·
    refine ⟨1153877949889166650954555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1538503933185555534606073 1153877949889166650954555)
    ·
      refine ⟨1730816924833749976431833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1153877949889166650954555 1730816924833749976431833)
      ·
        refine ⟨1298112693625312482323875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1730816924833749976431833 1298112693625312482323875)
        ·
          refine ⟨1947169040437968723485813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298112693625312482323875 1947169040437968723485813)
          ·
            refine ⟨182547097541059567826795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1947169040437968723485813 182547097541059567826795)
            ·
              refine ⟨273820646311589351740193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182547097541059567826795 273820646311589351740193)
              ·
                refine ⟨205365484733692013805145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273820646311589351740193 205365484733692013805145)
                ·
                  refine ⟨154024113550269010353859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205365484733692013805145 154024113550269010353859)
                  ·
                    refine ⟨231036170325403515530789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 154024113550269010353859 231036170325403515530789)
                    ·
                      refine ⟨43319281936013159162023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 231036170325403515530789 43319281936013159162023)
                      ·
                        rfl

theorem cell23_84364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_84364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84364 prefixEnd_84364 := by exact prefixLift 84364
  have htrace : WordTrace (prefixWord ++ tailWord_84364) baseStart_84364 baseEnd_84364 := by
    simpa [prefixWord, tailWord_84364, baseEnd_84364] using wordTrace_append hprefix tailTrace_84364
  have hstable : (prefixWord ++ tailWord_84364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84364).length < 2 ^ (prefixWord ++ tailWord_84364).sum := by decide
  have hdescent : baseEnd_84364 < baseStart_84364 := by decide
  rcases family_descends (prefixWord ++ tailWord_84364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84401 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 2, 2, 3]
def baseStart_84401 : Nat := 118140960795 + 84401 * 2 ^ 59
def prefixEnd_84401 : Nat := 4983230072969 + 3 ^ 40 * 84401 * 2
def baseEnd_84401 : Nat := 43338280720229514399353

theorem tailTrace_84401 : CollatzResearch.WordTrace tailWord_84401 prefixEnd_84401 43338280720229514399353 := by
  unfold tailWord_84401
  simp only [CollatzResearch.WordTrace]
  refine ⟨3078357367237066388309057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2052238244824710925539371 3078357367237066388309057)
  ·
    refine ⟨2308768025427799791231793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3078357367237066388309057 2308768025427799791231793)
    ·
      refine ⟨1731576019070849843423845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2308768025427799791231793 1731576019070849843423845)
      ·
        refine ⟨324670503575784345641971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1731576019070849843423845 324670503575784345641971)
        ·
          refine ⟨487005755363676518462957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324670503575784345641971 487005755363676518462957)
          ·
            refine ⟨182627158261378694423609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487005755363676518462957 182627158261378694423609)
            ·
              refine ⟨136970368696034020817707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182627158261378694423609 136970368696034020817707)
              ·
                refine ⟨205455553044051031226561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136970368696034020817707 205455553044051031226561)
                ·
                  refine ⟨154091664783038273419921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205455553044051031226561 154091664783038273419921)
                  ·
                    refine ⟨115568748587278705064941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154091664783038273419921 115568748587278705064941)
                    ·
                      refine ⟨43338280720229514399353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 115568748587278705064941 43338280720229514399353)
                      ·
                        rfl

theorem cell23_84401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_84401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84401 prefixEnd_84401 := by exact prefixLift 84401
  have htrace : WordTrace (prefixWord ++ tailWord_84401) baseStart_84401 baseEnd_84401 := by
    simpa [prefixWord, tailWord_84401, baseEnd_84401] using wordTrace_append hprefix tailTrace_84401
  have hstable : (prefixWord ++ tailWord_84401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84401).length < 2 ^ (prefixWord ++ tailWord_84401).sum := by decide
  have hdescent : baseEnd_84401 < baseStart_84401 := by decide
  rcases family_descends (prefixWord ++ tailWord_84401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84457 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 5]
def baseStart_84457 : Nat := 118140960795 + 84457 * 2 ^ 59
def prefixEnd_84457 : Nat := 4983230072969 + 3 ^ 40 * 84457 * 2
def baseEnd_84457 : Nat := 43367035636881295299095

theorem tailTrace_84457 : CollatzResearch.WordTrace tailWord_84457 prefixEnd_84457 43367035636881295299095 := by
  unfold tailWord_84457
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080399855034187952347625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2053599903356125301565083 3080399855034187952347625)
  ·
    refine ⟨2310299891275640964260719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3080399855034187952347625 2310299891275640964260719)
    ·
      refine ⟨3465449836913461446391079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2310299891275640964260719 3465449836913461446391079)
      ·
        refine ⟨5198174755370192169586619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3465449836913461446391079 5198174755370192169586619)
        ·
          refine ⟨7797262133055288254379929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198174755370192169586619 7797262133055288254379929)
          ·
            refine ⟨5847946599791466190784947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7797262133055288254379929 5847946599791466190784947)
            ·
              refine ⟨8771919899687199286177421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5847946599791466190784947 8771919899687199286177421)
              ·
                refine ⟨3289469962382699732316533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8771919899687199286177421 3289469962382699732316533)
                ·
                  refine ⟨308387808973378099904675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3289469962382699732316533 308387808973378099904675)
                  ·
                    refine ⟨462581713460067149857013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 308387808973378099904675 462581713460067149857013)
                    ·
                      refine ⟨43367035636881295299095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 462581713460067149857013 43367035636881295299095)
                      ·
                        rfl

theorem cell23_84457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_84457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84457 prefixEnd_84457 := by exact prefixLift 84457
  have htrace : WordTrace (prefixWord ++ tailWord_84457) baseStart_84457 baseEnd_84457 := by
    simpa [prefixWord, tailWord_84457, baseEnd_84457] using wordTrace_append hprefix tailTrace_84457
  have hstable : (prefixWord ++ tailWord_84457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84457).length < 2 ^ (prefixWord ++ tailWord_84457).sum := by decide
  have hdescent : baseEnd_84457 < baseStart_84457 := by decide
  rcases family_descends (prefixWord ++ tailWord_84457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84458 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_84458 : Nat := 118140960795 + 84458 * 2 ^ 59
def prefixEnd_84458 : Nat := 4983230072969 + 3 ^ 40 * 84458 * 2
def baseEnd_84458 : Nat := 43367549117535791386591

theorem tailTrace_84458 : CollatzResearch.WordTrace tailWord_84458 prefixEnd_84458 43367549117535791386591 := by
  unfold tailWord_84458
  simp only [CollatzResearch.WordTrace]
  refine ⟨770109082007641280783507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2053624218687043415422685 770109082007641280783507)
  ·
    refine ⟨1155163623011461921175261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770109082007641280783507 1155163623011461921175261)
    ·
      refine ⟨433186358629298220440723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1155163623011461921175261 433186358629298220440723)
      ·
        refine ⟨649779537943947330661085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433186358629298220440723 649779537943947330661085)
        ·
          refine ⟨243667326728980248997907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 649779537943947330661085 243667326728980248997907)
          ·
            refine ⟨365500990093470373496861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243667326728980248997907 365500990093470373496861)
            ·
              refine ⟨137062871285051390061323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365500990093470373496861 137062871285051390061323)
              ·
                refine ⟨205594306927577085091985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137062871285051390061323 205594306927577085091985)
                ·
                  refine ⟨154195730195682813818989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205594306927577085091985 154195730195682813818989)
                  ·
                    refine ⟨57823398823381055182121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154195730195682813818989 57823398823381055182121)
                    ·
                      refine ⟨43367549117535791386591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57823398823381055182121 43367549117535791386591)
                      ·
                        rfl

theorem cell23_84458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_84458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84458 prefixEnd_84458 := by exact prefixLift 84458
  have htrace : WordTrace (prefixWord ++ tailWord_84458) baseStart_84458 baseEnd_84458 := by
    simpa [prefixWord, tailWord_84458, baseEnd_84458] using wordTrace_append hprefix tailTrace_84458
  have hstable : (prefixWord ++ tailWord_84458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84458).length < 2 ^ (prefixWord ++ tailWord_84458).sum := by decide
  have hdescent : baseEnd_84458 < baseStart_84458 := by decide
  rcases family_descends (prefixWord ++ tailWord_84458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84464 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 4, 4]
def baseStart_84464 : Nat := 118140960795 + 84464 * 2 ^ 59
def prefixEnd_84464 : Nat := 4983230072969 + 3 ^ 40 * 84464 * 2
def baseEnd_84464 : Nat := 14456876667154255970521

theorem tailTrace_84464 : CollatzResearch.WordTrace tailWord_84464 prefixEnd_84464 14456876667154255970521 := by
  unfold tailWord_84464
  simp only [CollatzResearch.WordTrace]
  refine ⟨1540327583004414073926223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2053770110672552098568297 1540327583004414073926223)
  ·
    refine ⟨2310491374506621110889335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1540327583004414073926223 2310491374506621110889335)
    ·
      refine ⟨3465737061759931666334003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2310491374506621110889335 3465737061759931666334003)
      ·
        refine ⟨5198605592639897499501005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3465737061759931666334003 5198605592639897499501005)
        ·
          refine ⟨1949477097239961562312877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5198605592639897499501005 1949477097239961562312877)
          ·
            refine ⟨731053911464985585867329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1949477097239961562312877 731053911464985585867329)
            ·
              refine ⟨548290433598739189400497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731053911464985585867329 548290433598739189400497)
              ·
                refine ⟨411217825199054392050373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548290433598739189400497 411217825199054392050373)
                ·
                  refine ⟨77103342224822698509445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411217825199054392050373 77103342224822698509445)
                  ·
                    refine ⟨14456876667154255970521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77103342224822698509445 14456876667154255970521)
                    ·
                      rfl

theorem cell23_84464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4, 4].length) (baseStart_84464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84464 prefixEnd_84464 := by exact prefixLift 84464
  have htrace : WordTrace (prefixWord ++ tailWord_84464) baseStart_84464 baseEnd_84464 := by
    simpa [prefixWord, tailWord_84464, baseEnd_84464] using wordTrace_append hprefix tailTrace_84464
  have hstable : (prefixWord ++ tailWord_84464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84464).length < 2 ^ (prefixWord ++ tailWord_84464).sum := by decide
  have hdescent : baseEnd_84464 < baseStart_84464 := by decide
  rcases family_descends (prefixWord ++ tailWord_84464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84474 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3]
def baseStart_84474 : Nat := 118140960795 + 84474 * 2 ^ 59
def prefixEnd_84474 : Nat := 4983230072969 + 3 ^ 40 * 84474 * 2
def baseEnd_84474 : Nat := 43375764808007728786517

theorem tailTrace_84474 : CollatzResearch.WordTrace tailWord_84474 prefixEnd_84474 43375764808007728786517 := by
  unfold tailWord_84474
  simp only [CollatzResearch.WordTrace]
  refine ⟨770254973993149963929119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2054013263981733237144317 770254973993149963929119)
  ·
    refine ⟨1155382460989724945893679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770254973993149963929119 1155382460989724945893679)
    ·
      refine ⟨1733073691484587418840519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155382460989724945893679 1733073691484587418840519)
      ·
        refine ⟨2599610537226881128260779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733073691484587418840519 2599610537226881128260779)
        ·
          refine ⟨3899415805840321692391169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2599610537226881128260779 3899415805840321692391169)
          ·
            refine ⟨2924561854380241269293377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3899415805840321692391169 2924561854380241269293377)
            ·
              refine ⟨2193421390785180951970033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2924561854380241269293377 2193421390785180951970033)
              ·
                refine ⟨1645066043088885713977525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2193421390785180951970033 1645066043088885713977525)
                ·
                  refine ⟨154224941539583035685393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1645066043088885713977525 154224941539583035685393)
                  ·
                    refine ⟨115668706154687276764045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154224941539583035685393 115668706154687276764045)
                    ·
                      refine ⟨43375764808007728786517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 115668706154687276764045 43375764808007728786517)
                      ·
                        rfl

theorem cell23_84474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_84474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84474 prefixEnd_84474 := by exact prefixLift 84474
  have htrace : WordTrace (prefixWord ++ tailWord_84474) baseStart_84474 baseEnd_84474 := by
    simpa [prefixWord, tailWord_84474, baseEnd_84474] using wordTrace_append hprefix tailTrace_84474
  have hstable : (prefixWord ++ tailWord_84474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84474).length < 2 ^ (prefixWord ++ tailWord_84474).sum := by decide
  have hdescent : baseEnd_84474 < baseStart_84474 := by decide
  rcases family_descends (prefixWord ++ tailWord_84474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84477 : List Nat := [1, 4, 1, 1, 1, 3, 12]
def baseStart_84477 : Nat := 118140960795 + 84477 * 2 ^ 59
def prefixEnd_84477 : Nat := 4983230072969 + 3 ^ 40 * 84477 * 2
def baseEnd_84477 : Nat := 535522287036681691963

theorem tailTrace_84477 : CollatzResearch.WordTrace tailWord_84477 prefixEnd_84477 535522287036681691963 := by
  unfold tailWord_84477
  simp only [CollatzResearch.WordTrace]
  refine ⟨3081129314961731368075685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2054086209974487578717123 3081129314961731368075685)
  ·
    refine ⟨577711746555324631514191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3081129314961731368075685 577711746555324631514191)
    ·
      refine ⟨866567619832986947271287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 577711746555324631514191 866567619832986947271287)
      ·
        refine ⟨1299851429749480420906931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866567619832986947271287 1299851429749480420906931)
        ·
          refine ⟨1949777144624220631360397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299851429749480420906931 1949777144624220631360397)
          ·
            refine ⟨731166429234082736760149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1949777144624220631360397 731166429234082736760149)
            ·
              refine ⟨535522287036681691963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 731166429234082736760149 535522287036681691963)
              ·
                rfl

theorem cell23_84477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 12].length) (baseStart_84477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84477 prefixEnd_84477 := by exact prefixLift 84477
  have htrace : WordTrace (prefixWord ++ tailWord_84477) baseStart_84477 baseEnd_84477 := by
    simpa [prefixWord, tailWord_84477, baseEnd_84477] using wordTrace_append hprefix tailTrace_84477
  have hstable : (prefixWord ++ tailWord_84477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84477).length < 2 ^ (prefixWord ++ tailWord_84477).sum := by decide
  have hdescent : baseEnd_84477 < baseStart_84477 := by decide
  rcases family_descends (prefixWord ++ tailWord_84477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84481 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 4, 4]
def baseStart_84481 : Nat := 118140960795 + 84481 * 2 ^ 59
def prefixEnd_84481 : Nat := 4983230072969 + 3 ^ 40 * 84481 * 2
def baseEnd_84481 : Nat := 14459786390863067132995

theorem tailTrace_84481 : CollatzResearch.WordTrace tailWord_84481 prefixEnd_84481 14459786390863067132995 := by
  unfold tailWord_84481
  simp only [CollatzResearch.WordTrace]
  refine ⟨3081275206947240051221297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2054183471298160034147531 3081275206947240051221297)
  ·
    refine ⟨2310956405210430038415973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3081275206947240051221297 2310956405210430038415973)
    ·
      refine ⟨433304325976955632202995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2310956405210430038415973 433304325976955632202995)
      ·
        refine ⟨649956488965433448304493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433304325976955632202995 649956488965433448304493)
        ·
          refine ⟨243733683362037543114185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 649956488965433448304493 243733683362037543114185)
          ·
            refine ⟨182800262521528157335639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243733683362037543114185 182800262521528157335639)
            ·
              refine ⟨274200393782292236003459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182800262521528157335639 274200393782292236003459)
              ·
                refine ⟨411300590673438354005189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274200393782292236003459 411300590673438354005189)
                ·
                  refine ⟨77118860751269691375973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411300590673438354005189 77118860751269691375973)
                  ·
                    refine ⟨14459786390863067132995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77118860751269691375973 14459786390863067132995)
                    ·
                      rfl

theorem cell23_84481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_84481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84481 prefixEnd_84481 := by exact prefixLift 84481
  have htrace : WordTrace (prefixWord ++ tailWord_84481) baseStart_84481 baseEnd_84481 := by
    simpa [prefixWord, tailWord_84481, baseEnd_84481] using wordTrace_append hprefix tailTrace_84481
  have hstable : (prefixWord ++ tailWord_84481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84481).length < 2 ^ (prefixWord ++ tailWord_84481).sum := by decide
  have hdescent : baseEnd_84481 < baseStart_84481 := by decide
  rcases family_descends (prefixWord ++ tailWord_84481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84497 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 6]
def baseStart_84497 : Nat := 118140960795 + 84497 * 2 ^ 59
def prefixEnd_84497 : Nat := 4983230072969 + 3 ^ 40 * 84497 * 2
def baseEnd_84497 : Nat := 43387574863061138798911

theorem tailTrace_84497 : CollatzResearch.WordTrace tailWord_84497 prefixEnd_84497 43387574863061138798911 := by
  unfold tailWord_84497
  simp only [CollatzResearch.WordTrace]
  refine ⟨3081858774889274783803745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2054572516592849855869163 3081858774889274783803745)
  ·
    refine ⟨2311394081166956087852809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3081858774889274783803745 2311394081166956087852809)
    ·
      refine ⟨1733545560875217065889607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2311394081166956087852809 1733545560875217065889607)
      ·
        refine ⟨2600318341312825598834411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733545560875217065889607 2600318341312825598834411)
        ·
          refine ⟨3900477511969238398251617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600318341312825598834411 3900477511969238398251617)
          ·
            refine ⟨2925358133976928798688713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3900477511969238398251617 2925358133976928798688713)
            ·
              refine ⟨2194018600482696599016535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2925358133976928798688713 2194018600482696599016535)
              ·
                refine ⟨3291027900724044898524803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194018600482696599016535 3291027900724044898524803)
                ·
                  refine ⟨4936541851086067347787205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291027900724044898524803 4936541851086067347787205)
                  ·
                    refine ⟨925601597078637627710101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4936541851086067347787205 925601597078637627710101)
                    ·
                      refine ⟨43387574863061138798911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 925601597078637627710101 43387574863061138798911)
                      ·
                        rfl

theorem cell23_84497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_84497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84497 prefixEnd_84497 := by exact prefixLift 84497
  have htrace : WordTrace (prefixWord ++ tailWord_84497) baseStart_84497 baseEnd_84497 := by
    simpa [prefixWord, tailWord_84497, baseEnd_84497] using wordTrace_append hprefix tailTrace_84497
  have hstable : (prefixWord ++ tailWord_84497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84497).length < 2 ^ (prefixWord ++ tailWord_84497).sum := by decide
  have hdescent : baseEnd_84497 < baseStart_84497 := by decide
  rcases family_descends (prefixWord ++ tailWord_84497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84508 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_84508 : Nat := 118140960795 + 84508 * 2 ^ 59
def prefixEnd_84508 : Nat := 4983230072969 + 3 ^ 40 * 84508 * 2
def baseEnd_84508 : Nat := 43393223150260595761361

theorem tailTrace_84508 : CollatzResearch.WordTrace tailWord_84508 prefixEnd_84508 43393223150260595761361 := by
  unfold tailWord_84508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541129988924711831227089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2054839985232949108302785 1541129988924711831227089)
  ·
    refine ⟨1155847491693533873420317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1541129988924711831227089 1155847491693533873420317)
    ·
      refine ⟨433442809385075202532619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1155847491693533873420317 433442809385075202532619)
      ·
        refine ⟨650164214077612803798929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433442809385075202532619 650164214077612803798929)
        ·
          refine ⟨487623160558209602849197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 650164214077612803798929 487623160558209602849197)
          ·
            refine ⟨182858685209328601068449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 487623160558209602849197 182858685209328601068449)
            ·
              refine ⟨137144013906996450801337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182858685209328601068449 137144013906996450801337)
              ·
                refine ⟨102858010430247338101003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137144013906996450801337 102858010430247338101003)
                ·
                  refine ⟨154287015645371007151505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102858010430247338101003 154287015645371007151505)
                  ·
                    refine ⟨115715261734028255363629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154287015645371007151505 115715261734028255363629)
                    ·
                      refine ⟨43393223150260595761361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 115715261734028255363629 43393223150260595761361)
                      ·
                        rfl

theorem cell23_84508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_84508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84508 prefixEnd_84508 := by exact prefixLift 84508
  have htrace : WordTrace (prefixWord ++ tailWord_84508) baseStart_84508 baseEnd_84508 := by
    simpa [prefixWord, tailWord_84508, baseEnd_84508] using wordTrace_append hprefix tailTrace_84508
  have hstable : (prefixWord ++ tailWord_84508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84508).length < 2 ^ (prefixWord ++ tailWord_84508).sum := by decide
  have hdescent : baseEnd_84508 < baseStart_84508 := by decide
  rcases family_descends (prefixWord ++ tailWord_84508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84522 : List Nat := [3, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_84522 : Nat := 118140960795 + 84522 * 2 ^ 59
def prefixEnd_84522 : Nat := 4983230072969 + 3 ^ 40 * 84522 * 2
def baseEnd_84522 : Nat := 43400411879423540986297

theorem tailTrace_84522 : CollatzResearch.WordTrace tailWord_84522 prefixEnd_84522 43400411879423540986297 := by
  unfold tailWord_84522
  simp only [CollatzResearch.WordTrace]
  refine ⟨770692649949676013365955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2055180399865802702309213 770692649949676013365955)
  ·
    refine ⟨1156038974924514020048933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770692649949676013365955 1156038974924514020048933)
    ·
      refine ⟨216757307798346378759175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1156038974924514020048933 216757307798346378759175)
      ·
        refine ⟨325135961697519568138763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216757307798346378759175 325135961697519568138763)
        ·
          refine ⟨487703942546279352208145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325135961697519568138763 487703942546279352208145)
          ·
            refine ⟨365777956909709514156109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487703942546279352208145 365777956909709514156109)
            ·
              refine ⟨137166733841141067808541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365777956909709514156109 137166733841141067808541)
              ·
                refine ⟨51437525190427900428203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137166733841141067808541 51437525190427900428203)
                ·
                  refine ⟨77156287785641850642305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51437525190427900428203 77156287785641850642305)
                  ·
                    refine ⟨57867215839231387981729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77156287785641850642305 57867215839231387981729)
                    ·
                      refine ⟨43400411879423540986297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57867215839231387981729 43400411879423540986297)
                      ·
                        rfl

theorem cell23_84522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_84522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84522 prefixEnd_84522 := by exact prefixLift 84522
  have htrace : WordTrace (prefixWord ++ tailWord_84522) baseStart_84522 baseEnd_84522 := by
    simpa [prefixWord, tailWord_84522, baseEnd_84522] using wordTrace_append hprefix tailTrace_84522
  have hstable : (prefixWord ++ tailWord_84522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84522).length < 2 ^ (prefixWord ++ tailWord_84522).sum := by decide
  have hdescent : baseEnd_84522 < baseStart_84522 := by decide
  rcases family_descends (prefixWord ++ tailWord_84522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84527 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_84527 : Nat := 118140960795 + 84527 * 2 ^ 59
def prefixEnd_84527 : Nat := 4983230072969 + 3 ^ 40 * 84527 * 2
def baseEnd_84527 : Nat := 43402979282696021423773

theorem tailTrace_84527 : CollatzResearch.WordTrace tailWord_84527 prefixEnd_84527 43402979282696021423773 := by
  unfold tailWord_84527
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082952964780589907395835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2055301976520393271597223 3082952964780589907395835)
  ·
    refine ⟨4624429447170884861093753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3082952964780589907395835 4624429447170884861093753)
    ·
      refine ⟨3468322085378163645820315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4624429447170884861093753 3468322085378163645820315)
      ·
        refine ⟨5202483128067245468730473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468322085378163645820315 5202483128067245468730473)
        ·
          refine ⟨3901862346050434101547855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5202483128067245468730473 3901862346050434101547855)
          ·
            refine ⟨5852793519075651152321783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901862346050434101547855 5852793519075651152321783)
            ·
              refine ⟨8779190278613476728482675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5852793519075651152321783 8779190278613476728482675)
              ·
                refine ⟨13168785417920215092724013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8779190278613476728482675 13168785417920215092724013)
                ·
                  refine ⟨4938294531720080659771505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13168785417920215092724013 4938294531720080659771505)
                  ·
                    refine ⟨3703720898790060494828629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4938294531720080659771505 3703720898790060494828629)
                    ·
                      refine ⟨43402979282696021423773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 3703720898790060494828629 43402979282696021423773)
                      ·
                        rfl

theorem cell23_84527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_84527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84527 prefixEnd_84527 := by exact prefixLift 84527
  have htrace : WordTrace (prefixWord ++ tailWord_84527) baseStart_84527 baseEnd_84527 := by
    simpa [prefixWord, tailWord_84527, baseEnd_84527] using wordTrace_append hprefix tailTrace_84527
  have hstable : (prefixWord ++ tailWord_84527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84527).length < 2 ^ (prefixWord ++ tailWord_84527).sum := by decide
  have hdescent : baseEnd_84527 < baseStart_84527 := by decide
  rcases family_descends (prefixWord ++ tailWord_84527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84668 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 2, 4, 2]
def baseStart_84668 : Nat := 118140960795 + 84668 * 2 ^ 59
def prefixEnd_84668 : Nat := 4983230072969 + 3 ^ 40 * 84668 * 2
def baseEnd_84668 : Nat := 43475380054979969760625

theorem tailTrace_84668 : CollatzResearch.WordTrace tailWord_84668 prefixEnd_84668 43475380054979969760625 := by
  unfold tailWord_84668
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544047828634885494139329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2058730438179847325519105 1544047828634885494139329)
  ·
    refine ⟨1158035871476164120604497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1544047828634885494139329 1158035871476164120604497)
    ·
      refine ⟨868526903607123090453373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1158035871476164120604497 868526903607123090453373)
      ·
        refine ⟨325697588852671158920015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 868526903607123090453373 325697588852671158920015)
        ·
          refine ⟨488546383279006738380023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325697588852671158920015 488546383279006738380023)
          ·
            refine ⟨732819574918510107570035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488546383279006738380023 732819574918510107570035)
            ·
              refine ⟨1099229362377765161355053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732819574918510107570035 1099229362377765161355053)
              ·
                refine ⟨412211010891661935508145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1099229362377765161355053 412211010891661935508145)
                ·
                  refine ⟨309158258168746451631109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 412211010891661935508145 309158258168746451631109)
                  ·
                    refine ⟨57967173406639959680833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 309158258168746451631109 57967173406639959680833)
                    ·
                      refine ⟨43475380054979969760625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 57967173406639959680833 43475380054979969760625)
                      ·
                        rfl

theorem cell23_84668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_84668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84668 prefixEnd_84668 := by exact prefixLift 84668
  have htrace : WordTrace (prefixWord ++ tailWord_84668) baseStart_84668 baseEnd_84668 := by
    simpa [prefixWord, tailWord_84668, baseEnd_84668] using wordTrace_append hprefix tailTrace_84668
  have hstable : (prefixWord ++ tailWord_84668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84668).length < 2 ^ (prefixWord ++ tailWord_84668).sum := by decide
  have hdescent : baseEnd_84668 < baseStart_84668 := by decide
  rcases family_descends (prefixWord ++ tailWord_84668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84671 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 3]
def baseStart_84671 : Nat := 118140960795 + 84671 * 2 ^ 59
def prefixEnd_84671 : Nat := 4983230072969 + 3 ^ 40 * 84671 * 2
def baseEnd_84671 : Nat := 43476920496943458023111

theorem tailTrace_84671 : CollatzResearch.WordTrace tailWord_84671 prefixEnd_84671 43476920496943458023111 := by
  unfold tailWord_84671
  simp only [CollatzResearch.WordTrace]
  refine ⟨3088205076258902500637867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2058803384172601667091911 3088205076258902500637867)
  ·
    refine ⟨4632307614388353750956801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3088205076258902500637867 4632307614388353750956801)
    ·
      refine ⟨3474230710791265313217601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4632307614388353750956801 3474230710791265313217601)
      ·
        refine ⟨2605673033093448984913201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3474230710791265313217601 2605673033093448984913201)
        ·
          refine ⟨1954254774820086738684901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2605673033093448984913201 1954254774820086738684901)
          ·
            refine ⟨366422770278766263503419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1954254774820086738684901 366422770278766263503419)
            ·
              refine ⟨549634155418149395255129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366422770278766263503419 549634155418149395255129)
              ·
                refine ⟨412225616563612046441347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549634155418149395255129 412225616563612046441347)
                ·
                  refine ⟨618338424845418069662021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 412225616563612046441347 618338424845418069662021)
                  ·
                    refine ⟨115938454658515888061629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 618338424845418069662021 115938454658515888061629)
                    ·
                      refine ⟨43476920496943458023111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 115938454658515888061629 43476920496943458023111)
                      ·
                        rfl

theorem cell23_84671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_84671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84671 prefixEnd_84671 := by exact prefixLift 84671
  have htrace : WordTrace (prefixWord ++ tailWord_84671) baseStart_84671 baseEnd_84671 := by
    simpa [prefixWord, tailWord_84671, baseEnd_84671] using wordTrace_append hprefix tailTrace_84671
  have hstable : (prefixWord ++ tailWord_84671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84671).length < 2 ^ (prefixWord ++ tailWord_84671).sum := by decide
  have hdescent : baseEnd_84671 < baseStart_84671 := by decide
  rcases family_descends (prefixWord ++ tailWord_84671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84695 : List Nat := [1, 1, 3, 2, 1, 4, 3, 3, 1, 4]
def baseStart_84695 : Nat := 118140960795 + 84695 * 2 ^ 59
def prefixEnd_84695 : Nat := 4983230072969 + 3 ^ 40 * 84695 * 2
def baseEnd_84695 : Nat := 14496414677550454707667

theorem tailTrace_84695 : CollatzResearch.WordTrace tailWord_84695 prefixEnd_84695 14496414677550454707667 := by
  unfold tailWord_84695
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089080428171954599511539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2059386952114636399674359 3089080428171954599511539)
  ·
    refine ⟨4633620642257931899267309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3089080428171954599511539 4633620642257931899267309)
    ·
      refine ⟨1737607740846724462225241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4633620642257931899267309 1737607740846724462225241)
      ·
        refine ⟨1303205805635043346668931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1737607740846724462225241 1303205805635043346668931)
        ·
          refine ⟨1954808708452565020003397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303205805635043346668931 1954808708452565020003397)
          ·
            refine ⟨366526632834855941250637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1954808708452565020003397 366526632834855941250637)
            ·
              refine ⟨137447487313070977968989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 366526632834855941250637 137447487313070977968989)
              ·
                refine ⟨51542807742401616738371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137447487313070977968989 51542807742401616738371)
                ·
                  refine ⟨77314211613602425107557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51542807742401616738371 77314211613602425107557)
                  ·
                    refine ⟨14496414677550454707667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77314211613602425107557 14496414677550454707667)
                    ·
                      rfl

theorem cell23_84695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_84695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84695 prefixEnd_84695 := by exact prefixLift 84695
  have htrace : WordTrace (prefixWord ++ tailWord_84695) baseStart_84695 baseEnd_84695 := by
    simpa [prefixWord, tailWord_84695, baseEnd_84695] using wordTrace_append hprefix tailTrace_84695
  have hstable : (prefixWord ++ tailWord_84695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84695).length < 2 ^ (prefixWord ++ tailWord_84695).sum := by decide
  have hdescent : baseEnd_84695 < baseStart_84695 := by decide
  rcases family_descends (prefixWord ++ tailWord_84695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84712 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 3, 4]
def baseStart_84712 : Nat := 118140960795 + 84712 * 2 ^ 59
def prefixEnd_84712 : Nat := 4983230072969 + 3 ^ 40 * 84712 * 2
def baseEnd_84712 : Nat := 14499324401259265870141

theorem tailTrace_84712 : CollatzResearch.WordTrace tailWord_84712 prefixEnd_84712 14499324401259265870141 := by
  unfold tailWord_84712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544850234555183251440195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2059800312740244335253593 1544850234555183251440195)
  ·
    refine ⟨2317275351832774877160293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1544850234555183251440195 2317275351832774877160293)
    ·
      refine ⟨434489128468645289467555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2317275351832774877160293 434489128468645289467555)
      ·
        refine ⟨651733692702967934201333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434489128468645289467555 651733692702967934201333)
        ·
          refine ⟨61100033690903243831375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 651733692702967934201333 61100033690903243831375)
          ·
            refine ⟨91650050536354865747063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61100033690903243831375 91650050536354865747063)
            ·
              refine ⟨137475075804532298620595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91650050536354865747063 137475075804532298620595)
              ·
                refine ⟨206212613706798447930893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137475075804532298620595 206212613706798447930893)
                ·
                  refine ⟨77329730140049417974085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206212613706798447930893 77329730140049417974085)
                  ·
                    refine ⟨14499324401259265870141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77329730140049417974085 14499324401259265870141)
                    ·
                      rfl

theorem cell23_84712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_84712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84712 prefixEnd_84712 := by exact prefixLift 84712
  have htrace : WordTrace (prefixWord ++ tailWord_84712) baseStart_84712 baseEnd_84712 := by
    simpa [prefixWord, tailWord_84712, baseEnd_84712] using wordTrace_append hprefix tailTrace_84712
  have hstable : (prefixWord ++ tailWord_84712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84712).length < 2 ^ (prefixWord ++ tailWord_84712).sum := by decide
  have hdescent : baseEnd_84712 < baseStart_84712 := by decide
  rcases family_descends (prefixWord ++ tailWord_84712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84721 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 3, 5]
def baseStart_84721 : Nat := 118140960795 + 84721 * 2 ^ 59
def prefixEnd_84721 : Nat := 4983230072969 + 3 ^ 40 * 84721 * 2
def baseEnd_84721 : Nat := 14500864843222754132627

theorem tailTrace_84721 : CollatzResearch.WordTrace tailWord_84721 prefixEnd_84721 14500864843222754132627 := by
  unfold tailWord_84721
  simp only [CollatzResearch.WordTrace]
  refine ⟨3090028726077761039958017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2060019150718507359972011 3090028726077761039958017)
  ·
    refine ⟨2317521544558320779968513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3090028726077761039958017 2317521544558320779968513)
    ·
      refine ⟨1738141158418740584976385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2317521544558320779968513 1738141158418740584976385)
      ·
        refine ⟨1303605868814055438732289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1738141158418740584976385 1303605868814055438732289)
        ·
          refine ⟨977704401610541579049217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1303605868814055438732289 977704401610541579049217)
          ·
            refine ⟨733278301207906184286913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977704401610541579049217 733278301207906184286913)
            ·
              refine ⟨549958725905929638215185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 733278301207906184286913 549958725905929638215185)
              ·
                refine ⟨412469044429447228661389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549958725905929638215185 412469044429447228661389)
                ·
                  refine ⟨154675891661042710748021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 412469044429447228661389 154675891661042710748021)
                  ·
                    refine ⟨14500864843222754132627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 154675891661042710748021 14500864843222754132627)
                    ·
                      rfl

theorem cell23_84721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_84721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84721 prefixEnd_84721 := by exact prefixLift 84721
  have htrace : WordTrace (prefixWord ++ tailWord_84721) baseStart_84721 baseEnd_84721 := by
    simpa [prefixWord, tailWord_84721, baseEnd_84721] using wordTrace_append hprefix tailTrace_84721
  have hstable : (prefixWord ++ tailWord_84721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84721).length < 2 ^ (prefixWord ++ tailWord_84721).sum := by decide
  have hdescent : baseEnd_84721 < baseStart_84721 := by decide
  rcases family_descends (prefixWord ++ tailWord_84721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84728 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 4, 3, 2]
def baseStart_84728 : Nat := 118140960795 + 84728 * 2 ^ 59
def prefixEnd_84728 : Nat := 4983230072969 + 3 ^ 40 * 84728 * 2
def baseEnd_84728 : Nat := 43506188894249735010349

theorem tailTrace_84728 : CollatzResearch.WordTrace tailWord_84728 prefixEnd_84728 43506188894249735010349 := by
  unfold tailWord_84728
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545142018526200617731419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2060189358034934156975225 1545142018526200617731419)
  ·
    refine ⟨2317713027789300926597129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1545142018526200617731419 2317713027789300926597129)
    ·
      refine ⟨1738284770841975694947847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2317713027789300926597129 1738284770841975694947847)
      ·
        refine ⟨2607427156262963542421771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738284770841975694947847 2607427156262963542421771)
        ·
          refine ⟨3911140734394445313632657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607427156262963542421771 3911140734394445313632657)
          ·
            refine ⟨2933355550795833985224493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3911140734394445313632657 2933355550795833985224493)
            ·
              refine ⟨1100008331548437744459185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2933355550795833985224493 1100008331548437744459185)
              ·
                refine ⟨825006248661328308344389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100008331548437744459185 825006248661328308344389)
                ·
                  refine ⟨154688671623999057814573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 825006248661328308344389 154688671623999057814573)
                  ·
                    refine ⟨58008251858999646680465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 154688671623999057814573 58008251858999646680465)
                    ·
                      refine ⟨43506188894249735010349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58008251858999646680465 43506188894249735010349)
                      ·
                        rfl

theorem cell23_84728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_84728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84728 prefixEnd_84728 := by exact prefixLift 84728
  have htrace : WordTrace (prefixWord ++ tailWord_84728) baseStart_84728 baseEnd_84728 := by
    simpa [prefixWord, tailWord_84728, baseEnd_84728] using wordTrace_append hprefix tailTrace_84728
  have hstable : (prefixWord ++ tailWord_84728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84728).length < 2 ^ (prefixWord ++ tailWord_84728).sum := by decide
  have hdescent : baseEnd_84728 < baseStart_84728 := by decide
  rcases family_descends (prefixWord ++ tailWord_84728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84751 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 1, 6]
def baseStart_84751 : Nat := 118140960795 + 84751 * 2 ^ 59
def prefixEnd_84751 : Nat := 4983230072969 + 3 ^ 40 * 84751 * 2
def baseEnd_84751 : Nat := 14505999649767715007581

theorem tailTrace_84751 : CollatzResearch.WordTrace tailWord_84751 prefixEnd_84751 14505999649767715007581 := by
  unfold tailWord_84751
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091122915969076163550107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2060748610646050775700071 3091122915969076163550107)
  ·
    refine ⟨4636684373953614245325161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3091122915969076163550107 4636684373953614245325161)
    ·
      refine ⟨3477513280465210683993871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4636684373953614245325161 3477513280465210683993871)
      ·
        refine ⟨5216269920697816025990807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3477513280465210683993871 5216269920697816025990807)
        ·
          refine ⟨7824404881046724038986211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5216269920697816025990807 7824404881046724038986211)
          ·
            refine ⟨11736607321570086058479317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7824404881046724038986211 11736607321570086058479317)
            ·
              refine ⟨275076734099298891995609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11736607321570086058479317 275076734099298891995609)
              ·
                refine ⟨206307550574474168996707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275076734099298891995609 206307550574474168996707)
                ·
                  refine ⟨309461325861711253495061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206307550574474168996707 309461325861711253495061)
                  ·
                    refine ⟨14505999649767715007581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 309461325861711253495061 14505999649767715007581)
                    ·
                      rfl

theorem cell23_84751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_84751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84751 prefixEnd_84751 := by exact prefixLift 84751
  have htrace : WordTrace (prefixWord ++ tailWord_84751) baseStart_84751 baseEnd_84751 := by
    simpa [prefixWord, tailWord_84751, baseEnd_84751] using wordTrace_append hprefix tailTrace_84751
  have hstable : (prefixWord ++ tailWord_84751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84751).length < 2 ^ (prefixWord ++ tailWord_84751).sum := by decide
  have hdescent : baseEnd_84751 < baseStart_84751 := by decide
  rcases family_descends (prefixWord ++ tailWord_84751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84761 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 5]
def baseStart_84761 : Nat := 118140960795 + 84761 * 2 ^ 59
def prefixEnd_84761 : Nat := 4983230072969 + 3 ^ 40 * 84761 * 2
def baseEnd_84761 : Nat := 43523133755848105897697

theorem tailTrace_84761 : CollatzResearch.WordTrace tailWord_84761 prefixEnd_84761 43523133755848105897697 := by
  unfold tailWord_84761
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091487645932847871414137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2060991763955231914276091 3091487645932847871414137)
  ·
    refine ⟨2318615734449635903560603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3091487645932847871414137 2318615734449635903560603)
    ·
      refine ⟨3477923601674453855340905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318615734449635903560603 3477923601674453855340905)
      ·
        refine ⟨2608442701255840391505679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3477923601674453855340905 2608442701255840391505679)
        ·
          refine ⟨3912664051883760587258519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608442701255840391505679 3912664051883760587258519)
          ·
            refine ⟨5868996077825640880887779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912664051883760587258519 5868996077825640880887779)
            ·
              refine ⟨8803494116738461321331669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5868996077825640880887779 8803494116738461321331669)
              ·
                refine ⟨206331893361057687218711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8803494116738461321331669 206331893361057687218711)
                ·
                  refine ⟨309497840041586530828067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206331893361057687218711 309497840041586530828067)
                  ·
                    refine ⟨464246760062379796242101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 309497840041586530828067 464246760062379796242101)
                    ·
                      refine ⟨43523133755848105897697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 464246760062379796242101 43523133755848105897697)
                      ·
                        rfl

theorem cell23_84761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_84761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84761 prefixEnd_84761 := by exact prefixLift 84761
  have htrace : WordTrace (prefixWord ++ tailWord_84761) baseStart_84761 baseEnd_84761 := by
    simpa [prefixWord, tailWord_84761, baseEnd_84761] using wordTrace_append hprefix tailTrace_84761
  have hstable : (prefixWord ++ tailWord_84761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84761).length < 2 ^ (prefixWord ++ tailWord_84761).sum := by decide
  have hdescent : baseEnd_84761 < baseStart_84761 := by decide
  rcases family_descends (prefixWord ++ tailWord_84761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84771 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 4]
def baseStart_84771 : Nat := 118140960795 + 84771 * 2 ^ 59
def prefixEnd_84771 : Nat := 4983230072969 + 3 ^ 40 * 84771 * 2
def baseEnd_84771 : Nat := 43528268562393066772651

theorem tailTrace_84771 : CollatzResearch.WordTrace tailWord_84771 prefixEnd_84771 43528268562393066772651 := by
  unfold tailWord_84771
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091852375896619579278167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2061234917264413052852111 3091852375896619579278167)
  ·
    refine ⟨4637778563844929368917251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3091852375896619579278167 4637778563844929368917251)
    ·
      refine ⟨6956667845767394053375877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637778563844929368917251 6956667845767394053375877)
      ·
        refine ⟨1304375221081386385007977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6956667845767394053375877 1304375221081386385007977)
        ·
          refine ⟨978281415811039788755983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1304375221081386385007977 978281415811039788755983)
          ·
            refine ⟨1467422123716559683133975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978281415811039788755983 1467422123716559683133975)
            ·
              refine ⟨2201133185574839524700963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467422123716559683133975 2201133185574839524700963)
              ·
                refine ⟨3301699778362259287051445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201133185574839524700963 3301699778362259287051445)
                ·
                  refine ⟨309534354221461808161073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3301699778362259287051445 309534354221461808161073)
                  ·
                    refine ⟨232150765666096356120805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 309534354221461808161073 232150765666096356120805)
                    ·
                      refine ⟨43528268562393066772651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 232150765666096356120805 43528268562393066772651)
                      ·
                        rfl

theorem cell23_84771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_84771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84771 prefixEnd_84771 := by exact prefixLift 84771
  have htrace : WordTrace (prefixWord ++ tailWord_84771) baseStart_84771 baseEnd_84771 := by
    simpa [prefixWord, tailWord_84771, baseEnd_84771] using wordTrace_append hprefix tailTrace_84771
  have hstable : (prefixWord ++ tailWord_84771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84771).length < 2 ^ (prefixWord ++ tailWord_84771).sum := by decide
  have hdescent : baseEnd_84771 < baseStart_84771 := by decide
  rcases family_descends (prefixWord ++ tailWord_84771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84806 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_84806 : Nat := 118140960795 + 84806 * 2 ^ 59
def prefixEnd_84806 : Nat := 4983230072969 + 3 ^ 40 * 84806 * 2
def baseEnd_84806 : Nat := 14515413461766809944997

theorem tailTrace_84806 : CollatzResearch.WordTrace tailWord_84806 prefixEnd_84806 14515413461766809944997 := by
  unfold tailWord_84806
  simp only [CollatzResearch.WordTrace]
  refine ⟨96660279086556892400071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2062085953846547037868181 96660279086556892400071)
  ·
    refine ⟨144990418629835338600107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96660279086556892400071 144990418629835338600107)
    ·
      refine ⟨217485627944753007900161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144990418629835338600107 217485627944753007900161)
      ·
        refine ⟨163114220958564755925121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217485627944753007900161 163114220958564755925121)
        ·
          refine ⟨122335665718923566943841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163114220958564755925121 122335665718923566943841)
          ·
            refine ⟨91751749289192675207881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122335665718923566943841 91751749289192675207881)
            ·
              refine ⟨68813811966894506405911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91751749289192675207881 68813811966894506405911)
              ·
                refine ⟨103220717950341759608867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68813811966894506405911 103220717950341759608867)
                ·
                  refine ⟨154831076925512639413301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103220717950341759608867 154831076925512639413301)
                  ·
                    refine ⟨14515413461766809944997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 154831076925512639413301 14515413461766809944997)
                    ·
                      rfl

theorem cell23_84806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_84806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84806 prefixEnd_84806 := by exact prefixLift 84806
  have htrace : WordTrace (prefixWord ++ tailWord_84806) baseStart_84806 baseEnd_84806 := by
    simpa [prefixWord, tailWord_84806, baseEnd_84806] using wordTrace_append hprefix tailTrace_84806
  have hstable : (prefixWord ++ tailWord_84806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84806).length < 2 ^ (prefixWord ++ tailWord_84806).sum := by decide
  have hdescent : baseEnd_84806 < baseStart_84806 := by decide
  rcases family_descends (prefixWord ++ tailWord_84806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84808 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_84808 : Nat := 118140960795 + 84808 * 2 ^ 59
def prefixEnd_84808 : Nat := 4983230072969 + 3 ^ 40 * 84808 * 2
def baseEnd_84808 : Nat := 43547267346609422009981

theorem tailTrace_84808 : CollatzResearch.WordTrace tailWord_84808 prefixEnd_84808 43547267346609422009981 := by
  unfold tailWord_84808
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546600938381287449187539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2062134584508383265583385 1546600938381287449187539)
  ·
    refine ⟨2319901407571931173781309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1546600938381287449187539 2319901407571931173781309)
    ·
      refine ⟨869963027839474190167991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2319901407571931173781309 869963027839474190167991)
      ·
        refine ⟨1304944541759211285251987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869963027839474190167991 1304944541759211285251987)
        ·
          refine ⟨1957416812638816927877981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304944541759211285251987 1957416812638816927877981)
          ·
            refine ⟨734031304739556347954243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1957416812638816927877981 734031304739556347954243)
            ·
              refine ⟨1101046957109334521931365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734031304739556347954243 1101046957109334521931365)
              ·
                refine ⟨206446304458000222862131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1101046957109334521931365 206446304458000222862131)
                ·
                  refine ⟨309669456687000334293197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206446304458000222862131 309669456687000334293197)
                  ·
                    refine ⟨116126046257625125359949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 309669456687000334293197 116126046257625125359949)
                    ·
                      refine ⟨43547267346609422009981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116126046257625125359949 43547267346609422009981)
                      ·
                        rfl

theorem cell23_84808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_84808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84808 prefixEnd_84808 := by exact prefixLift 84808
  have htrace : WordTrace (prefixWord ++ tailWord_84808) baseStart_84808 baseEnd_84808 := by
    simpa [prefixWord, tailWord_84808, baseEnd_84808] using wordTrace_append hprefix tailTrace_84808
  have hstable : (prefixWord ++ tailWord_84808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84808).length < 2 ^ (prefixWord ++ tailWord_84808).sum := by decide
  have hdescent : baseEnd_84808 < baseStart_84808 := by decide
  rcases family_descends (prefixWord ++ tailWord_84808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84809 : List Nat := [1, 2, 1, 1, 2, 6, 2, 3, 1, 2, 2]
def baseStart_84809 : Nat := 118140960795 + 84809 * 2 ^ 59
def prefixEnd_84809 : Nat := 4983230072969 + 3 ^ 40 * 84809 * 2
def baseEnd_84809 : Nat := 43547780827263918097477

theorem tailTrace_84809 : CollatzResearch.WordTrace tailWord_84809 prefixEnd_84809 43547780827263918097477 := by
  unfold tailWord_84809
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093238349758952069161481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2062158899839301379440987 3093238349758952069161481)
  ·
    refine ⟨2319928762319214051871111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3093238349758952069161481 2319928762319214051871111)
    ·
      refine ⟨3479893143478821077806667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319928762319214051871111 3479893143478821077806667)
      ·
        refine ⟨5219839715218231616710001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479893143478821077806667 5219839715218231616710001)
        ·
          refine ⟨3914879786413673712532501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5219839715218231616710001 3914879786413673712532501)
          ·
            refine ⟨183509989988140955274961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3914879786413673712532501 183509989988140955274961)
            ·
              refine ⟨137632492491105716456221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183509989988140955274961 137632492491105716456221)
              ·
                refine ⟨51612184684164643671083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137632492491105716456221 51612184684164643671083)
                ·
                  refine ⟨77418277026246965506625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51612184684164643671083 77418277026246965506625)
                  ·
                    refine ⟨58063707769685224129969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77418277026246965506625 58063707769685224129969)
                    ·
                      refine ⟨43547780827263918097477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58063707769685224129969 43547780827263918097477)
                      ·
                        rfl

theorem cell23_84809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 1, 2, 2].length) (baseStart_84809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84809 prefixEnd_84809 := by exact prefixLift 84809
  have htrace : WordTrace (prefixWord ++ tailWord_84809) baseStart_84809 baseEnd_84809 := by
    simpa [prefixWord, tailWord_84809, baseEnd_84809] using wordTrace_append hprefix tailTrace_84809
  have hstable : (prefixWord ++ tailWord_84809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84809).length < 2 ^ (prefixWord ++ tailWord_84809).sum := by decide
  have hdescent : baseEnd_84809 < baseStart_84809 := by decide
  rcases family_descends (prefixWord ++ tailWord_84809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84812 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 1, 2, 3]
def baseStart_84812 : Nat := 118140960795 + 84812 * 2 ^ 59
def prefixEnd_84812 : Nat := 4983230072969 + 3 ^ 40 * 84812 * 2
def baseEnd_84812 : Nat := 43549321269227406359963

theorem tailTrace_84812 : CollatzResearch.WordTrace tailWord_84812 prefixEnd_84812 43549321269227406359963 := by
  unfold tailWord_84812
  simp only [CollatzResearch.WordTrace]
  refine ⟨1546673884374041790760345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2062231845832055721013793 1546673884374041790760345)
  ·
    refine ⟨1160005413280531343070259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1546673884374041790760345 1160005413280531343070259)
    ·
      refine ⟨1740008119920797014605389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1160005413280531343070259 1740008119920797014605389)
      ·
        refine ⟨652503044970298880477021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1740008119920797014605389 652503044970298880477021)
        ·
          refine ⟨244688641863862080178883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 652503044970298880477021 244688641863862080178883)
          ·
            refine ⟨367032962795793120268325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244688641863862080178883 367032962795793120268325)
            ·
              refine ⟨68818680524211210050311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 367032962795793120268325 68818680524211210050311)
              ·
                refine ⟨103228020786316815075467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68818680524211210050311 103228020786316815075467)
                ·
                  refine ⟨154842031179475222613201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103228020786316815075467 154842031179475222613201)
                  ·
                    refine ⟨116131523384606416959901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 154842031179475222613201 116131523384606416959901)
                    ·
                      refine ⟨43549321269227406359963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116131523384606416959901 43549321269227406359963)
                      ·
                        rfl

theorem cell23_84812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_84812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84812 prefixEnd_84812 := by exact prefixLift 84812
  have htrace : WordTrace (prefixWord ++ tailWord_84812) baseStart_84812 baseEnd_84812 := by
    simpa [prefixWord, tailWord_84812, baseEnd_84812] using wordTrace_append hprefix tailTrace_84812
  have hstable : (prefixWord ++ tailWord_84812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84812).length < 2 ^ (prefixWord ++ tailWord_84812).sum := by decide
  have hdescent : baseEnd_84812 < baseStart_84812 := by decide
  rcases family_descends (prefixWord ++ tailWord_84812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84825 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 4, 1, 3]
def baseStart_84825 : Nat := 118140960795 + 84825 * 2 ^ 59
def prefixEnd_84825 : Nat := 4983230072969 + 3 ^ 40 * 84825 * 2
def baseEnd_84825 : Nat := 43555996517735855497403

theorem tailTrace_84825 : CollatzResearch.WordTrace tailWord_84825 prefixEnd_84825 43555996517735855497403 := by
  unfold tailWord_84825
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093821917700986801743929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2062547945133991201162619 3093821917700986801743929)
  ·
    refine ⟨2320366438275740101307947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3093821917700986801743929 2320366438275740101307947)
    ·
      refine ⟨3480549657413610151961921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2320366438275740101307947 3480549657413610151961921)
      ·
        refine ⟨2610412243060207613971441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3480549657413610151961921 2610412243060207613971441)
        ·
          refine ⟨1957809182295155710478581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2610412243060207613971441 1957809182295155710478581)
          ·
            refine ⟨183544610840170847857367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1957809182295155710478581 183544610840170847857367)
            ·
              refine ⟨275316916260256271786051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183544610840170847857367 275316916260256271786051)
              ·
                refine ⟨412975374390384407679077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275316916260256271786051 412975374390384407679077)
                ·
                  refine ⟨77432882698197076439827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 412975374390384407679077 77432882698197076439827)
                  ·
                    refine ⟨116149324047295614659741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77432882698197076439827 116149324047295614659741)
                    ·
                      refine ⟨43555996517735855497403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116149324047295614659741 43555996517735855497403)
                      ·
                        rfl

theorem cell23_84825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_84825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84825 prefixEnd_84825 := by exact prefixLift 84825
  have htrace : WordTrace (prefixWord ++ tailWord_84825) baseStart_84825 baseEnd_84825 := by
    simpa [prefixWord, tailWord_84825, baseEnd_84825] using wordTrace_append hprefix tailTrace_84825
  have hstable : (prefixWord ++ tailWord_84825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84825).length < 2 ^ (prefixWord ++ tailWord_84825).sum := by decide
  have hdescent : baseEnd_84825 < baseStart_84825 := by decide
  rcases family_descends (prefixWord ++ tailWord_84825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84868 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_84868 : Nat := 118140960795 + 84868 * 2 ^ 59
def prefixEnd_84868 : Nat := 4983230072969 + 3 ^ 40 * 84868 * 2
def baseEnd_84868 : Nat := 43578076185879187259705

theorem tailTrace_84868 : CollatzResearch.WordTrace tailWord_84868 prefixEnd_84868 43578076185879187259705 := by
  unfold tailWord_84868
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547695128272602572779629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2063593504363470097039505 1547695128272602572779629)
  ·
    refine ⟨580385673102225964792361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1547695128272602572779629 580385673102225964792361)
    ·
      refine ⟨435289254826669473594271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 580385673102225964792361 435289254826669473594271)
      ·
        refine ⟨652933882240004210391407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435289254826669473594271 652933882240004210391407)
        ·
          refine ⟨979400823360006315587111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652933882240004210391407 979400823360006315587111)
          ·
            refine ⟨1469101235040009473380667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979400823360006315587111 1469101235040009473380667)
            ·
              refine ⟨2203651852560014210071001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469101235040009473380667 2203651852560014210071001)
              ·
                refine ⟨1652738889420010657553251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2203651852560014210071001 1652738889420010657553251)
                ·
                  refine ⟨2479108334130015986329877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652738889420010657553251 2479108334130015986329877)
                  ·
                    refine ⟨116208203162344499359213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2479108334130015986329877 116208203162344499359213)
                    ·
                      refine ⟨43578076185879187259705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116208203162344499359213 43578076185879187259705)
                      ·
                        rfl

theorem cell23_84868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_84868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84868 prefixEnd_84868 := by exact prefixLift 84868
  have htrace : WordTrace (prefixWord ++ tailWord_84868) baseStart_84868 baseEnd_84868 := by
    simpa [prefixWord, tailWord_84868, baseEnd_84868] using wordTrace_append hprefix tailTrace_84868
  have hstable : (prefixWord ++ tailWord_84868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84868).length < 2 ^ (prefixWord ++ tailWord_84868).sum := by decide
  have hdescent : baseEnd_84868 < baseStart_84868 := by decide
  rcases family_descends (prefixWord ++ tailWord_84868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84881 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 9]
def baseStart_84881 : Nat := 118140960795 + 84881 * 2 ^ 59
def prefixEnd_84881 : Nat := 4983230072969 + 3 ^ 40 * 84881 * 2
def baseEnd_84881 : Nat := 43584751434387636397145

theorem tailTrace_84881 : CollatzResearch.WordTrace tailWord_84881 prefixEnd_84881 43584751434387636397145 := by
  unfold tailWord_84881
  simp only [CollatzResearch.WordTrace]
  refine ⟨3095864405498108365782497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2063909603665405577188331 3095864405498108365782497)
  ·
    refine ⟨2321898304123581274336873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3095864405498108365782497 2321898304123581274336873)
    ·
      refine ⟨1741423728092685955752655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2321898304123581274336873 1741423728092685955752655)
      ·
        refine ⟨2612135592139028933628983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1741423728092685955752655 2612135592139028933628983)
        ·
          refine ⟨3918203388208543400443475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2612135592139028933628983 3918203388208543400443475)
          ·
            refine ⟨5877305082312815100665213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918203388208543400443475 5877305082312815100665213)
            ·
              refine ⟨2203989405867305662749455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5877305082312815100665213 2203989405867305662749455)
              ·
                refine ⟨3305984108800958494124183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203989405867305662749455 3305984108800958494124183)
                ·
                  refine ⟨4958976163201437741186275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305984108800958494124183 4958976163201437741186275)
                  ·
                    refine ⟨7438464244802156611779413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4958976163201437741186275 7438464244802156611779413)
                    ·
                      refine ⟨43584751434387636397145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 7438464244802156611779413 43584751434387636397145)
                      ·
                        rfl

theorem cell23_84881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_84881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84881 prefixEnd_84881 := by exact prefixLift 84881
  have htrace : WordTrace (prefixWord ++ tailWord_84881) baseStart_84881 baseEnd_84881 := by
    simpa [prefixWord, tailWord_84881, baseEnd_84881] using wordTrace_append hprefix tailTrace_84881
  have hstable : (prefixWord ++ tailWord_84881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84881).length < 2 ^ (prefixWord ++ tailWord_84881).sum := by decide
  have hdescent : baseEnd_84881 < baseStart_84881 := by decide
  rcases family_descends (prefixWord ++ tailWord_84881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84899 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 2, 2, 2]
def baseStart_84899 : Nat := 118140960795 + 84899 * 2 ^ 59
def prefixEnd_84899 : Nat := 4983230072969 + 3 ^ 40 * 84899 * 2
def baseEnd_84899 : Nat := 43593994086168565972063

theorem tailTrace_84899 : CollatzResearch.WordTrace tailWord_84899 prefixEnd_84899 43593994086168565972063 := by
  unfold tailWord_84899
  simp only [CollatzResearch.WordTrace]
  refine ⟨3096520919432897439937751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2064347279621931626625167 3096520919432897439937751)
  ·
    refine ⟨4644781379149346159906627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3096520919432897439937751 4644781379149346159906627)
    ·
      refine ⟨6967172068724019239859941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4644781379149346159906627 6967172068724019239859941)
      ·
        refine ⟨1306344762885753607473739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6967172068724019239859941 1306344762885753607473739)
        ·
          refine ⟨1959517144328630411210609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306344762885753607473739 1959517144328630411210609)
          ·
            refine ⟨1469637858246472808407957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1959517144328630411210609 1469637858246472808407957)
            ·
              refine ⟨68889274605303412894123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1469637858246472808407957 68889274605303412894123)
              ·
                refine ⟨103333911907955119341185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68889274605303412894123 103333911907955119341185)
                ·
                  refine ⟨77500433930966339505889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103333911907955119341185 77500433930966339505889)
                  ·
                    refine ⟨58125325448224754629417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77500433930966339505889 58125325448224754629417)
                    ·
                      refine ⟨43593994086168565972063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58125325448224754629417 43593994086168565972063)
                      ·
                        rfl

theorem cell23_84899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_84899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84899 prefixEnd_84899 := by exact prefixLift 84899
  have htrace : WordTrace (prefixWord ++ tailWord_84899) baseStart_84899 baseEnd_84899 := by
    simpa [prefixWord, tailWord_84899, baseEnd_84899] using wordTrace_append hprefix tailTrace_84899
  have hstable : (prefixWord ++ tailWord_84899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84899).length < 2 ^ (prefixWord ++ tailWord_84899).sum := by decide
  have hdescent : baseEnd_84899 < baseStart_84899 := by decide
  rcases family_descends (prefixWord ++ tailWord_84899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84928 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_84928 : Nat := 118140960795 + 84928 * 2 ^ 59
def prefixEnd_84928 : Nat := 4983230072969 + 3 ^ 40 * 84928 * 2
def baseEnd_84928 : Nat := 43608885025148952509429

theorem tailTrace_84928 : CollatzResearch.WordTrace tailWord_84928 prefixEnd_84928 43608885025148952509429 := by
  unfold tailWord_84928
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548789318163917696371719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2065052424218556928495625 1548789318163917696371719)
  ·
    refine ⟨2323183977245876544557579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1548789318163917696371719 2323183977245876544557579)
    ·
      refine ⟨3484775965868814816836369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2323183977245876544557579 3484775965868814816836369)
      ·
        refine ⟨2613581974401611112627277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3484775965868814816836369 2613581974401611112627277)
        ·
          refine ⟨980093240400604167235229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2613581974401611112627277 980093240400604167235229)
          ·
            refine ⟨367534965150226562713211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 980093240400604167235229 367534965150226562713211)
            ·
              refine ⟨551302447725339844069817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367534965150226562713211 551302447725339844069817)
              ·
                refine ⟨413476835794004883052363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 551302447725339844069817 413476835794004883052363)
                ·
                  refine ⟨620215253691007324578545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413476835794004883052363 620215253691007324578545)
                  ·
                    refine ⟨465161440268255493433909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 620215253691007324578545 465161440268255493433909)
                    ·
                      refine ⟨43608885025148952509429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 465161440268255493433909 43608885025148952509429)
                      ·
                        rfl

theorem cell23_84928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_84928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84928 prefixEnd_84928 := by exact prefixLift 84928
  have htrace : WordTrace (prefixWord ++ tailWord_84928) baseStart_84928 baseEnd_84928 := by
    simpa [prefixWord, tailWord_84928, baseEnd_84928] using wordTrace_append hprefix tailTrace_84928
  have hstable : (prefixWord ++ tailWord_84928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84928).length < 2 ^ (prefixWord ++ tailWord_84928).sum := by decide
  have hdescent : baseEnd_84928 < baseStart_84928 := by decide
  rcases family_descends (prefixWord ++ tailWord_84928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84938 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_84938 : Nat := 118140960795 + 84938 * 2 ^ 59
def prefixEnd_84938 : Nat := 4983230072969 + 3 ^ 40 * 84938 * 2
def baseEnd_84938 : Nat := 43614019831693913384383

theorem tailTrace_84938 : CollatzResearch.WordTrace tailWord_84938 prefixEnd_84938 43614019831693913384383 := by
  unfold tailWord_84938
  simp only [CollatzResearch.WordTrace]
  refine ⟨774485841572901775151867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2065295577527738067071645 774485841572901775151867)
  ·
    refine ⟨1161728762359352662727801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 774485841572901775151867 1161728762359352662727801)
    ·
      refine ⟨871296571769514497045851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1161728762359352662727801 871296571769514497045851)
      ·
        refine ⟨1306944857654271745568777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871296571769514497045851 1306944857654271745568777)
        ·
          refine ⟨980208643240703809176583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1306944857654271745568777 980208643240703809176583)
          ·
            refine ⟨1470312964861055713764875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980208643240703809176583 1470312964861055713764875)
            ·
              refine ⟨2205469447291583570647313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470312964861055713764875 2205469447291583570647313)
              ·
                refine ⟨1654102085468687677985485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2205469447291583570647313 1654102085468687677985485)
                ·
                  refine ⟨620288282050757879244557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1654102085468687677985485 620288282050757879244557)
                  ·
                    refine ⟨232608105769034204716709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 620288282050757879244557 232608105769034204716709)
                    ·
                      refine ⟨43614019831693913384383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 232608105769034204716709 43614019831693913384383)
                      ·
                        rfl

theorem cell23_84938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_84938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84938 prefixEnd_84938 := by exact prefixLift 84938
  have htrace : WordTrace (prefixWord ++ tailWord_84938) baseStart_84938 baseEnd_84938 := by
    simpa [prefixWord, tailWord_84938, baseEnd_84938] using wordTrace_append hprefix tailTrace_84938
  have hstable : (prefixWord ++ tailWord_84938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84938).length < 2 ^ (prefixWord ++ tailWord_84938).sum := by decide
  have hdescent : baseEnd_84938 < baseStart_84938 := by decide
  rcases family_descends (prefixWord ++ tailWord_84938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84975 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 3]
def baseStart_84975 : Nat := 118140960795 + 84975 * 2 ^ 59
def prefixEnd_84975 : Nat := 4983230072969 + 3 ^ 40 * 84975 * 2
def baseEnd_84975 : Nat := 43633018615910268621713

theorem tailTrace_84975 : CollatzResearch.WordTrace tailWord_84975 prefixEnd_84975 43633018615910268621713 := by
  unfold tailWord_84975
  simp only [CollatzResearch.WordTrace]
  refine ⟨3099292867157562419704379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2066195244771708279802919 3099292867157562419704379)
  ·
    refine ⟨4648939300736343629556569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3099292867157562419704379 4648939300736343629556569)
    ·
      refine ⟨3486704475552257722167427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4648939300736343629556569 3486704475552257722167427)
      ·
        refine ⟨5230056713328386583251141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3486704475552257722167427 5230056713328386583251141)
        ·
          refine ⟨980635633749072484359589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5230056713328386583251141 980635633749072484359589)
          ·
            refine ⟨183869181327951090817423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 980635633749072484359589 183869181327951090817423)
            ·
              refine ⟨275803771991926636226135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183869181327951090817423 275803771991926636226135)
              ·
                refine ⟨413705657987889954339203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275803771991926636226135 413705657987889954339203)
                ·
                  refine ⟨620558486981834931508805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413705657987889954339203 620558486981834931508805)
                  ·
                    refine ⟨116354716309094049657901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 620558486981834931508805 116354716309094049657901)
                    ·
                      refine ⟨43633018615910268621713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116354716309094049657901 43633018615910268621713)
                      ·
                        rfl

theorem cell23_84975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 3].length) (baseStart_84975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_84975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_84975 prefixEnd_84975 := by exact prefixLift 84975
  have htrace : WordTrace (prefixWord ++ tailWord_84975) baseStart_84975 baseEnd_84975 := by
    simpa [prefixWord, tailWord_84975, baseEnd_84975] using wordTrace_append hprefix tailTrace_84975
  have hstable : (prefixWord ++ tailWord_84975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84975).length < 2 ^ (prefixWord ++ tailWord_84975).sum := by decide
  have hdescent : baseEnd_84975 < baseStart_84975 := by decide
  rcases family_descends (prefixWord ++ tailWord_84975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85045 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_85045 : Nat := 118140960795 + 85045 * 2 ^ 59
def prefixEnd_85045 : Nat := 4983230072969 + 3 ^ 40 * 85045 * 2
def baseEnd_85045 : Nat := 43668962261724994746391

theorem tailTrace_85045 : CollatzResearch.WordTrace tailWord_85045 prefixEnd_85045 43668962261724994746391 := by
  unfold tailWord_85045
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101845976903964374752589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2067897317935976249835059 3101845976903964374752589)
  ·
    refine ⟨1163192241338986640532221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3101845976903964374752589 1163192241338986640532221)
    ·
      refine ⟨436197090502119990199583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1163192241338986640532221 436197090502119990199583)
      ·
        refine ⟨654295635753179985299375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436197090502119990199583 654295635753179985299375)
        ·
          refine ⟨981443453629769977949063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654295635753179985299375 981443453629769977949063)
          ·
            refine ⟨1472165180444654966923595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981443453629769977949063 1472165180444654966923595)
            ·
              refine ⟨2208247770666982450385393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472165180444654966923595 2208247770666982450385393)
              ·
                refine ⟨1656185828000236837789045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2208247770666982450385393 1656185828000236837789045)
                ·
                  refine ⟨155267421375022203542723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1656185828000236837789045 155267421375022203542723)
                  ·
                    refine ⟨232901132062533305314085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 155267421375022203542723 232901132062533305314085)
                    ·
                      refine ⟨43668962261724994746391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 232901132062533305314085 43668962261724994746391)
                      ·
                        rfl

theorem cell23_85045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_85045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85045 prefixEnd_85045 := by exact prefixLift 85045
  have htrace : WordTrace (prefixWord ++ tailWord_85045) baseStart_85045 baseEnd_85045 := by
    simpa [prefixWord, tailWord_85045, baseEnd_85045] using wordTrace_append hprefix tailTrace_85045
  have hstable : (prefixWord ++ tailWord_85045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85045).length < 2 ^ (prefixWord ++ tailWord_85045).sum := by decide
  have hdescent : baseEnd_85045 < baseStart_85045 := by decide
  rcases family_descends (prefixWord ++ tailWord_85045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85049 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 2, 3, 2]
def baseStart_85049 : Nat := 118140960795 + 85049 * 2 ^ 59
def prefixEnd_85049 : Nat := 4983230072969 + 3 ^ 40 * 85049 * 2
def baseEnd_85049 : Nat := 43671016184342979096373

theorem tailTrace_85049 : CollatzResearch.WordTrace tailWord_85049 prefixEnd_85049 43671016184342979096373 := by
  unfold tailWord_85049
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101991868889473057898201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2067994579259648705265467 3101991868889473057898201)
  ·
    refine ⟨2326493901667104793423651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3101991868889473057898201 2326493901667104793423651)
    ·
      refine ⟨3489740852500657190135477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2326493901667104793423651 3489740852500657190135477)
      ·
        refine ⟨327163204921936611575201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3489740852500657190135477 327163204921936611575201)
        ·
          refine ⟨245372403691452458681401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327163204921936611575201 245372403691452458681401)
          ·
            refine ⟨184029302768589344011051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245372403691452458681401 184029302768589344011051)
            ·
              refine ⟨276043954152884016016577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184029302768589344011051 276043954152884016016577)
              ·
                refine ⟨207032965614663012012433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276043954152884016016577 207032965614663012012433)
                ·
                  refine ⟨155274724210997259009325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207032965614663012012433 155274724210997259009325)
                  ·
                    refine ⟨58228021579123972128497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155274724210997259009325 58228021579123972128497)
                    ·
                      refine ⟨43671016184342979096373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58228021579123972128497 43671016184342979096373)
                      ·
                        rfl

theorem cell23_85049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_85049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85049 prefixEnd_85049 := by exact prefixLift 85049
  have htrace : WordTrace (prefixWord ++ tailWord_85049) baseStart_85049 baseEnd_85049 := by
    simpa [prefixWord, tailWord_85049, baseEnd_85049] using wordTrace_append hprefix tailTrace_85049
  have hstable : (prefixWord ++ tailWord_85049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85049).length < 2 ^ (prefixWord ++ tailWord_85049).sum := by decide
  have hdescent : baseEnd_85049 < baseStart_85049 := by decide
  rcases family_descends (prefixWord ++ tailWord_85049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85056 : List Nat := [2, 1, 1, 2, 2, 3, 5, 2, 1, 1, 3]
def baseStart_85056 : Nat := 118140960795 + 85056 * 2 ^ 59
def prefixEnd_85056 : Nat := 4983230072969 + 3 ^ 40 * 85056 * 2
def baseEnd_85056 : Nat := 43674610548924451708841

theorem tailTrace_85056 : CollatzResearch.WordTrace tailWord_85056 prefixEnd_85056 43674610548924451708841 := by
  unfold tailWord_85056
  simp only [CollatzResearch.WordTrace]
  refine ⟨1551123589932056626701511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2068164786576075502268681 1551123589932056626701511)
  ·
    refine ⟨2326685384898084940052267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1551123589932056626701511 2326685384898084940052267)
    ·
      refine ⟨3490028077347127410078401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2326685384898084940052267 3490028077347127410078401)
      ·
        refine ⟨2617521058010345557558801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3490028077347127410078401 2617521058010345557558801)
        ·
          refine ⟨1963140793507759168169101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2617521058010345557558801 1963140793507759168169101)
          ·
            refine ⟨736177797565409688063413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1963140793507759168169101 736177797565409688063413)
            ·
              refine ⟨69016668521757158255945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 736177797565409688063413 69016668521757158255945)
              ·
                refine ⟨51762501391317868691959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69016668521757158255945 51762501391317868691959)
                ·
                  refine ⟨77643752086976803037939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51762501391317868691959 77643752086976803037939)
                  ·
                    refine ⟨116465628130465204556909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77643752086976803037939 116465628130465204556909)
                    ·
                      refine ⟨43674610548924451708841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116465628130465204556909 43674610548924451708841)
                      ·
                        rfl

theorem cell23_85056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 1, 1, 3].length) (baseStart_85056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85056 prefixEnd_85056 := by exact prefixLift 85056
  have htrace : WordTrace (prefixWord ++ tailWord_85056) baseStart_85056 baseEnd_85056 := by
    simpa [prefixWord, tailWord_85056, baseEnd_85056] using wordTrace_append hprefix tailTrace_85056
  have hstable : (prefixWord ++ tailWord_85056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85056).length < 2 ^ (prefixWord ++ tailWord_85056).sum := by decide
  have hdescent : baseEnd_85056 < baseStart_85056 := by decide
  rcases family_descends (prefixWord ++ tailWord_85056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85082 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3]
def baseStart_85082 : Nat := 118140960795 + 85082 * 2 ^ 59
def prefixEnd_85082 : Nat := 4983230072969 + 3 ^ 40 * 85082 * 2
def baseEnd_85082 : Nat := 43687961045941349983721

theorem tailTrace_85082 : CollatzResearch.WordTrace tailWord_85082 prefixEnd_85082 43687961045941349983721 := by
  unfold tailWord_85082
  simp only [CollatzResearch.WordTrace]
  refine ⟨775798869442479923462375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2068796985179946462566333 775798869442479923462375)
  ·
    refine ⟨1163698304163719885193563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 775798869442479923462375 1163698304163719885193563)
    ·
      refine ⟨1745547456245579827790345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1163698304163719885193563 1745547456245579827790345)
      ·
        refine ⟨1309160592184184870842759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1745547456245579827790345 1309160592184184870842759)
        ·
          refine ⟨1963740888276277306264139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309160592184184870842759 1963740888276277306264139)
          ·
            refine ⟨2945611332414415959396209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963740888276277306264139 2945611332414415959396209)
            ·
              refine ⟨2209208499310811969547157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2945611332414415959396209 2209208499310811969547157)
              ·
                refine ⟨103556648405194311072523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2209208499310811969547157 103556648405194311072523)
                ·
                  refine ⟨155334972607791466608785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103556648405194311072523 155334972607791466608785)
                  ·
                    refine ⟨116501229455843599956589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155334972607791466608785 116501229455843599956589)
                    ·
                      refine ⟨43687961045941349983721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116501229455843599956589 43687961045941349983721)
                      ·
                        rfl

theorem cell23_85082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 1, 2, 3].length) (baseStart_85082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85082 prefixEnd_85082 := by exact prefixLift 85082
  have htrace : WordTrace (prefixWord ++ tailWord_85082) baseStart_85082 baseEnd_85082 := by
    simpa [prefixWord, tailWord_85082, baseEnd_85082] using wordTrace_append hprefix tailTrace_85082
  have hstable : (prefixWord ++ tailWord_85082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85082).length < 2 ^ (prefixWord ++ tailWord_85082).sum := by decide
  have hdescent : baseEnd_85082 < baseStart_85082 := by decide
  rcases family_descends (prefixWord ++ tailWord_85082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85112 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 4, 1, 3]
def baseStart_85112 : Nat := 118140960795 + 85112 * 2 ^ 59
def prefixEnd_85112 : Nat := 4983230072969 + 3 ^ 40 * 85112 * 2
def baseEnd_85112 : Nat := 43703365465576232608583

theorem tailTrace_85112 : CollatzResearch.WordTrace tailWord_85112 prefixEnd_85112 43703365465576232608583 := by
  unfold tailWord_85112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1552144833830617408720795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2069526445107489878294393 1552144833830617408720795)
  ·
    refine ⟨2328217250745926113081193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1552144833830617408720795 2328217250745926113081193)
    ·
      refine ⟨1746162938059444584810895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2328217250745926113081193 1746162938059444584810895)
      ·
        refine ⟨2619244407089166877216343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746162938059444584810895 2619244407089166877216343)
        ·
          refine ⟨3928866610633750315824515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2619244407089166877216343 3928866610633750315824515)
          ·
            refine ⟨5893299915950625473736773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928866610633750315824515 5893299915950625473736773)
            ·
              refine ⟨1104993734240742276325645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5893299915950625473736773 1104993734240742276325645)
              ·
                refine ⟨414372650340278353622117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1104993734240742276325645 414372650340278353622117)
                ·
                  refine ⟨77694871938802191304147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414372650340278353622117 77694871938802191304147)
                  ·
                    refine ⟨116542307908203286956221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77694871938802191304147 116542307908203286956221)
                    ·
                      refine ⟨43703365465576232608583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116542307908203286956221 43703365465576232608583)
                      ·
                        rfl

theorem cell23_85112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_85112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85112 prefixEnd_85112 := by exact prefixLift 85112
  have htrace : WordTrace (prefixWord ++ tailWord_85112) baseStart_85112 baseEnd_85112 := by
    simpa [prefixWord, tailWord_85112, baseEnd_85112] using wordTrace_append hprefix tailTrace_85112
  have hstable : (prefixWord ++ tailWord_85112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85112).length < 2 ^ (prefixWord ++ tailWord_85112).sum := by decide
  have hdescent : baseEnd_85112 < baseStart_85112 := by decide
  rcases family_descends (prefixWord ++ tailWord_85112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85113 : List Nat := [1, 2, 1, 3, 5, 1, 1, 4, 1, 2, 2]
def baseStart_85113 : Nat := 118140960795 + 85113 * 2 ^ 59
def prefixEnd_85113 : Nat := 4983230072969 + 3 ^ 40 * 85113 * 2
def baseEnd_85113 : Nat := 43703878946230728696079

theorem tailTrace_85113 : CollatzResearch.WordTrace tailWord_85113 prefixEnd_85113 43703878946230728696079 := by
  unfold tailWord_85113
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104326140657611988227993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2069550760438407992151995 3104326140657611988227993)
  ·
    refine ⟨2328244605493208991170995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3104326140657611988227993 2328244605493208991170995)
    ·
      refine ⟨3492366908239813486756493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2328244605493208991170995 3492366908239813486756493)
      ·
        refine ⟨1309637590589930057533685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3492366908239813486756493 1309637590589930057533685)
        ·
          refine ⟨122778524117805942893783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1309637590589930057533685 122778524117805942893783)
          ·
            refine ⟨184167786176708914340675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122778524117805942893783 184167786176708914340675)
            ·
              refine ⟨276251679265063371511013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184167786176708914340675 276251679265063371511013)
              ·
                refine ⟨51797189862199382158315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276251679265063371511013 51797189862199382158315)
                ·
                  refine ⟨77695784793299073237473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51797189862199382158315 77695784793299073237473)
                  ·
                    refine ⟨58271838594974304928105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77695784793299073237473 58271838594974304928105)
                    ·
                      refine ⟨43703878946230728696079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58271838594974304928105 43703878946230728696079)
                      ·
                        rfl

theorem cell23_85113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_85113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85113 prefixEnd_85113 := by exact prefixLift 85113
  have htrace : WordTrace (prefixWord ++ tailWord_85113) baseStart_85113 baseEnd_85113 := by
    simpa [prefixWord, tailWord_85113, baseEnd_85113] using wordTrace_append hprefix tailTrace_85113
  have hstable : (prefixWord ++ tailWord_85113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85113).length < 2 ^ (prefixWord ++ tailWord_85113).sum := by decide
  have hdescent : baseEnd_85113 < baseStart_85113 := by decide
  rcases family_descends (prefixWord ++ tailWord_85113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85129 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 2, 1, 3]
def baseStart_85129 : Nat := 118140960795 + 85129 * 2 ^ 59
def prefixEnd_85129 : Nat := 4983230072969 + 3 ^ 40 * 85129 * 2
def baseEnd_85129 : Nat := 43712094636702666096005

theorem tailTrace_85129 : CollatzResearch.WordTrace tailWord_85129 prefixEnd_85129 43712094636702666096005 := by
  unfold tailWord_85129
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104909708599646720810441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2069939805733097813873627 3104909708599646720810441)
  ·
    refine ⟨2328682281449735040607831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3104909708599646720810441 2328682281449735040607831)
    ·
      refine ⟨3493023422174602560911747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2328682281449735040607831 3493023422174602560911747)
      ·
        refine ⟨5239535133261903841367621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3493023422174602560911747 5239535133261903841367621)
        ·
          refine ⟨982412837486606970256429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5239535133261903841367621 982412837486606970256429)
          ·
            refine ⟨368404814057477613846161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 982412837486606970256429 368404814057477613846161)
            ·
              refine ⟨276303610543108210384621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368404814057477613846161 276303610543108210384621)
              ·
                refine ⟨103613853953665578894233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276303610543108210384621 103613853953665578894233)
                ·
                  refine ⟨77710390465249184170675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103613853953665578894233 77710390465249184170675)
                  ·
                    refine ⟨116565585697873776256013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77710390465249184170675 116565585697873776256013)
                    ·
                      refine ⟨43712094636702666096005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116565585697873776256013 43712094636702666096005)
                      ·
                        rfl

theorem cell23_85129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 1, 3].length) (baseStart_85129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85129 prefixEnd_85129 := by exact prefixLift 85129
  have htrace : WordTrace (prefixWord ++ tailWord_85129) baseStart_85129 baseEnd_85129 := by
    simpa [prefixWord, tailWord_85129, baseEnd_85129] using wordTrace_append hprefix tailTrace_85129
  have hstable : (prefixWord ++ tailWord_85129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85129).length < 2 ^ (prefixWord ++ tailWord_85129).sum := by decide
  have hdescent : baseEnd_85129 < baseStart_85129 := by decide
  rcases family_descends (prefixWord ++ tailWord_85129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85155 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 5]
def baseStart_85155 : Nat := 118140960795 + 85155 * 2 ^ 59
def prefixEnd_85155 : Nat := 4983230072969 + 3 ^ 40 * 85155 * 2
def baseEnd_85155 : Nat := 43725445133719564370885

theorem tailTrace_85155 : CollatzResearch.WordTrace tailWord_85155 prefixEnd_85155 43725445133719564370885 := by
  unfold tailWord_85155
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105858006505453161256919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2070572004336968774171279 3105858006505453161256919)
  ·
    refine ⟨4658787009758179741885379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3105858006505453161256919 4658787009758179741885379)
    ·
      refine ⟨6988180514637269612828069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4658787009758179741885379 6988180514637269612828069)
      ·
        refine ⟨1310283846494488052405263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6988180514637269612828069 1310283846494488052405263)
        ·
          refine ⟨1965425769741732078607895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310283846494488052405263 1965425769741732078607895)
          ·
            refine ⟨2948138654612598117911843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965425769741732078607895 2948138654612598117911843)
            ·
              refine ⟨4422207981918897176867765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2948138654612598117911843 4422207981918897176867765)
              ·
                refine ⟨414581998304896610331353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4422207981918897176867765 414581998304896610331353)
                ·
                  refine ⟨310936498728672457748515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414581998304896610331353 310936498728672457748515)
                  ·
                    refine ⟨466404748093008686622773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 310936498728672457748515 466404748093008686622773)
                    ·
                      refine ⟨43725445133719564370885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 466404748093008686622773 43725445133719564370885)
                      ·
                        rfl

theorem cell23_85155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_85155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85155 prefixEnd_85155 := by exact prefixLift 85155
  have htrace : WordTrace (prefixWord ++ tailWord_85155) baseStart_85155 baseEnd_85155 := by
    simpa [prefixWord, tailWord_85155, baseEnd_85155] using wordTrace_append hprefix tailTrace_85155
  have hstable : (prefixWord ++ tailWord_85155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85155).length < 2 ^ (prefixWord ++ tailWord_85155).sum := by decide
  have hdescent : baseEnd_85155 < baseStart_85155 := by decide
  rcases family_descends (prefixWord ++ tailWord_85155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85156 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 1, 3, 2]
def baseStart_85156 : Nat := 118140960795 + 85156 * 2 ^ 59
def prefixEnd_85156 : Nat := 4983230072969 + 3 ^ 40 * 85156 * 2
def baseEnd_85156 : Nat := 43725958614374060458381

theorem tailTrace_85156 : CollatzResearch.WordTrace tailWord_85156 prefixEnd_85156 43725958614374060458381 := by
  unfold tailWord_85156
  simp only [CollatzResearch.WordTrace]
  refine ⟨1552947239750915166021661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2070596319667886888028881 1552947239750915166021661)
  ·
    refine ⟨582355214906593187258123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1552947239750915166021661 582355214906593187258123)
    ·
      refine ⟨873532822359889780887185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582355214906593187258123 873532822359889780887185)
      ·
        refine ⟨655149616769917335665389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 873532822359889780887185 655149616769917335665389)
        ·
          refine ⟨245681106288719000874521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 655149616769917335665389 245681106288719000874521)
          ·
            refine ⟨184260829716539250655891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245681106288719000874521 184260829716539250655891)
            ·
              refine ⟨276391244574808875983837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184260829716539250655891 276391244574808875983837)
              ·
                refine ⟨103646716715553328493939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276391244574808875983837 103646716715553328493939)
                ·
                  refine ⟨155470075073329992740909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103646716715553328493939 155470075073329992740909)
                  ·
                    refine ⟨58301278152498747277841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 155470075073329992740909 58301278152498747277841)
                    ·
                      refine ⟨43725958614374060458381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58301278152498747277841 43725958614374060458381)
                      ·
                        rfl

theorem cell23_85156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_85156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85156 prefixEnd_85156 := by exact prefixLift 85156
  have htrace : WordTrace (prefixWord ++ tailWord_85156) baseStart_85156 baseEnd_85156 := by
    simpa [prefixWord, tailWord_85156, baseEnd_85156] using wordTrace_append hprefix tailTrace_85156
  have hstable : (prefixWord ++ tailWord_85156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85156).length < 2 ^ (prefixWord ++ tailWord_85156).sum := by decide
  have hdescent : baseEnd_85156 < baseStart_85156 := by decide
  rcases family_descends (prefixWord ++ tailWord_85156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85206 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_85206 : Nat := 118140960795 + 85206 * 2 ^ 59
def prefixEnd_85206 : Nat := 4983230072969 + 3 ^ 40 * 85206 * 2
def baseEnd_85206 : Nat := 43751632647098864833151

theorem tailTrace_85206 : CollatzResearch.WordTrace tailWord_85206 prefixEnd_85206 43751632647098864833151 := by
  unfold tailWord_85206
  simp only [CollatzResearch.WordTrace]
  refine ⟨194232383082543054460217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2071812086213792580908981 194232383082543054460217)
  ·
    refine ⟨145674287311907290845163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194232383082543054460217 145674287311907290845163)
    ·
      refine ⟨218511430967860936267745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145674287311907290845163 218511430967860936267745)
      ·
        refine ⟨163883573225895702200809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218511430967860936267745 163883573225895702200809)
        ·
          refine ⟨122912679919421776650607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163883573225895702200809 122912679919421776650607)
          ·
            refine ⟨184369019879132664975911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122912679919421776650607 184369019879132664975911)
            ·
              refine ⟨276553529818698997463867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184369019879132664975911 276553529818698997463867)
              ·
                refine ⟨414830294728048496195801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276553529818698997463867 414830294728048496195801)
                ·
                  refine ⟨311122721046036372146851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 414830294728048496195801 311122721046036372146851)
                  ·
                    refine ⟨466684081569054558220277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 311122721046036372146851 466684081569054558220277)
                    ·
                      refine ⟨43751632647098864833151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 466684081569054558220277 43751632647098864833151)
                      ·
                        rfl

theorem cell23_85206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_85206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85206 prefixEnd_85206 := by exact prefixLift 85206
  have htrace : WordTrace (prefixWord ++ tailWord_85206) baseStart_85206 baseEnd_85206 := by
    simpa [prefixWord, tailWord_85206, baseEnd_85206] using wordTrace_append hprefix tailTrace_85206
  have hstable : (prefixWord ++ tailWord_85206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85206).length < 2 ^ (prefixWord ++ tailWord_85206).sum := by decide
  have hdescent : baseEnd_85206 < baseStart_85206 := by decide
  rcases family_descends (prefixWord ++ tailWord_85206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85226 : List Nat := [3, 1, 3, 1, 1, 4, 3, 2, 5]
def baseStart_85226 : Nat := 118140960795 + 85226 * 2 ^ 59
def prefixEnd_85226 : Nat := 4983230072969 + 3 ^ 40 * 85226 * 2
def baseEnd_85226 : Nat := 4862433584465420731451

theorem tailTrace_85226 : CollatzResearch.WordTrace tailWord_85226 prefixEnd_85226 4862433584465420731451 := by
  unfold tailWord_85226
  simp only [CollatzResearch.WordTrace]
  refine ⟨777111897312058071772883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2072298392832154858061021 777111897312058071772883)
  ·
    refine ⟨1165667845968087107659325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 777111897312058071772883 1165667845968087107659325)
    ·
      refine ⟨437125442238032665372247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1165667845968087107659325 437125442238032665372247)
      ·
        refine ⟨655688163357048998058371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437125442238032665372247 655688163357048998058371)
        ·
          refine ⟨983532245035573497087557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655688163357048998058371 983532245035573497087557)
          ·
            refine ⟨184412295944170030703917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 983532245035573497087557 184412295944170030703917)
            ·
              refine ⟨69154610979063761513969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184412295944170030703917 69154610979063761513969)
              ·
                refine ⟨51865958234297821135477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69154610979063761513969 51865958234297821135477)
                ·
                  refine ⟨4862433584465420731451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51865958234297821135477 4862433584465420731451)
                  ·
                    rfl

theorem cell23_85226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_85226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85226 prefixEnd_85226 := by exact prefixLift 85226
  have htrace : WordTrace (prefixWord ++ tailWord_85226) baseStart_85226 baseEnd_85226 := by
    simpa [prefixWord, tailWord_85226, baseEnd_85226] using wordTrace_append hprefix tailTrace_85226
  have hstable : (prefixWord ++ tailWord_85226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85226).length < 2 ^ (prefixWord ++ tailWord_85226).sum := by decide
  have hdescent : baseEnd_85226 < baseStart_85226 := by decide
  rcases family_descends (prefixWord ++ tailWord_85226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85242 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4]
def baseStart_85242 : Nat := 118140960795 + 85242 * 2 ^ 59
def prefixEnd_85242 : Nat := 4983230072969 + 3 ^ 40 * 85242 * 2
def baseEnd_85242 : Nat := 43770117950660723982985

theorem tailTrace_85242 : CollatzResearch.WordTrace tailWord_85242 prefixEnd_85242 43770117950660723982985 := by
  unfold tailWord_85242
  simp only [CollatzResearch.WordTrace]
  refine ⟨777257789297566754918495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2072687438126844679782653 777257789297566754918495)
  ·
    refine ⟨1165886683946350132377743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 777257789297566754918495 1165886683946350132377743)
    ·
      refine ⟨1748830025919525198566615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1165886683946350132377743 1748830025919525198566615)
      ·
        refine ⟨2623245038879287797849923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1748830025919525198566615 2623245038879287797849923)
        ·
          refine ⟨3934867558318931696774885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2623245038879287797849923 3934867558318931696774885)
          ·
            refine ⟨737787667184799693145291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3934867558318931696774885 737787667184799693145291)
            ·
              refine ⟨1106681500777199539717937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737787667184799693145291 1106681500777199539717937)
              ·
                refine ⟨830011125582899654788453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106681500777199539717937 830011125582899654788453)
                ·
                  refine ⟨155627086046793685272835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 830011125582899654788453 155627086046793685272835)
                  ·
                    refine ⟨233440629070190527909253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 155627086046793685272835 233440629070190527909253)
                    ·
                      refine ⟨43770117950660723982985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 233440629070190527909253 43770117950660723982985)
                      ·
                        rfl

theorem cell23_85242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 1, 4].length) (baseStart_85242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85242 prefixEnd_85242 := by exact prefixLift 85242
  have htrace : WordTrace (prefixWord ++ tailWord_85242) baseStart_85242 baseEnd_85242 := by
    simpa [prefixWord, tailWord_85242, baseEnd_85242] using wordTrace_append hprefix tailTrace_85242
  have hstable : (prefixWord ++ tailWord_85242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85242).length < 2 ^ (prefixWord ++ tailWord_85242).sum := by decide
  have hdescent : baseEnd_85242 < baseStart_85242 := by decide
  rcases family_descends (prefixWord ++ tailWord_85242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85259 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 4]
def baseStart_85259 : Nat := 118140960795 + 85259 * 2 ^ 59
def prefixEnd_85259 : Nat := 4983230072969 + 3 ^ 40 * 85259 * 2
def baseEnd_85259 : Nat := 43778847121787157470407

theorem tailTrace_85259 : CollatzResearch.WordTrace tailWord_85259 prefixEnd_85259 43778847121787157470407 := by
  unfold tailWord_85259
  simp only [CollatzResearch.WordTrace]
  refine ⟨3109651198128678923042831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2073100798752452615361887 3109651198128678923042831)
  ·
    refine ⟨4664476797193018384564247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3109651198128678923042831 4664476797193018384564247)
    ·
      refine ⟨6996715195789527576846371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4664476797193018384564247 6996715195789527576846371)
      ·
        refine ⟨10495072793684291365269557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6996715195789527576846371 10495072793684291365269557)
        ·
          refine ⟨983913074407902315494021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10495072793684291365269557 983913074407902315494021)
          ·
            refine ⟨184483701451481684155129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 983913074407902315494021 184483701451481684155129)
            ·
              refine ⟨138362776088611263116347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184483701451481684155129 138362776088611263116347)
              ·
                refine ⟨207544164132916894674521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138362776088611263116347 207544164132916894674521)
                ·
                  refine ⟨155658123099687671005891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207544164132916894674521 155658123099687671005891)
                  ·
                    refine ⟨233487184649531506508837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 155658123099687671005891 233487184649531506508837)
                    ·
                      refine ⟨43778847121787157470407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 233487184649531506508837 43778847121787157470407)
                      ·
                        rfl

theorem cell23_85259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 4].length) (baseStart_85259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85259 prefixEnd_85259 := by exact prefixLift 85259
  have htrace : WordTrace (prefixWord ++ tailWord_85259) baseStart_85259 baseEnd_85259 := by
    simpa [prefixWord, tailWord_85259, baseEnd_85259] using wordTrace_append hprefix tailTrace_85259
  have hstable : (prefixWord ++ tailWord_85259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85259).length < 2 ^ (prefixWord ++ tailWord_85259).sum := by decide
  have hdescent : baseEnd_85259 < baseStart_85259 := by decide
  rcases family_descends (prefixWord ++ tailWord_85259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85292 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 3]
def baseStart_85292 : Nat := 118140960795 + 85292 * 2 ^ 59
def prefixEnd_85292 : Nat := 4983230072969 + 3 ^ 40 * 85292 * 2
def baseEnd_85292 : Nat := 43795791983385528357755

theorem tailTrace_85292 : CollatzResearch.WordTrace tailWord_85292 prefixEnd_85292 43795791983385528357755 := by
  unfold tailWord_85292
  simp only [CollatzResearch.WordTrace]
  refine ⟨1555427403504562779497065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2073903204672750372662753 1555427403504562779497065)
  ·
    refine ⟨1166570552628422084622799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1555427403504562779497065 1166570552628422084622799)
    ·
      refine ⟨1749855828942633126934199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166570552628422084622799 1749855828942633126934199)
      ·
        refine ⟨2624783743413949690401299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749855828942633126934199 2624783743413949690401299)
        ·
          refine ⟨3937175615120924535601949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624783743413949690401299 3937175615120924535601949)
          ·
            refine ⟨1476440855670346700850731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3937175615120924535601949 1476440855670346700850731)
            ·
              refine ⟨2214661283505520051276097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476440855670346700850731 2214661283505520051276097)
              ·
                refine ⟨1660995962629140038457073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214661283505520051276097 1660995962629140038457073)
                ·
                  refine ⟨1245746971971855028842805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1660995962629140038457073 1245746971971855028842805)
                  ·
                    refine ⟨116788778622361408954013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1245746971971855028842805 116788778622361408954013)
                    ·
                      refine ⟨43795791983385528357755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116788778622361408954013 43795791983385528357755)
                      ·
                        rfl

theorem cell23_85292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_85292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85292 prefixEnd_85292 := by exact prefixLift 85292
  have htrace : WordTrace (prefixWord ++ tailWord_85292) baseStart_85292 baseEnd_85292 := by
    simpa [prefixWord, tailWord_85292, baseEnd_85292] using wordTrace_append hprefix tailTrace_85292
  have hstable : (prefixWord ++ tailWord_85292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85292).length < 2 ^ (prefixWord ++ tailWord_85292).sum := by decide
  have hdescent : baseEnd_85292 < baseStart_85292 := by decide
  rcases family_descends (prefixWord ++ tailWord_85292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85293 : List Nat := [1, 5, 3, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_85293 : Nat := 118140960795 + 85293 * 2 ^ 59
def prefixEnd_85293 : Nat := 4983230072969 + 3 ^ 40 * 85293 * 2
def baseEnd_85293 : Nat := 43796305464040024445251

theorem tailTrace_85293 : CollatzResearch.WordTrace tailWord_85293 prefixEnd_85293 43796305464040024445251 := by
  unfold tailWord_85293
  simp only [CollatzResearch.WordTrace]
  refine ⟨3110891280005502729780533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2073927520003668486520355 3110891280005502729780533)
  ·
    refine ⟨291646057500515880916925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3110891280005502729780533 291646057500515880916925)
    ·
      refine ⟨109367271562693455343847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291646057500515880916925 109367271562693455343847)
      ·
        refine ⟨164050907344040183015771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109367271562693455343847 164050907344040183015771)
        ·
          refine ⟨246076361016060274523657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164050907344040183015771 246076361016060274523657)
          ·
            refine ⟨184557270762045205892743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246076361016060274523657 184557270762045205892743)
            ·
              refine ⟨276835906143067808839115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184557270762045205892743 276835906143067808839115)
              ·
                refine ⟨415253859214601713258673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276835906143067808839115 415253859214601713258673)
                ·
                  refine ⟨311440394410951284944005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 415253859214601713258673 311440394410951284944005)
                  ·
                    refine ⟨58395073952053365927001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 311440394410951284944005 58395073952053365927001)
                    ·
                      refine ⟨43796305464040024445251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58395073952053365927001 43796305464040024445251)
                      ·
                        rfl

theorem cell23_85293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_85293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85293 prefixEnd_85293 := by exact prefixLift 85293
  have htrace : WordTrace (prefixWord ++ tailWord_85293) baseStart_85293 baseEnd_85293 := by
    simpa [prefixWord, tailWord_85293, baseEnd_85293] using wordTrace_append hprefix tailTrace_85293
  have hstable : (prefixWord ++ tailWord_85293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85293).length < 2 ^ (prefixWord ++ tailWord_85293).sum := by decide
  have hdescent : baseEnd_85293 < baseStart_85293 := by decide
  rcases family_descends (prefixWord ++ tailWord_85293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85312 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 3, 5]
def baseStart_85312 : Nat := 118140960795 + 85312 * 2 ^ 59
def prefixEnd_85312 : Nat := 4983230072969 + 3 ^ 40 * 85312 * 2
def baseEnd_85312 : Nat := 14602020532158483369221

theorem tailTrace_85312 : CollatzResearch.WordTrace tailWord_85312 prefixEnd_85312 14602020532158483369221 := by
  unfold tailWord_85312
  simp only [CollatzResearch.WordTrace]
  refine ⟨1555792133468334487361095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2074389511291112649814793 1555792133468334487361095)
  ·
    refine ⟨2333688200202501731041643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1555792133468334487361095 2333688200202501731041643)
    ·
      refine ⟨3500532300303752596562465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2333688200202501731041643 3500532300303752596562465)
      ·
        refine ⟨2625399225227814447421849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3500532300303752596562465 2625399225227814447421849)
        ·
          refine ⟨1969049418920860835566387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2625399225227814447421849 1969049418920860835566387)
          ·
            refine ⟨2953574128381291253349581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969049418920860835566387 2953574128381291253349581)
            ·
              refine ⟨1107590298142984220006093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2953574128381291253349581 1107590298142984220006093)
              ·
                refine ⟨415346361803619082502285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1107590298142984220006093 415346361803619082502285)
                ·
                  refine ⟨155754885676357155938357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415346361803619082502285 155754885676357155938357)
                  ·
                    refine ⟨14602020532158483369221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 155754885676357155938357 14602020532158483369221)
                    ·
                      rfl

theorem cell23_85312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_85312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85312 prefixEnd_85312 := by exact prefixLift 85312
  have htrace : WordTrace (prefixWord ++ tailWord_85312) baseStart_85312 baseEnd_85312 := by
    simpa [prefixWord, tailWord_85312, baseEnd_85312] using wordTrace_append hprefix tailTrace_85312
  have hstable : (prefixWord ++ tailWord_85312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85312).length < 2 ^ (prefixWord ++ tailWord_85312).sum := by decide
  have hdescent : baseEnd_85312 < baseStart_85312 := by decide
  rcases family_descends (prefixWord ++ tailWord_85312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85313 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_85313 : Nat := 118140960795 + 85313 * 2 ^ 59
def prefixEnd_85313 : Nat := 4983230072969 + 3 ^ 40 * 85313 * 2
def baseEnd_85313 : Nat := 43806575077129946195159

theorem tailTrace_85313 : CollatzResearch.WordTrace tailWord_85313 prefixEnd_85313 43806575077129946195159 := by
  unfold tailWord_85313
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111620739933046145508593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2074413826622030763672395 3111620739933046145508593)
  ·
    refine ⟨2333715554949784609131445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3111620739933046145508593 2333715554949784609131445)
    ·
      refine ⟨218785833276542307106073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2333715554949784609131445 218785833276542307106073)
      ·
        refine ⟨164089374957406730329555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218785833276542307106073 164089374957406730329555)
        ·
          refine ⟨246134062436110095494333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164089374957406730329555 246134062436110095494333)
          ·
            refine ⟨92300273413541285810375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246134062436110095494333 92300273413541285810375)
            ·
              refine ⟨138450410120311928715563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92300273413541285810375 138450410120311928715563)
              ·
                refine ⟨207675615180467893073345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138450410120311928715563 207675615180467893073345)
                ·
                  refine ⟨155756711385350919805009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207675615180467893073345 155756711385350919805009)
                  ·
                    refine ⟨116817533539013189853757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155756711385350919805009 116817533539013189853757)
                    ·
                      refine ⟨43806575077129946195159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116817533539013189853757 43806575077129946195159)
                      ·
                        rfl

theorem cell23_85313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_85313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85313 prefixEnd_85313 := by exact prefixLift 85313
  have htrace : WordTrace (prefixWord ++ tailWord_85313) baseStart_85313 baseEnd_85313 := by
    simpa [prefixWord, tailWord_85313, baseEnd_85313] using wordTrace_append hprefix tailTrace_85313
  have hstable : (prefixWord ++ tailWord_85313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85313).length < 2 ^ (prefixWord ++ tailWord_85313).sum := by decide
  have hdescent : baseEnd_85313 < baseStart_85313 := by decide
  rcases family_descends (prefixWord ++ tailWord_85313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85329 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 1, 5]
def baseStart_85329 : Nat := 118140960795 + 85329 * 2 ^ 59
def prefixEnd_85329 : Nat := 4983230072969 + 3 ^ 40 * 85329 * 2
def baseEnd_85329 : Nat := 14604930255867294531695

theorem tailTrace_85329 : CollatzResearch.WordTrace tailWord_85329 prefixEnd_85329 14604930255867294531695 := by
  unfold tailWord_85329
  simp only [CollatzResearch.WordTrace]
  refine ⟨3112204307875080878091041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2074802871916720585394027 3112204307875080878091041)
  ·
    refine ⟨2334153230906310658568281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3112204307875080878091041 2334153230906310658568281)
    ·
      refine ⟨1750614923179732993926211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2334153230906310658568281 1750614923179732993926211)
      ·
        refine ⟨2625922384769599490889317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750614923179732993926211 2625922384769599490889317)
        ·
          refine ⟨492360447144299904541747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2625922384769599490889317 492360447144299904541747)
          ·
            refine ⟨738540670716449856812621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492360447144299904541747 738540670716449856812621)
            ·
              refine ⟨276952751518668696304733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 738540670716449856812621 276952751518668696304733)
              ·
                refine ⟨103857281819500761114275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276952751518668696304733 103857281819500761114275)
                ·
                  refine ⟨155785922729251141671413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103857281819500761114275 155785922729251141671413)
                  ·
                    refine ⟨14604930255867294531695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 155785922729251141671413 14604930255867294531695)
                    ·
                      rfl

theorem cell23_85329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_85329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85329 prefixEnd_85329 := by exact prefixLift 85329
  have htrace : WordTrace (prefixWord ++ tailWord_85329) baseStart_85329 baseEnd_85329 := by
    simpa [prefixWord, tailWord_85329, baseEnd_85329] using wordTrace_append hprefix tailTrace_85329
  have hstable : (prefixWord ++ tailWord_85329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85329).length < 2 ^ (prefixWord ++ tailWord_85329).sum := by decide
  have hdescent : baseEnd_85329 < baseStart_85329 := by decide
  rcases family_descends (prefixWord ++ tailWord_85329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85369 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 3, 2, 3]
def baseStart_85369 : Nat := 118140960795 + 85369 * 2 ^ 59
def prefixEnd_85369 : Nat := 4983230072969 + 3 ^ 40 * 85369 * 2
def baseEnd_85369 : Nat := 43835329993781727094901

theorem tailTrace_85369 : CollatzResearch.WordTrace tailWord_85369 prefixEnd_85369 43835329993781727094901 := by
  unfold tailWord_85369
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113663227730167709547161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2075775485153445139698107 3113663227730167709547161)
  ·
    refine ⟨2335247420797625782160371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3113663227730167709547161 2335247420797625782160371)
    ·
      refine ⟨3502871131196438673240557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2335247420797625782160371 3502871131196438673240557)
      ·
        refine ⟨1313576674198664502465209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3502871131196438673240557 1313576674198664502465209)
        ·
          refine ⟨985182505648998376848907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1313576674198664502465209 985182505648998376848907)
          ·
            refine ⟨1477773758473497565273361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 985182505648998376848907 1477773758473497565273361)
            ·
              refine ⟨1108330318855123173955021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477773758473497565273361 1108330318855123173955021)
              ·
                refine ⟨415623869570671190233133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1108330318855123173955021 415623869570671190233133)
                ·
                  refine ⟨155858951089001696337425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 415623869570671190233133 155858951089001696337425)
                  ·
                    refine ⟨116894213316751272253069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 155858951089001696337425 116894213316751272253069)
                    ·
                      refine ⟨43835329993781727094901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116894213316751272253069 43835329993781727094901)
                      ·
                        rfl

theorem cell23_85369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_85369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85369 prefixEnd_85369 := by exact prefixLift 85369
  have htrace : WordTrace (prefixWord ++ tailWord_85369) baseStart_85369 baseEnd_85369 := by
    simpa [prefixWord, tailWord_85369, baseEnd_85369] using wordTrace_append hprefix tailTrace_85369
  have hstable : (prefixWord ++ tailWord_85369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85369).length < 2 ^ (prefixWord ++ tailWord_85369).sum := by decide
  have hdescent : baseEnd_85369 < baseStart_85369 := by decide
  rcases family_descends (prefixWord ++ tailWord_85369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85372 : List Nat := [2, 2, 2, 1, 1, 1, 5, 9]
def baseStart_85372 : Nat := 118140960795 + 85372 * 2 ^ 59
def prefixEnd_85372 : Nat := 4983230072969 + 3 ^ 40 * 85372 * 2
def baseEnd_85372 : Nat := 1623587793916489457681

theorem tailTrace_85372 : CollatzResearch.WordTrace tailWord_85372 prefixEnd_85372 1623587793916489457681 := by
  unfold tailWord_85372
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556886323359649610953185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2075848431146199481270913 1556886323359649610953185)
  ·
    refine ⟨1167664742519737208214889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1556886323359649610953185 1167664742519737208214889)
    ·
      refine ⟨875748556889802906161167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1167664742519737208214889 875748556889802906161167)
      ·
        refine ⟨1313622835334704359241751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 875748556889802906161167 1313622835334704359241751)
        ·
          refine ⟨1970434253002056538862627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313622835334704359241751 1970434253002056538862627)
          ·
            refine ⟨2955651379503084808293941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1970434253002056538862627 2955651379503084808293941)
            ·
              refine ⟨277092316828414200777557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2955651379503084808293941 277092316828414200777557)
              ·
                refine ⟨1623587793916489457681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 277092316828414200777557 1623587793916489457681)
                ·
                  rfl

theorem cell23_85372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 9].length) (baseStart_85372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85372 prefixEnd_85372 := by exact prefixLift 85372
  have htrace : WordTrace (prefixWord ++ tailWord_85372) baseStart_85372 baseEnd_85372 := by
    simpa [prefixWord, tailWord_85372, baseEnd_85372] using wordTrace_append hprefix tailTrace_85372
  have hstable : (prefixWord ++ tailWord_85372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85372).length < 2 ^ (prefixWord ++ tailWord_85372).sum := by decide
  have hdescent : baseEnd_85372 < baseStart_85372 := by decide
  rcases family_descends (prefixWord ++ tailWord_85372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85377 : List Nat := [1, 2, 4, 3, 2, 2, 1, 3, 1, 1, 3]
def baseStart_85377 : Nat := 118140960795 + 85377 * 2 ^ 59
def prefixEnd_85377 : Nat := 4983230072969 + 3 ^ 40 * 85377 * 2
def baseEnd_85377 : Nat := 43839437839017695794865

theorem tailTrace_85377 : CollatzResearch.WordTrace tailWord_85377 prefixEnd_85377 43839437839017695794865 := by
  unfold tailWord_85377
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113955011701185075838385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2075970007800790050558923 3113955011701185075838385)
  ·
    refine ⟨2335466258775888806878789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3113955011701185075838385 2335466258775888806878789)
    ·
      refine ⟨437899923520479151289773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2335466258775888806878789 437899923520479151289773)
      ·
        refine ⟨164212471320179681733665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 437899923520479151289773 164212471320179681733665)
        ·
          refine ⟨123159353490134761300249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164212471320179681733665 123159353490134761300249)
          ·
            refine ⟨92369515117601070975187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123159353490134761300249 92369515117601070975187)
            ·
              refine ⟨138554272676401606462781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92369515117601070975187 138554272676401606462781)
              ·
                refine ⟨51957852253650602423543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138554272676401606462781 51957852253650602423543)
                ·
                  refine ⟨77936778380475903635315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51957852253650602423543 77936778380475903635315)
                  ·
                    refine ⟨116905167570713855452973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77936778380475903635315 116905167570713855452973)
                    ·
                      refine ⟨43839437839017695794865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116905167570713855452973 43839437839017695794865)
                      ·
                        rfl

theorem cell23_85377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_85377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85377 prefixEnd_85377 := by exact prefixLift 85377
  have htrace : WordTrace (prefixWord ++ tailWord_85377) baseStart_85377 baseEnd_85377 := by
    simpa [prefixWord, tailWord_85377, baseEnd_85377] using wordTrace_append hprefix tailTrace_85377
  have hstable : (prefixWord ++ tailWord_85377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85377).length < 2 ^ (prefixWord ++ tailWord_85377).sum := by decide
  have hdescent : baseEnd_85377 < baseStart_85377 := by decide
  rcases family_descends (prefixWord ++ tailWord_85377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85394 : List Nat := [3, 2, 3, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_85394 : Nat := 118140960795 + 85394 * 2 ^ 59
def prefixEnd_85394 : Nat := 4983230072969 + 3 ^ 40 * 85394 * 2
def baseEnd_85394 : Nat := 43848167010144129282287

theorem tailTrace_85394 : CollatzResearch.WordTrace tailWord_85394 prefixEnd_85394 43848167010144129282287 := by
  unfold tailWord_85394
  simp only [CollatzResearch.WordTrace]
  refine ⟨778643763159899244801809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2076383368426397986138157 778643763159899244801809)
  ·
    refine ⟨583982822369924433601357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 778643763159899244801809 583982822369924433601357)
    ·
      refine ⟨218993558388721662600509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 583982822369924433601357 218993558388721662600509)
      ·
        refine ⟨82122584395770623475191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218993558388721662600509 82122584395770623475191)
        ·
          refine ⟨123183876593655935212787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82122584395770623475191 123183876593655935212787)
          ·
            refine ⟨184775814890483902819181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123183876593655935212787 184775814890483902819181)
            ·
              refine ⟨69290930583931463557193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184775814890483902819181 69290930583931463557193)
              ·
                refine ⟨51968197937948597667895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69290930583931463557193 51968197937948597667895)
                ·
                  refine ⟨77952296906922896501843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51968197937948597667895 77952296906922896501843)
                  ·
                    refine ⟨116928445360384344752765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77952296906922896501843 116928445360384344752765)
                    ·
                      refine ⟨43848167010144129282287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 116928445360384344752765 43848167010144129282287)
                      ·
                        rfl

theorem cell23_85394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_85394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85394 prefixEnd_85394 := by exact prefixLift 85394
  have htrace : WordTrace (prefixWord ++ tailWord_85394) baseStart_85394 baseEnd_85394 := by
    simpa [prefixWord, tailWord_85394, baseEnd_85394] using wordTrace_append hprefix tailTrace_85394
  have hstable : (prefixWord ++ tailWord_85394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85394).length < 2 ^ (prefixWord ++ tailWord_85394).sum := by decide
  have hdescent : baseEnd_85394 < baseStart_85394 := by decide
  rcases family_descends (prefixWord ++ tailWord_85394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85410 : List Nat := [3, 3, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_85410 : Nat := 118140960795 + 85410 * 2 ^ 59
def prefixEnd_85410 : Nat := 4983230072969 + 3 ^ 40 * 85410 * 2
def baseEnd_85410 : Nat := 14618794233538688894071

theorem tailTrace_85410 : CollatzResearch.WordTrace tailWord_85410 prefixEnd_85410 14618794233538688894071 := by
  unfold tailWord_85410
  simp only [CollatzResearch.WordTrace]
  refine ⟨778789655145407927947421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2076772413721087807859789 778789655145407927947421)
  ·
    refine ⟨292046120679527972980283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 778789655145407927947421 292046120679527972980283)
    ·
      refine ⟨438069181019291959470425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292046120679527972980283 438069181019291959470425)
      ·
        refine ⟨328551885764468969602819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438069181019291959470425 328551885764468969602819)
        ·
          refine ⟨492827828646703454404229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328551885764468969602819 492827828646703454404229)
          ·
            refine ⟨92405217871256897700793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 492827828646703454404229 92405217871256897700793)
            ·
              refine ⟨69303913403442673275595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92405217871256897700793 69303913403442673275595)
              ·
                refine ⟨103955870105164009913393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69303913403442673275595 103955870105164009913393)
                ·
                  refine ⟨77966902578873007435045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103955870105164009913393 77966902578873007435045)
                  ·
                    refine ⟨14618794233538688894071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77966902578873007435045 14618794233538688894071)
                    ·
                      rfl

theorem cell23_85410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_85410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85410 prefixEnd_85410 := by exact prefixLift 85410
  have htrace : WordTrace (prefixWord ++ tailWord_85410) baseStart_85410 baseEnd_85410 := by
    simpa [prefixWord, tailWord_85410, baseEnd_85410] using wordTrace_append hprefix tailTrace_85410
  have hstable : (prefixWord ++ tailWord_85410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85410).length < 2 ^ (prefixWord ++ tailWord_85410).sum := by decide
  have hdescent : baseEnd_85410 < baseStart_85410 := by decide
  rcases family_descends (prefixWord ++ tailWord_85410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85473 : List Nat := [1, 2, 3, 1, 2, 4, 2, 1, 1, 4, 2]
def baseStart_85473 : Nat := 118140960795 + 85473 * 2 ^ 59
def prefixEnd_85473 : Nat := 4983230072969 + 3 ^ 40 * 85473 * 2
def baseEnd_85473 : Nat := 43888731981849320194423

theorem tailTrace_85473 : CollatzResearch.WordTrace tailWord_85473 prefixEnd_85473 43888731981849320194423 := by
  unfold tailWord_85473
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117456419353393471333073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2078304279568928980888715 3117456419353393471333073)
  ·
    refine ⟨2338092314515045103499805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3117456419353393471333073 2338092314515045103499805)
    ·
      refine ⟨876784617943141913812427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2338092314515045103499805 876784617943141913812427)
      ·
        refine ⟨1315176926914712870718641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876784617943141913812427 1315176926914712870718641)
        ·
          refine ⟨986382695186034653038981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1315176926914712870718641 986382695186034653038981)
          ·
            refine ⟨184946755347381497444809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 986382695186034653038981 184946755347381497444809)
            ·
              refine ⟨138710066510536123083607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184946755347381497444809 138710066510536123083607)
              ·
                refine ⟨208065099765804184625411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138710066510536123083607 208065099765804184625411)
                ·
                  refine ⟨312097649648706276938117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208065099765804184625411 312097649648706276938117)
                  ·
                    refine ⟨58518309309132426925897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 312097649648706276938117 58518309309132426925897)
                    ·
                      refine ⟨43888731981849320194423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58518309309132426925897 43888731981849320194423)
                      ·
                        rfl

theorem cell23_85473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_85473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85473 prefixEnd_85473 := by exact prefixLift 85473
  have htrace : WordTrace (prefixWord ++ tailWord_85473) baseStart_85473 baseEnd_85473 := by
    simpa [prefixWord, tailWord_85473, baseEnd_85473] using wordTrace_append hprefix tailTrace_85473
  have hstable : (prefixWord ++ tailWord_85473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85473).length < 2 ^ (prefixWord ++ tailWord_85473).sum := by decide
  have hdescent : baseEnd_85473 < baseStart_85473 := by decide
  rcases family_descends (prefixWord ++ tailWord_85473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85479 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 9]
def baseStart_85479 : Nat := 118140960795 + 85479 * 2 ^ 59
def prefixEnd_85479 : Nat := 4983230072969 + 3 ^ 40 * 85479 * 2
def baseEnd_85479 : Nat := 4876868096197366302155

theorem tailTrace_85479 : CollatzResearch.WordTrace tailWord_85479 prefixEnd_85479 4876868096197366302155 := by
  unfold tailWord_85479
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117675257331656496051491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2078450171554437664034327 3117675257331656496051491)
  ·
    refine ⟨4676512885997484744077237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3117675257331656496051491 4676512885997484744077237)
    ·
      refine ⟨438423083062264194757241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4676512885997484744077237 438423083062264194757241)
      ·
        refine ⟨328817312296698146067931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438423083062264194757241 328817312296698146067931)
        ·
          refine ⟨493225968445047219101897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328817312296698146067931 493225968445047219101897)
          ·
            refine ⟨369919476333785414326423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493225968445047219101897 369919476333785414326423)
            ·
              refine ⟨554879214500678121489635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369919476333785414326423 554879214500678121489635)
              ·
                refine ⟨832318821751017182234453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 554879214500678121489635 832318821751017182234453)
                ·
                  refine ⟨4876868096197366302155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 832318821751017182234453 4876868096197366302155)
                  ·
                    rfl

theorem cell23_85479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 9].length) (baseStart_85479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85479 prefixEnd_85479 := by exact prefixLift 85479
  have htrace : WordTrace (prefixWord ++ tailWord_85479) baseStart_85479 baseEnd_85479 := by
    simpa [prefixWord, tailWord_85479, baseEnd_85479] using wordTrace_append hprefix tailTrace_85479
  have hstable : (prefixWord ++ tailWord_85479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85479).length < 2 ^ (prefixWord ++ tailWord_85479).sum := by decide
  have hdescent : baseEnd_85479 < baseStart_85479 := by decide
  rcases family_descends (prefixWord ++ tailWord_85479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85496 : List Nat := [2, 1, 2, 1, 1, 5, 1, 5, 5]
def baseStart_85496 : Nat := 118140960795 + 85496 * 2 ^ 59
def prefixEnd_85496 : Nat := 4983230072969 + 3 ^ 40 * 85496 * 2
def baseEnd_85496 : Nat := 4877838004100303356313

theorem tailTrace_85496 : CollatzResearch.WordTrace tailWord_85496 prefixEnd_85496 4877838004100303356313 := by
  unfold tailWord_85496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559147649135034199710171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2078863532180045599613561 1559147649135034199710171)
  ·
    refine ⟨2338721473702551299565257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1559147649135034199710171 2338721473702551299565257)
    ·
      refine ⟨1754041105276913474673943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2338721473702551299565257 1754041105276913474673943)
      ·
        refine ⟨2631061657915370212010915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1754041105276913474673943 2631061657915370212010915)
        ·
          refine ⟨3946592486873055318016373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2631061657915370212010915 3946592486873055318016373)
          ·
            refine ⟨369993045644348936064035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3946592486873055318016373 369993045644348936064035)
            ·
              refine ⟨554989568466523404096053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369993045644348936064035 554989568466523404096053)
              ·
                refine ⟨52030272043736569134005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 554989568466523404096053 52030272043736569134005)
                ·
                  refine ⟨4877838004100303356313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52030272043736569134005 4877838004100303356313)
                  ·
                    rfl

theorem cell23_85496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 5].length) (baseStart_85496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85496 prefixEnd_85496 := by exact prefixLift 85496
  have htrace : WordTrace (prefixWord ++ tailWord_85496) baseStart_85496 baseEnd_85496 := by
    simpa [prefixWord, tailWord_85496, baseEnd_85496] using wordTrace_append hprefix tailTrace_85496
  have hstable : (prefixWord ++ tailWord_85496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85496).length < 2 ^ (prefixWord ++ tailWord_85496).sum := by decide
  have hdescent : baseEnd_85496 < baseStart_85496 := by decide
  rcases family_descends (prefixWord ++ tailWord_85496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85509 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_85509 : Nat := 118140960795 + 85509 * 2 ^ 59
def prefixEnd_85509 : Nat := 4983230072969 + 3 ^ 40 * 85509 * 2
def baseEnd_85509 : Nat := 14635739095137059781419

theorem tailTrace_85509 : CollatzResearch.WordTrace tailWord_85509 prefixEnd_85509 14635739095137059781419 := by
  unfold tailWord_85509
  simp only [CollatzResearch.WordTrace]
  refine ⟨3118769447222971619643581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2079179631481981079762387 3118769447222971619643581)
  ·
    refine ⟨1169538542708614357366343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3118769447222971619643581 1169538542708614357366343)
    ·
      refine ⟨1754307814062921536049515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1169538542708614357366343 1754307814062921536049515)
      ·
        refine ⟨2631461721094382304074273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1754307814062921536049515 2631461721094382304074273)
        ·
          refine ⟨1973596290820786728055705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2631461721094382304074273 1973596290820786728055705)
          ·
            refine ⟨1480197218115590046041779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1973596290820786728055705 1480197218115590046041779)
            ·
              refine ⟨2220295827173385069062669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1480197218115590046041779 2220295827173385069062669)
              ·
                refine ⟨832610935190019400898501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2220295827173385069062669 832610935190019400898501)
                ·
                  refine ⟨156114550348128637668469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 832610935190019400898501 156114550348128637668469)
                  ·
                    refine ⟨14635739095137059781419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 156114550348128637668469 14635739095137059781419)
                    ·
                      rfl

theorem cell23_85509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_85509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85509 prefixEnd_85509 := by exact prefixLift 85509
  have htrace : WordTrace (prefixWord ++ tailWord_85509) baseStart_85509 baseEnd_85509 := by
    simpa [prefixWord, tailWord_85509, baseEnd_85509] using wordTrace_append hprefix tailTrace_85509
  have hstable : (prefixWord ++ tailWord_85509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85509).length < 2 ^ (prefixWord ++ tailWord_85509).sum := by decide
  have hdescent : baseEnd_85509 < baseStart_85509 := by decide
  rcases family_descends (prefixWord ++ tailWord_85509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85524 : List Nat := [2, 4, 3, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_85524 : Nat := 118140960795 + 85524 * 2 ^ 59
def prefixEnd_85524 : Nat := 4983230072969 + 3 ^ 40 * 85524 * 2
def baseEnd_85524 : Nat := 43914919495228620656689

theorem tailTrace_85524 : CollatzResearch.WordTrace tailWord_85524 prefixEnd_85524 43914919495228620656689 := by
  unfold tailWord_85524
  simp only [CollatzResearch.WordTrace]
  refine ⟨1559658271084314590719813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2079544361445752787626417 1559658271084314590719813)
  ·
    refine ⟨292435925828308985759965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1559658271084314590719813 292435925828308985759965)
    ·
      refine ⟨109663472185615869659987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292435925828308985759965 109663472185615869659987)
      ·
        refine ⟨164495208278423804489981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109663472185615869659987 164495208278423804489981)
        ·
          refine ⟨61685703104408926683743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164495208278423804489981 61685703104408926683743)
          ·
            refine ⟨92528554656613390025615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61685703104408926683743 92528554656613390025615)
            ·
              refine ⟨138792831984920085038423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92528554656613390025615 138792831984920085038423)
              ·
                refine ⟨208189247977380127557635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138792831984920085038423 208189247977380127557635)
                ·
                  refine ⟨312283871966070191336453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208189247977380127557635 312283871966070191336453)
                  ·
                    refine ⟨58553225993638160875585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 312283871966070191336453 58553225993638160875585)
                    ·
                      refine ⟨43914919495228620656689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58553225993638160875585 43914919495228620656689)
                      ·
                        rfl

theorem cell23_85524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_85524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85524 prefixEnd_85524 := by exact prefixLift 85524
  have htrace : WordTrace (prefixWord ++ tailWord_85524) baseStart_85524 baseEnd_85524 := by
    simpa [prefixWord, tailWord_85524, baseEnd_85524] using wordTrace_append hprefix tailTrace_85524
  have hstable : (prefixWord ++ tailWord_85524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85524).length < 2 ^ (prefixWord ++ tailWord_85524).sum := by decide
  have hdescent : baseEnd_85524 < baseStart_85524 := by decide
  rcases family_descends (prefixWord ++ tailWord_85524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85546 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_85546 : Nat := 118140960795 + 85546 * 2 ^ 59
def prefixEnd_85546 : Nat := 4983230072969 + 3 ^ 40 * 85546 * 2
def baseEnd_85546 : Nat := 43926216069627534581587

theorem tailTrace_85546 : CollatzResearch.WordTrace tailWord_85546 prefixEnd_85546 43926216069627534581587 := by
  unfold tailWord_85546
  simp only [CollatzResearch.WordTrace]
  refine ⟨780029737022231734685123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2080079298725951292493661 780029737022231734685123)
  ·
    refine ⟨1170044605533347602027685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 780029737022231734685123 1170044605533347602027685)
    ·
      refine ⟨219383363537502675380191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1170044605533347602027685 219383363537502675380191)
      ·
        refine ⟨329075045306254013070287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219383363537502675380191 329075045306254013070287)
        ·
          refine ⟨493612567959381019605431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329075045306254013070287 493612567959381019605431)
          ·
            refine ⟨740418851939071529408147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493612567959381019605431 740418851939071529408147)
            ·
              refine ⟨1110628277908607294112221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740418851939071529408147 1110628277908607294112221)
              ·
                refine ⟨416485604215727735292083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110628277908607294112221 416485604215727735292083)
                ·
                  refine ⟨624728406323591602938125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416485604215727735292083 624728406323591602938125)
                  ·
                    refine ⟨234273152371346851101797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 624728406323591602938125 234273152371346851101797)
                    ·
                      refine ⟨43926216069627534581587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 234273152371346851101797 43926216069627534581587)
                      ·
                        rfl

theorem cell23_85546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_85546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85546 prefixEnd_85546 := by exact prefixLift 85546
  have htrace : WordTrace (prefixWord ++ tailWord_85546) baseStart_85546 baseEnd_85546 := by
    simpa [prefixWord, tailWord_85546, baseEnd_85546] using wordTrace_append hprefix tailTrace_85546
  have hstable : (prefixWord ++ tailWord_85546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85546).length < 2 ^ (prefixWord ++ tailWord_85546).sum := by decide
  have hdescent : baseEnd_85546 < baseStart_85546 := by decide
  rcases family_descends (prefixWord ++ tailWord_85546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85597 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_85597 : Nat := 118140960795 + 85597 * 2 ^ 59
def prefixEnd_85597 : Nat := 4983230072969 + 3 ^ 40 * 85597 * 2
def baseEnd_85597 : Nat := 43952403583006835043853

theorem tailTrace_85597 : CollatzResearch.WordTrace tailWord_85597 prefixEnd_85597 43952403583006835043853 := by
  unfold tailWord_85597
  simp only [CollatzResearch.WordTrace]
  refine ⟨3121979070904162648847045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2081319380602775099231363 3121979070904162648847045)
  ·
    refine ⟨585371075794530496658821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3121979070904162648847045 585371075794530496658821)
    ·
      refine ⟨109757076711474468123529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 585371075794530496658821 109757076711474468123529)
      ·
        refine ⟨82317807533605851092647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109757076711474468123529 82317807533605851092647)
        ·
          refine ⟨123476711300408776638971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82317807533605851092647 123476711300408776638971)
          ·
            refine ⟨185215066950613164958457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123476711300408776638971 185215066950613164958457)
            ·
              refine ⟨138911300212959873718843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185215066950613164958457 138911300212959873718843)
              ·
                refine ⟨208366950319439810578265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138911300212959873718843 208366950319439810578265)
                ·
                  refine ⟨156275212739579857933699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208366950319439810578265 156275212739579857933699)
                  ·
                    refine ⟨234412819109369786900549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 156275212739579857933699 234412819109369786900549)
                    ·
                      refine ⟨43952403583006835043853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 234412819109369786900549 43952403583006835043853)
                      ·
                        rfl

theorem cell23_85597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_85597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85597 prefixEnd_85597 := by exact prefixLift 85597
  have htrace : WordTrace (prefixWord ++ tailWord_85597) baseStart_85597 baseEnd_85597 := by
    simpa [prefixWord, tailWord_85597, baseEnd_85597] using wordTrace_append hprefix tailTrace_85597
  have hstable : (prefixWord ++ tailWord_85597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85597).length < 2 ^ (prefixWord ++ tailWord_85597).sum := by decide
  have hdescent : baseEnd_85597 < baseStart_85597 := by decide
  rcases family_descends (prefixWord ++ tailWord_85597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85687 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 3, 2, 2]
def baseStart_85687 : Nat := 118140960795 + 85687 * 2 ^ 59
def prefixEnd_85687 : Nat := 4983230072969 + 3 ^ 40 * 85687 * 2
def baseEnd_85687 : Nat := 43998616841911482918439

theorem tailTrace_85687 : CollatzResearch.WordTrace tailWord_85687 prefixEnd_85687 43998616841911482918439 := by
  unfold tailWord_85687
  simp only [CollatzResearch.WordTrace]
  refine ⟨3125261640578108019623315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2083507760385405346415543 3125261640578108019623315)
  ·
    refine ⟨4687892460867162029434973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3125261640578108019623315 4687892460867162029434973)
    ·
      refine ⟨1757959672825185761038115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4687892460867162029434973 1757959672825185761038115)
      ·
        refine ⟨2636939509237778641557173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1757959672825185761038115 2636939509237778641557173)
        ·
          refine ⟨247213078991041747645985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2636939509237778641557173 247213078991041747645985)
          ·
            refine ⟨185409809243281310734489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247213078991041747645985 185409809243281310734489)
            ·
              refine ⟨139057356932460983050867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185409809243281310734489 139057356932460983050867)
              ·
                refine ⟨208586035398691474576301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139057356932460983050867 208586035398691474576301)
                ·
                  refine ⟨78219763274509302966113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208586035398691474576301 78219763274509302966113)
                  ·
                    refine ⟨58664822455881977224585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78219763274509302966113 58664822455881977224585)
                    ·
                      refine ⟨43998616841911482918439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58664822455881977224585 43998616841911482918439)
                      ·
                        rfl

theorem cell23_85687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_85687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85687 prefixEnd_85687 := by exact prefixLift 85687
  have htrace : WordTrace (prefixWord ++ tailWord_85687) baseStart_85687 baseEnd_85687 := by
    simpa [prefixWord, tailWord_85687, baseEnd_85687] using wordTrace_append hprefix tailTrace_85687
  have hstable : (prefixWord ++ tailWord_85687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85687).length < 2 ^ (prefixWord ++ tailWord_85687).sum := by decide
  have hdescent : baseEnd_85687 < baseStart_85687 := by decide
  rcases family_descends (prefixWord ++ tailWord_85687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85764 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_85764 : Nat := 118140960795 + 85764 * 2 ^ 59
def prefixEnd_85764 : Nat := 4983230072969 + 3 ^ 40 * 85764 * 2
def baseEnd_85764 : Nat := 44038154852307681655585

theorem tailTrace_85764 : CollatzResearch.WordTrace tailWord_85764 prefixEnd_85764 44038154852307681655585 := by
  unfold tailWord_85764
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564035030649575085088173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2085380040866100113450897 1564035030649575085088173)
  ·
    refine ⟨586513136493590656908065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1564035030649575085088173 586513136493590656908065)
    ·
      refine ⟨439884852370192992681049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 586513136493590656908065 439884852370192992681049)
      ·
        refine ⟨329913639277644744510787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439884852370192992681049 329913639277644744510787)
        ·
          refine ⟨494870458916467116766181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329913639277644744510787 494870458916467116766181)
          ·
            refine ⟨92788211046837584393659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 494870458916467116766181 92788211046837584393659)
            ·
              refine ⟨139182316570256376590489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92788211046837584393659 139182316570256376590489)
              ·
                refine ⟨104386737427692282442867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139182316570256376590489 104386737427692282442867)
                ·
                  refine ⟨156580106141538423664301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104386737427692282442867 156580106141538423664301)
                  ·
                    refine ⟨58717539803076908874113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 156580106141538423664301 58717539803076908874113)
                    ·
                      refine ⟨44038154852307681655585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58717539803076908874113 44038154852307681655585)
                      ·
                        rfl

theorem cell23_85764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_85764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85764 prefixEnd_85764 := by exact prefixLift 85764
  have htrace : WordTrace (prefixWord ++ tailWord_85764) baseStart_85764 baseEnd_85764 := by
    simpa [prefixWord, tailWord_85764, baseEnd_85764] using wordTrace_append hprefix tailTrace_85764
  have hstable : (prefixWord ++ tailWord_85764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85764).length < 2 ^ (prefixWord ++ tailWord_85764).sum := by decide
  have hdescent : baseEnd_85764 < baseStart_85764 := by decide
  rcases family_descends (prefixWord ++ tailWord_85764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85794 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_85794 : Nat := 118140960795 + 85794 * 2 ^ 59
def prefixEnd_85794 : Nat := 4983230072969 + 3 ^ 40 * 85794 * 2
def baseEnd_85794 : Nat := 44053559271942564280447

theorem tailTrace_85794 : CollatzResearch.WordTrace tailWord_85794 prefixEnd_85794 44053559271942564280447 := by
  unfold tailWord_85794
  simp only [CollatzResearch.WordTrace]
  refine ⟨782291062797616323442109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2086109500793643529178957 782291062797616323442109)
  ·
    refine ⟨293359148549106121290791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 782291062797616323442109 293359148549106121290791)
    ·
      refine ⟨440038722823659181936187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293359148549106121290791 440038722823659181936187)
      ·
        refine ⟨660058084235488772904281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440038722823659181936187 660058084235488772904281)
        ·
          refine ⟨495043563176616579678211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 660058084235488772904281 495043563176616579678211)
          ·
            refine ⟨742565344764924869517317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495043563176616579678211 742565344764924869517317)
            ·
              refine ⟨139231002143423413034497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 742565344764924869517317 139231002143423413034497)
              ·
                refine ⟨104423251607567559775873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139231002143423413034497 104423251607567559775873)
                ·
                  refine ⟨78317438705675669831905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104423251607567559775873 78317438705675669831905)
                  ·
                    refine ⟨58738079029256752373929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78317438705675669831905 58738079029256752373929)
                    ·
                      refine ⟨44053559271942564280447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58738079029256752373929 44053559271942564280447)
                      ·
                        rfl

theorem cell23_85794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_85794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85794 prefixEnd_85794 := by exact prefixLift 85794
  have htrace : WordTrace (prefixWord ++ tailWord_85794) baseStart_85794 baseEnd_85794 := by
    simpa [prefixWord, tailWord_85794, baseEnd_85794] using wordTrace_append hprefix tailTrace_85794
  have hstable : (prefixWord ++ tailWord_85794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85794).length < 2 ^ (prefixWord ++ tailWord_85794).sum := by decide
  have hdescent : baseEnd_85794 < baseStart_85794 := by decide
  rcases family_descends (prefixWord ++ tailWord_85794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85810 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_85810 : Nat := 118140960795 + 85810 * 2 ^ 59
def prefixEnd_85810 : Nat := 4983230072969 + 3 ^ 40 * 85810 * 2
def baseEnd_85810 : Nat := 44061774962414501680373

theorem tailTrace_85810 : CollatzResearch.WordTrace tailWord_85810 prefixEnd_85810 44061774962414501680373 := by
  unfold tailWord_85810
  simp only [CollatzResearch.WordTrace]
  refine ⟨782436954783125006587721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2086498546088333350900589 782436954783125006587721)
  ·
    refine ⟨586827716087343754940791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 782436954783125006587721 586827716087343754940791)
    ·
      refine ⟨880241574131015632411187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586827716087343754940791 880241574131015632411187)
      ·
        refine ⟨1320362361196523448616781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880241574131015632411187 1320362361196523448616781)
        ·
          refine ⟨495135885448696293231293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1320362361196523448616781 495135885448696293231293)
          ·
            refine ⟨185675957043261109961735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 495135885448696293231293 185675957043261109961735)
            ·
              refine ⟨278513935564891664942603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185675957043261109961735 278513935564891664942603)
              ·
                refine ⟨417770903347337497413905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278513935564891664942603 417770903347337497413905)
                ·
                  refine ⟨313328177510503123060429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417770903347337497413905 313328177510503123060429)
                  ·
                    refine ⟨117498066566438671147661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 313328177510503123060429 117498066566438671147661)
                    ·
                      refine ⟨44061774962414501680373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 117498066566438671147661 44061774962414501680373)
                      ·
                        rfl

theorem cell23_85810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_85810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85810 prefixEnd_85810 := by exact prefixLift 85810
  have htrace : WordTrace (prefixWord ++ tailWord_85810) baseStart_85810 baseEnd_85810 := by
    simpa [prefixWord, tailWord_85810, baseEnd_85810] using wordTrace_append hprefix tailTrace_85810
  have hstable : (prefixWord ++ tailWord_85810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85810).length < 2 ^ (prefixWord ++ tailWord_85810).sum := by decide
  have hdescent : baseEnd_85810 < baseStart_85810 := by decide
  rcases family_descends (prefixWord ++ tailWord_85810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85833 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 4]
def baseStart_85833 : Nat := 118140960795 + 85833 * 2 ^ 59
def prefixEnd_85833 : Nat := 4983230072969 + 3 ^ 40 * 85833 * 2
def baseEnd_85833 : Nat := 44073585017467911692767

theorem tailTrace_85833 : CollatzResearch.WordTrace tailWord_85833 prefixEnd_85833 44073585017467911692767 := by
  unfold tailWord_85833
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130586698049174954438153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2087057798699449969625435 3130586698049174954438153)
  ·
    refine ⟨2347940023536881215828615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3130586698049174954438153 2347940023536881215828615)
    ·
      refine ⟨3521910035305321823742923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2347940023536881215828615 3521910035305321823742923)
      ·
        refine ⟨5282865052957982735614385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3521910035305321823742923 5282865052957982735614385)
        ·
          refine ⟨3962148789718487051710789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5282865052957982735614385 3962148789718487051710789)
          ·
            refine ⟨742902898072216322195773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3962148789718487051710789 742902898072216322195773)
            ·
              refine ⟨278588586777081120823415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742902898072216322195773 278588586777081120823415)
              ·
                refine ⟨417882880165621681235123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278588586777081120823415 417882880165621681235123)
                ·
                  refine ⟨626824320248432521852685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417882880165621681235123 626824320248432521852685)
                  ·
                    refine ⟨235059120093162195694757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 626824320248432521852685 235059120093162195694757)
                    ·
                      refine ⟨44073585017467911692767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 235059120093162195694757 44073585017467911692767)
                      ·
                        rfl

theorem cell23_85833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_85833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85833 prefixEnd_85833 := by exact prefixLift 85833
  have htrace : WordTrace (prefixWord ++ tailWord_85833) baseStart_85833 baseEnd_85833 := by
    simpa [prefixWord, tailWord_85833, baseEnd_85833] using wordTrace_append hprefix tailTrace_85833
  have hstable : (prefixWord ++ tailWord_85833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85833).length < 2 ^ (prefixWord ++ tailWord_85833).sum := by decide
  have hdescent : baseEnd_85833 < baseStart_85833 := by decide
  rcases family_descends (prefixWord ++ tailWord_85833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85850 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2]
def baseStart_85850 : Nat := 118140960795 + 85850 * 2 ^ 59
def prefixEnd_85850 : Nat := 4983230072969 + 3 ^ 40 * 85850 * 2
def baseEnd_85850 : Nat := 44082314188594345180189

theorem tailTrace_85850 : CollatzResearch.WordTrace tailWord_85850 prefixEnd_85850 44082314188594345180189 := by
  unfold tailWord_85850
  simp only [CollatzResearch.WordTrace]
  refine ⟨782801684746896714451751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2087471159325057905204669 782801684746896714451751)
  ·
    refine ⟨1174202527120345071677627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 782801684746896714451751 1174202527120345071677627)
    ·
      refine ⟨1761303790680517607516441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174202527120345071677627 1761303790680517607516441)
      ·
        refine ⟨1320977843010388205637331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1761303790680517607516441 1320977843010388205637331)
        ·
          refine ⟨1981466764515582308455997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1320977843010388205637331 1981466764515582308455997)
          ·
            refine ⟨743050036693343365670999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1981466764515582308455997 743050036693343365670999)
            ·
              refine ⟨1114575055040015048506499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743050036693343365670999 1114575055040015048506499)
              ·
                refine ⟨1671862582560022572759749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114575055040015048506499 1671862582560022572759749)
                ·
                  refine ⟨313474234230004232392453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671862582560022572759749 313474234230004232392453)
                  ·
                    refine ⟨58776418918125793573585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 313474234230004232392453 58776418918125793573585)
                    ·
                      refine ⟨44082314188594345180189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58776418918125793573585 44082314188594345180189)
                      ·
                        rfl

theorem cell23_85850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_85850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85850 prefixEnd_85850 := by exact prefixLift 85850
  have htrace : WordTrace (prefixWord ++ tailWord_85850) baseStart_85850 baseEnd_85850 := by
    simpa [prefixWord, tailWord_85850, baseEnd_85850] using wordTrace_append hprefix tailTrace_85850
  have hstable : (prefixWord ++ tailWord_85850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85850).length < 2 ^ (prefixWord ++ tailWord_85850).sum := by decide
  have hdescent : baseEnd_85850 < baseStart_85850 := by decide
  rcases family_descends (prefixWord ++ tailWord_85850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85863 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_85863 : Nat := 118140960795 + 85863 * 2 ^ 59
def prefixEnd_85863 : Nat := 4983230072969 + 3 ^ 40 * 85863 * 2
def baseEnd_85863 : Nat := 44088989437102794317629

theorem tailTrace_85863 : CollatzResearch.WordTrace tailWord_85863 prefixEnd_85863 44088989437102794317629 := by
  unfold tailWord_85863
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131680887940490078030243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2087787258626993385353495 3131680887940490078030243)
  ·
    refine ⟨4697521331910735117045365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3131680887940490078030243 4697521331910735117045365)
    ·
      refine ⟨440392624866631417223003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4697521331910735117045365 440392624866631417223003)
      ·
        refine ⟨660588937299947125834505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440392624866631417223003 660588937299947125834505)
        ·
          refine ⟨495441702974960344375879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 660588937299947125834505 495441702974960344375879)
          ·
            refine ⟨743162554462440516563819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495441702974960344375879 743162554462440516563819)
            ·
              refine ⟨1114743831693660774845729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743162554462440516563819 1114743831693660774845729)
              ·
                refine ⟨836057873770245581134297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114743831693660774845729 836057873770245581134297)
                ·
                  refine ⟨627043405327684185850723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 836057873770245581134297 627043405327684185850723)
                  ·
                    refine ⟨940565107991526278776085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 627043405327684185850723 940565107991526278776085)
                    ·
                      refine ⟨44088989437102794317629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 940565107991526278776085 44088989437102794317629)
                      ·
                        rfl

theorem cell23_85863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_85863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85863 prefixEnd_85863 := by exact prefixLift 85863
  have htrace : WordTrace (prefixWord ++ tailWord_85863) baseStart_85863 baseEnd_85863 := by
    simpa [prefixWord, tailWord_85863, baseEnd_85863] using wordTrace_append hprefix tailTrace_85863
  have hstable : (prefixWord ++ tailWord_85863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85863).length < 2 ^ (prefixWord ++ tailWord_85863).sum := by decide
  have hdescent : baseEnd_85863 < baseStart_85863 := by decide
  rcases family_descends (prefixWord ++ tailWord_85863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85883 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 3]
def baseStart_85883 : Nat := 118140960795 + 85883 * 2 ^ 59
def prefixEnd_85883 : Nat := 4983230072969 + 3 ^ 40 * 85883 * 2
def baseEnd_85883 : Nat := 44099259050192716067537

theorem tailTrace_85883 : CollatzResearch.WordTrace tailWord_85883 prefixEnd_85883 44099259050192716067537 := by
  unfold tailWord_85883
  simp only [CollatzResearch.WordTrace]
  refine ⟨3132410347868033493758303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2088273565245355662505535 3132410347868033493758303)
  ·
    refine ⟨4698615521802050240637455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3132410347868033493758303 4698615521802050240637455)
    ·
      refine ⟨7047923282703075360956183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4698615521802050240637455 7047923282703075360956183)
      ·
        refine ⟨10571884924054613041434275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7047923282703075360956183 10571884924054613041434275)
        ·
          refine ⟨15857827386081919562151413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10571884924054613041434275 15857827386081919562151413)
          ·
            refine ⟨1486671317445179958951695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15857827386081919562151413 1486671317445179958951695)
            ·
              refine ⟨2230006976167769938427543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486671317445179958951695 2230006976167769938427543)
              ·
                refine ⟨3345010464251654907641315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2230006976167769938427543 3345010464251654907641315)
                ·
                  refine ⟨5017515696377482361461973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345010464251654907641315 5017515696377482361461973)
                  ·
                    refine ⟨117598024133847242846765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5017515696377482361461973 117598024133847242846765)
                    ·
                      refine ⟨44099259050192716067537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 117598024133847242846765 44099259050192716067537)
                      ·
                        rfl

theorem cell23_85883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 3].length) (baseStart_85883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85883 prefixEnd_85883 := by exact prefixLift 85883
  have htrace : WordTrace (prefixWord ++ tailWord_85883) baseStart_85883 baseEnd_85883 := by
    simpa [prefixWord, tailWord_85883, baseEnd_85883] using wordTrace_append hprefix tailTrace_85883
  have hstable : (prefixWord ++ tailWord_85883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85883).length < 2 ^ (prefixWord ++ tailWord_85883).sum := by decide
  have hdescent : baseEnd_85883 < baseStart_85883 := by decide
  rcases family_descends (prefixWord ++ tailWord_85883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85923 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 4]
def baseStart_85923 : Nat := 118140960795 + 85923 * 2 ^ 59
def prefixEnd_85923 : Nat := 4983230072969 + 3 ^ 40 * 85923 * 2
def baseEnd_85923 : Nat := 44119798276372559567353

theorem tailTrace_85923 : CollatzResearch.WordTrace tailWord_85923 prefixEnd_85923 44119798276372559567353 := by
  unfold tailWord_85923
  simp only [CollatzResearch.WordTrace]
  refine ⟨3133869267723120325214423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2089246178482080216809615 3133869267723120325214423)
  ·
    refine ⟨4700803901584680487821635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3133869267723120325214423 4700803901584680487821635)
    ·
      refine ⟨7051205852377020731732453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4700803901584680487821635 7051205852377020731732453)
      ·
        refine ⟨1322101097320691387199835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7051205852377020731732453 1322101097320691387199835)
        ·
          refine ⟨1983151645981037080799753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322101097320691387199835 1983151645981037080799753)
          ·
            refine ⟨1487363734485777810599815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1983151645981037080799753 1487363734485777810599815)
            ·
              refine ⟨2231045601728666715899723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487363734485777810599815 2231045601728666715899723)
              ·
                refine ⟨3346568402593000073849585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231045601728666715899723 3346568402593000073849585)
                ·
                  refine ⟨2509926301944750055387189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3346568402593000073849585 2509926301944750055387189)
                  ·
                    refine ⟨235305590807320317692549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2509926301944750055387189 235305590807320317692549)
                    ·
                      refine ⟨44119798276372559567353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 235305590807320317692549 44119798276372559567353)
                      ·
                        rfl

theorem cell23_85923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_85923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85923 prefixEnd_85923 := by exact prefixLift 85923
  have htrace : WordTrace (prefixWord ++ tailWord_85923) baseStart_85923 baseEnd_85923 := by
    simpa [prefixWord, tailWord_85923, baseEnd_85923] using wordTrace_append hprefix tailTrace_85923
  have hstable : (prefixWord ++ tailWord_85923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85923).length < 2 ^ (prefixWord ++ tailWord_85923).sum := by decide
  have hdescent : baseEnd_85923 < baseStart_85923 := by decide
  rcases family_descends (prefixWord ++ tailWord_85923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85937 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 1, 5]
def baseStart_85937 : Nat := 118140960795 + 85937 * 2 ^ 59
def prefixEnd_85937 : Nat := 4983230072969 + 3 ^ 40 * 85937 * 2
def baseEnd_85937 : Nat := 14708995668511834930763

theorem tailTrace_85937 : CollatzResearch.WordTrace tailWord_85937 prefixEnd_85937 14708995668511834930763 := by
  unfold tailWord_85937
  simp only [CollatzResearch.WordTrace]
  refine ⟨3134379889672400716224065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2089586593114933810816043 3134379889672400716224065)
  ·
    refine ⟨2350784917254300537168049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3134379889672400716224065 2350784917254300537168049)
    ·
      refine ⟨1763088687940725402876037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2350784917254300537168049 1763088687940725402876037)
      ·
        refine ⟨330579128988886013039257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1763088687940725402876037 330579128988886013039257)
        ·
          refine ⟨247934346741664509779443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330579128988886013039257 247934346741664509779443)
          ·
            refine ⟨371901520112496764669165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247934346741664509779443 371901520112496764669165)
            ·
              refine ⟨139463070042186286750937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 371901520112496764669165 139463070042186286750937)
              ·
                refine ⟨104597302531639715063203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139463070042186286750937 104597302531639715063203)
                ·
                  refine ⟨156895953797459572594805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104597302531639715063203 156895953797459572594805)
                  ·
                    refine ⟨14708995668511834930763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 156895953797459572594805 14708995668511834930763)
                    ·
                      rfl

theorem cell23_85937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 5].length) (baseStart_85937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85937 prefixEnd_85937 := by exact prefixLift 85937
  have htrace : WordTrace (prefixWord ++ tailWord_85937) baseStart_85937 baseEnd_85937 := by
    simpa [prefixWord, tailWord_85937, baseEnd_85937] using wordTrace_append hprefix tailTrace_85937
  have hstable : (prefixWord ++ tailWord_85937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85937).length < 2 ^ (prefixWord ++ tailWord_85937).sum := by decide
  have hdescent : baseEnd_85937 < baseStart_85937 := by decide
  rcases family_descends (prefixWord ++ tailWord_85937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85950 : List Nat := [4, 2, 1, 1, 1, 3, 1, 1, 3, 6]
def baseStart_85950 : Nat := 118140960795 + 85950 * 2 ^ 59
def prefixEnd_85950 : Nat := 4983230072969 + 3 ^ 40 * 85950 * 2
def baseEnd_85950 : Nat := 14711220751347984643243

theorem tailTrace_85950 : CollatzResearch.WordTrace tailWord_85950 prefixEnd_85950 14711220751347984643243 := by
  unfold tailWord_85950
  simp only [CollatzResearch.WordTrace]
  refine ⟨391856754828162992055913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2089902692416869290964869 391856754828162992055913)
  ·
    refine ⟨293892566121122244041935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 391856754828162992055913 293892566121122244041935)
    ·
      refine ⟨440838849181683366062903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293892566121122244041935 440838849181683366062903)
      ·
        refine ⟨661258273772525049094355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440838849181683366062903 661258273772525049094355)
        ·
          refine ⟨991887410658787573641533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661258273772525049094355 991887410658787573641533)
          ·
            refine ⟨371957778997045340115575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 991887410658787573641533 371957778997045340115575)
            ·
              refine ⟨557936668495568010173363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371957778997045340115575 557936668495568010173363)
              ·
                refine ⟨836905002743352015260045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557936668495568010173363 836905002743352015260045)
                ·
                  refine ⟨313839376028757005722517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836905002743352015260045 313839376028757005722517)
                  ·
                    refine ⟨14711220751347984643243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 313839376028757005722517 14711220751347984643243)
                    ·
                      rfl

theorem cell23_85950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_85950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85950 prefixEnd_85950 := by exact prefixLift 85950
  have htrace : WordTrace (prefixWord ++ tailWord_85950) baseStart_85950 baseEnd_85950 := by
    simpa [prefixWord, tailWord_85950, baseEnd_85950] using wordTrace_append hprefix tailTrace_85950
  have hstable : (prefixWord ++ tailWord_85950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85950).length < 2 ^ (prefixWord ++ tailWord_85950).sum := by decide
  have hdescent : baseEnd_85950 < baseStart_85950 := by decide
  rcases family_descends (prefixWord ++ tailWord_85950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85957 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 7, 2, 2]
def baseStart_85957 : Nat := 118140960795 + 85957 * 2 ^ 59
def prefixEnd_85957 : Nat := 4983230072969 + 3 ^ 40 * 85957 * 2
def baseEnd_85957 : Nat := 44137256618625426542197

theorem tailTrace_85957 : CollatzResearch.WordTrace tailWord_85957 prefixEnd_85957 44137256618625426542197 := by
  unfold tailWord_85957
  simp only [CollatzResearch.WordTrace]
  refine ⟨3135109349599944131952125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2090072899733296087968083 3135109349599944131952125)
  ·
    refine ⟨1175666006099979049482047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3135109349599944131952125 1175666006099979049482047)
    ·
      refine ⟨1763499009149968574223071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1175666006099979049482047 1763499009149968574223071)
      ·
        refine ⟨2645248513724952861334607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763499009149968574223071 2645248513724952861334607)
        ·
          refine ⟨3967872770587429292001911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2645248513724952861334607 3967872770587429292001911)
          ·
            refine ⟨5951809155881143938002867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967872770587429292001911 5951809155881143938002867)
            ·
              refine ⟨8927713733821715907004301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5951809155881143938002867 8927713733821715907004301)
              ·
                refine ⟨3347892650183143465126613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8927713733821715907004301 3347892650183143465126613)
                ·
                  refine ⟨78466233988667424963905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3347892650183143465126613 78466233988667424963905)
                  ·
                    refine ⟨58849675491500568722929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78466233988667424963905 58849675491500568722929)
                    ·
                      refine ⟨44137256618625426542197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58849675491500568722929 44137256618625426542197)
                      ·
                        rfl

theorem cell23_85957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_85957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85957 prefixEnd_85957 := by exact prefixLift 85957
  have htrace : WordTrace (prefixWord ++ tailWord_85957) baseStart_85957 baseEnd_85957 := by
    simpa [prefixWord, tailWord_85957, baseEnd_85957] using wordTrace_append hprefix tailTrace_85957
  have hstable : (prefixWord ++ tailWord_85957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85957).length < 2 ^ (prefixWord ++ tailWord_85957).sum := by decide
  have hdescent : baseEnd_85957 < baseStart_85957 := by decide
  rcases family_descends (prefixWord ++ tailWord_85957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85967 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 2, 4]
def baseStart_85967 : Nat := 118140960795 + 85967 * 2 ^ 59
def prefixEnd_85967 : Nat := 4983230072969 + 3 ^ 40 * 85967 * 2
def baseEnd_85967 : Nat := 14714130475056795805717

theorem tailTrace_85967 : CollatzResearch.WordTrace tailWord_85967 prefixEnd_85967 14714130475056795805717 := by
  unfold tailWord_85967
  simp only [CollatzResearch.WordTrace]
  refine ⟨3135474079563715839816155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2090316053042477226544103 3135474079563715839816155)
  ·
    refine ⟨4703211119345573759724233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3135474079563715839816155 4703211119345573759724233)
    ·
      refine ⟨3527408339509180319793175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4703211119345573759724233 3527408339509180319793175)
      ·
        refine ⟨5291112509263770479689763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3527408339509180319793175 5291112509263770479689763)
        ·
          refine ⟨7936668763895655719534645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5291112509263770479689763 7936668763895655719534645)
          ·
            refine ⟨744062696615217723706373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7936668763895655719534645 744062696615217723706373)
            ·
              refine ⟨139511755615353323194945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 744062696615217723706373 139511755615353323194945)
              ·
                refine ⟨104633816711514992396209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139511755615353323194945 104633816711514992396209)
                ·
                  refine ⟨78475362533636244297157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104633816711514992396209 78475362533636244297157)
                  ·
                    refine ⟨14714130475056795805717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78475362533636244297157 14714130475056795805717)
                    ·
                      rfl

theorem cell23_85967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 4].length) (baseStart_85967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85967 prefixEnd_85967 := by exact prefixLift 85967
  have htrace : WordTrace (prefixWord ++ tailWord_85967) baseStart_85967 baseEnd_85967 := by
    simpa [prefixWord, tailWord_85967, baseEnd_85967] using wordTrace_append hprefix tailTrace_85967
  have hstable : (prefixWord ++ tailWord_85967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85967).length < 2 ^ (prefixWord ++ tailWord_85967).sum := by decide
  have hdescent : baseEnd_85967 < baseStart_85967 := by decide
  rcases family_descends (prefixWord ++ tailWord_85967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85987 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 4]
def baseStart_85987 : Nat := 118140960795 + 85987 * 2 ^ 59
def prefixEnd_85987 : Nat := 4983230072969 + 3 ^ 40 * 85987 * 2
def baseEnd_85987 : Nat := 44152661038260309167059

theorem tailTrace_85987 : CollatzResearch.WordTrace tailWord_85987 prefixEnd_85987 44152661038260309167059 := by
  unfold tailWord_85987
  simp only [CollatzResearch.WordTrace]
  refine ⟨3136203539491259255544215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2090802359660839503696143 3136203539491259255544215)
  ·
    refine ⟨4704305309236888883316323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3136203539491259255544215 4704305309236888883316323)
    ·
      refine ⟨7056457963855333324974485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4704305309236888883316323 7056457963855333324974485)
      ·
        refine ⟨330771467055718749608179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7056457963855333324974485 330771467055718749608179)
        ·
          refine ⟨496157200583578124412269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330771467055718749608179 496157200583578124412269)
          ·
            refine ⟨186058950218841796654601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 496157200583578124412269 186058950218841796654601)
            ·
              refine ⟨139544212664131347490951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186058950218841796654601 139544212664131347490951)
              ·
                refine ⟨209316318996197021236427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139544212664131347490951 209316318996197021236427)
                ·
                  refine ⟨313974478494295531854641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209316318996197021236427 313974478494295531854641)
                  ·
                    refine ⟨235480858870721648890981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 313974478494295531854641 235480858870721648890981)
                    ·
                      refine ⟨44152661038260309167059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 235480858870721648890981 44152661038260309167059)
                      ·
                        rfl

theorem cell23_85987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_85987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85987 prefixEnd_85987 := by exact prefixLift 85987
  have htrace : WordTrace (prefixWord ++ tailWord_85987) baseStart_85987 baseEnd_85987 := by
    simpa [prefixWord, tailWord_85987, baseEnd_85987] using wordTrace_append hprefix tailTrace_85987
  have hstable : (prefixWord ++ tailWord_85987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85987).length < 2 ^ (prefixWord ++ tailWord_85987).sum := by decide
  have hdescent : baseEnd_85987 < baseStart_85987 := by decide
  rcases family_descends (prefixWord ++ tailWord_85987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85991 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_85991 : Nat := 118140960795 + 85991 * 2 ^ 59
def prefixEnd_85991 : Nat := 4983230072969 + 3 ^ 40 * 85991 * 2
def baseEnd_85991 : Nat := 44154714960878293517041

theorem tailTrace_85991 : CollatzResearch.WordTrace tailWord_85991 prefixEnd_85991 44154714960878293517041 := by
  unfold tailWord_85991
  simp only [CollatzResearch.WordTrace]
  refine ⟨3136349431476767938689827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2090899620984511959126551 3136349431476767938689827)
  ·
    refine ⟨4704524147215151908034741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3136349431476767938689827 4704524147215151908034741)
    ·
      refine ⟨441049138801420491378257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4704524147215151908034741 441049138801420491378257)
      ·
        refine ⟨330786854101065368533693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441049138801420491378257 330786854101065368533693)
        ·
          refine ⟨124045070287899513200135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330786854101065368533693 124045070287899513200135)
          ·
            refine ⟨186067605431849269800203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124045070287899513200135 186067605431849269800203)
            ·
              refine ⟨279101408147773904700305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186067605431849269800203 279101408147773904700305)
              ·
                refine ⟨209326056110830428525229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279101408147773904700305 209326056110830428525229)
                ·
                  refine ⟨78497271041561410696961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209326056110830428525229 78497271041561410696961)
                  ·
                    refine ⟨58872953281171058022721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78497271041561410696961 58872953281171058022721)
                    ·
                      refine ⟨44154714960878293517041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58872953281171058022721 44154714960878293517041)
                      ·
                        rfl

theorem cell23_85991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_85991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_85991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_85991 prefixEnd_85991 := by exact prefixLift 85991
  have htrace : WordTrace (prefixWord ++ tailWord_85991) baseStart_85991 baseEnd_85991 := by
    simpa [prefixWord, tailWord_85991, baseEnd_85991] using wordTrace_append hprefix tailTrace_85991
  have hstable : (prefixWord ++ tailWord_85991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85991).length < 2 ^ (prefixWord ++ tailWord_85991).sum := by decide
  have hdescent : baseEnd_85991 < baseStart_85991 := by decide
  rcases family_descends (prefixWord ++ tailWord_85991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86040 : List Nat := [2, 1, 2, 3, 2, 1, 1, 3, 2, 6]
def baseStart_86040 : Nat := 118140960795 + 86040 * 2 ^ 59
def prefixEnd_86040 : Nat := 4983230072969 + 3 ^ 40 * 86040 * 2
def baseEnd_86040 : Nat := 14726625170982867268105

theorem tailTrace_86040 : CollatzResearch.WordTrace tailWord_86040 prefixEnd_86040 14726625170982867268105 := by
  unfold tailWord_86040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569068304149624653611787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2092091072199499538149049 1569068304149624653611787)
  ·
    refine ⟨2353602456224436980417681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1569068304149624653611787 2353602456224436980417681)
    ·
      refine ⟨1765201842168327735313261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2353602456224436980417681 1765201842168327735313261)
      ·
        refine ⟨661950690813122900742473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1765201842168327735313261 661950690813122900742473)
        ·
          refine ⟨496463018109842175556855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 661950690813122900742473 496463018109842175556855)
          ·
            refine ⟨744694527164763263335283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496463018109842175556855 744694527164763263335283)
            ·
              refine ⟨1117041790747144895002925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744694527164763263335283 1117041790747144895002925)
              ·
                refine ⟨418890671530179335626097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1117041790747144895002925 418890671530179335626097)
                ·
                  refine ⟨314168003647634501719573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418890671530179335626097 314168003647634501719573)
                  ·
                    refine ⟨14726625170982867268105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 314168003647634501719573 14726625170982867268105)
                    ·
                      rfl

theorem cell23_86040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_86040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86040 prefixEnd_86040 := by exact prefixLift 86040
  have htrace : WordTrace (prefixWord ++ tailWord_86040) baseStart_86040 baseEnd_86040 := by
    simpa [prefixWord, tailWord_86040, baseEnd_86040] using wordTrace_append hprefix tailTrace_86040
  have hstable : (prefixWord ++ tailWord_86040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86040).length < 2 ^ (prefixWord ++ tailWord_86040).sum := by decide
  have hdescent : baseEnd_86040 < baseStart_86040 := by decide
  rcases family_descends (prefixWord ++ tailWord_86040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86060 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_86060 : Nat := 118140960795 + 86060 * 2 ^ 59
def prefixEnd_86060 : Nat := 4983230072969 + 3 ^ 40 * 86060 * 2
def baseEnd_86060 : Nat := 44190145126038523554223

theorem tailTrace_86060 : CollatzResearch.WordTrace tailWord_86060 prefixEnd_86060 44190145126038523554223 := by
  unfold tailWord_86060
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569433034113396361475817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2092577378817861815301089 1569433034113396361475817)
  ·
    refine ⟨1177074775585047271106863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1569433034113396361475817 1177074775585047271106863)
    ·
      refine ⟨1765612163377570906660295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177074775585047271106863 1765612163377570906660295)
      ·
        refine ⟨2648418245066356359990443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765612163377570906660295 2648418245066356359990443)
        ·
          refine ⟨3972627367599534539985665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648418245066356359990443 3972627367599534539985665)
          ·
            refine ⟨2979470525699650904989249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3972627367599534539985665 2979470525699650904989249)
            ·
              refine ⟨2234602894274738178741937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2979470525699650904989249 2234602894274738178741937)
              ·
                refine ⟨1675952170706053634056453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2234602894274738178741937 1675952170706053634056453)
                ·
                  refine ⟨314241032007385056385585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1675952170706053634056453 314241032007385056385585)
                  ·
                    refine ⟨235680774005538792289189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 314241032007385056385585 235680774005538792289189)
                    ·
                      refine ⟨44190145126038523554223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 235680774005538792289189 44190145126038523554223)
                      ·
                        rfl

theorem cell23_86060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_86060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86060 prefixEnd_86060 := by exact prefixLift 86060
  have htrace : WordTrace (prefixWord ++ tailWord_86060) baseStart_86060 baseEnd_86060 := by
    simpa [prefixWord, tailWord_86060, baseEnd_86060] using wordTrace_append hprefix tailTrace_86060
  have hstable : (prefixWord ++ tailWord_86060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86060).length < 2 ^ (prefixWord ++ tailWord_86060).sum := by decide
  have hdescent : baseEnd_86060 < baseStart_86060 := by decide
  rcases family_descends (prefixWord ++ tailWord_86060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86064 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 4, 2, 2]
def baseStart_86064 : Nat := 118140960795 + 86064 * 2 ^ 59
def prefixEnd_86064 : Nat := 4983230072969 + 3 ^ 40 * 86064 * 2
def baseEnd_86064 : Nat := 44192199048656507904205

theorem tailTrace_86064 : CollatzResearch.WordTrace tailWord_86064 prefixEnd_86064 44192199048656507904205 := by
  unfold tailWord_86064
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569505980106150703048623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2092674640141534270731497 1569505980106150703048623)
  ·
    refine ⟨2354258970159226054572935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1569505980106150703048623 2354258970159226054572935)
    ·
      refine ⟨3531388455238839081859403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354258970159226054572935 3531388455238839081859403)
      ·
        refine ⟨5297082682858258622789105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531388455238839081859403 5297082682858258622789105)
        ·
          refine ⟨3972812012143693967091829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5297082682858258622789105 3972812012143693967091829)
          ·
            refine ⟨372451126138471309414859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3972812012143693967091829 372451126138471309414859)
            ·
              refine ⟨558676689207706964122289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372451126138471309414859 558676689207706964122289)
              ·
                refine ⟨419007516905780223091717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558676689207706964122289 419007516905780223091717)
                ·
                  refine ⟨78563909419833791829697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 419007516905780223091717 78563909419833791829697)
                  ·
                    refine ⟨58922932064875343872273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78563909419833791829697 58922932064875343872273)
                    ·
                      refine ⟨44192199048656507904205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58922932064875343872273 44192199048656507904205)
                      ·
                        rfl

theorem cell23_86064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 4, 2, 2].length) (baseStart_86064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86064 prefixEnd_86064 := by exact prefixLift 86064
  have htrace : WordTrace (prefixWord ++ tailWord_86064) baseStart_86064 baseEnd_86064 := by
    simpa [prefixWord, tailWord_86064, baseEnd_86064] using wordTrace_append hprefix tailTrace_86064
  have hstable : (prefixWord ++ tailWord_86064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86064).length < 2 ^ (prefixWord ++ tailWord_86064).sum := by decide
  have hdescent : baseEnd_86064 < baseStart_86064 := by decide
  rcases family_descends (prefixWord ++ tailWord_86064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86081 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_86081 : Nat := 118140960795 + 86081 * 2 ^ 59
def prefixEnd_86081 : Nat := 4983230072969 + 3 ^ 40 * 86081 * 2
def baseEnd_86081 : Nat := 44200928219782941391627

theorem tailTrace_86081 : CollatzResearch.WordTrace tailWord_86081 prefixEnd_86081 44200928219782941391627 := by
  unfold tailWord_86081
  simp only [CollatzResearch.WordTrace]
  refine ⟨3139632001150713309466097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2093088000767142206310731 3139632001150713309466097)
  ·
    refine ⟨2354724000863034982099573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3139632001150713309466097 2354724000863034982099573)
    ·
      refine ⟨220755375080909529571835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2354724000863034982099573 220755375080909529571835)
      ·
        refine ⟨331133062621364294357753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220755375080909529571835 331133062621364294357753)
        ·
          refine ⟨248349796966023220768315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 331133062621364294357753 248349796966023220768315)
          ·
            refine ⟨372524695449034831152473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248349796966023220768315 372524695449034831152473)
            ·
              refine ⟨279393521586776123364355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372524695449034831152473 279393521586776123364355)
              ·
                refine ⟨419090282380164185046533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279393521586776123364355 419090282380164185046533)
                ·
                  refine ⟨78579427946280784696225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 419090282380164185046533 78579427946280784696225)
                  ·
                    refine ⟨58934570959710588522169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78579427946280784696225 58934570959710588522169)
                    ·
                      refine ⟨44200928219782941391627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58934570959710588522169 44200928219782941391627)
                      ·
                        rfl

theorem cell23_86081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_86081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86081 prefixEnd_86081 := by exact prefixLift 86081
  have htrace : WordTrace (prefixWord ++ tailWord_86081) baseStart_86081 baseEnd_86081 := by
    simpa [prefixWord, tailWord_86081, baseEnd_86081] using wordTrace_append hprefix tailTrace_86081
  have hstable : (prefixWord ++ tailWord_86081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86081).length < 2 ^ (prefixWord ++ tailWord_86081).sum := by decide
  have hdescent : baseEnd_86081 < baseStart_86081 := by decide
  rcases family_descends (prefixWord ++ tailWord_86081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86098 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_86098 : Nat := 118140960795 + 86098 * 2 ^ 59
def prefixEnd_86098 : Nat := 4983230072969 + 3 ^ 40 * 86098 * 2
def baseEnd_86098 : Nat := 44209657390909374879049

theorem tailTrace_86098 : CollatzResearch.WordTrace tailWord_86098 prefixEnd_86098 44209657390909374879049 := by
  unfold tailWord_86098
  simp only [CollatzResearch.WordTrace]
  refine ⟨785063010522281303208737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2093501361392750141889965 785063010522281303208737)
  ·
    refine ⟨588797257891710977406553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 785063010522281303208737 588797257891710977406553)
    ·
      refine ⟨441597943418783233054915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 588797257891710977406553 441597943418783233054915)
      ·
        refine ⟨662396915128174849582373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441597943418783233054915 662396915128174849582373)
        ·
          refine ⟨124199421586532784296695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 662396915128174849582373 124199421586532784296695)
          ·
            refine ⟨186299132379799176445043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124199421586532784296695 186299132379799176445043)
            ·
              refine ⟨279448698569698764667565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186299132379799176445043 279448698569698764667565)
              ·
                refine ⟨104793261963637036750337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 279448698569698764667565 104793261963637036750337)
                ·
                  refine ⟨78594946472727777562753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104793261963637036750337 78594946472727777562753)
                  ·
                    refine ⟨58946209854545833172065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78594946472727777562753 58946209854545833172065)
                    ·
                      refine ⟨44209657390909374879049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58946209854545833172065 44209657390909374879049)
                      ·
                        rfl

theorem cell23_86098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_86098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86098 prefixEnd_86098 := by exact prefixLift 86098
  have htrace : WordTrace (prefixWord ++ tailWord_86098) baseStart_86098 baseEnd_86098 := by
    simpa [prefixWord, tailWord_86098, baseEnd_86098] using wordTrace_append hprefix tailTrace_86098
  have hstable : (prefixWord ++ tailWord_86098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86098).length < 2 ^ (prefixWord ++ tailWord_86098).sum := by decide
  have hdescent : baseEnd_86098 < baseStart_86098 := by decide
  rcases family_descends (prefixWord ++ tailWord_86098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86117 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_86117 : Nat := 118140960795 + 86117 * 2 ^ 59
def prefixEnd_86117 : Nat := 4983230072969 + 3 ^ 40 * 86117 * 2
def baseEnd_86117 : Nat := 14739804507781600180487

theorem tailTrace_86117 : CollatzResearch.WordTrace tailWord_86117 prefixEnd_86117 14739804507781600180487 := by
  unfold tailWord_86117
  simp only [CollatzResearch.WordTrace]
  refine ⟨3140945029020291457776605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2093963352680194305184403 3140945029020291457776605)
  ·
    refine ⟨1177854385882609296666227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3140945029020291457776605 1177854385882609296666227)
    ·
      refine ⟨1766781578823913944999341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177854385882609296666227 1766781578823913944999341)
      ·
        refine ⟨662543092058967729374753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1766781578823913944999341 662543092058967729374753)
        ·
          refine ⟨496907319044225797031065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662543092058967729374753 496907319044225797031065)
          ·
            refine ⟨372680489283169347773299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496907319044225797031065 372680489283169347773299)
            ·
              refine ⟨559020733924754021659949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372680489283169347773299 559020733924754021659949)
              ·
                refine ⟨209632775221782758122481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559020733924754021659949 209632775221782758122481)
                ·
                  refine ⟨157224581416337068591861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209632775221782758122481 157224581416337068591861)
                  ·
                    refine ⟨14739804507781600180487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 157224581416337068591861 14739804507781600180487)
                    ·
                      rfl

theorem cell23_86117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_86117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86117 prefixEnd_86117 := by exact prefixLift 86117
  have htrace : WordTrace (prefixWord ++ tailWord_86117) baseStart_86117 baseEnd_86117 := by
    simpa [prefixWord, tailWord_86117, baseEnd_86117] using wordTrace_append hprefix tailTrace_86117
  have hstable : (prefixWord ++ tailWord_86117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86117).length < 2 ^ (prefixWord ++ tailWord_86117).sum := by decide
  have hdescent : baseEnd_86117 < baseStart_86117 := by decide
  rcases family_descends (prefixWord ++ tailWord_86117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86134 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_86134 : Nat := 118140960795 + 86134 * 2 ^ 59
def prefixEnd_86134 : Nat := 4983230072969 + 3 ^ 40 * 86134 * 2
def baseEnd_86134 : Nat := 14742714231490411342961

theorem tailTrace_86134 : CollatzResearch.WordTrace tailWord_86134 prefixEnd_86134 14742714231490411342961 := by
  unfold tailWord_86134
  simp only [CollatzResearch.WordTrace]
  refine ⟨196347816872418960071591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2094376713305802240763637 196347816872418960071591)
  ·
    refine ⟨294521725308628440107387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 196347816872418960071591 294521725308628440107387)
    ·
      refine ⟨441782587962942660161081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294521725308628440107387 441782587962942660161081)
      ·
        refine ⟨331336940972206995120811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441782587962942660161081 331336940972206995120811)
        ·
          refine ⟨497005411458310492681217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331336940972206995120811 497005411458310492681217)
          ·
            refine ⟨372754058593732869510913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497005411458310492681217 372754058593732869510913)
            ·
              refine ⟨279565543945299652133185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372754058593732869510913 279565543945299652133185)
              ·
                refine ⟨209674157958974739099889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279565543945299652133185 209674157958974739099889)
                ·
                  refine ⟨157255618469231054324917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209674157958974739099889 157255618469231054324917)
                  ·
                    refine ⟨14742714231490411342961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 157255618469231054324917 14742714231490411342961)
                    ·
                      rfl

theorem cell23_86134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_86134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86134 prefixEnd_86134 := by exact prefixLift 86134
  have htrace : WordTrace (prefixWord ++ tailWord_86134) baseStart_86134 baseEnd_86134 := by
    simpa [prefixWord, tailWord_86134, baseEnd_86134] using wordTrace_append hprefix tailTrace_86134
  have hstable : (prefixWord ++ tailWord_86134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86134).length < 2 ^ (prefixWord ++ tailWord_86134).sum := by decide
  have hdescent : baseEnd_86134 < baseStart_86134 := by decide
  rcases family_descends (prefixWord ++ tailWord_86134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86154 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2]
def baseStart_86154 : Nat := 118140960795 + 86154 * 2 ^ 59
def prefixEnd_86154 : Nat := 4983230072969 + 3 ^ 40 * 86154 * 2
def baseEnd_86154 : Nat := 44238412307561155778791

theorem tailTrace_86154 : CollatzResearch.WordTrace tailWord_86154 prefixEnd_86154 44238412307561155778791 := by
  unfold tailWord_86154
  simp only [CollatzResearch.WordTrace]
  refine ⟨785573632471561694218379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2094863019924164517915677 785573632471561694218379)
  ·
    refine ⟨1178360448707342541327569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 785573632471561694218379 1178360448707342541327569)
    ·
      refine ⟨883770336530506905995677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1178360448707342541327569 883770336530506905995677)
      ·
        refine ⟨331413876198940089748379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 883770336530506905995677 331413876198940089748379)
        ·
          refine ⟨497120814298410134622569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331413876198940089748379 497120814298410134622569)
          ·
            refine ⟨372840610723807600966927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497120814298410134622569 372840610723807600966927)
            ·
              refine ⟨559260916085711401450391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372840610723807600966927 559260916085711401450391)
              ·
                refine ⟨838891374128567102175587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559260916085711401450391 838891374128567102175587)
                ·
                  refine ⟨1258337061192850653263381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838891374128567102175587 1258337061192850653263381)
                  ·
                    refine ⟨58984549743414874371721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1258337061192850653263381 58984549743414874371721)
                    ·
                      refine ⟨44238412307561155778791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 58984549743414874371721 44238412307561155778791)
                      ·
                        rfl

theorem cell23_86154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_86154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86154 prefixEnd_86154 := by exact prefixLift 86154
  have htrace : WordTrace (prefixWord ++ tailWord_86154) baseStart_86154 baseEnd_86154 := by
    simpa [prefixWord, tailWord_86154, baseEnd_86154] using wordTrace_append hprefix tailTrace_86154
  have hstable : (prefixWord ++ tailWord_86154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86154).length < 2 ^ (prefixWord ++ tailWord_86154).sum := by decide
  have hdescent : baseEnd_86154 < baseStart_86154 := by decide
  rcases family_descends (prefixWord ++ tailWord_86154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86181 : List Nat := [1, 3, 1, 2, 1, 3, 4, 3, 1, 4]
def baseStart_86181 : Nat := 118140960795 + 86181 * 2 ^ 59
def prefixEnd_86181 : Nat := 4983230072969 + 3 ^ 40 * 86181 * 2
def baseEnd_86181 : Nat := 14750758761744183380389

theorem tailTrace_86181 : CollatzResearch.WordTrace tailWord_86181 prefixEnd_86181 14750758761744183380389 := by
  unfold tailWord_86181
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143279300788430388106397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2095519533858953592070931 3143279300788430388106397)
  ·
    refine ⟨1178729737795661395539899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3143279300788430388106397 1178729737795661395539899)
    ·
      refine ⟨1768094606693492093309849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1178729737795661395539899 1768094606693492093309849)
      ·
        refine ⟨1326070955020119069982387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1768094606693492093309849 1326070955020119069982387)
        ·
          refine ⟨1989106432530178604973581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326070955020119069982387 1989106432530178604973581)
          ·
            refine ⟨745914912198816976865093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1989106432530178604973581 745914912198816976865093)
            ·
              refine ⟨139859046037278183162205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 745914912198816976865093 139859046037278183162205)
              ·
                refine ⟨52447142263979318685827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139859046037278183162205 52447142263979318685827)
                ·
                  refine ⟨78670713395968978028741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52447142263979318685827 78670713395968978028741)
                  ·
                    refine ⟨14750758761744183380389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78670713395968978028741 14750758761744183380389)
                    ·
                      rfl

theorem cell23_86181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_86181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86181 prefixEnd_86181 := by exact prefixLift 86181
  have htrace : WordTrace (prefixWord ++ tailWord_86181) baseStart_86181 baseEnd_86181 := by
    simpa [prefixWord, tailWord_86181, baseEnd_86181] using wordTrace_append hprefix tailTrace_86181
  have hstable : (prefixWord ++ tailWord_86181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86181).length < 2 ^ (prefixWord ++ tailWord_86181).sum := by decide
  have hdescent : baseEnd_86181 < baseStart_86181 := by decide
  rcases family_descends (prefixWord ++ tailWord_86181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86255 : List Nat := [1, 1, 2, 1, 6, 2, 3, 2, 1, 1, 3]
def baseStart_86255 : Nat := 118140960795 + 86255 * 2 ^ 59
def prefixEnd_86255 : Nat := 4983230072969 + 3 ^ 40 * 86255 * 2
def baseEnd_86255 : Nat := 44290273853665260615827

theorem tailTrace_86255 : CollatzResearch.WordTrace tailWord_86255 prefixEnd_86255 44290273853665260615827 := by
  unfold tailWord_86255
  simp only [CollatzResearch.WordTrace]
  refine ⟨3145978302520341026300219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2097318868346894017533479 3145978302520341026300219)
  ·
    refine ⟨4718967453780511539450329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3145978302520341026300219 4718967453780511539450329)
    ·
      refine ⟨3539225590335383654587747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4718967453780511539450329 3539225590335383654587747)
      ·
        refine ⟨5308838385503075481881621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3539225590335383654587747 5308838385503075481881621)
        ·
          refine ⟨248851799320456663213201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5308838385503075481881621 248851799320456663213201)
          ·
            refine ⟨186638849490342497409901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 248851799320456663213201 186638849490342497409901)
            ·
              refine ⟨69989568558878436528713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186638849490342497409901 69989568558878436528713)
              ·
                refine ⟨52492176419158827396535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69989568558878436528713 52492176419158827396535)
                ·
                  refine ⟨78738264628738241094803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52492176419158827396535 78738264628738241094803)
                  ·
                    refine ⟨118107396943107361642205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78738264628738241094803 118107396943107361642205)
                    ·
                      refine ⟨44290273853665260615827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 118107396943107361642205 44290273853665260615827)
                      ·
                        rfl

theorem cell23_86255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 1, 1, 3].length) (baseStart_86255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86255 prefixEnd_86255 := by exact prefixLift 86255
  have htrace : WordTrace (prefixWord ++ tailWord_86255) baseStart_86255 baseEnd_86255 := by
    simpa [prefixWord, tailWord_86255, baseEnd_86255] using wordTrace_append hprefix tailTrace_86255
  have hstable : (prefixWord ++ tailWord_86255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86255).length < 2 ^ (prefixWord ++ tailWord_86255).sum := by decide
  have hdescent : baseEnd_86255 < baseStart_86255 := by decide
  rcases family_descends (prefixWord ++ tailWord_86255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86257 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 6]
def baseStart_86257 : Nat := 118140960795 + 86257 * 2 ^ 59
def prefixEnd_86257 : Nat := 4983230072969 + 3 ^ 40 * 86257 * 2
def baseEnd_86257 : Nat := 44291300814974252790817

theorem tailTrace_86257 : CollatzResearch.WordTrace tailWord_86257 prefixEnd_86257 44291300814974252790817 := by
  unfold tailWord_86257
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146051248513095367873025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2097367499008730245248683 3146051248513095367873025)
  ·
    refine ⟨2359538436384821525904769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3146051248513095367873025 2359538436384821525904769)
    ·
      refine ⟨1769653827288616144428577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2359538436384821525904769 1769653827288616144428577)
      ·
        refine ⟨1327240370466462108321433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1769653827288616144428577 1327240370466462108321433)
        ·
          refine ⟨995430277849846581241075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1327240370466462108321433 995430277849846581241075)
          ·
            refine ⟨1493145416774769871861613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995430277849846581241075 1493145416774769871861613)
            ·
              refine ⟨559929531290538701948105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493145416774769871861613 559929531290538701948105)
              ·
                refine ⟨419947148467904026461079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 559929531290538701948105 419947148467904026461079)
                ·
                  refine ⟨629920722701856039691619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419947148467904026461079 629920722701856039691619)
                  ·
                    refine ⟨944881084052784059537429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 629920722701856039691619 944881084052784059537429)
                    ·
                      refine ⟨44291300814974252790817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 944881084052784059537429 44291300814974252790817)
                      ·
                        rfl

theorem cell23_86257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_86257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86257 prefixEnd_86257 := by exact prefixLift 86257
  have htrace : WordTrace (prefixWord ++ tailWord_86257) baseStart_86257 baseEnd_86257 := by
    simpa [prefixWord, tailWord_86257, baseEnd_86257] using wordTrace_append hprefix tailTrace_86257
  have hstable : (prefixWord ++ tailWord_86257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86257).length < 2 ^ (prefixWord ++ tailWord_86257).sum := by decide
  have hdescent : baseEnd_86257 < baseStart_86257 := by decide
  rcases family_descends (prefixWord ++ tailWord_86257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86281 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 1, 2, 3]
def baseStart_86281 : Nat := 118140960795 + 86281 * 2 ^ 59
def prefixEnd_86281 : Nat := 4983230072969 + 3 ^ 40 * 86281 * 2
def baseEnd_86281 : Nat := 44303624350682158890707

theorem tailTrace_86281 : CollatzResearch.WordTrace tailWord_86281 prefixEnd_86281 44303624350682158890707 := by
  unfold tailWord_86281
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146926600426147466746697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2097951066950764977831131 3146926600426147466746697)
  ·
    refine ⟨2360194950319610600060023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3146926600426147466746697 2360194950319610600060023)
    ·
      refine ⟨3540292425479415900090035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360194950319610600060023 3540292425479415900090035)
      ·
        refine ⟨5310438638219123850135053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3540292425479415900090035 5310438638219123850135053)
        ·
          refine ⟨1991414489332171443800645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5310438638219123850135053 1991414489332171443800645)
          ·
            refine ⟨373390216749782145712621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1991414489332171443800645 373390216749782145712621)
            ·
              refine ⟨140021331281168304642233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373390216749782145712621 140021331281168304642233)
              ·
                refine ⟨105015998460876228481675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140021331281168304642233 105015998460876228481675)
                ·
                  refine ⟨157523997691314342722513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105015998460876228481675 157523997691314342722513)
                  ·
                    refine ⟨118142998268485757041885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157523997691314342722513 118142998268485757041885)
                    ·
                      refine ⟨44303624350682158890707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 118142998268485757041885 44303624350682158890707)
                      ·
                        rfl

theorem cell23_86281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 1, 2, 3].length) (baseStart_86281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86281 prefixEnd_86281 := by exact prefixLift 86281
  have htrace : WordTrace (prefixWord ++ tailWord_86281) baseStart_86281 baseEnd_86281 := by
    simpa [prefixWord, tailWord_86281, baseEnd_86281] using wordTrace_append hprefix tailTrace_86281
  have hstable : (prefixWord ++ tailWord_86281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86281).length < 2 ^ (prefixWord ++ tailWord_86281).sum := by decide
  have hdescent : baseEnd_86281 < baseStart_86281 := by decide
  rcases family_descends (prefixWord ++ tailWord_86281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86298 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5]
def baseStart_86298 : Nat := 118140960795 + 86298 * 2 ^ 59
def prefixEnd_86298 : Nat := 4983230072969 + 3 ^ 40 * 86298 * 2
def baseEnd_86298 : Nat := 44312353521808592378129

theorem tailTrace_86298 : CollatzResearch.WordTrace tailWord_86298 prefixEnd_86298 44312353521808592378129 := by
  unfold tailWord_86298
  simp only [CollatzResearch.WordTrace]
  refine ⟨786886660341139842528887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2098364427576372913410365 786886660341139842528887)
  ·
    refine ⟨1180329990511709763793331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 786886660341139842528887 1180329990511709763793331)
    ·
      refine ⟨1770494985767564645689997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180329990511709763793331 1770494985767564645689997)
      ·
        refine ⟨663935619662836742133749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1770494985767564645689997 663935619662836742133749)
        ·
          refine ⟨62243964343390944575039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 663935619662836742133749 62243964343390944575039)
          ·
            refine ⟨93365946515086416862559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62243964343390944575039 93365946515086416862559)
            ·
              refine ⟨140048919772629625293839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93365946515086416862559 140048919772629625293839)
              ·
                refine ⟨210073379658944437940759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140048919772629625293839 210073379658944437940759)
                ·
                  refine ⟨315110069488416656911139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210073379658944437940759 315110069488416656911139)
                  ·
                    refine ⟨472665104232624985366709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 315110069488416656911139 472665104232624985366709)
                    ·
                      refine ⟨44312353521808592378129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 472665104232624985366709 44312353521808592378129)
                      ·
                        rfl

theorem cell23_86298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_86298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86298 prefixEnd_86298 := by exact prefixLift 86298
  have htrace : WordTrace (prefixWord ++ tailWord_86298) baseStart_86298 baseEnd_86298 := by
    simpa [prefixWord, tailWord_86298, baseEnd_86298] using wordTrace_append hprefix tailTrace_86298
  have hstable : (prefixWord ++ tailWord_86298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86298).length < 2 ^ (prefixWord ++ tailWord_86298).sum := by decide
  have hdescent : baseEnd_86298 < baseStart_86298 := by decide
  rcases family_descends (prefixWord ++ tailWord_86298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86312 : List Nat := [2, 1, 5, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_86312 : Nat := 118140960795 + 86312 * 2 ^ 59
def prefixEnd_86312 : Nat := 4983230072969 + 3 ^ 40 * 86312 * 2
def baseEnd_86312 : Nat := 44319542250971537603065

theorem tailTrace_86312 : CollatzResearch.WordTrace tailWord_86312 prefixEnd_86312 44319542250971537603065 := by
  unfold tailWord_86312
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574028631656919880562595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2098704842209226507416793 1574028631656919880562595)
  ·
    refine ⟨2361042947485379820843893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1574028631656919880562595 2361042947485379820843893)
    ·
      refine ⟨221347776326754358204115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2361042947485379820843893 221347776326754358204115)
      ·
        refine ⟨332021664490131537306173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221347776326754358204115 332021664490131537306173)
        ·
          refine ⟨124508124183799326489815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 332021664490131537306173 124508124183799326489815)
          ·
            refine ⟨186762186275698989734723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124508124183799326489815 186762186275698989734723)
            ·
              refine ⟨280143279413548484602085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186762186275698989734723 280143279413548484602085)
              ·
                refine ⟨52526864890040340862891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280143279413548484602085 52526864890040340862891)
                ·
                  refine ⟨78790297335060511294337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52526864890040340862891 78790297335060511294337)
                  ·
                    refine ⟨59092723001295383470753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78790297335060511294337 59092723001295383470753)
                    ·
                      refine ⟨44319542250971537603065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 59092723001295383470753 44319542250971537603065)
                      ·
                        rfl

theorem cell23_86312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_86312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86312 prefixEnd_86312 := by exact prefixLift 86312
  have htrace : WordTrace (prefixWord ++ tailWord_86312) baseStart_86312 baseEnd_86312 := by
    simpa [prefixWord, tailWord_86312, baseEnd_86312] using wordTrace_append hprefix tailTrace_86312
  have hstable : (prefixWord ++ tailWord_86312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86312).length < 2 ^ (prefixWord ++ tailWord_86312).sum := by decide
  have hdescent : baseEnd_86312 < baseStart_86312 := by decide
  rcases family_descends (prefixWord ++ tailWord_86312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86318 : List Nat := [4, 1, 3, 3, 1, 2, 1, 8]
def baseStart_86318 : Nat := 118140960795 + 86318 * 2 ^ 59
def prefixEnd_86318 : Nat := 4983230072969 + 3 ^ 40 * 86318 * 2
def baseEnd_86318 : Nat := 1641578634625870893631

theorem tailTrace_86318 : CollatzResearch.WordTrace tailWord_86318 prefixEnd_86318 1641578634625870893631 := by
  unfold tailWord_86318
  simp only [CollatzResearch.WordTrace]
  refine ⟨393534512661512848230451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2098850734194735190562405 393534512661512848230451)
  ·
    refine ⟨590301768992269272345677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 393534512661512848230451 590301768992269272345677)
    ·
      refine ⟨221363163372100977129629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 590301768992269272345677 221363163372100977129629)
      ·
        refine ⟨83011186264537866423611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221363163372100977129629 83011186264537866423611)
        ·
          refine ⟨124516779396806799635417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83011186264537866423611 124516779396806799635417)
          ·
            refine ⟨93387584547605099726563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124516779396806799635417 93387584547605099726563)
            ·
              refine ⟨140081376821407649589845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93387584547605099726563 140081376821407649589845)
              ·
                refine ⟨1641578634625870893631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 140081376821407649589845 1641578634625870893631)
                ·
                  rfl

theorem cell23_86318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_86318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86318 prefixEnd_86318 := by exact prefixLift 86318
  have htrace : WordTrace (prefixWord ++ tailWord_86318) baseStart_86318 baseEnd_86318 := by
    simpa [prefixWord, tailWord_86318, baseEnd_86318] using wordTrace_append hprefix tailTrace_86318
  have hstable : (prefixWord ++ tailWord_86318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86318).length < 2 ^ (prefixWord ++ tailWord_86318).sum := by decide
  have hdescent : baseEnd_86318 < baseStart_86318 := by decide
  rcases family_descends (prefixWord ++ tailWord_86318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86354 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_86354 : Nat := 118140960795 + 86354 * 2 ^ 59
def prefixEnd_86354 : Nat := 4983230072969 + 3 ^ 40 * 86354 * 2
def baseEnd_86354 : Nat := 44341108438460373277871

theorem tailTrace_86354 : CollatzResearch.WordTrace tailWord_86354 prefixEnd_86354 44341108438460373277871 := by
  unfold tailWord_86354
  simp only [CollatzResearch.WordTrace]
  refine ⟨787397282290420233538529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2099726086107787289436077 787397282290420233538529)
  ·
    refine ⟨590547961717815175153897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 787397282290420233538529 590547961717815175153897)
    ·
      refine ⟨442910971288361381365423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 590547961717815175153897 442910971288361381365423)
      ·
        refine ⟨664366456932542072048135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 442910971288361381365423 664366456932542072048135)
        ·
          refine ⟨996549685398813108072203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664366456932542072048135 996549685398813108072203)
          ·
            refine ⟨1494824528098219662108305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996549685398813108072203 1494824528098219662108305)
            ·
              refine ⟨1121118396073664746581229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494824528098219662108305 1121118396073664746581229)
              ·
                refine ⟨420419398527624279967961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1121118396073664746581229 420419398527624279967961)
                ·
                  refine ⟨315314548895718209975971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420419398527624279967961 315314548895718209975971)
                  ·
                    refine ⟨472971823343577314963957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 315314548895718209975971 472971823343577314963957)
                    ·
                      refine ⟨44341108438460373277871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 472971823343577314963957 44341108438460373277871)
                      ·
                        rfl

theorem cell23_86354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_86354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86354 prefixEnd_86354 := by exact prefixLift 86354
  have htrace : WordTrace (prefixWord ++ tailWord_86354) baseStart_86354 baseEnd_86354 := by
    simpa [prefixWord, tailWord_86354, baseEnd_86354] using wordTrace_append hprefix tailTrace_86354
  have hstable : (prefixWord ++ tailWord_86354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86354).length < 2 ^ (prefixWord ++ tailWord_86354).sum := by decide
  have hdescent : baseEnd_86354 < baseStart_86354 := by decide
  rcases family_descends (prefixWord ++ tailWord_86354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86404 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_86404 : Nat := 118140960795 + 86404 * 2 ^ 59
def prefixEnd_86404 : Nat := 4983230072969 + 3 ^ 40 * 86404 * 2
def baseEnd_86404 : Nat := 14788927490395059217547

theorem tailTrace_86404 : CollatzResearch.WordTrace tailWord_86404 prefixEnd_86404 14788927490395059217547 := by
  unfold tailWord_86404
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575706389490269736737133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2100941852653692982316177 1575706389490269736737133)
  ·
    refine ⟨590889896058851151276425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1575706389490269736737133 590889896058851151276425)
    ·
      refine ⟨443167422044138363457319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 590889896058851151276425 443167422044138363457319)
      ·
        refine ⟨664751133066207545185979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443167422044138363457319 664751133066207545185979)
        ·
          refine ⟨997126699599311317778969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664751133066207545185979 997126699599311317778969)
          ·
            refine ⟨747845024699483488334227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 997126699599311317778969 747845024699483488334227)
            ·
              refine ⟨1121767537049225232501341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747845024699483488334227 1121767537049225232501341)
              ·
                refine ⟨420662826393459462188003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1121767537049225232501341 420662826393459462188003)
                ·
                  refine ⟨630994239590189193282005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420662826393459462188003 630994239590189193282005)
                  ·
                    refine ⟨14788927490395059217547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 630994239590189193282005 14788927490395059217547)
                    ·
                      rfl

theorem cell23_86404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_86404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86404 prefixEnd_86404 := by exact prefixLift 86404
  have htrace : WordTrace (prefixWord ++ tailWord_86404) baseStart_86404 baseEnd_86404 := by
    simpa [prefixWord, tailWord_86404, baseEnd_86404] using wordTrace_append hprefix tailTrace_86404
  have hstable : (prefixWord ++ tailWord_86404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86404).length < 2 ^ (prefixWord ++ tailWord_86404).sum := by decide
  have hdescent : baseEnd_86404 < baseStart_86404 := by decide
  rcases family_descends (prefixWord ++ tailWord_86404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86441 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 2, 4, 2]
def baseStart_86441 : Nat := 118140960795 + 86441 * 2 ^ 59
def prefixEnd_86441 : Nat := 4983230072969 + 3 ^ 40 * 86441 * 2
def baseEnd_86441 : Nat := 44385781255401532889971

theorem tailTrace_86441 : CollatzResearch.WordTrace tailWord_86441 prefixEnd_86441 44385781255401532889971 := by
  unfold tailWord_86441
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152762279846494792571177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2101841519897663195047451 3152762279846494792571177)
  ·
    refine ⟨2364571709884871094428383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3152762279846494792571177 2364571709884871094428383)
    ·
      refine ⟨3546857564827306641642575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364571709884871094428383 3546857564827306641642575)
      ·
        refine ⟨5320286347240959962463863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546857564827306641642575 5320286347240959962463863)
        ·
          refine ⟨7980429520861439943695795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320286347240959962463863 7980429520861439943695795)
          ·
            refine ⟨11970644281292159915543693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7980429520861439943695795 11970644281292159915543693)
            ·
              refine ⟨4488991605484559968328885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11970644281292159915543693 4488991605484559968328885)
              ·
                refine ⟨420842963014177497030833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4488991605484559968328885 420842963014177497030833)
                ·
                  refine ⟨315632222260633122773125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420842963014177497030833 315632222260633122773125)
                  ·
                    refine ⟨59181041673868710519961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315632222260633122773125 59181041673868710519961)
                    ·
                      refine ⟨44385781255401532889971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 59181041673868710519961 44385781255401532889971)
                      ·
                        rfl

theorem cell23_86441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 4, 2].length) (baseStart_86441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86441 prefixEnd_86441 := by exact prefixLift 86441
  have htrace : WordTrace (prefixWord ++ tailWord_86441) baseStart_86441 baseEnd_86441 := by
    simpa [prefixWord, tailWord_86441, baseEnd_86441] using wordTrace_append hprefix tailTrace_86441
  have hstable : (prefixWord ++ tailWord_86441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86441).length < 2 ^ (prefixWord ++ tailWord_86441).sum := by decide
  have hdescent : baseEnd_86441 < baseStart_86441 := by decide
  rcases family_descends (prefixWord ++ tailWord_86441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86485 : List Nat := [1, 3, 2, 3, 1, 3, 1, 4, 1, 4]
def baseStart_86485 : Nat := 118140960795 + 86485 * 2 ^ 59
def prefixEnd_86485 : Nat := 4983230072969 + 3 ^ 40 * 86485 * 2
def baseEnd_86485 : Nat := 14802791468066453579923

theorem tailTrace_86485 : CollatzResearch.WordTrace tailWord_86485 prefixEnd_86485 14802791468066453579923 := by
  unfold tailWord_86485
  simp only [CollatzResearch.WordTrace]
  refine ⟨3154367091687090307172909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2102911394458060204781939 3154367091687090307172909)
  ·
    refine ⟨1182887659382658865189841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3154367091687090307172909 1182887659382658865189841)
    ·
      refine ⟨887165744536994148892381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1182887659382658865189841 887165744536994148892381)
      ·
        refine ⟨332687154201372805834643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 887165744536994148892381 332687154201372805834643)
        ·
          refine ⟨499030731302059208751965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332687154201372805834643 499030731302059208751965)
          ·
            refine ⟨187136524238272203281987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 499030731302059208751965 187136524238272203281987)
            ·
              refine ⟨280704786357408304922981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187136524238272203281987 280704786357408304922981)
              ·
                refine ⟨52632147442014057173059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280704786357408304922981 52632147442014057173059)
                ·
                  refine ⟨78948221163021085759589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52632147442014057173059 78948221163021085759589)
                  ·
                    refine ⟨14802791468066453579923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78948221163021085759589 14802791468066453579923)
                    ·
                      rfl

theorem cell23_86485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_86485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86485 prefixEnd_86485 := by exact prefixLift 86485
  have htrace : WordTrace (prefixWord ++ tailWord_86485) baseStart_86485 baseEnd_86485 := by
    simpa [prefixWord, tailWord_86485, baseEnd_86485] using wordTrace_append hprefix tailTrace_86485
  have hstable : (prefixWord ++ tailWord_86485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86485).length < 2 ^ (prefixWord ++ tailWord_86485).sum := by decide
  have hdescent : baseEnd_86485 < baseStart_86485 := by decide
  rcases family_descends (prefixWord ++ tailWord_86485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86508 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 3]
def baseStart_86508 : Nat := 118140960795 + 86508 * 2 ^ 59
def prefixEnd_86508 : Nat := 4983230072969 + 3 ^ 40 * 86508 * 2
def baseEnd_86508 : Nat := 44420184459252770752163

theorem tailTrace_86508 : CollatzResearch.WordTrace tailWord_86508 prefixEnd_86508 44420184459252770752163 := by
  unfold tailWord_86508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1577602985301882617630089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2103470647069176823506785 1577602985301882617630089)
  ·
    refine ⟨1183202238976411963222567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1577602985301882617630089 1183202238976411963222567)
    ·
      refine ⟨1774803358464617944833851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1183202238976411963222567 1774803358464617944833851)
      ·
        refine ⟨2662205037696926917250777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1774803358464617944833851 2662205037696926917250777)
        ·
          refine ⟨1996653778272695187938083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2662205037696926917250777 1996653778272695187938083)
          ·
            refine ⟨2994980667409042781907125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1996653778272695187938083 2994980667409042781907125)
            ·
              refine ⟨280779437569597760803793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2994980667409042781907125 280779437569597760803793)
              ·
                refine ⟨210584578177198320602845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280779437569597760803793 210584578177198320602845)
                ·
                  refine ⟨78969216816449370226067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210584578177198320602845 78969216816449370226067)
                  ·
                    refine ⟨118453825224674055339101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78969216816449370226067 118453825224674055339101)
                    ·
                      refine ⟨44420184459252770752163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 118453825224674055339101 44420184459252770752163)
                      ·
                        rfl

theorem cell23_86508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_86508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86508 prefixEnd_86508 := by exact prefixLift 86508
  have htrace : WordTrace (prefixWord ++ tailWord_86508) baseStart_86508 baseEnd_86508 := by
    simpa [prefixWord, tailWord_86508, baseEnd_86508] using wordTrace_append hprefix tailTrace_86508
  have hstable : (prefixWord ++ tailWord_86508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86508).length < 2 ^ (prefixWord ++ tailWord_86508).sum := by decide
  have hdescent : baseEnd_86508 < baseStart_86508 := by decide
  rcases family_descends (prefixWord ++ tailWord_86508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86511 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 1, 5]
def baseStart_86511 : Nat := 118140960795 + 86511 * 2 ^ 59
def prefixEnd_86511 : Nat := 4983230072969 + 3 ^ 40 * 86511 * 2
def baseEnd_86511 : Nat := 14807241633738753004883

theorem tailTrace_86511 : CollatzResearch.WordTrace tailWord_86511 prefixEnd_86511 14807241633738753004883 := by
  unfold tailWord_86511
  simp only [CollatzResearch.WordTrace]
  refine ⟨3155315389592896747619387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2103543593061931165079591 3155315389592896747619387)
  ·
    refine ⟨4732973084389345121429081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3155315389592896747619387 4732973084389345121429081)
    ·
      refine ⟨3549729813292008841071811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4732973084389345121429081 3549729813292008841071811)
      ·
        refine ⟨5324594719938013261607717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549729813292008841071811 5324594719938013261607717)
        ·
          refine ⟨998361509988377486551447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5324594719938013261607717 998361509988377486551447)
          ·
            refine ⟨1497542264982566229827171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998361509988377486551447 1497542264982566229827171)
            ·
              refine ⟨2246313397473849344740757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497542264982566229827171 2246313397473849344740757)
              ·
                refine ⟨105295940506586688034723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2246313397473849344740757 105295940506586688034723)
                ·
                  refine ⟨157943910759880032052085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105295940506586688034723 157943910759880032052085)
                  ·
                    refine ⟨14807241633738753004883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 157943910759880032052085 14807241633738753004883)
                    ·
                      rfl

theorem cell23_86511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 5].length) (baseStart_86511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86511 prefixEnd_86511 := by exact prefixLift 86511
  have htrace : WordTrace (prefixWord ++ tailWord_86511) baseStart_86511 baseEnd_86511 := by
    simpa [prefixWord, tailWord_86511, baseEnd_86511] using wordTrace_append hprefix tailTrace_86511
  have hstable : (prefixWord ++ tailWord_86511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86511).length < 2 ^ (prefixWord ++ tailWord_86511).sum := by decide
  have hdescent : baseEnd_86511 < baseStart_86511 := by decide
  rcases family_descends (prefixWord ++ tailWord_86511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86542 : List Nat := [4, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3]
def baseStart_86542 : Nat := 118140960795 + 86542 * 2 ^ 59
def prefixEnd_86542 : Nat := 4983230072969 + 3 ^ 40 * 86542 * 2
def baseEnd_86542 : Nat := 44437642801505637727007

theorem tailTrace_86542 : CollatzResearch.WordTrace tailWord_86542 prefixEnd_86542 44437642801505637727007 := by
  unfold tailWord_86542
  simp only [CollatzResearch.WordTrace]
  refine ⟨394555756560073630249735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2104297368320392694665253 394555756560073630249735)
  ·
    refine ⟨591833634840110445374603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 394555756560073630249735 591833634840110445374603)
    ·
      refine ⟨887750452260165668061905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 591833634840110445374603 887750452260165668061905)
      ·
        refine ⟨665812839195124251046429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 887750452260165668061905 665812839195124251046429)
        ·
          refine ⟨249679814698171594142411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 665812839195124251046429 249679814698171594142411)
          ·
            refine ⟨374519722047257391213617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249679814698171594142411 374519722047257391213617)
            ·
              refine ⟨280889791535443043410213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374519722047257391213617 280889791535443043410213)
              ·
                refine ⟨52666835912895570639415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280889791535443043410213 52666835912895570639415)
                ·
                  refine ⟨79000253869343355959123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52666835912895570639415 79000253869343355959123)
                  ·
                    refine ⟨118500380804015033938685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79000253869343355959123 118500380804015033938685)
                    ·
                      refine ⟨44437642801505637727007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 118500380804015033938685 44437642801505637727007)
                      ·
                        rfl

theorem cell23_86542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_86542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86542 prefixEnd_86542 := by exact prefixLift 86542
  have htrace : WordTrace (prefixWord ++ tailWord_86542) baseStart_86542 baseEnd_86542 := by
    simpa [prefixWord, tailWord_86542, baseEnd_86542] using wordTrace_append hprefix tailTrace_86542
  have hstable : (prefixWord ++ tailWord_86542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86542).length < 2 ^ (prefixWord ++ tailWord_86542).sum := by decide
  have hdescent : baseEnd_86542 < baseStart_86542 := by decide
  rcases family_descends (prefixWord ++ tailWord_86542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86544 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_86544 : Nat := 118140960795 + 86544 * 2 ^ 59
def prefixEnd_86544 : Nat := 4983230072969 + 3 ^ 40 * 86544 * 2
def baseEnd_86544 : Nat := 44438669762814629901997

theorem tailTrace_86544 : CollatzResearch.WordTrace tailWord_86544 prefixEnd_86544 44438669762814629901997 := by
  unfold tailWord_86544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578259499236671691785343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2104345998982228922380457 1578259499236671691785343)
  ·
    refine ⟨2367389248855007537678015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1578259499236671691785343 2367389248855007537678015)
    ·
      refine ⟨3551083873282511306517023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2367389248855007537678015 3551083873282511306517023)
      ·
        refine ⟨5326625809923766959775535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551083873282511306517023 5326625809923766959775535)
        ·
          refine ⟨7989938714885650439663303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5326625809923766959775535 7989938714885650439663303)
          ·
            refine ⟨11984908072328475659494955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7989938714885650439663303 11984908072328475659494955)
            ·
              refine ⟨17977362108492713489242433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11984908072328475659494955 17977362108492713489242433)
              ·
                refine ⟨13483021581369535116931825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17977362108492713489242433 13483021581369535116931825)
                ·
                  refine ⟨10112266186027151337698869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13483021581369535116931825 10112266186027151337698869)
                  ·
                    refine ⟨948024954940045437909269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10112266186027151337698869 948024954940045437909269)
                    ·
                      refine ⟨44438669762814629901997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 948024954940045437909269 44438669762814629901997)
                      ·
                        rfl

theorem cell23_86544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_86544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86544 prefixEnd_86544 := by exact prefixLift 86544
  have htrace : WordTrace (prefixWord ++ tailWord_86544) baseStart_86544 baseEnd_86544 := by
    simpa [prefixWord, tailWord_86544, baseEnd_86544] using wordTrace_append hprefix tailTrace_86544
  have hstable : (prefixWord ++ tailWord_86544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86544).length < 2 ^ (prefixWord ++ tailWord_86544).sum := by decide
  have hdescent : baseEnd_86544 < baseStart_86544 := by decide
  rcases family_descends (prefixWord ++ tailWord_86544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86561 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 6]
def baseStart_86561 : Nat := 118140960795 + 86561 * 2 ^ 59
def prefixEnd_86561 : Nat := 4983230072969 + 3 ^ 40 * 86561 * 2
def baseEnd_86561 : Nat := 44447398933941063389419

theorem tailTrace_86561 : CollatzResearch.WordTrace tailWord_86561 prefixEnd_86561 44447398933941063389419 := by
  unfold tailWord_86561
  simp only [CollatzResearch.WordTrace]
  refine ⟨3157139039411755286939537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2104759359607836857959691 3157139039411755286939537)
  ·
    refine ⟨2367854279558816465204653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3157139039411755286939537 2367854279558816465204653)
    ·
      refine ⟨887945354834556174451745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2367854279558816465204653 887945354834556174451745)
      ·
        refine ⟨665959016125917130838809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 887945354834556174451745 665959016125917130838809)
        ·
          refine ⟨499469262094437848129107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 665959016125917130838809 499469262094437848129107)
          ·
            refine ⟨749203893141656772193661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499469262094437848129107 749203893141656772193661)
            ·
              refine ⟨280951459928121289572623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749203893141656772193661 280951459928121289572623)
              ·
                refine ⟨421427189892181934358935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280951459928121289572623 421427189892181934358935)
                ·
                  refine ⟨632140784838272901538403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421427189892181934358935 632140784838272901538403)
                  ·
                    refine ⟨948211177257409352307605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 632140784838272901538403 948211177257409352307605)
                    ·
                      refine ⟨44447398933941063389419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 948211177257409352307605 44447398933941063389419)
                      ·
                        rfl

theorem cell23_86561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_86561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86561 prefixEnd_86561 := by exact prefixLift 86561
  have htrace : WordTrace (prefixWord ++ tailWord_86561) baseStart_86561 baseEnd_86561 := by
    simpa [prefixWord, tailWord_86561, baseEnd_86561] using wordTrace_append hprefix tailTrace_86561
  have hstable : (prefixWord ++ tailWord_86561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86561).length < 2 ^ (prefixWord ++ tailWord_86561).sum := by decide
  have hdescent : baseEnd_86561 < baseStart_86561 := by decide
  rcases family_descends (prefixWord ++ tailWord_86561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86565 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 3, 2, 2]
def baseStart_86565 : Nat := 118140960795 + 86565 * 2 ^ 59
def prefixEnd_86565 : Nat := 4983230072969 + 3 ^ 40 * 86565 * 2
def baseEnd_86565 : Nat := 44449452856559047739401

theorem tailTrace_86565 : CollatzResearch.WordTrace tailWord_86565 prefixEnd_86565 44449452856559047739401 := by
  unfold tailWord_86565
  simp only [CollatzResearch.WordTrace]
  refine ⟨3157284931397263970085149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2104856620931509313390099 3157284931397263970085149)
  ·
    refine ⟨1183981849273973988781931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3157284931397263970085149 1183981849273973988781931)
    ·
      refine ⟨1775972773910960983172897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1183981849273973988781931 1775972773910960983172897)
      ·
        refine ⟨1331979580433220737379673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1775972773910960983172897 1331979580433220737379673)
        ·
          refine ⟨998984685324915553034755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1331979580433220737379673 998984685324915553034755)
          ·
            refine ⟨1498477027987373329552133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998984685324915553034755 1498477027987373329552133)
            ·
              refine ⟨280964442747632499291025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1498477027987373329552133 280964442747632499291025)
              ·
                refine ⟨210723332060724374468269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280964442747632499291025 210723332060724374468269)
                ·
                  refine ⟨79021249522771640425601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210723332060724374468269 79021249522771640425601)
                  ·
                    refine ⟨59265937142078730319201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79021249522771640425601 59265937142078730319201)
                    ·
                      refine ⟨44449452856559047739401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 59265937142078730319201 44449452856559047739401)
                      ·
                        rfl

theorem cell23_86565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_86565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86565 prefixEnd_86565 := by exact prefixLift 86565
  have htrace : WordTrace (prefixWord ++ tailWord_86565) baseStart_86565 baseEnd_86565 := by
    simpa [prefixWord, tailWord_86565, baseEnd_86565] using wordTrace_append hprefix tailTrace_86565
  have hstable : (prefixWord ++ tailWord_86565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86565).length < 2 ^ (prefixWord ++ tailWord_86565).sum := by decide
  have hdescent : baseEnd_86565 < baseStart_86565 := by decide
  rcases family_descends (prefixWord ++ tailWord_86565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86615 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 2, 1, 3]
def baseStart_86615 : Nat := 118140960795 + 86615 * 2 ^ 59
def prefixEnd_86615 : Nat := 4983230072969 + 3 ^ 40 * 86615 * 2
def baseEnd_86615 : Nat := 44475126889283852114171

theorem tailTrace_86615 : CollatzResearch.WordTrace tailWord_86615 prefixEnd_86615 44475126889283852114171 := by
  unfold tailWord_86615
  simp only [CollatzResearch.WordTrace]
  refine ⟨3159108581216122509405299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2106072387477415006270199 3159108581216122509405299)
  ·
    refine ⟨4738662871824183764107949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3159108581216122509405299 4738662871824183764107949)
    ·
      refine ⟨1776998576934068911540481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4738662871824183764107949 1776998576934068911540481)
      ·
        refine ⟨1332748932700551683655361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1776998576934068911540481 1332748932700551683655361)
        ·
          refine ⟨999561699525413762741521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1332748932700551683655361 999561699525413762741521)
          ·
            refine ⟨749671274644060322056141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 999561699525413762741521 749671274644060322056141)
            ·
              refine ⟨281126727991522620771053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749671274644060322056141 281126727991522620771053)
              ·
                refine ⟨105422522996820982789145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281126727991522620771053 105422522996820982789145)
                ·
                  refine ⟨79066892247615737091859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105422522996820982789145 79066892247615737091859)
                  ·
                    refine ⟨118600338371423605637789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79066892247615737091859 118600338371423605637789)
                    ·
                      refine ⟨44475126889283852114171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 118600338371423605637789 44475126889283852114171)
                      ·
                        rfl

theorem cell23_86615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_86615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86615 prefixEnd_86615 := by exact prefixLift 86615
  have htrace : WordTrace (prefixWord ++ tailWord_86615) baseStart_86615 baseEnd_86615 := by
    simpa [prefixWord, tailWord_86615, baseEnd_86615] using wordTrace_append hprefix tailTrace_86615
  have hstable : (prefixWord ++ tailWord_86615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86615).length < 2 ^ (prefixWord ++ tailWord_86615).sum := by decide
  have hdescent : baseEnd_86615 < baseStart_86615 := by decide
  rcases family_descends (prefixWord ++ tailWord_86615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86625 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 3, 3, 2]
def baseStart_86625 : Nat := 118140960795 + 86625 * 2 ^ 59
def prefixEnd_86625 : Nat := 4983230072969 + 3 ^ 40 * 86625 * 2
def baseEnd_86625 : Nat := 44480261695828812989125

theorem tailTrace_86625 : CollatzResearch.WordTrace tailWord_86625 prefixEnd_86625 44480261695828812989125 := by
  unfold tailWord_86625
  simp only [CollatzResearch.WordTrace]
  refine ⟨3159473311179894217269329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2106315540786596144846219 3159473311179894217269329)
  ·
    refine ⟨2369604983384920662951997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3159473311179894217269329 2369604983384920662951997)
    ·
      refine ⟨888601868769345248606999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2369604983384920662951997 888601868769345248606999)
      ·
        refine ⟨1332902803154017872910499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888601868769345248606999 1332902803154017872910499)
        ·
          refine ⟨1999354204731026809365749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332902803154017872910499 1999354204731026809365749)
          ·
            refine ⟨187439456693533763378039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1999354204731026809365749 187439456693533763378039)
            ·
              refine ⟨281159185040300645067059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187439456693533763378039 281159185040300645067059)
              ·
                refine ⟨421738777560450967600589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281159185040300645067059 421738777560450967600589)
                ·
                  refine ⟨158152041585169112850221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421738777560450967600589 158152041585169112850221)
                  ·
                    refine ⟨59307015594438417318833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158152041585169112850221 59307015594438417318833)
                    ·
                      refine ⟨44480261695828812989125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 59307015594438417318833 44480261695828812989125)
                      ·
                        rfl

theorem cell23_86625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_86625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86625 prefixEnd_86625 := by exact prefixLift 86625
  have htrace : WordTrace (prefixWord ++ tailWord_86625) baseStart_86625 baseEnd_86625 := by
    simpa [prefixWord, tailWord_86625, baseEnd_86625] using wordTrace_append hprefix tailTrace_86625
  have hstable : (prefixWord ++ tailWord_86625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86625).length < 2 ^ (prefixWord ++ tailWord_86625).sum := by decide
  have hdescent : baseEnd_86625 < baseStart_86625 := by decide
  rcases family_descends (prefixWord ++ tailWord_86625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86631 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 4, 6]
def baseStart_86631 : Nat := 118140960795 + 86631 * 2 ^ 59
def prefixEnd_86631 : Nat := 4983230072969 + 3 ^ 40 * 86631 * 2
def baseEnd_86631 : Nat := 14827780859918596504699

theorem tailTrace_86631 : CollatzResearch.WordTrace tailWord_86631 prefixEnd_86631 14827780859918596504699 := by
  unfold tailWord_86631
  simp only [CollatzResearch.WordTrace]
  refine ⟨3159692149158157241987747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2106461432772104827991831 3159692149158157241987747)
  ·
    refine ⟨4739538223737235862981621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3159692149158157241987747 4739538223737235862981621)
    ·
      refine ⟨444331708475365862154527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4739538223737235862981621 444331708475365862154527)
      ·
        refine ⟨666497562713048793231791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444331708475365862154527 666497562713048793231791)
        ·
          refine ⟨999746344069573189847687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666497562713048793231791 999746344069573189847687)
          ·
            refine ⟨1499619516104359784771531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999746344069573189847687 1499619516104359784771531)
            ·
              refine ⟨2249429274156539677157297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499619516104359784771531 2249429274156539677157297)
              ·
                refine ⟨1687071955617404757867973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2249429274156539677157297 1687071955617404757867973)
                ·
                  refine ⟨316325991678263392100245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1687071955617404757867973 316325991678263392100245)
                  ·
                    refine ⟨14827780859918596504699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 316325991678263392100245 14827780859918596504699)
                    ·
                      rfl

theorem cell23_86631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_86631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86631 prefixEnd_86631 := by exact prefixLift 86631
  have htrace : WordTrace (prefixWord ++ tailWord_86631) baseStart_86631 baseEnd_86631 := by
    simpa [prefixWord, tailWord_86631, baseEnd_86631] using wordTrace_append hprefix tailTrace_86631
  have hstable : (prefixWord ++ tailWord_86631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86631).length < 2 ^ (prefixWord ++ tailWord_86631).sum := by decide
  have hdescent : baseEnd_86631 < baseStart_86631 := by decide
  rcases family_descends (prefixWord ++ tailWord_86631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86718 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_86718 : Nat := 118140960795 + 86718 * 2 ^ 59
def prefixEnd_86718 : Nat := 4983230072969 + 3 ^ 40 * 86718 * 2
def baseEnd_86718 : Nat := 44528015396696949126197

theorem tailTrace_86718 : CollatzResearch.WordTrace tailWord_86718 prefixEnd_86718 44528015396696949126197 := by
  unfold tailWord_86718
  simp only [CollatzResearch.WordTrace]
  refine ⟨395358162480371387550601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2108576866561980733603205 395358162480371387550601)
  ·
    refine ⟨296518621860278540662951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 395358162480371387550601 296518621860278540662951)
    ·
      refine ⟨444777932790417810994427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296518621860278540662951 444777932790417810994427)
      ·
        refine ⟨667166899185626716491641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444777932790417810994427 667166899185626716491641)
        ·
          refine ⟨500375174389220037368731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667166899185626716491641 500375174389220037368731)
          ·
            refine ⟨750562761583830056053097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500375174389220037368731 750562761583830056053097)
            ·
              refine ⟨562922071187872542039823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750562761583830056053097 562922071187872542039823)
              ·
                refine ⟨844383106781808813059735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562922071187872542039823 844383106781808813059735)
                ·
                  refine ⟨1266574660172713219589603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844383106781808813059735 1266574660172713219589603)
                  ·
                    refine ⟨1899861990259069829384405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1266574660172713219589603 1899861990259069829384405)
                    ·
                      refine ⟨44528015396696949126197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 1899861990259069829384405 44528015396696949126197)
                      ·
                        rfl

theorem cell23_86718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_86718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86718 prefixEnd_86718 := by exact prefixLift 86718
  have htrace : WordTrace (prefixWord ++ tailWord_86718) baseStart_86718 baseEnd_86718 := by
    simpa [prefixWord, tailWord_86718, baseEnd_86718] using wordTrace_append hprefix tailTrace_86718
  have hstable : (prefixWord ++ tailWord_86718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86718).length < 2 ^ (prefixWord ++ tailWord_86718).sum := by decide
  have hdescent : baseEnd_86718 < baseStart_86718 := by decide
  rcases family_descends (prefixWord ++ tailWord_86718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86728 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_86728 : Nat := 118140960795 + 86728 * 2 ^ 59
def prefixEnd_86728 : Nat := 4983230072969 + 3 ^ 40 * 86728 * 2
def baseEnd_86728 : Nat := 44533150203241910001151

theorem tailTrace_86728 : CollatzResearch.WordTrace tailWord_86728 prefixEnd_86728 44533150203241910001151 := by
  unfold tailWord_86728
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581615014903371404134419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2108820019871161872179225 1581615014903371404134419)
  ·
    refine ⟨2372422522355057106201629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1581615014903371404134419 2372422522355057106201629)
    ·
      refine ⟨889658445883146414825611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2372422522355057106201629 889658445883146414825611)
      ·
        refine ⟨1334487668824719622238417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889658445883146414825611 1334487668824719622238417)
        ·
          refine ⟨1000865751618539716678813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1334487668824719622238417 1000865751618539716678813)
          ·
            refine ⟨375324656856952393754555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1000865751618539716678813 375324656856952393754555)
            ·
              refine ⟨562986985285428590631833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375324656856952393754555 562986985285428590631833)
              ·
                refine ⟨422240238964071442973875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562986985285428590631833 422240238964071442973875)
                ·
                  refine ⟨633360358446107164460813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422240238964071442973875 633360358446107164460813)
                  ·
                    refine ⟨237510134417290186672805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 633360358446107164460813 237510134417290186672805)
                    ·
                      refine ⟨44533150203241910001151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 237510134417290186672805 44533150203241910001151)
                      ·
                        rfl

theorem cell23_86728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_86728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86728 prefixEnd_86728 := by exact prefixLift 86728
  have htrace : WordTrace (prefixWord ++ tailWord_86728) baseStart_86728 baseEnd_86728 := by
    simpa [prefixWord, tailWord_86728, baseEnd_86728] using wordTrace_append hprefix tailTrace_86728
  have hstable : (prefixWord ++ tailWord_86728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86728).length < 2 ^ (prefixWord ++ tailWord_86728).sum := by decide
  have hdescent : baseEnd_86728 < baseStart_86728 := by decide
  rcases family_descends (prefixWord ++ tailWord_86728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86768 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 6]
def baseStart_86768 : Nat := 118140960795 + 86768 * 2 ^ 59
def prefixEnd_86768 : Nat := 4983230072969 + 3 ^ 40 * 86768 * 2
def baseEnd_86768 : Nat := 4950409936602417055663

theorem tailTrace_86768 : CollatzResearch.WordTrace tailWord_86768 prefixEnd_86768 4950409936602417055663 := by
  unfold tailWord_86768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582344474830914819862479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2109792633107886426483305 1582344474830914819862479)
  ·
    refine ⟨2373516712246372229793719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582344474830914819862479 2373516712246372229793719)
    ·
      refine ⟨3560275068369558344690579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2373516712246372229793719 3560275068369558344690579)
      ·
        refine ⟨5340412602554337517035869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560275068369558344690579 5340412602554337517035869)
        ·
          refine ⟨2002654725957876568888451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5340412602554337517035869 2002654725957876568888451)
          ·
            refine ⟨3003982088936814853332677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2002654725957876568888451 3003982088936814853332677)
            ·
              refine ⟨563246641675652784999877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3003982088936814853332677 563246641675652784999877)
              ·
                refine ⟨105608745314184897187477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 563246641675652784999877 105608745314184897187477)
                ·
                  refine ⟨4950409936602417055663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105608745314184897187477 4950409936602417055663)
                  ·
                    rfl

theorem cell23_86768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 6].length) (baseStart_86768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86768 prefixEnd_86768 := by exact prefixLift 86768
  have htrace : WordTrace (prefixWord ++ tailWord_86768) baseStart_86768 baseEnd_86768 := by
    simpa [prefixWord, tailWord_86768, baseEnd_86768] using wordTrace_append hprefix tailTrace_86768
  have hstable : (prefixWord ++ tailWord_86768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86768).length < 2 ^ (prefixWord ++ tailWord_86768).sum := by decide
  have hdescent : baseEnd_86768 < baseStart_86768 := by decide
  rcases family_descends (prefixWord ++ tailWord_86768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86795 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 5, 1, 3]
def baseStart_86795 : Nat := 118140960795 + 86795 * 2 ^ 59
def prefixEnd_86795 : Nat := 4983230072969 + 3 ^ 40 * 86795 * 2
def baseEnd_86795 : Nat := 44567553407093147863343

theorem tailTrace_86795 : CollatzResearch.WordTrace tailWord_86795 prefixEnd_86795 44567553407093147863343 := by
  unfold tailWord_86795
  simp only [CollatzResearch.WordTrace]
  refine ⟨3165673720564013250957839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2110449147042675500638559 3165673720564013250957839)
  ·
    refine ⟨4748510580846019876436759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3165673720564013250957839 4748510580846019876436759)
    ·
      refine ⟨7122765871269029814655139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4748510580846019876436759 7122765871269029814655139)
      ·
        refine ⟨10684148806903544721982709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7122765871269029814655139 10684148806903544721982709)
        ·
          refine ⟨1001638950647207317685879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10684148806903544721982709 1001638950647207317685879)
          ·
            refine ⟨1502458425970810976528819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001638950647207317685879 1502458425970810976528819)
            ·
              refine ⟨2253687638956216464793229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502458425970810976528819 2253687638956216464793229)
              ·
                refine ⟨845132864608581174297461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2253687638956216464793229 845132864608581174297461)
                ·
                  refine ⟨79231206057054485090387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 845132864608581174297461 79231206057054485090387)
                  ·
                    refine ⟨118846809085581727635581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79231206057054485090387 118846809085581727635581)
                    ·
                      refine ⟨44567553407093147863343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 118846809085581727635581 44567553407093147863343)
                      ·
                        rfl

theorem cell23_86795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5, 1, 3].length) (baseStart_86795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86795 prefixEnd_86795 := by exact prefixLift 86795
  have htrace : WordTrace (prefixWord ++ tailWord_86795) baseStart_86795 baseEnd_86795 := by
    simpa [prefixWord, tailWord_86795, baseEnd_86795] using wordTrace_append hprefix tailTrace_86795
  have hstable : (prefixWord ++ tailWord_86795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86795).length < 2 ^ (prefixWord ++ tailWord_86795).sum := by decide
  have hdescent : baseEnd_86795 < baseStart_86795 := by decide
  rcases family_descends (prefixWord ++ tailWord_86795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86828 : List Nat := [2, 2, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_86828 : Nat := 118140960795 + 86828 * 2 ^ 59
def prefixEnd_86828 : Nat := 4983230072969 + 3 ^ 40 * 86828 * 2
def baseEnd_86828 : Nat := 14861499422897172916897

theorem tailTrace_86828 : CollatzResearch.WordTrace tailWord_86828 prefixEnd_86828 14861499422897172916897 := by
  unfold tailWord_86828
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583438664722229943454569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2111251552962973257939425 1583438664722229943454569)
  ·
    refine ⟨1187578998541672457590927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1583438664722229943454569 1187578998541672457590927)
    ·
      refine ⟨1781368497812508686386391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187578998541672457590927 1781368497812508686386391)
      ·
        refine ⟨2672052746718763029579587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781368497812508686386391 2672052746718763029579587)
        ·
          refine ⟨4008079120078144544369381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2672052746718763029579587 4008079120078144544369381)
          ·
            refine ⟨751514835014652102069259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4008079120078144544369381 751514835014652102069259)
            ·
              refine ⟨1127272252521978153103889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751514835014652102069259 1127272252521978153103889)
              ·
                refine ⟨845454189391483614827917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127272252521978153103889 845454189391483614827917)
                ·
                  refine ⟨317045321021806355560469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845454189391483614827917 317045321021806355560469)
                  ·
                    refine ⟨14861499422897172916897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 317045321021806355560469 14861499422897172916897)
                    ·
                      rfl

theorem cell23_86828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_86828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86828 prefixEnd_86828 := by exact prefixLift 86828
  have htrace : WordTrace (prefixWord ++ tailWord_86828) baseStart_86828 baseEnd_86828 := by
    simpa [prefixWord, tailWord_86828, baseEnd_86828] using wordTrace_append hprefix tailTrace_86828
  have hstable : (prefixWord ++ tailWord_86828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86828).length < 2 ^ (prefixWord ++ tailWord_86828).sum := by decide
  have hdescent : baseEnd_86828 < baseStart_86828 := by decide
  rcases family_descends (prefixWord ++ tailWord_86828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86835 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 4]
def baseStart_86835 : Nat := 118140960795 + 86835 * 2 ^ 59
def prefixEnd_86835 : Nat := 4983230072969 + 3 ^ 40 * 86835 * 2
def baseEnd_86835 : Nat := 44588092633272991363159

theorem tailTrace_86835 : CollatzResearch.WordTrace tailWord_86835 prefixEnd_86835 44588092633272991363159 := by
  unfold tailWord_86835
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167132640419100082413959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2111421760279400054942639 3167132640419100082413959)
  ·
    refine ⟨4750698960628650123620939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3167132640419100082413959 4750698960628650123620939)
    ·
      refine ⟨7126048440942975185431409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4750698960628650123620939 7126048440942975185431409)
      ·
        refine ⟨5344536330707231389073557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7126048440942975185431409 5344536330707231389073557)
        ·
          refine ⟨250525140501901471362823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5344536330707231389073557 250525140501901471362823)
          ·
            refine ⟨375787710752852207044235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250525140501901471362823 375787710752852207044235)
            ·
              refine ⟨563681566129278310566353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375787710752852207044235 563681566129278310566353)
              ·
                refine ⟨422761174596958732924765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563681566129278310566353 422761174596958732924765)
                ·
                  refine ⟨158535440473859524846787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422761174596958732924765 158535440473859524846787)
                  ·
                    refine ⟨237803160710789287270181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158535440473859524846787 237803160710789287270181)
                    ·
                      refine ⟨44588092633272991363159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 237803160710789287270181 44588092633272991363159)
                      ·
                        rfl

theorem cell23_86835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_86835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86835 prefixEnd_86835 := by exact prefixLift 86835
  have htrace : WordTrace (prefixWord ++ tailWord_86835) baseStart_86835 baseEnd_86835 := by
    simpa [prefixWord, tailWord_86835, baseEnd_86835] using wordTrace_append hprefix tailTrace_86835
  have hstable : (prefixWord ++ tailWord_86835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86835).length < 2 ^ (prefixWord ++ tailWord_86835).sum := by decide
  have hdescent : baseEnd_86835 < baseStart_86835 := by decide
  rcases family_descends (prefixWord ++ tailWord_86835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86848 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_86848 : Nat := 118140960795 + 86848 * 2 ^ 59
def prefixEnd_86848 : Nat := 4983230072969 + 3 ^ 40 * 86848 * 2
def baseEnd_86848 : Nat := 44594767881781440500599

theorem tailTrace_86848 : CollatzResearch.WordTrace tailWord_86848 prefixEnd_86848 44594767881781440500599 := by
  unfold tailWord_86848
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583803394686001651318599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2111737859581335535091465 1583803394686001651318599)
  ·
    refine ⟨2375705092029002476977899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1583803394686001651318599 2375705092029002476977899)
    ·
      refine ⟨3563557638043503715466849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2375705092029002476977899 3563557638043503715466849)
      ·
        refine ⟨2672668228532627786600137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3563557638043503715466849 2672668228532627786600137)
        ·
          refine ⟨2004501171399470839950103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2672668228532627786600137 2004501171399470839950103)
          ·
            refine ⟨3006751757099206259925155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004501171399470839950103 3006751757099206259925155)
            ·
              refine ⟨4510127635648809389887733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006751757099206259925155 4510127635648809389887733)
              ·
                refine ⟨422824465842075880301975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4510127635648809389887733 422824465842075880301975)
                ·
                  refine ⟨634236698763113820452963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422824465842075880301975 634236698763113820452963)
                  ·
                    refine ⟨951355048144670730679445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 634236698763113820452963 951355048144670730679445)
                    ·
                      refine ⟨44594767881781440500599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 951355048144670730679445 44594767881781440500599)
                      ·
                        rfl

theorem cell23_86848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_86848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86848 prefixEnd_86848 := by exact prefixLift 86848
  have htrace : WordTrace (prefixWord ++ tailWord_86848) baseStart_86848 baseEnd_86848 := by
    simpa [prefixWord, tailWord_86848, baseEnd_86848] using wordTrace_append hprefix tailTrace_86848
  have hstable : (prefixWord ++ tailWord_86848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86848).length < 2 ^ (prefixWord ++ tailWord_86848).sum := by decide
  have hdescent : baseEnd_86848 < baseStart_86848 := by decide
  rcases family_descends (prefixWord ++ tailWord_86848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86885 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 3, 3, 3]
def baseStart_86885 : Nat := 118140960795 + 86885 * 2 ^ 59
def prefixEnd_86885 : Nat := 4983230072969 + 3 ^ 40 * 86885 * 2
def baseEnd_86885 : Nat := 44613766665997795737929

theorem tailTrace_86885 : CollatzResearch.WordTrace tailWord_86885 prefixEnd_86885 44613766665997795737929 := by
  unfold tailWord_86885
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168956290237958621734109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2112637526825305747822739 3168956290237958621734109)
  ·
    refine ⟨1188358608839234483150291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3168956290237958621734109 1188358608839234483150291)
    ·
      refine ⟨1782537913258851724725437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1188358608839234483150291 1782537913258851724725437)
      ·
        refine ⟨668451717472069396772039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1782537913258851724725437 668451717472069396772039)
        ·
          refine ⟨1002677576208104095158059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668451717472069396772039 1002677576208104095158059)
          ·
            refine ⟨1504016364312156142737089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002677576208104095158059 1504016364312156142737089)
            ·
              refine ⟨1128012273234117107052817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504016364312156142737089 1128012273234117107052817)
              ·
                refine ⟨846009204925587830289613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128012273234117107052817 846009204925587830289613)
                ·
                  refine ⟨317253451847095436358605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846009204925587830289613 317253451847095436358605)
                  ·
                    refine ⟨118970044442660788634477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317253451847095436358605 118970044442660788634477)
                    ·
                      refine ⟨44613766665997795737929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 118970044442660788634477 44613766665997795737929)
                      ·
                        rfl

theorem cell23_86885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_86885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86885 prefixEnd_86885 := by exact prefixLift 86885
  have htrace : WordTrace (prefixWord ++ tailWord_86885) baseStart_86885 baseEnd_86885 := by
    simpa [prefixWord, tailWord_86885, baseEnd_86885] using wordTrace_append hprefix tailTrace_86885
  have hstable : (prefixWord ++ tailWord_86885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86885).length < 2 ^ (prefixWord ++ tailWord_86885).sum := by decide
  have hdescent : baseEnd_86885 < baseStart_86885 := by decide
  rcases family_descends (prefixWord ++ tailWord_86885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86965 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 9]
def baseStart_86965 : Nat := 118140960795 + 86965 * 2 ^ 59
def prefixEnd_86965 : Nat := 4983230072969 + 3 ^ 40 * 86965 * 2
def baseEnd_86965 : Nat := 4961649457595275859729

theorem tailTrace_86965 : CollatzResearch.WordTrace tailWord_86965 prefixEnd_86965 4961649457595275859729 := by
  unfold tailWord_86965
  simp only [CollatzResearch.WordTrace]
  refine ⟨3171874129948132284646349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2114582753298754856430899 3171874129948132284646349)
  ·
    refine ⟨1189452798730549606742381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3171874129948132284646349 1189452798730549606742381)
    ·
      refine ⟨446044799523956102528393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1189452798730549606742381 446044799523956102528393)
      ·
        refine ⟨334533599642967076896295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446044799523956102528393 334533599642967076896295)
        ·
          refine ⟨501800399464450615344443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334533599642967076896295 501800399464450615344443)
          ·
            refine ⟨752700599196675923016665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501800399464450615344443 752700599196675923016665)
            ·
              refine ⟨564525449397506942262499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752700599196675923016665 564525449397506942262499)
              ·
                refine ⟨846788174096260413393749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564525449397506942262499 846788174096260413393749)
                ·
                  refine ⟨4961649457595275859729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 846788174096260413393749 4961649457595275859729)
                  ·
                    rfl

theorem cell23_86965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 9].length) (baseStart_86965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86965 prefixEnd_86965 := by exact prefixLift 86965
  have htrace : WordTrace (prefixWord ++ tailWord_86965) baseStart_86965 baseEnd_86965 := by
    simpa [prefixWord, tailWord_86965, baseEnd_86965] using wordTrace_append hprefix tailTrace_86965
  have hstable : (prefixWord ++ tailWord_86965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86965).length < 2 ^ (prefixWord ++ tailWord_86965).sum := by decide
  have hdescent : baseEnd_86965 < baseStart_86965 := by decide
  rcases family_descends (prefixWord ++ tailWord_86965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86975 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 3]
def baseStart_86975 : Nat := 118140960795 + 86975 * 2 ^ 59
def prefixEnd_86975 : Nat := 4983230072969 + 3 ^ 40 * 86975 * 2
def baseEnd_86975 : Nat := 44659979924902443612515

theorem tailTrace_86975 : CollatzResearch.WordTrace tailWord_86975 prefixEnd_86975 44659979924902443612515 := by
  unfold tailWord_86975
  simp only [CollatzResearch.WordTrace]
  refine ⟨3172238859911903992510379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2114825906607935995006919 3172238859911903992510379)
  ·
    refine ⟨4758358289867855988765569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3172238859911903992510379 4758358289867855988765569)
    ·
      refine ⟨3568768717400891991574177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4758358289867855988765569 3568768717400891991574177)
      ·
        refine ⟨2676576538050668993680633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3568768717400891991574177 2676576538050668993680633)
        ·
          refine ⟨2007432403538001745260475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2676576538050668993680633 2007432403538001745260475)
          ·
            refine ⟨3011148605307002617890713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007432403538001745260475 3011148605307002617890713)
            ·
              refine ⟨2258361453980251963418035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3011148605307002617890713 2258361453980251963418035)
              ·
                refine ⟨3387542180970377945127053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258361453980251963418035 3387542180970377945127053)
                ·
                  refine ⟨1270328317863891729422645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3387542180970377945127053 1270328317863891729422645)
                  ·
                    refine ⟨119093279799739849633373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1270328317863891729422645 119093279799739849633373)
                    ·
                      refine ⟨44659979924902443612515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 119093279799739849633373 44659979924902443612515)
                      ·
                        rfl

theorem cell23_86975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_86975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86975 prefixEnd_86975 := by exact prefixLift 86975
  have htrace : WordTrace (prefixWord ++ tailWord_86975) baseStart_86975 baseEnd_86975 := by
    simpa [prefixWord, tailWord_86975, baseEnd_86975] using wordTrace_append hprefix tailTrace_86975
  have hstable : (prefixWord ++ tailWord_86975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86975).length < 2 ^ (prefixWord ++ tailWord_86975).sum := by decide
  have hdescent : baseEnd_86975 < baseStart_86975 := by decide
  rcases family_descends (prefixWord ++ tailWord_86975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86980 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_86980 : Nat := 118140960795 + 86980 * 2 ^ 59
def prefixEnd_86980 : Nat := 4983230072969 + 3 ^ 40 * 86980 * 2
def baseEnd_86980 : Nat := 44662547328174924049993

theorem tailTrace_86980 : CollatzResearch.WordTrace tailWord_86980 prefixEnd_86980 44662547328174924049993 := by
  unfold tailWord_86980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586210612446894923221197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2114947483262526564294929 1586210612446894923221197)
  ·
    refine ⟨594828979667585596207949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1586210612446894923221197 594828979667585596207949)
    ·
      refine ⟨223060867375344598577981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 594828979667585596207949 223060867375344598577981)
      ·
        refine ⟨83647825265754224466743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223060867375344598577981 83647825265754224466743)
        ·
          refine ⟨125471737898631336700115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83647825265754224466743 125471737898631336700115)
          ·
            refine ⟨188207606847947005050173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125471737898631336700115 188207606847947005050173)
            ·
              refine ⟨70577852567980126893815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188207606847947005050173 70577852567980126893815)
              ·
                refine ⟨105866778851970190340723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70577852567980126893815 105866778851970190340723)
                ·
                  refine ⟨158800168277955285511085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105866778851970190340723 158800168277955285511085)
                  ·
                    refine ⟨59550063104233232066657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 158800168277955285511085 59550063104233232066657)
                    ·
                      refine ⟨44662547328174924049993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 59550063104233232066657 44662547328174924049993)
                      ·
                        rfl

theorem cell23_86980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_86980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_86980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_86980 prefixEnd_86980 := by exact prefixLift 86980
  have htrace : WordTrace (prefixWord ++ tailWord_86980) baseStart_86980 baseEnd_86980 := by
    simpa [prefixWord, tailWord_86980, baseEnd_86980] using wordTrace_append hprefix tailTrace_86980
  have hstable : (prefixWord ++ tailWord_86980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86980).length < 2 ^ (prefixWord ++ tailWord_86980).sum := by decide
  have hdescent : baseEnd_86980 < baseStart_86980 := by decide
  rcases family_descends (prefixWord ++ tailWord_86980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87032 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 3, 6, 2]
def baseStart_87032 : Nat := 118140960795 + 87032 * 2 ^ 59
def prefixEnd_87032 : Nat := 4983230072969 + 3 ^ 40 * 87032 * 2
def baseEnd_87032 : Nat := 44689248322208720599753

theorem tailTrace_87032 : CollatzResearch.WordTrace tailWord_87032 prefixEnd_87032 44689248322208720599753 := by
  unfold tailWord_87032
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587158910352701363667675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2116211880470268484890233 1587158910352701363667675)
  ·
    refine ⟨2380738365529052045501513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1587158910352701363667675 2380738365529052045501513)
    ·
      refine ⟨1785553774146789034126135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2380738365529052045501513 1785553774146789034126135)
      ·
        refine ⟨2678330661220183551189203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785553774146789034126135 2678330661220183551189203)
        ·
          refine ⟨4017495991830275326783805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2678330661220183551189203 4017495991830275326783805)
          ·
            refine ⟨1506560996936353247543927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4017495991830275326783805 1506560996936353247543927)
            ·
              refine ⟨2259841495404529871315891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506560996936353247543927 2259841495404529871315891)
              ·
                refine ⟨3389762243106794806973837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2259841495404529871315891 3389762243106794806973837)
                ·
                  refine ⟨1271160841165048052615189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3389762243106794806973837 1271160841165048052615189)
                  ·
                    refine ⟨59585664429611627466337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1271160841165048052615189 59585664429611627466337)
                    ·
                      refine ⟨44689248322208720599753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 59585664429611627466337 44689248322208720599753)
                      ·
                        rfl

theorem cell23_87032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_87032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87032 prefixEnd_87032 := by exact prefixLift 87032
  have htrace : WordTrace (prefixWord ++ tailWord_87032) baseStart_87032 baseEnd_87032 := by
    simpa [prefixWord, tailWord_87032, baseEnd_87032] using wordTrace_append hprefix tailTrace_87032
  have hstable : (prefixWord ++ tailWord_87032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87032).length < 2 ^ (prefixWord ++ tailWord_87032).sum := by decide
  have hdescent : baseEnd_87032 < baseStart_87032 := by decide
  rcases family_descends (prefixWord ++ tailWord_87032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87045 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_87045 : Nat := 118140960795 + 87045 * 2 ^ 59
def prefixEnd_87045 : Nat := 4983230072969 + 3 ^ 40 * 87045 * 2
def baseEnd_87045 : Nat := 44695923570717169737193

theorem tailTrace_87045 : CollatzResearch.WordTrace tailWord_87045 prefixEnd_87045 44695923570717169737193 := by
  unfold tailWord_87045
  simp only [CollatzResearch.WordTrace]
  refine ⟨3174791969658305947558589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2116527979772203965039059 3174791969658305947558589)
  ·
    refine ⟨1190546988621864730334471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3174791969658305947558589 1190546988621864730334471)
    ·
      refine ⟨1785820482932797095501707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1190546988621864730334471 1785820482932797095501707)
      ·
        refine ⟨2678730724399195643252561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785820482932797095501707 2678730724399195643252561)
        ·
          refine ⟨2009048043299396732439421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2678730724399195643252561 2009048043299396732439421)
          ·
            refine ⟨753393016237273774664783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2009048043299396732439421 753393016237273774664783)
            ·
              refine ⟨1130089524355910661997175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753393016237273774664783 1130089524355910661997175)
              ·
                refine ⟨1695134286533865992995763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130089524355910661997175 1695134286533865992995763)
                ·
                  refine ⟨2542701429800798989493645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1695134286533865992995763 2542701429800798989493645)
                  ·
                    refine ⟨953513036175299621060117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2542701429800798989493645 953513036175299621060117)
                    ·
                      refine ⟨44695923570717169737193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 953513036175299621060117 44695923570717169737193)
                      ·
                        rfl

theorem cell23_87045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_87045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87045 prefixEnd_87045 := by exact prefixLift 87045
  have htrace : WordTrace (prefixWord ++ tailWord_87045) baseStart_87045 baseEnd_87045 := by
    simpa [prefixWord, tailWord_87045, baseEnd_87045] using wordTrace_append hprefix tailTrace_87045
  have hstable : (prefixWord ++ tailWord_87045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87045).length < 2 ^ (prefixWord ++ tailWord_87045).sum := by decide
  have hdescent : baseEnd_87045 < baseStart_87045 := by decide
  rcases family_descends (prefixWord ++ tailWord_87045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87109 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 4, 3, 2]
def baseStart_87109 : Nat := 118140960795 + 87109 * 2 ^ 59
def prefixEnd_87109 : Nat := 4983230072969 + 3 ^ 40 * 87109 * 2
def baseEnd_87109 : Nat := 44728786332604919336899

theorem tailTrace_87109 : CollatzResearch.WordTrace tailWord_87109 prefixEnd_87109 44728786332604919336899 := by
  unfold tailWord_87109
  simp only [CollatzResearch.WordTrace]
  refine ⟨3177126241426444877888381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2118084160950963251925587 3177126241426444877888381)
  ·
    refine ⟨1191422340534916829208143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3177126241426444877888381 1191422340534916829208143)
    ·
      refine ⟨1787133510802375243812215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191422340534916829208143 1787133510802375243812215)
      ·
        refine ⟨2680700266203562865718323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1787133510802375243812215 2680700266203562865718323)
        ·
          refine ⟨4021050399305344298577485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2680700266203562865718323 4021050399305344298577485)
          ·
            refine ⟨1507893899739504111966557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4021050399305344298577485 1507893899739504111966557)
            ·
              refine ⟨565460212402314041987459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1507893899739504111966557 565460212402314041987459)
              ·
                refine ⟨848190318603471062981189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565460212402314041987459 848190318603471062981189)
                ·
                  refine ⟨159035684738150824308973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 848190318603471062981189 159035684738150824308973)
                  ·
                    refine ⟨59638381776806559115865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159035684738150824308973 59638381776806559115865)
                    ·
                      refine ⟨44728786332604919336899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 59638381776806559115865 44728786332604919336899)
                      ·
                        rfl

theorem cell23_87109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_87109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87109 prefixEnd_87109 := by exact prefixLift 87109
  have htrace : WordTrace (prefixWord ++ tailWord_87109) baseStart_87109 baseEnd_87109 := by
    simpa [prefixWord, tailWord_87109, baseEnd_87109] using wordTrace_append hprefix tailTrace_87109
  have hstable : (prefixWord ++ tailWord_87109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87109).length < 2 ^ (prefixWord ++ tailWord_87109).sum := by decide
  have hdescent : baseEnd_87109 < baseStart_87109 := by decide
  rcases family_descends (prefixWord ++ tailWord_87109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87115 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 2, 10]
def baseStart_87115 : Nat := 118140960795 + 87115 * 2 ^ 59
def prefixEnd_87115 : Nat := 4983230072969 + 3 ^ 40 * 87115 * 2
def baseEnd_87115 : Nat := 14910622405510631953957

theorem tailTrace_87115 : CollatzResearch.WordTrace tailWord_87115 prefixEnd_87115 14910622405510631953957 := by
  unfold tailWord_87115
  simp only [CollatzResearch.WordTrace]
  refine ⟨3177345079404707902606799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2118230052936471935071199 3177345079404707902606799)
  ·
    refine ⟨4766017619107061853910199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3177345079404707902606799 4766017619107061853910199)
    ·
      refine ⟨7149026428660592780865299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4766017619107061853910199 7149026428660592780865299)
      ·
        refine ⟨10723539642990889171297949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7149026428660592780865299 10723539642990889171297949)
        ·
          refine ⟨4021327366121583439236731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10723539642990889171297949 4021327366121583439236731)
          ·
            refine ⟨6031991049182375158855097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021327366121583439236731 6031991049182375158855097)
            ·
              refine ⟨4523993286886781369141323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6031991049182375158855097 4523993286886781369141323)
              ·
                refine ⟨6785989930330172053711985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4523993286886781369141323 6785989930330172053711985)
                ·
                  refine ⟨5089492447747629040283989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6785989930330172053711985 5089492447747629040283989)
                  ·
                    refine ⟨14910622405510631953957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 5089492447747629040283989 14910622405510631953957)
                    ·
                      rfl

theorem cell23_87115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 10].length) (baseStart_87115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87115 prefixEnd_87115 := by exact prefixLift 87115
  have htrace : WordTrace (prefixWord ++ tailWord_87115) baseStart_87115 baseEnd_87115 := by
    simpa [prefixWord, tailWord_87115, baseEnd_87115] using wordTrace_append hprefix tailTrace_87115
  have hstable : (prefixWord ++ tailWord_87115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87115).length < 2 ^ (prefixWord ++ tailWord_87115).sum := by decide
  have hdescent : baseEnd_87115 < baseStart_87115 := by decide
  rcases family_descends (prefixWord ++ tailWord_87115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87149 : List Nat := [1, 5, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_87149 : Nat := 118140960795 + 87149 * 2 ^ 59
def prefixEnd_87149 : Nat := 4983230072969 + 3 ^ 40 * 87149 * 2
def baseEnd_87149 : Nat := 14916441852928254278905

theorem tailTrace_87149 : CollatzResearch.WordTrace tailWord_87149 prefixEnd_87149 14916441852928254278905 := by
  unfold tailWord_87149
  simp only [CollatzResearch.WordTrace]
  refine ⟨3178585161281531709344501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2119056774187687806229667 3178585161281531709344501)
  ·
    refine ⟨297992358870143597751047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3178585161281531709344501 297992358870143597751047)
    ·
      refine ⟨446988538305215396626571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297992358870143597751047 446988538305215396626571)
      ·
        refine ⟨670482807457823094939857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446988538305215396626571 670482807457823094939857)
        ·
          refine ⟨502862105593367321204893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 670482807457823094939857 502862105593367321204893)
          ·
            refine ⟨188573289597512745451835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 502862105593367321204893 188573289597512745451835)
            ·
              refine ⟨282859934396269118177753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188573289597512745451835 282859934396269118177753)
              ·
                refine ⟨212144950797201838633315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282859934396269118177753 212144950797201838633315)
                ·
                  refine ⟨318217426195802757949973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212144950797201838633315 318217426195802757949973)
                  ·
                    refine ⟨14916441852928254278905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 318217426195802757949973 14916441852928254278905)
                    ·
                      rfl

theorem cell23_87149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_87149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87149 prefixEnd_87149 := by exact prefixLift 87149
  have htrace : WordTrace (prefixWord ++ tailWord_87149) baseStart_87149 baseEnd_87149 := by
    simpa [prefixWord, tailWord_87149, baseEnd_87149] using wordTrace_append hprefix tailTrace_87149
  have hstable : (prefixWord ++ tailWord_87149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87149).length < 2 ^ (prefixWord ++ tailWord_87149).sum := by decide
  have hdescent : baseEnd_87149 < baseStart_87149 := by decide
  rcases family_descends (prefixWord ++ tailWord_87149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87186 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_87186 : Nat := 118140960795 + 87186 * 2 ^ 59
def prefixEnd_87186 : Nat := 4983230072969 + 3 ^ 40 * 87186 * 2
def baseEnd_87186 : Nat := 44768324343001118074045

theorem tailTrace_87186 : CollatzResearch.WordTrace tailWord_87186 prefixEnd_87186 44768324343001118074045 := by
  unfold tailWord_87186
  simp only [CollatzResearch.WordTrace]
  refine ⟨794983665536871757110353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2119956441431658018960941 794983665536871757110353)
  ·
    refine ⟨596237749152653817832765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 794983665536871757110353 596237749152653817832765)
    ·
      refine ⟨223589155932245181687287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 596237749152653817832765 223589155932245181687287)
      ·
        refine ⟨335383733898367772530931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223589155932245181687287 335383733898367772530931)
        ·
          refine ⟨503075600847551658796397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335383733898367772530931 503075600847551658796397)
          ·
            refine ⟨188653350317831872048649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 503075600847551658796397 188653350317831872048649)
            ·
              refine ⟨141490012738373904036487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188653350317831872048649 141490012738373904036487)
              ·
                refine ⟨212235019107560856054731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141490012738373904036487 212235019107560856054731)
                ·
                  refine ⟨318352528661341284082097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212235019107560856054731 318352528661341284082097)
                  ·
                    refine ⟨238764396496005963061573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 318352528661341284082097 238764396496005963061573)
                    ·
                      refine ⟨44768324343001118074045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 238764396496005963061573 44768324343001118074045)
                      ·
                        rfl

theorem cell23_87186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_87186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87186 prefixEnd_87186 := by exact prefixLift 87186
  have htrace : WordTrace (prefixWord ++ tailWord_87186) baseStart_87186 baseEnd_87186 := by
    simpa [prefixWord, tailWord_87186, baseEnd_87186] using wordTrace_append hprefix tailTrace_87186
  have hstable : (prefixWord ++ tailWord_87186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87186).length < 2 ^ (prefixWord ++ tailWord_87186).sum := by decide
  have hdescent : baseEnd_87186 < baseStart_87186 := by decide
  rcases family_descends (prefixWord ++ tailWord_87186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87207 : List Nat := [1, 1, 6, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_87207 : Nat := 118140960795 + 87207 * 2 ^ 59
def prefixEnd_87207 : Nat := 4983230072969 + 3 ^ 40 * 87207 * 2
def baseEnd_87207 : Nat := 44779107436745535911449

theorem tailTrace_87207 : CollatzResearch.WordTrace tailWord_87207 prefixEnd_87207 44779107436745535911449 := by
  unfold tailWord_87207
  simp only [CollatzResearch.WordTrace]
  refine ⟨3180700595071407614955875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2120467063380938409970583 3180700595071407614955875)
  ·
    refine ⟨4771050892607111422433813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3180700595071407614955875 4771050892607111422433813)
    ·
      refine ⟨223643010590958347926585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4771050892607111422433813 223643010590958347926585)
      ·
        refine ⟨167732257943218760944939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223643010590958347926585 167732257943218760944939)
        ·
          refine ⟨251598386914828141417409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167732257943218760944939 251598386914828141417409)
          ·
            refine ⟨188698790186121106063057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251598386914828141417409 188698790186121106063057)
            ·
              refine ⟨141524092639590829547293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188698790186121106063057 141524092639590829547293)
              ·
                refine ⟨53071534739846561080235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141524092639590829547293 53071534739846561080235)
                ·
                  refine ⟨79607302109769841620353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53071534739846561080235 79607302109769841620353)
                  ·
                    refine ⟨59705476582327381215265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79607302109769841620353 59705476582327381215265)
                    ·
                      refine ⟨44779107436745535911449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 59705476582327381215265 44779107436745535911449)
                      ·
                        rfl

theorem cell23_87207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_87207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87207 prefixEnd_87207 := by exact prefixLift 87207
  have htrace : WordTrace (prefixWord ++ tailWord_87207) baseStart_87207 baseEnd_87207 := by
    simpa [prefixWord, tailWord_87207, baseEnd_87207] using wordTrace_append hprefix tailTrace_87207
  have hstable : (prefixWord ++ tailWord_87207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87207).length < 2 ^ (prefixWord ++ tailWord_87207).sum := by decide
  have hdescent : baseEnd_87207 < baseStart_87207 := by decide
  rcases family_descends (prefixWord ++ tailWord_87207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87210 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_87210 : Nat := 118140960795 + 87210 * 2 ^ 59
def prefixEnd_87210 : Nat := 4983230072969 + 3 ^ 40 * 87210 * 2
def baseEnd_87210 : Nat := 44780647878709024173935

theorem tailTrace_87210 : CollatzResearch.WordTrace tailWord_87210 prefixEnd_87210 44780647878709024173935 := by
  unfold tailWord_87210
  simp only [CollatzResearch.WordTrace]
  refine ⟨795202503515134781828771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2120540009373692751543389 795202503515134781828771)
  ·
    refine ⟨1192803755272702172743157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 795202503515134781828771 1192803755272702172743157)
    ·
      refine ⟨111825352056815828694671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1192803755272702172743157 111825352056815828694671)
      ·
        refine ⟨167738028085223743042007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111825352056815828694671 167738028085223743042007)
        ·
          refine ⟨251607042127835614563011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167738028085223743042007 251607042127835614563011)
          ·
            refine ⟨377410563191753421844517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251607042127835614563011 377410563191753421844517)
            ·
              refine ⟨70764480598453766595847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 377410563191753421844517 70764480598453766595847)
              ·
                refine ⟨106146720897680649893771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70764480598453766595847 106146720897680649893771)
                ·
                  refine ⟨159220081346520974840657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106146720897680649893771 159220081346520974840657)
                  ·
                    refine ⟨119415061009890731130493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159220081346520974840657 119415061009890731130493)
                    ·
                      refine ⟨44780647878709024173935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 119415061009890731130493 44780647878709024173935)
                      ·
                        rfl

theorem cell23_87210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_87210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87210 prefixEnd_87210 := by exact prefixLift 87210
  have htrace : WordTrace (prefixWord ++ tailWord_87210) baseStart_87210 baseEnd_87210 := by
    simpa [prefixWord, tailWord_87210, baseEnd_87210] using wordTrace_append hprefix tailTrace_87210
  have hstable : (prefixWord ++ tailWord_87210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87210).length < 2 ^ (prefixWord ++ tailWord_87210).sum := by decide
  have hdescent : baseEnd_87210 < baseStart_87210 := by decide
  rcases family_descends (prefixWord ++ tailWord_87210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87212 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 4]
def baseStart_87212 : Nat := 118140960795 + 87212 * 2 ^ 59
def prefixEnd_87212 : Nat := 4983230072969 + 3 ^ 40 * 87212 * 2
def baseEnd_87212 : Nat := 44781674840018016348925

theorem tailTrace_87212 : CollatzResearch.WordTrace tailWord_87212 prefixEnd_87212 44781674840018016348925 := by
  unfold tailWord_87212
  simp only [CollatzResearch.WordTrace]
  refine ⟨1590441480026646734443945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2120588640035528979258593 1590441480026646734443945)
  ·
    refine ⟨1192831110019985050832959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1590441480026646734443945 1192831110019985050832959)
    ·
      refine ⟨1789246665029977576249439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1192831110019985050832959 1789246665029977576249439)
      ·
        refine ⟨2683869997544966364374159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1789246665029977576249439 2683869997544966364374159)
        ·
          refine ⟨4025804996317449546561239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683869997544966364374159 4025804996317449546561239)
          ·
            refine ⟨6038707494476174319841859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025804996317449546561239 6038707494476174319841859)
            ·
              refine ⟨9058061241714261479762789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6038707494476174319841859 9058061241714261479762789)
              ·
                refine ⟨1698386482821424027455523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9058061241714261479762789 1698386482821424027455523)
                ·
                  refine ⟨2547579724232136041183285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698386482821424027455523 2547579724232136041183285)
                  ·
                    refine ⟨238835599146762753860933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2547579724232136041183285 238835599146762753860933)
                    ·
                      refine ⟨44781674840018016348925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 238835599146762753860933 44781674840018016348925)
                      ·
                        rfl

theorem cell23_87212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_87212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87212 prefixEnd_87212 := by exact prefixLift 87212
  have htrace : WordTrace (prefixWord ++ tailWord_87212) baseStart_87212 baseEnd_87212 := by
    simpa [prefixWord, tailWord_87212, baseEnd_87212] using wordTrace_append hprefix tailTrace_87212
  have hstable : (prefixWord ++ tailWord_87212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87212).length < 2 ^ (prefixWord ++ tailWord_87212).sum := by decide
  have hdescent : baseEnd_87212 < baseStart_87212 := by decide
  rcases family_descends (prefixWord ++ tailWord_87212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87216 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 1, 3, 2]
def baseStart_87216 : Nat := 118140960795 + 87216 * 2 ^ 59
def prefixEnd_87216 : Nat := 4983230072969 + 3 ^ 40 * 87216 * 2
def baseEnd_87216 : Nat := 44783728762636000698907

theorem tailTrace_87216 : CollatzResearch.WordTrace tailWord_87216 prefixEnd_87216 44783728762636000698907 := by
  unfold tailWord_87216
  simp only [CollatzResearch.WordTrace]
  refine ⟨1590514426019401076016751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2120685901359201434689001 1590514426019401076016751)
  ·
    refine ⟨2385771639029101614025127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1590514426019401076016751 2385771639029101614025127)
    ·
      refine ⟨3578657458543652421037691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2385771639029101614025127 3578657458543652421037691)
      ·
        refine ⟨5367986187815478631556537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3578657458543652421037691 5367986187815478631556537)
        ·
          refine ⟨4025989640861608973667403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5367986187815478631556537 4025989640861608973667403)
          ·
            refine ⟨6038984461292413460501105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025989640861608973667403 6038984461292413460501105)
            ·
              refine ⟨4529238345969310095375829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6038984461292413460501105 4529238345969310095375829)
              ·
                refine ⟨106154023733655705360371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4529238345969310095375829 106154023733655705360371)
                ·
                  refine ⟨159231035600483558040557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106154023733655705360371 159231035600483558040557)
                  ·
                    refine ⟨59711638350181334265209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159231035600483558040557 59711638350181334265209)
                    ·
                      refine ⟨44783728762636000698907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 59711638350181334265209 44783728762636000698907)
                      ·
                        rfl

theorem cell23_87216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 1, 3, 2].length) (baseStart_87216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87216 prefixEnd_87216 := by exact prefixLift 87216
  have htrace : WordTrace (prefixWord ++ tailWord_87216) baseStart_87216 baseEnd_87216 := by
    simpa [prefixWord, tailWord_87216, baseEnd_87216] using wordTrace_append hprefix tailTrace_87216
  have hstable : (prefixWord ++ tailWord_87216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87216).length < 2 ^ (prefixWord ++ tailWord_87216).sum := by decide
  have hdescent : baseEnd_87216 < baseStart_87216 := by decide
  rcases family_descends (prefixWord ++ tailWord_87216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87297 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 2, 2, 2]
def baseStart_87297 : Nat := 118140960795 + 87297 * 2 ^ 59
def prefixEnd_87297 : Nat := 4983230072969 + 3 ^ 40 * 87297 * 2
def baseEnd_87297 : Nat := 44825320695650183786035

theorem tailTrace_87297 : CollatzResearch.WordTrace tailWord_87297 prefixEnd_87297 44825320695650183786035 := by
  unfold tailWord_87297
  simp only [CollatzResearch.WordTrace]
  refine ⟨3183983164745352985732145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2122655443163568657154763 3183983164745352985732145)
  ·
    refine ⟨2387987373559014739299109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3183983164745352985732145 2387987373559014739299109)
    ·
      refine ⟨447747632542315263618583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2387987373559014739299109 447747632542315263618583)
      ·
        refine ⟨671621448813472895427875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447747632542315263618583 671621448813472895427875)
        ·
          refine ⟨1007432173220209343141813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671621448813472895427875 1007432173220209343141813)
          ·
            refine ⟨94446766239394625919545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1007432173220209343141813 94446766239394625919545)
            ·
              refine ⟨70835074679545969439659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94446766239394625919545 70835074679545969439659)
              ·
                refine ⟨106252612019318954159489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70835074679545969439659 106252612019318954159489)
                ·
                  refine ⟨79689459014489215619617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106252612019318954159489 79689459014489215619617)
                  ·
                    refine ⟨59767094260866911714713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79689459014489215619617 59767094260866911714713)
                    ·
                      refine ⟨44825320695650183786035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 59767094260866911714713 44825320695650183786035)
                      ·
                        rfl

theorem cell23_87297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 2, 2, 2].length) (baseStart_87297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87297 prefixEnd_87297 := by exact prefixLift 87297
  have htrace : WordTrace (prefixWord ++ tailWord_87297) baseStart_87297 baseEnd_87297 := by
    simpa [prefixWord, tailWord_87297, baseEnd_87297] using wordTrace_append hprefix tailTrace_87297
  have hstable : (prefixWord ++ tailWord_87297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87297).length < 2 ^ (prefixWord ++ tailWord_87297).sum := by decide
  have hdescent : baseEnd_87297 < baseStart_87297 := by decide
  rcases family_descends (prefixWord ++ tailWord_87297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87380 : List Nat := [2, 4, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_87380 : Nat := 118140960795 + 87380 * 2 ^ 59
def prefixEnd_87380 : Nat := 4983230072969 + 3 ^ 40 * 87380 * 2
def baseEnd_87380 : Nat := 14955979863324453016051

theorem tailTrace_87380 : CollatzResearch.WordTrace tailWord_87380 prefixEnd_87380 14955979863324453016051 := by
  unfold tailWord_87380
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593505211722329080501797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2124673615629772107335729 1593505211722329080501797)
  ·
    refine ⟨298782227197936702594087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1593505211722329080501797 298782227197936702594087)
    ·
      refine ⟨448173340796905053891131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298782227197936702594087 448173340796905053891131)
      ·
        refine ⟨672260011195357580836697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448173340796905053891131 672260011195357580836697)
        ·
          refine ⟨504195008396518185627523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 672260011195357580836697 504195008396518185627523)
          ·
            refine ⟨756292512594777278441285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504195008396518185627523 756292512594777278441285)
            ·
              refine ⟨141804846111520739707741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 756292512594777278441285 141804846111520739707741)
              ·
                refine ⟨53176817291820277390403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141804846111520739707741 53176817291820277390403)
                ·
                  refine ⟨79765225937730416085605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53176817291820277390403 79765225937730416085605)
                  ·
                    refine ⟨14955979863324453016051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79765225937730416085605 14955979863324453016051)
                    ·
                      rfl

theorem cell23_87380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_87380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87380 prefixEnd_87380 := by exact prefixLift 87380
  have htrace : WordTrace (prefixWord ++ tailWord_87380) baseStart_87380 baseEnd_87380 := by
    simpa [prefixWord, tailWord_87380, baseEnd_87380] using wordTrace_append hprefix tailTrace_87380
  have hstable : (prefixWord ++ tailWord_87380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87380).length < 2 ^ (prefixWord ++ tailWord_87380).sum := by decide
  have hdescent : baseEnd_87380 < baseStart_87380 := by decide
  rcases family_descends (prefixWord ++ tailWord_87380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87436 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 6, 4]
def baseStart_87436 : Nat := 118140960795 + 87436 * 2 ^ 59
def prefixEnd_87436 : Nat := 4983230072969 + 3 ^ 40 * 87436 * 2
def baseEnd_87436 : Nat := 14965564835541713315965

theorem tailTrace_87436 : CollatzResearch.WordTrace tailWord_87436 prefixEnd_87436 14965564835541713315965 := by
  unfold tailWord_87436
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594526455620889862521081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2126035274161186483361441 1594526455620889862521081)
  ·
    refine ⟨1195894841715667396890811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1594526455620889862521081 1195894841715667396890811)
    ·
      refine ⟨1793842262573501095336217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195894841715667396890811 1793842262573501095336217)
      ·
        refine ⟨1345381696930125821502163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1793842262573501095336217 1345381696930125821502163)
        ·
          refine ⟨2018072545395188732253245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345381696930125821502163 2018072545395188732253245)
          ·
            refine ⟨756777204523195774594967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2018072545395188732253245 756777204523195774594967)
            ·
              refine ⟨1135165806784793661892451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756777204523195774594967 1135165806784793661892451)
              ·
                refine ⟨1702748710177190492838677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135165806784793661892451 1702748710177190492838677)
                ·
                  refine ⟨79816345789555804351813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1702748710177190492838677 79816345789555804351813)
                  ·
                    refine ⟨14965564835541713315965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79816345789555804351813 14965564835541713315965)
                    ·
                      rfl

theorem cell23_87436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_87436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87436 prefixEnd_87436 := by exact prefixLift 87436
  have htrace : WordTrace (prefixWord ++ tailWord_87436) baseStart_87436 baseEnd_87436 := by
    simpa [prefixWord, tailWord_87436, baseEnd_87436] using wordTrace_append hprefix tailTrace_87436
  have hstable : (prefixWord ++ tailWord_87436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87436).length < 2 ^ (prefixWord ++ tailWord_87436).sum := by decide
  have hdescent : baseEnd_87436 < baseStart_87436 := by decide
  rcases family_descends (prefixWord ++ tailWord_87436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87449 : List Nat := [1, 2, 1, 2, 1, 5, 11]
def baseStart_87449 : Nat := 118140960795 + 87449 * 2 ^ 59
def prefixEnd_87449 : Nat := 4983230072969 + 3 ^ 40 * 87449 * 2
def baseEnd_87449 : Nat := 554362589569550482535

theorem tailTrace_87449 : CollatzResearch.WordTrace tailWord_87449 prefixEnd_87449 554362589569550482535 := by
  unfold tailWord_87449
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189527060194682945265401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2126351373463121963510267 3189527060194682945265401)
  ·
    refine ⟨2392145295146012208949051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3189527060194682945265401 2392145295146012208949051)
    ·
      refine ⟨3588217942719018313423577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2392145295146012208949051 3588217942719018313423577)
      ·
        refine ⟨2691163457039263735067683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3588217942719018313423577 2691163457039263735067683)
        ·
          refine ⟨4036745185558895602601525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2691163457039263735067683 4036745185558895602601525)
          ·
            refine ⟨378444861146146462743893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4036745185558895602601525 378444861146146462743893)
            ·
              refine ⟨554362589569550482535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 378444861146146462743893 554362589569550482535)
              ·
                rfl

theorem cell23_87449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 11].length) (baseStart_87449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87449 prefixEnd_87449 := by exact prefixLift 87449
  have htrace : WordTrace (prefixWord ++ tailWord_87449) baseStart_87449 baseEnd_87449 := by
    simpa [prefixWord, tailWord_87449, baseEnd_87449] using wordTrace_append hprefix tailTrace_87449
  have hstable : (prefixWord ++ tailWord_87449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87449).length < 2 ^ (prefixWord ++ tailWord_87449).sum := by decide
  have hdescent : baseEnd_87449 < baseStart_87449 := by decide
  rcases family_descends (prefixWord ++ tailWord_87449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87453 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_87453 : Nat := 118140960795 + 87453 * 2 ^ 59
def prefixEnd_87453 : Nat := 4983230072969 + 3 ^ 40 * 87453 * 2
def baseEnd_87453 : Nat := 14968474559250524478439

theorem tailTrace_87453 : CollatzResearch.WordTrace tailWord_87453 prefixEnd_87453 14968474559250524478439 := by
  unfold tailWord_87453
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189672952180191628411013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2126448634786794418940675 3189672952180191628411013)
  ·
    refine ⟨598063678533785930327065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3189672952180191628411013 598063678533785930327065)
    ·
      refine ⟨448547758900339447745299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 598063678533785930327065 448547758900339447745299)
      ·
        refine ⟨672821638350509171617949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448547758900339447745299 672821638350509171617949)
        ·
          refine ⟨252308114381440939356731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 672821638350509171617949 252308114381440939356731)
          ·
            refine ⟨378462171572161409035097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252308114381440939356731 378462171572161409035097)
            ·
              refine ⟨283846628679121056776323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378462171572161409035097 283846628679121056776323)
              ·
                refine ⟨425769943018681585164485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283846628679121056776323 425769943018681585164485)
                ·
                  refine ⟨79831864316002797218341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425769943018681585164485 79831864316002797218341)
                  ·
                    refine ⟨14968474559250524478439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79831864316002797218341 14968474559250524478439)
                    ·
                      rfl

theorem cell23_87453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_87453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87453 prefixEnd_87453 := by exact prefixLift 87453
  have htrace : WordTrace (prefixWord ++ tailWord_87453) baseStart_87453 baseEnd_87453 := by
    simpa [prefixWord, tailWord_87453, baseEnd_87453] using wordTrace_append hprefix tailTrace_87453
  have hstable : (prefixWord ++ tailWord_87453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87453).length < 2 ^ (prefixWord ++ tailWord_87453).sum := by decide
  have hdescent : baseEnd_87453 < baseStart_87453 := by decide
  rcases family_descends (prefixWord ++ tailWord_87453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87454 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_87454 : Nat := 118140960795 + 87454 * 2 ^ 59
def prefixEnd_87454 : Nat := 4983230072969 + 3 ^ 40 * 87454 * 2
def baseEnd_87454 : Nat := 44905937158406069522813

theorem tailTrace_87454 : CollatzResearch.WordTrace tailWord_87454 prefixEnd_87454 44905937158406069522813 := by
  unfold tailWord_87454
  simp only [CollatzResearch.WordTrace]
  refine ⟨398713678147071099899677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2126472950117712532798277 398713678147071099899677)
  ·
    refine ⟨149517629305151662462379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 398713678147071099899677 149517629305151662462379)
    ·
      refine ⟨224276443957727493693569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149517629305151662462379 224276443957727493693569)
      ·
        refine ⟨168207332968295620270177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224276443957727493693569 168207332968295620270177)
        ·
          refine ⟨126155499726221715202633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168207332968295620270177 126155499726221715202633)
          ·
            refine ⟨94616624794666286401975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126155499726221715202633 94616624794666286401975)
            ·
              refine ⟨141924937191999429602963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94616624794666286401975 141924937191999429602963)
              ·
                refine ⟨212887405787999144404445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141924937191999429602963 212887405787999144404445)
                ·
                  refine ⟨79832777170499679151667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212887405787999144404445 79832777170499679151667)
                  ·
                    refine ⟨119749165755749518727501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79832777170499679151667 119749165755749518727501)
                    ·
                      refine ⟨44905937158406069522813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 119749165755749518727501 44905937158406069522813)
                      ·
                        rfl

theorem cell23_87454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_87454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87454 prefixEnd_87454 := by exact prefixLift 87454
  have htrace : WordTrace (prefixWord ++ tailWord_87454) baseStart_87454 baseEnd_87454 := by
    simpa [prefixWord, tailWord_87454, baseEnd_87454] using wordTrace_append hprefix tailTrace_87454
  have hstable : (prefixWord ++ tailWord_87454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87454).length < 2 ^ (prefixWord ++ tailWord_87454).sum := by decide
  have hdescent : baseEnd_87454 < baseStart_87454 := by decide
  rcases family_descends (prefixWord ++ tailWord_87454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87463 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_87463 : Nat := 118140960795 + 87463 * 2 ^ 59
def prefixEnd_87463 : Nat := 4983230072969 + 3 ^ 40 * 87463 * 2
def baseEnd_87463 : Nat := 44910558484296534310271

theorem tailTrace_87463 : CollatzResearch.WordTrace tailWord_87463 prefixEnd_87463 44910558484296534310271 := by
  unfold tailWord_87463
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190037682143963336275043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2126691788095975557516695 3190037682143963336275043)
  ·
    refine ⟨4785056523215945004412565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3190037682143963336275043 4785056523215945004412565)
    ·
      refine ⟨224299524525747422081839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4785056523215945004412565 224299524525747422081839)
      ·
        refine ⟨336449286788621133122759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224299524525747422081839 336449286788621133122759)
        ·
          refine ⟨504673930182931699684139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336449286788621133122759 504673930182931699684139)
          ·
            refine ⟨757010895274397549526209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504673930182931699684139 757010895274397549526209)
            ·
              refine ⟨567758171455798162144657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757010895274397549526209 567758171455798162144657)
              ·
                refine ⟨425818628591848621608493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567758171455798162144657 425818628591848621608493)
                ·
                  refine ⟨159681985721943233103185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425818628591848621608493 159681985721943233103185)
                  ·
                    refine ⟨119761489291457424827389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159681985721943233103185 119761489291457424827389)
                    ·
                      refine ⟨44910558484296534310271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 119761489291457424827389 44910558484296534310271)
                      ·
                        rfl

theorem cell23_87463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_87463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87463 prefixEnd_87463 := by exact prefixLift 87463
  have htrace : WordTrace (prefixWord ++ tailWord_87463) baseStart_87463 baseEnd_87463 := by
    simpa [prefixWord, tailWord_87463, baseEnd_87463] using wordTrace_append hprefix tailTrace_87463
  have hstable : (prefixWord ++ tailWord_87463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87463).length < 2 ^ (prefixWord ++ tailWord_87463).sum := by decide
  have hdescent : baseEnd_87463 < baseStart_87463 := by decide
  rcases family_descends (prefixWord ++ tailWord_87463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87546 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_87546 : Nat := 118140960795 + 87546 * 2 ^ 59
def prefixEnd_87546 : Nat := 4983230072969 + 3 ^ 40 * 87546 * 2
def baseEnd_87546 : Nat := 44953177378619709572389

theorem tailTrace_87546 : CollatzResearch.WordTrace tailWord_87546 prefixEnd_87546 44953177378619709572389 := by
  unfold tailWord_87546
  simp only [CollatzResearch.WordTrace]
  refine ⟨798266235210817127886623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2128709960562179007697661 798266235210817127886623)
  ·
    refine ⟨1197399352816225691829935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 798266235210817127886623 1197399352816225691829935)
    ·
      refine ⟨1796099029224338537744903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197399352816225691829935 1796099029224338537744903)
      ·
        refine ⟨2694148543836507806617355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796099029224338537744903 2694148543836507806617355)
        ·
          refine ⟨4041222815754761709926033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694148543836507806617355 4041222815754761709926033)
          ·
            refine ⟨3030917111816071282444525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4041222815754761709926033 3030917111816071282444525)
            ·
              refine ⟨1136593916931026730916697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3030917111816071282444525 1136593916931026730916697)
              ·
                refine ⟨852445437698270048187523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1136593916931026730916697 852445437698270048187523)
                ·
                  refine ⟨1278668156547405072281285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 852445437698270048187523 1278668156547405072281285)
                  ·
                    refine ⟨239750279352638451052741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1278668156547405072281285 239750279352638451052741)
                    ·
                      refine ⟨44953177378619709572389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 239750279352638451052741 44953177378619709572389)
                      ·
                        rfl

theorem cell23_87546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_87546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87546 prefixEnd_87546 := by exact prefixLift 87546
  have htrace : WordTrace (prefixWord ++ tailWord_87546) baseStart_87546 baseEnd_87546 := by
    simpa [prefixWord, tailWord_87546, baseEnd_87546] using wordTrace_append hprefix tailTrace_87546
  have hstable : (prefixWord ++ tailWord_87546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87546).length < 2 ^ (prefixWord ++ tailWord_87546).sum := by decide
  have hdescent : baseEnd_87546 < baseStart_87546 := by decide
  rcases family_descends (prefixWord ++ tailWord_87546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87554 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_87554 : Nat := 118140960795 + 87554 * 2 ^ 59
def prefixEnd_87554 : Nat := 4983230072969 + 3 ^ 40 * 87554 * 2
def baseEnd_87554 : Nat := 44957285223855678272353

theorem tailTrace_87554 : CollatzResearch.WordTrace tailWord_87554 prefixEnd_87554 44957285223855678272353 := by
  unfold tailWord_87554
  simp only [CollatzResearch.WordTrace]
  refine ⟨798339181203571469459429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2128904483209523918558477 798339181203571469459429)
  ·
    refine ⟨149688596475669650523643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 798339181203571469459429 149688596475669650523643)
    ·
      refine ⟨224532894713504475785465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149688596475669650523643 224532894713504475785465)
      ·
        refine ⟨168399671035128356839099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224532894713504475785465 168399671035128356839099)
        ·
          refine ⟨252599506552692535258649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168399671035128356839099 252599506552692535258649)
          ·
            refine ⟨189449629914519401443987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252599506552692535258649 189449629914519401443987)
            ·
              refine ⟨284174444871779102165981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189449629914519401443987 284174444871779102165981)
              ·
                refine ⟨106565416826917163312243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284174444871779102165981 106565416826917163312243)
                ·
                  refine ⟨159848125240375744968365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106565416826917163312243 159848125240375744968365)
                  ·
                    refine ⟨59943046965140904363137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159848125240375744968365 59943046965140904363137)
                    ·
                      refine ⟨44957285223855678272353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 59943046965140904363137 44957285223855678272353)
                      ·
                        rfl

theorem cell23_87554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_87554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87554 prefixEnd_87554 := by exact prefixLift 87554
  have htrace : WordTrace (prefixWord ++ tailWord_87554) baseStart_87554 baseEnd_87554 := by
    simpa [prefixWord, tailWord_87554, baseEnd_87554] using wordTrace_append hprefix tailTrace_87554
  have hstable : (prefixWord ++ tailWord_87554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87554).length < 2 ^ (prefixWord ++ tailWord_87554).sum := by decide
  have hdescent : baseEnd_87554 < baseStart_87554 := by decide
  rcases family_descends (prefixWord ++ tailWord_87554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87573 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 7]
def baseStart_87573 : Nat := 118140960795 + 87573 * 2 ^ 59
def prefixEnd_87573 : Nat := 4983230072969 + 3 ^ 40 * 87573 * 2
def baseEnd_87573 : Nat := 4996337928476789326085

theorem tailTrace_87573 : CollatzResearch.WordTrace tailWord_87573 prefixEnd_87573 4996337928476789326085 := by
  unfold tailWord_87573
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194049711745452122779373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2129366474496968081852915 3194049711745452122779373)
  ·
    refine ⟨1197768641904544546042265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3194049711745452122779373 1197768641904544546042265)
    ·
      refine ⟨898326481428408409531699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1197768641904544546042265 898326481428408409531699)
      ·
        refine ⟨1347489722142612614297549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898326481428408409531699 1347489722142612614297549)
        ·
          refine ⟨505308645803479730361581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1347489722142612614297549 505308645803479730361581)
          ·
            refine ⟨189490742176304898885593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 505308645803479730361581 189490742176304898885593)
            ·
              refine ⟨142118056632228674164195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189490742176304898885593 142118056632228674164195)
              ·
                refine ⟨213177084948343011246293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142118056632228674164195 213177084948343011246293)
                ·
                  refine ⟨4996337928476789326085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 213177084948343011246293 4996337928476789326085)
                  ·
                    rfl

theorem cell23_87573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_87573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87573 prefixEnd_87573 := by exact prefixLift 87573
  have htrace : WordTrace (prefixWord ++ tailWord_87573) baseStart_87573 baseEnd_87573 := by
    simpa [prefixWord, tailWord_87573, baseEnd_87573] using wordTrace_append hprefix tailTrace_87573
  have hstable : (prefixWord ++ tailWord_87573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87573).length < 2 ^ (prefixWord ++ tailWord_87573).sum := by decide
  have hdescent : baseEnd_87573 < baseStart_87573 := by decide
  rcases family_descends (prefixWord ++ tailWord_87573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87583 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 3]
def baseStart_87583 : Nat := 118140960795 + 87583 * 2 ^ 59
def prefixEnd_87583 : Nat := 4983230072969 + 3 ^ 40 * 87583 * 2
def baseEnd_87583 : Nat := 44972176162836064809719

theorem tailTrace_87583 : CollatzResearch.WordTrace tailWord_87583 prefixEnd_87583 44972176162836064809719 := by
  unfold tailWord_87583
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194414441709223830643403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2129609627806149220428935 3194414441709223830643403)
  ·
    refine ⟨4791621662563835745965105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3194414441709223830643403 4791621662563835745965105)
    ·
      refine ⟨3593716246922876809473829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4791621662563835745965105 3593716246922876809473829)
      ·
        refine ⟨673821796298039401776343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3593716246922876809473829 673821796298039401776343)
        ·
          refine ⟨1010732694447059102664515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673821796298039401776343 1010732694447059102664515)
          ·
            refine ⟨1516099041670588653996773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010732694447059102664515 1516099041670588653996773)
            ·
              refine ⟨284268570313235372624395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1516099041670588653996773 284268570313235372624395)
              ·
                refine ⟨426402855469853058936593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284268570313235372624395 426402855469853058936593)
                ·
                  refine ⟨319802141602389794202445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426402855469853058936593 319802141602389794202445)
                  ·
                    refine ⟨119925803100896172825917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 319802141602389794202445 119925803100896172825917)
                    ·
                      refine ⟨44972176162836064809719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 119925803100896172825917 44972176162836064809719)
                      ·
                        rfl

theorem cell23_87583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_87583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87583 prefixEnd_87583 := by exact prefixLift 87583
  have htrace : WordTrace (prefixWord ++ tailWord_87583) baseStart_87583 baseEnd_87583 := by
    simpa [prefixWord, tailWord_87583, baseEnd_87583] using wordTrace_append hprefix tailTrace_87583
  have hstable : (prefixWord ++ tailWord_87583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87583).length < 2 ^ (prefixWord ++ tailWord_87583).sum := by decide
  have hdescent : baseEnd_87583 < baseStart_87583 := by decide
  rcases family_descends (prefixWord ++ tailWord_87583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87596 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 5]
def baseStart_87596 : Nat := 118140960795 + 87596 * 2 ^ 59
def prefixEnd_87596 : Nat := 4983230072969 + 3 ^ 40 * 87596 * 2
def baseEnd_87596 : Nat := 44978851411344513947159

theorem tailTrace_87596 : CollatzResearch.WordTrace tailWord_87596 prefixEnd_87596 44978851411344513947159 := by
  unfold tailWord_87596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1597444295331063525433321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2129925727108084700577761 1597444295331063525433321)
  ·
    refine ⟨1198083221498297644074991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1597444295331063525433321 1198083221498297644074991)
    ·
      refine ⟨1797124832247446466112487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198083221498297644074991 1797124832247446466112487)
      ·
        refine ⟨2695687248371169699168731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797124832247446466112487 2695687248371169699168731)
        ·
          refine ⟨4043530872556754548753097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2695687248371169699168731 4043530872556754548753097)
          ·
            refine ⟨3032648154417565911564823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4043530872556754548753097 3032648154417565911564823)
            ·
              refine ⟨4548972231626348867347235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3032648154417565911564823 4548972231626348867347235)
              ·
                refine ⟨6823458347439523301020853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4548972231626348867347235 6823458347439523301020853)
                ·
                  refine ⟨639699220072455309470705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6823458347439523301020853 639699220072455309470705)
                  ·
                    refine ⟨479774415054341482103029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 639699220072455309470705 479774415054341482103029)
                    ·
                      refine ⟨44978851411344513947159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 479774415054341482103029 44978851411344513947159)
                      ·
                        rfl

theorem cell23_87596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_87596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87596 prefixEnd_87596 := by exact prefixLift 87596
  have htrace : WordTrace (prefixWord ++ tailWord_87596) baseStart_87596 baseEnd_87596 := by
    simpa [prefixWord, tailWord_87596, baseEnd_87596] using wordTrace_append hprefix tailTrace_87596
  have hstable : (prefixWord ++ tailWord_87596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87596).length < 2 ^ (prefixWord ++ tailWord_87596).sum := by decide
  have hdescent : baseEnd_87596 < baseStart_87596 := by decide
  rcases family_descends (prefixWord ++ tailWord_87596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87684 : List Nat := [2, 3, 2, 1, 4, 1, 1, 4, 1, 4]
def baseStart_87684 : Nat := 118140960795 + 87684 * 2 ^ 59
def prefixEnd_87684 : Nat := 4983230072969 + 3 ^ 40 * 87684 * 2
def baseEnd_87684 : Nat := 15008012569646723215585

theorem tailTrace_87684 : CollatzResearch.WordTrace tailWord_87684 prefixEnd_87684 15008012569646723215585 := by
  unfold tailWord_87684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599049107171659040035053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2132065476228878720046737 1599049107171659040035053)
  ·
    refine ⟨599643415189372140013145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1599049107171659040035053 599643415189372140013145)
    ·
      refine ⟨449732561392029105009859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 599643415189372140013145 449732561392029105009859)
      ·
        refine ⟨674598842088043657514789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449732561392029105009859 674598842088043657514789)
        ·
          refine ⟨126487282891508185784023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 674598842088043657514789 126487282891508185784023)
          ·
            refine ⟨189730924337262278676035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126487282891508185784023 189730924337262278676035)
            ·
              refine ⟨284596386505893418014053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189730924337262278676035 284596386505893418014053)
              ·
                refine ⟨53361822469855015877635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284596386505893418014053 53361822469855015877635)
                ·
                  refine ⟨80042733704782523816453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53361822469855015877635 80042733704782523816453)
                  ·
                    refine ⟨15008012569646723215585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80042733704782523816453 15008012569646723215585)
                    ·
                      rfl

theorem cell23_87684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_87684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87684 prefixEnd_87684 := by exact prefixLift 87684
  have htrace : WordTrace (prefixWord ++ tailWord_87684) baseStart_87684 baseEnd_87684 := by
    simpa [prefixWord, tailWord_87684, baseEnd_87684] using wordTrace_append hprefix tailTrace_87684
  have hstable : (prefixWord ++ tailWord_87684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87684).length < 2 ^ (prefixWord ++ tailWord_87684).sum := by decide
  have hdescent : baseEnd_87684 < baseStart_87684 := by decide
  rcases family_descends (prefixWord ++ tailWord_87684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87711 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 2, 2, 3]
def baseStart_87711 : Nat := 118140960795 + 87711 * 2 ^ 59
def prefixEnd_87711 : Nat := 4983230072969 + 3 ^ 40 * 87711 * 2
def baseEnd_87711 : Nat := 45037901686611564009131

theorem tailTrace_87711 : CollatzResearch.WordTrace tailWord_87711 prefixEnd_87711 45037901686611564009131 := by
  unfold tailWord_87711
  simp only [CollatzResearch.WordTrace]
  refine ⟨3199082985245501691302987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2132721990163667794201991 3199082985245501691302987)
  ·
    refine ⟨4798624477868252536954481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3199082985245501691302987 4798624477868252536954481)
    ·
      refine ⟨3598968358401189402715861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4798624477868252536954481 3598968358401189402715861)
      ·
        refine ⟨84350820900027876626153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3598968358401189402715861 84350820900027876626153)
        ·
          refine ⟨63263115675020907469615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84350820900027876626153 63263115675020907469615)
          ·
            refine ⟨94894673512531361204423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63263115675020907469615 94894673512531361204423)
            ·
              refine ⟨142342010268797041806635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94894673512531361204423 142342010268797041806635)
              ·
                refine ⟨213513015403195562709953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142342010268797041806635 213513015403195562709953)
                ·
                  refine ⟨160134761552396672032465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213513015403195562709953 160134761552396672032465)
                  ·
                    refine ⟨120101071164297504024349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160134761552396672032465 120101071164297504024349)
                    ·
                      refine ⟨45037901686611564009131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 120101071164297504024349 45037901686611564009131)
                      ·
                        rfl

theorem cell23_87711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_87711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87711 prefixEnd_87711 := by exact prefixLift 87711
  have htrace : WordTrace (prefixWord ++ tailWord_87711) baseStart_87711 baseEnd_87711 := by
    simpa [prefixWord, tailWord_87711, baseEnd_87711] using wordTrace_append hprefix tailTrace_87711
  have hstable : (prefixWord ++ tailWord_87711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87711).length < 2 ^ (prefixWord ++ tailWord_87711).sum := by decide
  have hdescent : baseEnd_87711 < baseStart_87711 := by decide
  rcases family_descends (prefixWord ++ tailWord_87711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87717 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 2, 3, 2]
def baseStart_87717 : Nat := 118140960795 + 87717 * 2 ^ 59
def prefixEnd_87717 : Nat := 4983230072969 + 3 ^ 40 * 87717 * 2
def baseEnd_87717 : Nat := 45040982570538540534103

theorem tailTrace_87717 : CollatzResearch.WordTrace tailWord_87717 prefixEnd_87717 45040982570538540534103 := by
  unfold tailWord_87717
  simp only [CollatzResearch.WordTrace]
  refine ⟨3199301823223764716021405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2132867882149176477347603 3199301823223764716021405)
  ·
    refine ⟨1199738183708911768508027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3199301823223764716021405 1199738183708911768508027)
    ·
      refine ⟨1799607275563367652762041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1199738183708911768508027 1799607275563367652762041)
      ·
        refine ⟨1349705456672525739571531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1799607275563367652762041 1349705456672525739571531)
        ·
          refine ⟨2024558185008788609357297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349705456672525739571531 2024558185008788609357297)
          ·
            refine ⟨1518418638756591457017973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2024558185008788609357297 1518418638756591457017973)
            ·
              refine ⟨142351747383430449095435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1518418638756591457017973 142351747383430449095435)
              ·
                refine ⟨213527621075145673643153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142351747383430449095435 213527621075145673643153)
                ·
                  refine ⟨160145715806359255232365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213527621075145673643153 160145715806359255232365)
                  ·
                    refine ⟨60054643427384720712137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160145715806359255232365 60054643427384720712137)
                    ·
                      refine ⟨45040982570538540534103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60054643427384720712137 45040982570538540534103)
                      ·
                        rfl

theorem cell23_87717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_87717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87717 prefixEnd_87717 := by exact prefixLift 87717
  have htrace : WordTrace (prefixWord ++ tailWord_87717) baseStart_87717 baseEnd_87717 := by
    simpa [prefixWord, tailWord_87717, baseEnd_87717] using wordTrace_append hprefix tailTrace_87717
  have hstable : (prefixWord ++ tailWord_87717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87717).length < 2 ^ (prefixWord ++ tailWord_87717).sum := by decide
  have hdescent : baseEnd_87717 < baseStart_87717 := by decide
  rcases family_descends (prefixWord ++ tailWord_87717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87743 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_87743 : Nat := 118140960795 + 87743 * 2 ^ 59
def prefixEnd_87743 : Nat := 4983230072969 + 3 ^ 40 * 87743 * 2
def baseEnd_87743 : Nat := 45054333067555438808983

theorem tailTrace_87743 : CollatzResearch.WordTrace tailWord_87743 prefixEnd_87743 45054333067555438808983 := by
  unfold tailWord_87743
  simp only [CollatzResearch.WordTrace]
  refine ⟨3200250121129571156467883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2133500080753047437645255 3200250121129571156467883)
  ·
    refine ⟨4800375181694356734701825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3200250121129571156467883 4800375181694356734701825)
    ·
      refine ⟨3600281386270767551026369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4800375181694356734701825 3600281386270767551026369)
      ·
        refine ⟨2700211039703075663269777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3600281386270767551026369 2700211039703075663269777)
        ·
          refine ⟨2025158279777306747452333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2700211039703075663269777 2025158279777306747452333)
          ·
            refine ⟨759434354916490030294625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2025158279777306747452333 759434354916490030294625)
            ·
              refine ⟨569575766187367522720969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759434354916490030294625 569575766187367522720969)
              ·
                refine ⟨427181824640525642040727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569575766187367522720969 427181824640525642040727)
                ·
                  refine ⟨640772736960788463061091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 427181824640525642040727 640772736960788463061091)
                  ·
                    refine ⟨961159105441182694591637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 640772736960788463061091 961159105441182694591637)
                    ·
                      refine ⟨45054333067555438808983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 961159105441182694591637 45054333067555438808983)
                      ·
                        rfl

theorem cell23_87743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_87743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87743 prefixEnd_87743 := by exact prefixLift 87743
  have htrace : WordTrace (prefixWord ++ tailWord_87743) baseStart_87743 baseEnd_87743 := by
    simpa [prefixWord, tailWord_87743, baseEnd_87743] using wordTrace_append hprefix tailTrace_87743
  have hstable : (prefixWord ++ tailWord_87743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87743).length < 2 ^ (prefixWord ++ tailWord_87743).sum := by decide
  have hdescent : baseEnd_87743 < baseStart_87743 := by decide
  rcases family_descends (prefixWord ++ tailWord_87743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87764 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_87764 : Nat := 118140960795 + 87764 * 2 ^ 59
def prefixEnd_87764 : Nat := 4983230072969 + 3 ^ 40 * 87764 * 2
def baseEnd_87764 : Nat := 45065116161299856646387

theorem tailTrace_87764 : CollatzResearch.WordTrace tailWord_87764 prefixEnd_87764 45065116161299856646387 := by
  unfold tailWord_87764
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600508027026745871491173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2134010702702327828654897 1600508027026745871491173)
  ·
    refine ⟨300095255067514850904595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1600508027026745871491173 300095255067514850904595)
    ·
      refine ⟨450142882601272276356893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300095255067514850904595 450142882601272276356893)
      ·
        refine ⟨168803580975477103633835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450142882601272276356893 168803580975477103633835)
        ·
          refine ⟨253205371463215655450753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168803580975477103633835 253205371463215655450753)
          ·
            refine ⟨189904028597411741588065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253205371463215655450753 189904028597411741588065)
            ·
              refine ⟨142428021448058806191049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189904028597411741588065 142428021448058806191049)
              ·
                refine ⟨106821016086044104643287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142428021448058806191049 106821016086044104643287)
                ·
                  refine ⟨160231524129066156964931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106821016086044104643287 160231524129066156964931)
                  ·
                    refine ⟨240347286193599235447397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 160231524129066156964931 240347286193599235447397)
                    ·
                      refine ⟨45065116161299856646387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 240347286193599235447397 45065116161299856646387)
                      ·
                        rfl

theorem cell23_87764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_87764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87764 prefixEnd_87764 := by exact prefixLift 87764
  have htrace : WordTrace (prefixWord ++ tailWord_87764) baseStart_87764 baseEnd_87764 := by
    simpa [prefixWord, tailWord_87764, baseEnd_87764] using wordTrace_append hprefix tailTrace_87764
  have hstable : (prefixWord ++ tailWord_87764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87764).length < 2 ^ (prefixWord ++ tailWord_87764).sum := by decide
  have hdescent : baseEnd_87764 < baseStart_87764 := by decide
  rcases family_descends (prefixWord ++ tailWord_87764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87767 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 1, 2, 3]
def baseStart_87767 : Nat := 118140960795 + 87767 * 2 ^ 59
def prefixEnd_87767 : Nat := 4983230072969 + 3 ^ 40 * 87767 * 2
def baseEnd_87767 : Nat := 45066656603263344908873

theorem tailTrace_87767 : CollatzResearch.WordTrace tailWord_87767 prefixEnd_87767 45066656603263344908873 := by
  unfold tailWord_87767
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201125473042623255341555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2134083648695082170227703 3201125473042623255341555)
  ·
    refine ⟨4801688209563934883012333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3201125473042623255341555 4801688209563934883012333)
    ·
      refine ⟨1800633078586475581129625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4801688209563934883012333 1800633078586475581129625)
      ·
        refine ⟨1350474808939856685847219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1800633078586475581129625 1350474808939856685847219)
        ·
          refine ⟨2025712213409785028770829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350474808939856685847219 2025712213409785028770829)
          ·
            refine ⟨759642080028669385789061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2025712213409785028770829 759642080028669385789061)
            ·
              refine ⟨142432890005375509835449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 759642080028669385789061 142432890005375509835449)
              ·
                refine ⟨106824667504031632376587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142432890005375509835449 106824667504031632376587)
                ·
                  refine ⟨160237001256047448564881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106824667504031632376587 160237001256047448564881)
                  ·
                    refine ⟨120177750942035586423661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160237001256047448564881 120177750942035586423661)
                    ·
                      refine ⟨45066656603263344908873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 120177750942035586423661 45066656603263344908873)
                      ·
                        rfl

theorem cell23_87767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_87767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87767 prefixEnd_87767 := by exact prefixLift 87767
  have htrace : WordTrace (prefixWord ++ tailWord_87767) baseStart_87767 baseEnd_87767 := by
    simpa [prefixWord, tailWord_87767, baseEnd_87767] using wordTrace_append hprefix tailTrace_87767
  have hstable : (prefixWord ++ tailWord_87767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87767).length < 2 ^ (prefixWord ++ tailWord_87767).sum := by decide
  have hdescent : baseEnd_87767 < baseStart_87767 := by decide
  rcases family_descends (prefixWord ++ tailWord_87767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87770 : List Nat := [3, 1, 1, 2, 2, 3, 4, 7]
def baseStart_87770 : Nat := 118140960795 + 87770 * 2 ^ 59
def prefixEnd_87770 : Nat := 4983230072969 + 3 ^ 40 * 87770 * 2
def baseEnd_87770 : Nat := 1669192483156549376717

theorem tailTrace_87770 : CollatzResearch.WordTrace tailWord_87770 prefixEnd_87770 1669192483156549376717 := by
  unfold tailWord_87770
  simp only [CollatzResearch.WordTrace]
  refine ⟨800308723007938691925191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2134156594687836511800509 800308723007938691925191)
  ·
    refine ⟨1200463084511908037887787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 800308723007938691925191 1200463084511908037887787)
    ·
      refine ⟨1800694626767862056831681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1200463084511908037887787 1800694626767862056831681)
      ·
        refine ⟨1350520970075896542623761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1800694626767862056831681 1350520970075896542623761)
        ·
          refine ⟨1012890727556922406967821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1350520970075896542623761 1012890727556922406967821)
          ·
            refine ⟨379834022833845902612933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1012890727556922406967821 379834022833845902612933)
            ·
              refine ⟨71218879281346106739925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 379834022833845902612933 71218879281346106739925)
              ·
                refine ⟨1669192483156549376717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 71218879281346106739925 1669192483156549376717)
                ·
                  rfl

theorem cell23_87770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 7].length) (baseStart_87770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87770 prefixEnd_87770 := by exact prefixLift 87770
  have htrace : WordTrace (prefixWord ++ tailWord_87770) baseStart_87770 baseEnd_87770 := by
    simpa [prefixWord, tailWord_87770, baseEnd_87770] using wordTrace_append hprefix tailTrace_87770
  have hstable : (prefixWord ++ tailWord_87770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87770).length < 2 ^ (prefixWord ++ tailWord_87770).sum := by decide
  have hdescent : baseEnd_87770 < baseStart_87770 := by decide
  rcases family_descends (prefixWord ++ tailWord_87770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87780 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_87780 : Nat := 118140960795 + 87780 * 2 ^ 59
def prefixEnd_87780 : Nat := 4983230072969 + 3 ^ 40 * 87780 * 2
def baseEnd_87780 : Nat := 45073331851771794046313

theorem tailTrace_87780 : CollatzResearch.WordTrace tailWord_87780 prefixEnd_87780 45073331851771794046313 := by
  unfold tailWord_87780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600799810997763237782397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2134399747997017650376529 1600799810997763237782397)
  ·
    refine ⟨600299929124161214168399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1600799810997763237782397 600299929124161214168399)
    ·
      refine ⟨900449893686241821252599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600299929124161214168399 900449893686241821252599)
      ·
        refine ⟨1350674840529362731878899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900449893686241821252599 1350674840529362731878899)
        ·
          refine ⟨2026012260794044097818349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350674840529362731878899 2026012260794044097818349)
          ·
            refine ⟨759754597797766536681881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2026012260794044097818349 759754597797766536681881)
            ·
              refine ⟨569815948348324902511411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759754597797766536681881 569815948348324902511411)
              ·
                refine ⟨854723922522487353767117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569815948348324902511411 854723922522487353767117)
                ·
                  refine ⟨320521470945932757662669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854723922522487353767117 320521470945932757662669)
                  ·
                    refine ⟨120195551604724784123501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320521470945932757662669 120195551604724784123501)
                    ·
                      refine ⟨45073331851771794046313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 120195551604724784123501 45073331851771794046313)
                      ·
                        rfl

theorem cell23_87780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_87780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87780 prefixEnd_87780 := by exact prefixLift 87780
  have htrace : WordTrace (prefixWord ++ tailWord_87780) baseStart_87780 baseEnd_87780 := by
    simpa [prefixWord, tailWord_87780, baseEnd_87780] using wordTrace_append hprefix tailTrace_87780
  have hstable : (prefixWord ++ tailWord_87780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87780).length < 2 ^ (prefixWord ++ tailWord_87780).sum := by decide
  have hdescent : baseEnd_87780 < baseStart_87780 := by decide
  rcases family_descends (prefixWord ++ tailWord_87780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87833 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 6]
def baseStart_87833 : Nat := 118140960795 + 87833 * 2 ^ 59
def prefixEnd_87833 : Nat := 4983230072969 + 3 ^ 40 * 87833 * 2
def baseEnd_87833 : Nat := 45100546326460086683569

theorem tailTrace_87833 : CollatzResearch.WordTrace tailWord_87833 prefixEnd_87833 45100546326460086683569 := by
  unfold tailWord_87833
  simp only [CollatzResearch.WordTrace]
  refine ⟨3203532690803516527244153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2135688460535677684829435 3203532690803516527244153)
  ·
    refine ⟨2402649518102637395433115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3203532690803516527244153 2402649518102637395433115)
    ·
      refine ⟨3603974277153956093149673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2402649518102637395433115 3603974277153956093149673)
      ·
        refine ⟨2702980707865467069862255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3603974277153956093149673 2702980707865467069862255)
        ·
          refine ⟨4054471061798200604793383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702980707865467069862255 4054471061798200604793383)
          ·
            refine ⟨6081706592697300907190075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054471061798200604793383 6081706592697300907190075)
            ·
              refine ⟨9122559889045951360785113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6081706592697300907190075 9122559889045951360785113)
              ·
                refine ⟨6841919916784463520588835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9122559889045951360785113 6841919916784463520588835)
                ·
                  refine ⟨10262879875176695280883253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6841919916784463520588835 10262879875176695280883253)
                  ·
                    refine ⟨962144988297815182582805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10262879875176695280883253 962144988297815182582805)
                    ·
                      refine ⟨45100546326460086683569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 962144988297815182582805 45100546326460086683569)
                      ·
                        rfl

theorem cell23_87833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_87833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87833 prefixEnd_87833 := by exact prefixLift 87833
  have htrace : WordTrace (prefixWord ++ tailWord_87833) baseStart_87833 baseEnd_87833 := by
    simpa [prefixWord, tailWord_87833, baseEnd_87833] using wordTrace_append hprefix tailTrace_87833
  have hstable : (prefixWord ++ tailWord_87833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87833).length < 2 ^ (prefixWord ++ tailWord_87833).sum := by decide
  have hdescent : baseEnd_87833 < baseStart_87833 := by decide
  rcases family_descends (prefixWord ++ tailWord_87833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87840 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 5]
def baseStart_87840 : Nat := 118140960795 + 87840 * 2 ^ 59
def prefixEnd_87840 : Nat := 4983230072969 + 3 ^ 40 * 87840 * 2
def baseEnd_87840 : Nat := 45104140691041559296037

theorem tailTrace_87840 : CollatzResearch.WordTrace tailWord_87840 prefixEnd_87840 45104140691041559296037 := by
  unfold tailWord_87840
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601894000889078361374487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2135858667852104481832649 1601894000889078361374487)
  ·
    refine ⟨2402841001333617542061731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1601894000889078361374487 2402841001333617542061731)
    ·
      refine ⟨3604261502000426313092597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2402841001333617542061731 3604261502000426313092597)
      ·
        refine ⟨337899515812539966852431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3604261502000426313092597 337899515812539966852431)
        ·
          refine ⟨506849273718809950278647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337899515812539966852431 506849273718809950278647)
          ·
            refine ⟨760273910578214925417971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506849273718809950278647 760273910578214925417971)
            ·
              refine ⟨1140410865867322388126957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760273910578214925417971 1140410865867322388126957)
              ·
                refine ⟨427654074700245895547609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1140410865867322388126957 427654074700245895547609)
                ·
                  refine ⟨320740556025184421660707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427654074700245895547609 320740556025184421660707)
                  ·
                    refine ⟨481110834037776632491061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 320740556025184421660707 481110834037776632491061)
                    ·
                      refine ⟨45104140691041559296037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 481110834037776632491061 45104140691041559296037)
                      ·
                        rfl

theorem cell23_87840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_87840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87840 prefixEnd_87840 := by exact prefixLift 87840
  have htrace : WordTrace (prefixWord ++ tailWord_87840) baseStart_87840 baseEnd_87840 := by
    simpa [prefixWord, tailWord_87840, baseEnd_87840] using wordTrace_append hprefix tailTrace_87840
  have hstable : (prefixWord ++ tailWord_87840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87840).length < 2 ^ (prefixWord ++ tailWord_87840).sum := by decide
  have hdescent : baseEnd_87840 < baseStart_87840 := by decide
  rcases family_descends (prefixWord ++ tailWord_87840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87841 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 1, 3, 2]
def baseStart_87841 : Nat := 118140960795 + 87841 * 2 ^ 59
def prefixEnd_87841 : Nat := 4983230072969 + 3 ^ 40 * 87841 * 2
def baseEnd_87841 : Nat := 45104654171696055383533

theorem tailTrace_87841 : CollatzResearch.WordTrace tailWord_87841 prefixEnd_87841 45104654171696055383533 := by
  unfold tailWord_87841
  simp only [CollatzResearch.WordTrace]
  refine ⟨3203824474774533893535377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2135882983183022595690251 3203824474774533893535377)
  ·
    refine ⟨2402868356080900420151533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3203824474774533893535377 2402868356080900420151533)
    ·
      refine ⟨901075633530337657556825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2402868356080900420151533 901075633530337657556825)
      ·
        refine ⟨675806725147753243167619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 901075633530337657556825 675806725147753243167619)
        ·
          refine ⟨1013710087721629864751429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675806725147753243167619 1013710087721629864751429)
          ·
            refine ⟨190070641447805599640893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1013710087721629864751429 190070641447805599640893)
            ·
              refine ⟨71276490542927099865335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 190070641447805599640893 71276490542927099865335)
              ·
                refine ⟨106914735814390649798003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71276490542927099865335 106914735814390649798003)
                ·
                  refine ⟨160372103721585974697005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106914735814390649798003 160372103721585974697005)
                  ·
                    refine ⟨60139538895594740511377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160372103721585974697005 60139538895594740511377)
                    ·
                      refine ⟨45104654171696055383533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60139538895594740511377 45104654171696055383533)
                      ·
                        rfl

theorem cell23_87841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_87841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87841 prefixEnd_87841 := by exact prefixLift 87841
  have htrace : WordTrace (prefixWord ++ tailWord_87841) baseStart_87841 baseEnd_87841 := by
    simpa [prefixWord, tailWord_87841, baseEnd_87841] using wordTrace_append hprefix tailTrace_87841
  have hstable : (prefixWord ++ tailWord_87841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87841).length < 2 ^ (prefixWord ++ tailWord_87841).sum := by decide
  have hdescent : baseEnd_87841 < baseStart_87841 := by decide
  rcases family_descends (prefixWord ++ tailWord_87841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87947 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 3]
def baseStart_87947 : Nat := 118140960795 + 87947 * 2 ^ 59
def prefixEnd_87947 : Nat := 4983230072969 + 3 ^ 40 * 87947 * 2
def baseEnd_87947 : Nat := 45159083121072640658045

theorem tailTrace_87947 : CollatzResearch.WordTrace tailWord_87947 prefixEnd_87947 45159083121072640658045 := by
  unfold tailWord_87947
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207690612390513996894095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2138460408260342664596063 3207690612390513996894095)
  ·
    refine ⟨4811535918585770995341143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3207690612390513996894095 4811535918585770995341143)
    ·
      refine ⟨7217303877878656493011715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4811535918585770995341143 7217303877878656493011715)
      ·
        refine ⟨10825955816817984739517573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7217303877878656493011715 10825955816817984739517573)
        ·
          refine ⟨2029866715653372138659545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10825955816817984739517573 2029866715653372138659545)
          ·
            refine ⟨1522400036740029103994659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2029866715653372138659545 1522400036740029103994659)
            ·
              refine ⟨2283600055110043655991989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522400036740029103994659 2283600055110043655991989)
              ·
                refine ⟨214087505166566592749249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2283600055110043655991989 214087505166566592749249)
                ·
                  refine ⟨160565628874924944561937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214087505166566592749249 160565628874924944561937)
                  ·
                    refine ⟨120424221656193708421453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160565628874924944561937 120424221656193708421453)
                    ·
                      refine ⟨45159083121072640658045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 120424221656193708421453 45159083121072640658045)
                      ·
                        rfl

theorem cell23_87947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 3].length) (baseStart_87947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87947 prefixEnd_87947 := by exact prefixLift 87947
  have htrace : WordTrace (prefixWord ++ tailWord_87947) baseStart_87947 baseEnd_87947 := by
    simpa [prefixWord, tailWord_87947, baseEnd_87947] using wordTrace_append hprefix tailTrace_87947
  have hstable : (prefixWord ++ tailWord_87947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87947).length < 2 ^ (prefixWord ++ tailWord_87947).sum := by decide
  have hdescent : baseEnd_87947 < baseStart_87947 := by decide
  rcases family_descends (prefixWord ++ tailWord_87947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87958 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_87958 : Nat := 118140960795 + 87958 * 2 ^ 59
def prefixEnd_87958 : Nat := 4983230072969 + 3 ^ 40 * 87958 * 2
def baseEnd_87958 : Nat := 15054910469424032540165

theorem tailTrace_87958 : CollatzResearch.WordTrace tailWord_87958 prefixEnd_87958 15054910469424032540165 := by
  unfold tailWord_87958
  simp only [CollatzResearch.WordTrace]
  refine ⟨200505738459416429721533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2138727876900441917029685 200505738459416429721533)
  ·
    refine ⟨75189651922281161145575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 200505738459416429721533 75189651922281161145575)
    ·
      refine ⟨112784477883421741718363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75189651922281161145575 112784477883421741718363)
      ·
        refine ⟨169176716825132612577545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112784477883421741718363 169176716825132612577545)
        ·
          refine ⟨126882537618849459433159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169176716825132612577545 126882537618849459433159)
          ·
            refine ⟨190323806428274189149739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126882537618849459433159 190323806428274189149739)
            ·
              refine ⟨285485709642411283724609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190323806428274189149739 285485709642411283724609)
              ·
                refine ⟨214114282231808462793457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285485709642411283724609 214114282231808462793457)
                ·
                  refine ⟨160585711673856347095093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214114282231808462793457 160585711673856347095093)
                  ·
                    refine ⟨15054910469424032540165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 160585711673856347095093 15054910469424032540165)
                    ·
                      rfl

theorem cell23_87958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_87958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87958 prefixEnd_87958 := by exact prefixLift 87958
  have htrace : WordTrace (prefixWord ++ tailWord_87958) baseStart_87958 baseEnd_87958 := by
    simpa [prefixWord, tailWord_87958, baseEnd_87958] using wordTrace_append hprefix tailTrace_87958
  have hstable : (prefixWord ++ tailWord_87958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87958).length < 2 ^ (prefixWord ++ tailWord_87958).sum := by decide
  have hdescent : baseEnd_87958 < baseStart_87958 := by decide
  rcases family_descends (prefixWord ++ tailWord_87958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87964 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_87964 : Nat := 118140960795 + 87964 * 2 ^ 59
def prefixEnd_87964 : Nat := 4983230072969 + 3 ^ 40 * 87964 * 2
def baseEnd_87964 : Nat := 45167812292199074145467

theorem tailTrace_87964 : CollatzResearch.WordTrace tailWord_87964 prefixEnd_87964 45167812292199074145467 := by
  unfold tailWord_87964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604155326664462950131473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2138873768885950600175297 1604155326664462950131473)
  ·
    refine ⟨1203116494998347212598605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1604155326664462950131473 1203116494998347212598605)
    ·
      refine ⟨451168685624380204724477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1203116494998347212598605 451168685624380204724477)
      ·
        refine ⟨169188257109142576771679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451168685624380204724477 169188257109142576771679)
        ·
          refine ⟨253782385663713865157519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169188257109142576771679 253782385663713865157519)
          ·
            refine ⟨380673578495570797736279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253782385663713865157519 380673578495570797736279)
            ·
              refine ⟨571010367743356196604419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380673578495570797736279 571010367743356196604419)
              ·
                refine ⟨856515551615034294906629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571010367743356196604419 856515551615034294906629)
                ·
                  refine ⟨160596665927818930294993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 856515551615034294906629 160596665927818930294993)
                  ·
                    refine ⟨120447499445864197721245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160596665927818930294993 120447499445864197721245)
                    ·
                      refine ⟨45167812292199074145467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 120447499445864197721245 45167812292199074145467)
                      ·
                        rfl

theorem cell23_87964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_87964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_87964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_87964 prefixEnd_87964 := by exact prefixLift 87964
  have htrace : WordTrace (prefixWord ++ tailWord_87964) baseStart_87964 baseEnd_87964 := by
    simpa [prefixWord, tailWord_87964, baseEnd_87964] using wordTrace_append hprefix tailTrace_87964
  have hstable : (prefixWord ++ tailWord_87964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87964).length < 2 ^ (prefixWord ++ tailWord_87964).sum := by decide
  have hdescent : baseEnd_87964 < baseStart_87964 := by decide
  rcases family_descends (prefixWord ++ tailWord_87964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88011 : List Nat := [1, 1, 1, 1, 3, 4, 2, 5, 1, 1, 3]
def baseStart_88011 : Nat := 118140960795 + 88011 * 2 ^ 59
def prefixEnd_88011 : Nat := 4983230072969 + 3 ^ 40 * 88011 * 2
def baseEnd_88011 : Nat := 45191945882960390257751

theorem tailTrace_88011 : CollatzResearch.WordTrace tailWord_88011 prefixEnd_88011 45191945882960390257751 := by
  unfold tailWord_88011
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210024884158652927223887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2140016589439101951482591 3210024884158652927223887)
  ·
    refine ⟨4815037326237979390835831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3210024884158652927223887 4815037326237979390835831)
    ·
      refine ⟨7222555989356969086253747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4815037326237979390835831 7222555989356969086253747)
      ·
        refine ⟨10833833984035453629380621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7222555989356969086253747 10833833984035453629380621)
        ·
          refine ⟨4062687744013295111017733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10833833984035453629380621 4062687744013295111017733)
          ·
            refine ⟨761753952002492833315825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4062687744013295111017733 761753952002492833315825)
            ·
              refine ⟨571315464001869624986869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 761753952002492833315825 571315464001869624986869)
              ·
                refine ⟨53560824750175277342519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 571315464001869624986869 53560824750175277342519)
                ·
                  refine ⟨80341237125262916013779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53560824750175277342519 80341237125262916013779)
                  ·
                    refine ⟨120511855687894374020669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 80341237125262916013779 120511855687894374020669)
                    ·
                      refine ⟨45191945882960390257751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 120511855687894374020669 45191945882960390257751)
                      ·
                        rfl

theorem cell23_88011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 1, 1, 3].length) (baseStart_88011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88011 prefixEnd_88011 := by exact prefixLift 88011
  have htrace : WordTrace (prefixWord ++ tailWord_88011) baseStart_88011 baseEnd_88011 := by
    simpa [prefixWord, tailWord_88011, baseEnd_88011] using wordTrace_append hprefix tailTrace_88011
  have hstable : (prefixWord ++ tailWord_88011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88011).length < 2 ^ (prefixWord ++ tailWord_88011).sum := by decide
  have hdescent : baseEnd_88011 < baseStart_88011 := by decide
  rcases family_descends (prefixWord ++ tailWord_88011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88021 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 2, 3, 2]
def baseStart_88021 : Nat := 118140960795 + 88021 * 2 ^ 59
def prefixEnd_88021 : Nat := 4983230072969 + 3 ^ 40 * 88021 * 2
def baseEnd_88021 : Nat := 45197080689505351132705

theorem tailTrace_88021 : CollatzResearch.WordTrace tailWord_88021 prefixEnd_88021 45197080689505351132705 := by
  unfold tailWord_88021
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210389614122424635087917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2140259742748283090058611 3210389614122424635087917)
  ·
    refine ⟨1203896105295909238157969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3210389614122424635087917 1203896105295909238157969)
    ·
      refine ⟨902922078971931928618477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1203896105295909238157969 902922078971931928618477)
      ·
        refine ⟨338595779614474473231929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 902922078971931928618477 338595779614474473231929)
        ·
          refine ⟨253946834710855854923947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338595779614474473231929 253946834710855854923947)
          ·
            refine ⟨380920252066283782385921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253946834710855854923947 380920252066283782385921)
            ·
              refine ⟨285690189049712836789441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380920252066283782385921 285690189049712836789441)
              ·
                refine ⟨214267641787284627592081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285690189049712836789441 214267641787284627592081)
                ·
                  refine ⟨160700731340463470694061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214267641787284627592081 160700731340463470694061)
                  ·
                    refine ⟨60262774252673801510273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160700731340463470694061 60262774252673801510273)
                    ·
                      refine ⟨45197080689505351132705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 60262774252673801510273 45197080689505351132705)
                      ·
                        rfl

theorem cell23_88021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_88021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88021 prefixEnd_88021 := by exact prefixLift 88021
  have htrace : WordTrace (prefixWord ++ tailWord_88021) baseStart_88021 baseEnd_88021 := by
    simpa [prefixWord, tailWord_88021, baseEnd_88021] using wordTrace_append hprefix tailTrace_88021
  have hstable : (prefixWord ++ tailWord_88021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88021).length < 2 ^ (prefixWord ++ tailWord_88021).sum := by decide
  have hdescent : baseEnd_88021 < baseStart_88021 := by decide
  rcases family_descends (prefixWord ++ tailWord_88021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88022 : List Nat := [5, 2, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_88022 : Nat := 118140960795 + 88022 * 2 ^ 59
def prefixEnd_88022 : Nat := 4983230072969 + 3 ^ 40 * 88022 * 2
def baseEnd_88022 : Nat := 15065864723386615740067

theorem tailTrace_88022 : CollatzResearch.WordTrace tailWord_88022 prefixEnd_88022 15065864723386615740067 := by
  unfold tailWord_88022
  simp only [CollatzResearch.WordTrace]
  refine ⟨200651630444925112867145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2140284058079201203916213 200651630444925112867145)
  ·
    refine ⟨150488722833693834650359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200651630444925112867145 150488722833693834650359)
    ·
      refine ⟨225733084250540751975539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150488722833693834650359 225733084250540751975539)
      ·
        refine ⟨338599626375811127963309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225733084250540751975539 338599626375811127963309)
        ·
          refine ⟨126974859890929172986241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338599626375811127963309 126974859890929172986241)
          ·
            refine ⟨95231144918196879739681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126974859890929172986241 95231144918196879739681)
            ·
              refine ⟨71423358688647659804761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95231144918196879739681 71423358688647659804761)
              ·
                refine ⟨53567519016485744853571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71423358688647659804761 53567519016485744853571)
                ·
                  refine ⟨80351278524728617280357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53567519016485744853571 80351278524728617280357)
                  ·
                    refine ⟨15065864723386615740067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 80351278524728617280357 15065864723386615740067)
                    ·
                      rfl

theorem cell23_88022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_88022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88022 prefixEnd_88022 := by exact prefixLift 88022
  have htrace : WordTrace (prefixWord ++ tailWord_88022) baseStart_88022 baseEnd_88022 := by
    simpa [prefixWord, tailWord_88022, baseEnd_88022] using wordTrace_append hprefix tailTrace_88022
  have hstable : (prefixWord ++ tailWord_88022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88022).length < 2 ^ (prefixWord ++ tailWord_88022).sum := by decide
  have hdescent : baseEnd_88022 < baseStart_88022 := by decide
  rcases family_descends (prefixWord ++ tailWord_88022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88068 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_88068 : Nat := 118140960795 + 88068 * 2 ^ 59
def prefixEnd_88068 : Nat := 4983230072969 + 3 ^ 40 * 88068 * 2
def baseEnd_88068 : Nat := 45221214280266667244989

theorem tailTrace_88068 : CollatzResearch.WordTrace tailWord_88068 prefixEnd_88068 45221214280266667244989 := by
  unfold tailWord_88068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1606051922476075831024429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2141402563301434441365905 1606051922476075831024429)
  ·
    refine ⟨602269470928528436634161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1606051922476075831024429 602269470928528436634161)
    ·
      refine ⟨451702103196396327475621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 602269470928528436634161 451702103196396327475621)
      ·
        refine ⟨84694144349324311401679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 451702103196396327475621 84694144349324311401679)
        ·
          refine ⟨127041216523986467102519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84694144349324311401679 127041216523986467102519)
          ·
            refine ⟨190561824785979700653779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127041216523986467102519 190561824785979700653779)
            ·
              refine ⟨285842737178969550980669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190561824785979700653779 285842737178969550980669)
              ·
                refine ⟨107191026442113581617751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285842737178969550980669 107191026442113581617751)
                ·
                  refine ⟨160786539663170372426627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107191026442113581617751 160786539663170372426627)
                  ·
                    refine ⟨241179809494755558639941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 160786539663170372426627 241179809494755558639941)
                    ·
                      refine ⟨45221214280266667244989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 241179809494755558639941 45221214280266667244989)
                      ·
                        rfl

theorem cell23_88068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_88068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88068 prefixEnd_88068 := by exact prefixLift 88068
  have htrace : WordTrace (prefixWord ++ tailWord_88068) baseStart_88068 baseEnd_88068 := by
    simpa [prefixWord, tailWord_88068, baseEnd_88068] using wordTrace_append hprefix tailTrace_88068
  have hstable : (prefixWord ++ tailWord_88068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88068).length < 2 ^ (prefixWord ++ tailWord_88068).sum := by decide
  have hdescent : baseEnd_88068 < baseStart_88068 := by decide
  rcases family_descends (prefixWord ++ tailWord_88068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88071 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_88071 : Nat := 118140960795 + 88071 * 2 ^ 59
def prefixEnd_88071 : Nat := 4983230072969 + 3 ^ 40 * 88071 * 2
def baseEnd_88071 : Nat := 45222754722230155507475

theorem tailTrace_88071 : CollatzResearch.WordTrace tailWord_88071 prefixEnd_88071 45222754722230155507475 := by
  unfold tailWord_88071
  simp only [CollatzResearch.WordTrace]
  refine ⟨3212213263941283174408067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2141475509294188782938711 3212213263941283174408067)
  ·
    refine ⟨4818319895911924761612101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3212213263941283174408067 4818319895911924761612101)
    ·
      refine ⟨903434980483485892802269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4818319895911924761612101 903434980483485892802269)
      ·
        refine ⟨338788117681307209800851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 903434980483485892802269 338788117681307209800851)
        ·
          refine ⟨508182176521960814701277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338788117681307209800851 508182176521960814701277)
          ·
            refine ⟨190568316195735305512979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 508182176521960814701277 190568316195735305512979)
            ·
              refine ⟨285852474293602958269469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190568316195735305512979 285852474293602958269469)
              ·
                refine ⟨107194677860101109351051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285852474293602958269469 107194677860101109351051)
                ·
                  refine ⟨160792016790151664026577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107194677860101109351051 160792016790151664026577)
                  ·
                    refine ⟨120594012592613748019933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160792016790151664026577 120594012592613748019933)
                    ·
                      refine ⟨45222754722230155507475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 120594012592613748019933 45222754722230155507475)
                      ·
                        rfl

theorem cell23_88071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_88071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88071 prefixEnd_88071 := by exact prefixLift 88071
  have htrace : WordTrace (prefixWord ++ tailWord_88071) baseStart_88071 baseEnd_88071 := by
    simpa [prefixWord, tailWord_88071, baseEnd_88071] using wordTrace_append hprefix tailTrace_88071
  have hstable : (prefixWord ++ tailWord_88071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88071).length < 2 ^ (prefixWord ++ tailWord_88071).sum := by decide
  have hdescent : baseEnd_88071 < baseStart_88071 := by decide
  rcases family_descends (prefixWord ++ tailWord_88071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88101 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 1, 3, 3]
def baseStart_88101 : Nat := 118140960795 + 88101 * 2 ^ 59
def prefixEnd_88101 : Nat := 4983230072969 + 3 ^ 40 * 88101 * 2
def baseEnd_88101 : Nat := 45238159141865038132337

theorem tailTrace_88101 : CollatzResearch.WordTrace tailWord_88101 prefixEnd_88101 45238159141865038132337 := by
  unfold tailWord_88101
  simp only [CollatzResearch.WordTrace]
  refine ⟨3213307453832598298000157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2142204969221732198666771 3213307453832598298000157)
  ·
    refine ⟨1204990295187224361750059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3213307453832598298000157 1204990295187224361750059)
    ·
      refine ⟨1807485442780836542625089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1204990295187224361750059 1807485442780836542625089)
      ·
        refine ⟨1355614082085627406968817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1807485442780836542625089 1355614082085627406968817)
        ·
          refine ⟨1016710561564220555226613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1355614082085627406968817 1016710561564220555226613)
          ·
            refine ⟨95316615146645677052495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1016710561564220555226613 95316615146645677052495)
            ·
              refine ⟨142974922719968515578743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95316615146645677052495 142974922719968515578743)
              ·
                refine ⟨214462384079952773368115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142974922719968515578743 214462384079952773368115)
                ·
                  refine ⟨321693576119929160052173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214462384079952773368115 321693576119929160052173)
                  ·
                    refine ⟨120635091044973435019565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 321693576119929160052173 120635091044973435019565)
                    ·
                      refine ⟨45238159141865038132337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 120635091044973435019565 45238159141865038132337)
                      ·
                        rfl

theorem cell23_88101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_88101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_88101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_88101 prefixEnd_88101 := by exact prefixLift 88101
  have htrace : WordTrace (prefixWord ++ tailWord_88101) baseStart_88101 baseEnd_88101 := by
    simpa [prefixWord, tailWord_88101, baseEnd_88101] using wordTrace_append hprefix tailTrace_88101
  have hstable : (prefixWord ++ tailWord_88101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88101).length < 2 ^ (prefixWord ++ tailWord_88101).sum := by decide
  have hdescent : baseEnd_88101 < baseStart_88101 := by decide
  rcases family_descends (prefixWord ++ tailWord_88101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
