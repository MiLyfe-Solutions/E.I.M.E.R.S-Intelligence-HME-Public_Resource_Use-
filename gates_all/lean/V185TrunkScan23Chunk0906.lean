import V185TrunkScan23Chunk0905

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5361977 : List Nat := [1, 2, 1, 6, 1, 2, 2, 3, 1, 4]
def baseStart_5361977 : Nat := 118140960795 + 5361977 * 2 ^ 59
def prefixEnd_5361977 : Nat := 4983230072969 + 3 ^ 40 * 5361977 * 2
def baseEnd_5361977 : Nat := 917757153117690991342741

theorem tailTrace_5361977 : CollatzResearch.WordTrace tailWord_5361977 prefixEnd_5361977 917757153117690991342741 := by
  unfold tailWord_5361977
  simp only [CollatzResearch.WordTrace]
  refine ⟨195567367695480556609908185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130378245130320371073272123 195567367695480556609908185)
  ·
    refine ⟨146675525771610417457431139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195567367695480556609908185 146675525771610417457431139)
    ·
      refine ⟨220013288657415626186146709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146675525771610417457431139 220013288657415626186146709)
      ·
        refine ⟨10313122905816357477475627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 220013288657415626186146709 10313122905816357477475627)
        ·
          refine ⟨15469684358724536216213441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10313122905816357477475627 15469684358724536216213441)
          ·
            refine ⟨11602263269043402162160081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15469684358724536216213441 11602263269043402162160081)
            ·
              refine ⟨8701697451782551621620061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11602263269043402162160081 8701697451782551621620061)
              ·
                refine ⟨3263136544418456858107523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8701697451782551621620061 3263136544418456858107523)
                ·
                  refine ⟨4894704816627685287161285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263136544418456858107523 4894704816627685287161285)
                  ·
                    refine ⟨917757153117690991342741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4894704816627685287161285 917757153117690991342741)
                    ·
                      rfl

theorem cell23_5361977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 1, 4].length) (baseStart_5361977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361977 prefixEnd_5361977 := by exact prefixLift 5361977
  have htrace : WordTrace (prefixWord ++ tailWord_5361977) baseStart_5361977 baseEnd_5361977 := by
    simpa [prefixWord, tailWord_5361977, baseEnd_5361977] using wordTrace_append hprefix tailTrace_5361977
  have hstable : (prefixWord ++ tailWord_5361977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361977).length < 2 ^ (prefixWord ++ tailWord_5361977).sum := by decide
  have hdescent : baseEnd_5361977 < baseStart_5361977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361983 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 5, 1, 3]
def baseStart_5361983 : Nat := 118140960795 + 5361983 * 2 ^ 59
def prefixEnd_5361983 : Nat := 4983230072969 + 3 ^ 40 * 5361983 * 2
def baseEnd_5361983 : Nat := 2753274540236999950553195

theorem tailTrace_5361983 : CollatzResearch.WordTrace tailWord_5361983 prefixEnd_5361983 2753274540236999950553195 := by
  unfold tailWord_5361983
  simp only [CollatzResearch.WordTrace]
  refine ⟨195567586533458819634626603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130378391022305879756417735 195567586533458819634626603)
  ·
    refine ⟨293351379800188229451939905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195567586533458819634626603 293351379800188229451939905)
    ·
      refine ⟨220013534850141172088954929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293351379800188229451939905 220013534850141172088954929)
      ·
        refine ⟨165010151137605879066716197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220013534850141172088954929 165010151137605879066716197)
        ·
          refine ⟨30939403338301102325009287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165010151137605879066716197 30939403338301102325009287)
          ·
            refine ⟨46409105007451653487513931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30939403338301102325009287 46409105007451653487513931)
            ·
              refine ⟨69613657511177480231270897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46409105007451653487513931 69613657511177480231270897)
              ·
                refine ⟨52210243133383110173453173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69613657511177480231270897 52210243133383110173453173)
                ·
                  refine ⟨4894710293754666578761235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52210243133383110173453173 4894710293754666578761235)
                  ·
                    refine ⟨7342065440631999868141853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4894710293754666578761235 7342065440631999868141853)
                    ·
                      refine ⟨2753274540236999950553195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7342065440631999868141853 2753274540236999950553195)
                      ·
                        rfl

theorem cell23_5361983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_5361983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361983 prefixEnd_5361983 := by exact prefixLift 5361983
  have htrace : WordTrace (prefixWord ++ tailWord_5361983) baseStart_5361983 baseEnd_5361983 := by
    simpa [prefixWord, tailWord_5361983, baseEnd_5361983] using wordTrace_append hprefix tailTrace_5361983
  have hstable : (prefixWord ++ tailWord_5361983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361983).length < 2 ^ (prefixWord ++ tailWord_5361983).sum := by decide
  have hdescent : baseEnd_5361983 < baseStart_5361983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5361993 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 4, 3, 2]
def baseStart_5361993 : Nat := 118140960795 + 5361993 * 2 ^ 59
def prefixEnd_5361993 : Nat := 4983230072969 + 3 ^ 40 * 5361993 * 2
def baseEnd_5361993 : Nat := 2753279675043544911428149

theorem tailTrace_5361993 : CollatzResearch.WordTrace tailWord_5361993 prefixEnd_5361993 2753279675043544911428149 := by
  unfold tailWord_5361993
  simp only [CollatzResearch.WordTrace]
  refine ⟨195567951263422591342490633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130378634175615060894993755 195567951263422591342490633)
  ·
    refine ⟨146675963447566943506867975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195567951263422591342490633 146675963447566943506867975)
    ·
      refine ⟨220013945171350415260301963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146675963447566943506867975 220013945171350415260301963)
      ·
        refine ⟨330020917757025622890452945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220013945171350415260301963 330020917757025622890452945)
        ·
          refine ⟨247515688317769217167839709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330020917757025622890452945 247515688317769217167839709)
          ·
            refine ⟨92818383119163456437939891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247515688317769217167839709 92818383119163456437939891)
            ·
              refine ⟨139227574678745184656909837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92818383119163456437939891 139227574678745184656909837)
              ·
                refine ⟨52210340504529444246341189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139227574678745184656909837 52210340504529444246341189)
                ·
                  refine ⟨9789438844599270796188973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52210340504529444246341189 9789438844599270796188973)
                  ·
                    refine ⟨3671039566724726548570865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9789438844599270796188973 3671039566724726548570865)
                    ·
                      refine ⟨2753279675043544911428149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671039566724726548570865 2753279675043544911428149)
                      ·
                        rfl

theorem cell23_5361993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 3, 2].length) (baseStart_5361993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5361993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5361993 prefixEnd_5361993 := by exact prefixLift 5361993
  have htrace : WordTrace (prefixWord ++ tailWord_5361993) baseStart_5361993 baseEnd_5361993 := by
    simpa [prefixWord, tailWord_5361993, baseEnd_5361993] using wordTrace_append hprefix tailTrace_5361993
  have hstable : (prefixWord ++ tailWord_5361993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5361993).length < 2 ^ (prefixWord ++ tailWord_5361993).sum := by decide
  have hdescent : baseEnd_5361993 < baseStart_5361993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5361993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362000 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 3, 1, 3]
def baseStart_5362000 : Nat := 118140960795 + 5362000 * 2 ^ 59
def prefixEnd_5362000 : Nat := 4983230072969 + 3 ^ 40 * 5362000 * 2
def baseEnd_5362000 : Nat := 2753283269408126384040617

theorem tailTrace_5362000 : CollatzResearch.WordTrace tailWord_5362000 prefixEnd_5362000 2753283269408126384040617 := by
  unfold tailWord_5362000
  simp only [CollatzResearch.WordTrace]
  refine ⟨97784103287198615768997727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130378804382931487691996969 97784103287198615768997727)
  ·
    refine ⟨146676154930797923653496591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97784103287198615768997727 146676154930797923653496591)
    ·
      refine ⟨220014232396196885480244887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146676154930797923653496591 220014232396196885480244887)
      ·
        refine ⟨330021348594295328220367331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220014232396196885480244887 330021348594295328220367331)
        ·
          refine ⟨495032022891442992330550997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330021348594295328220367331 495032022891442992330550997)
          ·
            refine ⟨11602313036518195132747289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 495032022891442992330550997 11602313036518195132747289)
            ·
              refine ⟨8701734777388646349560467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11602313036518195132747289 8701734777388646349560467)
              ·
                refine ⟨13052602166082969524340701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8701734777388646349560467 13052602166082969524340701)
                ·
                  refine ⟨4894725812281113571627763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13052602166082969524340701 4894725812281113571627763)
                  ·
                    refine ⟨7342088718421670357441645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4894725812281113571627763 7342088718421670357441645)
                    ·
                      refine ⟨2753283269408126384040617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7342088718421670357441645 2753283269408126384040617)
                      ·
                        rfl

theorem cell23_5362000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 3, 1, 3].length) (baseStart_5362000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362000 prefixEnd_5362000 := by exact prefixLift 5362000
  have htrace : WordTrace (prefixWord ++ tailWord_5362000) baseStart_5362000 baseEnd_5362000 := by
    simpa [prefixWord, tailWord_5362000, baseEnd_5362000] using wordTrace_append hprefix tailTrace_5362000
  have hstable : (prefixWord ++ tailWord_5362000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362000).length < 2 ^ (prefixWord ++ tailWord_5362000).sum := by decide
  have hdescent : baseEnd_5362000 < baseStart_5362000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362034 : List Nat := [3, 2, 1, 2, 1, 5, 1, 3, 1, 1, 3]
def baseStart_5362034 : Nat := 118140960795 + 5362034 * 2 ^ 59
def prefixEnd_5362034 : Nat := 4983230072969 + 3 ^ 40 * 5362034 * 2
def baseEnd_5362034 : Nat := 2753300727750379251015461

theorem tailTrace_5362034 : CollatzResearch.WordTrace tailWord_5362034 prefixEnd_5362034 2753300727750379251015461 := by
  unfold tailWord_5362034
  simp only [CollatzResearch.WordTrace]
  refine ⟨48892361664068513836183289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130379631104182703563155437 48892361664068513836183289)
  ·
    refine ⟨36669271248051385377137467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48892361664068513836183289 36669271248051385377137467)
    ·
      refine ⟨55003906872077078065706201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36669271248051385377137467 55003906872077078065706201)
      ·
        refine ⟨41252930154057808549279651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55003906872077078065706201 41252930154057808549279651)
        ·
          refine ⟨61879395231086712823919477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41252930154057808549279651 61879395231086712823919477)
          ·
            refine ⟨5801193302914379327242451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61879395231086712823919477 5801193302914379327242451)
            ·
              refine ⟨8701789954371568990863677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801193302914379327242451 8701789954371568990863677)
              ·
                refine ⟨3263171232889338371573879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8701789954371568990863677 3263171232889338371573879)
                ·
                  refine ⟨4894756849334007557360819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263171232889338371573879 4894756849334007557360819)
                  ·
                    refine ⟨7342135274001011336041229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4894756849334007557360819 7342135274001011336041229)
                    ·
                      refine ⟨2753300727750379251015461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7342135274001011336041229 2753300727750379251015461)
                      ·
                        rfl

theorem cell23_5362034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_5362034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362034 prefixEnd_5362034 := by exact prefixLift 5362034
  have htrace : WordTrace (prefixWord ++ tailWord_5362034) baseStart_5362034 baseEnd_5362034 := by
    simpa [prefixWord, tailWord_5362034, baseEnd_5362034] using wordTrace_append hprefix tailTrace_5362034
  have hstable : (prefixWord ++ tailWord_5362034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362034).length < 2 ^ (prefixWord ++ tailWord_5362034).sum := by decide
  have hdescent : baseEnd_5362034 < baseStart_5362034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362043 : List Nat := [1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 5]
def baseStart_5362043 : Nat := 118140960795 + 5362043 * 2 ^ 59
def prefixEnd_5362043 : Nat := 4983230072969 + 3 ^ 40 * 5362043 * 2
def baseEnd_5362043 : Nat := 2753305349076269715802919

theorem tailTrace_5362043 : CollatzResearch.WordTrace tailWord_5362043 prefixEnd_5362043 2753305349076269715802919 := by
  unfold tailWord_5362043
  simp only [CollatzResearch.WordTrace]
  refine ⟨195569774913241449881810783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130379849942160966587873855 195569774913241449881810783)
  ·
    refine ⟨293354662369862174822716175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195569774913241449881810783 293354662369862174822716175)
    ·
      refine ⟨440031993554793262234074263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293354662369862174822716175 440031993554793262234074263)
      ·
        refine ⟨660047990332189893351111395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440031993554793262234074263 660047990332189893351111395)
        ·
          refine ⟨990071985498284840026667093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660047990332189893351111395 990071985498284840026667093)
          ·
            refine ⟨11602406080058025469062505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 990071985498284840026667093 11602406080058025469062505)
            ·
              refine ⟨8701804560043519101796879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11602406080058025469062505 8701804560043519101796879)
              ·
                refine ⟨13052706840065278652695319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8701804560043519101796879 13052706840065278652695319)
                ·
                  refine ⟨19579060260097917979042979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13052706840065278652695319 19579060260097917979042979)
                  ·
                    refine ⟨29368590390146876968564469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19579060260097917979042979 29368590390146876968564469)
                    ·
                      refine ⟨2753305349076269715802919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29368590390146876968564469 2753305349076269715802919)
                      ·
                        rfl

theorem cell23_5362043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 5].length) (baseStart_5362043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362043 prefixEnd_5362043 := by exact prefixLift 5362043
  have htrace : WordTrace (prefixWord ++ tailWord_5362043) baseStart_5362043 baseEnd_5362043 := by
    simpa [prefixWord, tailWord_5362043, baseEnd_5362043] using wordTrace_append hprefix tailTrace_5362043
  have hstable : (prefixWord ++ tailWord_5362043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362043).length < 2 ^ (prefixWord ++ tailWord_5362043).sum := by decide
  have hdescent : baseEnd_5362043 < baseStart_5362043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362057 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 3, 2, 2]
def baseStart_5362057 : Nat := 118140960795 + 5362057 * 2 ^ 59
def prefixEnd_5362057 : Nat := 4983230072969 + 3 ^ 40 * 5362057 * 2
def baseEnd_5362057 : Nat := 2753312537805432661027855

theorem tailTrace_5362057 : CollatzResearch.WordTrace tailWord_5362057 prefixEnd_5362057 2753312537805432661027855 := by
  unfold tailWord_5362057
  simp only [CollatzResearch.WordTrace]
  refine ⟨195570285535190730272820425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130380190356793820181880283 195570285535190730272820425)
  ·
    refine ⟨146677714151393047704615319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195570285535190730272820425 146677714151393047704615319)
    ·
      refine ⟨220016571227089571556922979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146677714151393047704615319 220016571227089571556922979)
      ·
        refine ⟨330024856840634357335384469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220016571227089571556922979 330024856840634357335384469)
        ·
          refine ⟨15469915164404735500096147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 330024856840634357335384469 15469915164404735500096147)
          ·
            refine ⟨23204872746607103250144221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15469915164404735500096147 23204872746607103250144221)
            ·
              refine ⟨8701827279977663718804083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23204872746607103250144221 8701827279977663718804083)
              ·
                refine ⟨13052740919966495578206125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8701827279977663718804083 13052740919966495578206125)
                ·
                  refine ⟨4894777844987435841827297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13052740919966495578206125 4894777844987435841827297)
                  ·
                    refine ⟨3671083383740576881370473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4894777844987435841827297 3671083383740576881370473)
                    ·
                      refine ⟨2753312537805432661027855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671083383740576881370473 2753312537805432661027855)
                      ·
                        rfl

theorem cell23_5362057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 2, 2].length) (baseStart_5362057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362057 prefixEnd_5362057 := by exact prefixLift 5362057
  have htrace : WordTrace (prefixWord ++ tailWord_5362057) baseStart_5362057 baseEnd_5362057 := by
    simpa [prefixWord, tailWord_5362057, baseEnd_5362057] using wordTrace_append hprefix tailTrace_5362057
  have hstable : (prefixWord ++ tailWord_5362057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362057).length < 2 ^ (prefixWord ++ tailWord_5362057).sum := by decide
  have hdescent : baseEnd_5362057 < baseStart_5362057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362073 : List Nat := [1, 2, 1, 2, 1, 4, 2, 3, 1, 3, 3]
def baseStart_5362073 : Nat := 118140960795 + 5362073 * 2 ^ 59
def prefixEnd_5362073 : Nat := 4983230072969 + 3 ^ 40 * 5362073 * 2
def baseEnd_5362073 : Nat := 2753320753495904598427781

theorem tailTrace_5362073 : CollatzResearch.WordTrace tailWord_5362073 prefixEnd_5362073 2753320753495904598427781 := by
  unfold tailWord_5362073
  simp only [CollatzResearch.WordTrace]
  refine ⟨195570869103132765005402873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130380579402088510003601915 195570869103132765005402873)
  ·
    refine ⟨146678151827349573754052155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195570869103132765005402873 146678151827349573754052155)
    ·
      refine ⟨220017227741024360631078233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146678151827349573754052155 220017227741024360631078233)
      ·
        refine ⟨165012920805768270473308675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220017227741024360631078233 165012920805768270473308675)
        ·
          refine ⟨247519381208652405709963013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165012920805768270473308675 247519381208652405709963013)
          ·
            refine ⟨46409883976622326070618065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247519381208652405709963013 46409883976622326070618065)
            ·
              refine ⟨34807412982466744552963549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46409883976622326070618065 34807412982466744552963549)
              ·
                refine ⟨13052779868425029207361331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34807412982466744552963549 13052779868425029207361331)
                ·
                  refine ⟨19579169802637543811041997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13052779868425029207361331 19579169802637543811041997)
                  ·
                    refine ⟨7342188675989078929140749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19579169802637543811041997 7342188675989078929140749)
                    ·
                      refine ⟨2753320753495904598427781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7342188675989078929140749 2753320753495904598427781)
                      ·
                        rfl

theorem cell23_5362073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3, 3].length) (baseStart_5362073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362073 prefixEnd_5362073 := by exact prefixLift 5362073
  have htrace : WordTrace (prefixWord ++ tailWord_5362073) baseStart_5362073 baseEnd_5362073 := by
    simpa [prefixWord, tailWord_5362073, baseEnd_5362073] using wordTrace_append hprefix tailTrace_5362073
  have hstable : (prefixWord ++ tailWord_5362073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362073).length < 2 ^ (prefixWord ++ tailWord_5362073).sum := by decide
  have hdescent : baseEnd_5362073 < baseStart_5362073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362106 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 3, 8]
def baseStart_5362106 : Nat := 118140960795 + 5362106 * 2 ^ 59
def prefixEnd_5362106 : Nat := 4983230072969 + 3 ^ 40 * 5362106 * 2
def baseEnd_5362106 : Nat := 917779232785834323105043

theorem tailTrace_5362106 : CollatzResearch.WordTrace tailWord_5362106 prefixEnd_5362106 917779232785834323105043 := by
  unfold tailWord_5362106
  simp only [CollatzResearch.WordTrace]
  refine ⟨48893018178003302910338543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130381381808008807760902781 48893018178003302910338543)
  ·
    refine ⟨73339527267004954365507815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48893018178003302910338543 73339527267004954365507815)
    ·
      refine ⟨110009290900507431548261723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73339527267004954365507815 110009290900507431548261723)
      ·
        refine ⟨165013936350761147322392585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110009290900507431548261723 165013936350761147322392585)
        ·
          refine ⟨123760452263070860491794439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165013936350761147322392585 123760452263070860491794439)
          ·
            refine ⟨185640678394606290737691659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123760452263070860491794439 185640678394606290737691659)
            ·
              refine ⟨278461017591909436106537489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185640678394606290737691659 278461017591909436106537489)
              ·
                refine ⟨208845763193932077079903117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278461017591909436106537489 208845763193932077079903117)
                ·
                  refine ⟨78317161197724528904963669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208845763193932077079903117 78317161197724528904963669)
                  ·
                    refine ⟨917779232785834323105043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78317161197724528904963669 917779232785834323105043)
                    ·
                      rfl

theorem cell23_5362106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_5362106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362106 prefixEnd_5362106 := by exact prefixLift 5362106
  have htrace : WordTrace (prefixWord ++ tailWord_5362106) baseStart_5362106 baseEnd_5362106 := by
    simpa [prefixWord, tailWord_5362106, baseEnd_5362106] using wordTrace_append hprefix tailTrace_5362106
  have hstable : (prefixWord ++ tailWord_5362106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362106).length < 2 ^ (prefixWord ++ tailWord_5362106).sum := by decide
  have hdescent : baseEnd_5362106 < baseStart_5362106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362108 : List Nat := [2, 2, 2, 4, 1, 3, 2, 2, 1, 2, 2]
def baseStart_5362108 : Nat := 118140960795 + 5362108 * 2 ^ 59
def prefixEnd_5362108 : Nat := 4983230072969 + 3 ^ 40 * 5362108 * 2
def baseEnd_5362108 : Nat := 2753338725318811961490121

theorem tailTrace_5362108 : CollatzResearch.WordTrace tailWord_5362108 prefixEnd_5362108 2753338725318811961490121 := by
  unfold tailWord_5362108
  simp only [CollatzResearch.WordTrace]
  refine ⟨97786072829002982991463489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130381430438670643988617985 97786072829002982991463489)
  ·
    refine ⟨73339554621752237243597617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97786072829002982991463489 73339554621752237243597617)
    ·
      refine ⟨55004665966314177932698213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73339554621752237243597617 55004665966314177932698213)
      ·
        refine ⟨10313374868683908362380915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55004665966314177932698213 10313374868683908362380915)
        ·
          refine ⟨15470062303025862543571373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10313374868683908362380915 15470062303025862543571373)
          ·
            refine ⟨5801273363634698453839265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15470062303025862543571373 5801273363634698453839265)
            ·
              refine ⟨4350955022726023840379449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5801273363634698453839265 4350955022726023840379449)
              ·
                refine ⟨3263216267044517880284587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4350955022726023840379449 3263216267044517880284587)
                ·
                  refine ⟨4894824400566776820426881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263216267044517880284587 4894824400566776820426881)
                  ·
                    refine ⟨3671118300425082615320161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4894824400566776820426881 3671118300425082615320161)
                    ·
                      refine ⟨2753338725318811961490121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671118300425082615320161 2753338725318811961490121)
                      ·
                        rfl

theorem cell23_5362108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_5362108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362108 prefixEnd_5362108 := by exact prefixLift 5362108
  have htrace : WordTrace (prefixWord ++ tailWord_5362108) baseStart_5362108 baseEnd_5362108 := by
    simpa [prefixWord, tailWord_5362108, baseEnd_5362108] using wordTrace_append hprefix tailTrace_5362108
  have hstable : (prefixWord ++ tailWord_5362108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362108).length < 2 ^ (prefixWord ++ tailWord_5362108).sum := by decide
  have hdescent : baseEnd_5362108 < baseStart_5362108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362134 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2]
def baseStart_5362134 : Nat := 118140960795 + 5362134 * 2 ^ 59
def prefixEnd_5362134 : Nat := 4983230072969 + 3 ^ 40 * 5362134 * 2
def baseEnd_5362134 : Nat := 2753352075815828859765001

theorem tailTrace_5362134 : CollatzResearch.WordTrace tailWord_5362134 prefixEnd_5362134 2753352075815828859765001 := by
  unfold tailWord_5362134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12223318372244485776460841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130382062637274514948915637 12223318372244485776460841)
  ·
    refine ⟨9167488779183364332345631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12223318372244485776460841 9167488779183364332345631)
    ·
      refine ⟨13751233168775046498518447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9167488779183364332345631 13751233168775046498518447)
      ·
        refine ⟨20626849753162569747777671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13751233168775046498518447 20626849753162569747777671)
        ·
          refine ⟨30940274629743854621666507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20626849753162569747777671 30940274629743854621666507)
          ·
            refine ⟨46410411944615781932499761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30940274629743854621666507 46410411944615781932499761)
            ·
              refine ⟨34807808958461836449374821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46410411944615781932499761 34807808958461836449374821)
              ·
                refine ⟨6526464179711594334257779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34807808958461836449374821 6526464179711594334257779)
                ·
                  refine ⟨9789696269567391501386669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6526464179711594334257779 9789696269567391501386669)
                  ·
                    refine ⟨3671136101087771813020001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9789696269567391501386669 3671136101087771813020001)
                    ·
                      refine ⟨2753352075815828859765001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671136101087771813020001 2753352075815828859765001)
                      ·
                        rfl

theorem cell23_5362134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_5362134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362134 prefixEnd_5362134 := by exact prefixLift 5362134
  have htrace : WordTrace (prefixWord ++ tailWord_5362134) baseStart_5362134 baseEnd_5362134 := by
    simpa [prefixWord, tailWord_5362134, baseEnd_5362134] using wordTrace_append hprefix tailTrace_5362134
  have hstable : (prefixWord ++ tailWord_5362134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362134).length < 2 ^ (prefixWord ++ tailWord_5362134).sum := by decide
  have hdescent : baseEnd_5362134 < baseStart_5362134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362163 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 3]
def baseStart_5362163 : Nat := 118140960795 + 5362163 * 2 ^ 59
def prefixEnd_5362163 : Nat := 4983230072969 + 3 ^ 40 * 5362163 * 2
def baseEnd_5362163 : Nat := 2753366966754809246302367

theorem tailTrace_5362163 : CollatzResearch.WordTrace tailWord_5362163 prefixEnd_5362163 2753366966754809246302367 := by
  unfold tailWord_5362163
  simp only [CollatzResearch.WordTrace]
  refine ⟨195574151672806710376179143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130382767781871140250786095 195574151672806710376179143)
  ·
    refine ⟨293361227509210065564268715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195574151672806710376179143 293361227509210065564268715)
    ·
      refine ⟨440041841263815098346403073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293361227509210065564268715 440041841263815098346403073)
      ·
        refine ⟨330031380947861323759802305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440041841263815098346403073 330031380947861323759802305)
        ·
          refine ⟨247523535710895992819851729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330031380947861323759802305 247523535710895992819851729)
          ·
            refine ⟨185642651783171994614888797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247523535710895992819851729 185642651783171994614888797)
            ·
              refine ⟨69615994418689497980583299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185642651783171994614888797 69615994418689497980583299)
              ·
                refine ⟨104423991628034246970874949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69615994418689497980583299 104423991628034246970874949)
                ·
                  refine ⟨19579498430256421307039053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104423991628034246970874949 19579498430256421307039053)
                  ·
                    refine ⟨7342311911346157990139645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19579498430256421307039053 7342311911346157990139645)
                    ·
                      refine ⟨2753366966754809246302367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7342311911346157990139645 2753366966754809246302367)
                      ·
                        rfl

theorem cell23_5362163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 3].length) (baseStart_5362163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362163 prefixEnd_5362163 := by exact prefixLift 5362163
  have htrace : WordTrace (prefixWord ++ tailWord_5362163) baseStart_5362163 baseEnd_5362163 := by
    simpa [prefixWord, tailWord_5362163, baseEnd_5362163] using wordTrace_append hprefix tailTrace_5362163
  have hstable : (prefixWord ++ tailWord_5362163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362163).length < 2 ^ (prefixWord ++ tailWord_5362163).sum := by decide
  have hdescent : baseEnd_5362163 < baseStart_5362163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362203 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 4]
def baseStart_5362203 : Nat := 118140960795 + 5362203 * 2 ^ 59
def prefixEnd_5362203 : Nat := 4983230072969 + 3 ^ 40 * 5362203 * 2
def baseEnd_5362203 : Nat := 2753387505980989089802183

theorem tailTrace_5362203 : CollatzResearch.WordTrace tailWord_5362203 prefixEnd_5362203 2753387505980989089802183 := by
  unfold tailWord_5362203
  simp only [CollatzResearch.WordTrace]
  refine ⟨195575610592661797207635263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130383740395107864805090175 195575610592661797207635263)
  ·
    refine ⟨293363415888992695811452895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195575610592661797207635263 293363415888992695811452895)
    ·
      refine ⟨440045123833489043717179343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293363415888992695811452895 440045123833489043717179343)
      ·
        refine ⟨660067685750233565575769015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440045123833489043717179343 660067685750233565575769015)
        ·
          refine ⟨990101528625350348363653523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660067685750233565575769015 990101528625350348363653523)
          ·
            refine ⟨1485152292938025522545480285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990101528625350348363653523 1485152292938025522545480285)
            ·
              refine ⟨556932109851759570954555107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1485152292938025522545480285 556932109851759570954555107)
              ·
                refine ⟨835398164777639356431832661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556932109851759570954555107 835398164777639356431832661)
                ·
                  refine ⟨9789822243487961208185539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 835398164777639356431832661 9789822243487961208185539)
                  ·
                    refine ⟨14684733365231941812278309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9789822243487961208185539 14684733365231941812278309)
                    ·
                      refine ⟨2753387505980989089802183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14684733365231941812278309 2753387505980989089802183)
                      ·
                        rfl

theorem cell23_5362203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 4].length) (baseStart_5362203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362203 prefixEnd_5362203 := by exact prefixLift 5362203
  have htrace : WordTrace (prefixWord ++ tailWord_5362203) baseStart_5362203 baseEnd_5362203 := by
    simpa [prefixWord, tailWord_5362203, baseEnd_5362203] using wordTrace_append hprefix tailTrace_5362203
  have hstable : (prefixWord ++ tailWord_5362203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362203).length < 2 ^ (prefixWord ++ tailWord_5362203).sum := by decide
  have hdescent : baseEnd_5362203 < baseStart_5362203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362220 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 4, 4, 2]
def baseStart_5362220 : Nat := 118140960795 + 5362220 * 2 ^ 59
def prefixEnd_5362220 : Nat := 4983230072969 + 3 ^ 40 * 5362220 * 2
def baseEnd_5362220 : Nat := 2753396235152115523289605

theorem tailTrace_5362220 : CollatzResearch.WordTrace tailWord_5362220 prefixEnd_5362220 2753396235152115523289605 := by
  unfold tailWord_5362220
  simp only [CollatzResearch.WordTrace]
  refine ⟨97788115316800104555502057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130384153755733472740669409 97788115316800104555502057)
  ·
    refine ⟨73341086487600078416626543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97788115316800104555502057 73341086487600078416626543)
    ·
      refine ⟨110011629731400117624939815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73341086487600078416626543 110011629731400117624939815)
      ·
        refine ⟨165017444597100176437409723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110011629731400117624939815 165017444597100176437409723)
        ·
          refine ⟨247526166895650264656114585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165017444597100176437409723 247526166895650264656114585)
          ·
            refine ⟨185644625171737698492085939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247526166895650264656114585 185644625171737698492085939)
            ·
              refine ⟨278466937757606547738128909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185644625171737698492085939 278466937757606547738128909)
              ·
                refine ⟨104425101659102455401798341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278466937757606547738128909 104425101659102455401798341)
                ·
                  refine ⟨19579706561081710387837189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104425101659102455401798341 19579706561081710387837189)
                  ·
                    refine ⟨3671194980202820697719473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19579706561081710387837189 3671194980202820697719473)
                    ·
                      refine ⟨2753396235152115523289605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671194980202820697719473 2753396235152115523289605)
                      ·
                        rfl

theorem cell23_5362220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 4, 2].length) (baseStart_5362220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362220 prefixEnd_5362220 := by exact prefixLift 5362220
  have htrace : WordTrace (prefixWord ++ tailWord_5362220) baseStart_5362220 baseEnd_5362220 := by
    simpa [prefixWord, tailWord_5362220, baseEnd_5362220] using wordTrace_append hprefix tailTrace_5362220
  have hstable : (prefixWord ++ tailWord_5362220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362220).length < 2 ^ (prefixWord ++ tailWord_5362220).sum := by decide
  have hdescent : baseEnd_5362220 < baseStart_5362220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362221 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 7]
def baseStart_5362221 : Nat := 118140960795 + 5362221 * 2 ^ 59
def prefixEnd_5362221 : Nat := 4983230072969 + 3 ^ 40 * 5362221 * 2
def baseEnd_5362221 : Nat := 305932972070307779930789

theorem tailTrace_5362221 : CollatzResearch.WordTrace tailWord_5362221 prefixEnd_5362221 305932972070307779930789 := by
  unfold tailWord_5362221
  simp only [CollatzResearch.WordTrace]
  refine ⟨195576267106596586281790517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130384178071064390854527011 195576267106596586281790517)
  ·
    refine ⟨18335275041243429963917861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195576267106596586281790517 18335275041243429963917861)
    ·
      refine ⟨3437864070233143118234599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18335275041243429963917861 3437864070233143118234599)
      ·
        refine ⟨5156796105349714677351899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3437864070233143118234599 5156796105349714677351899)
        ·
          refine ⟨7735194158024572016027849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5156796105349714677351899 7735194158024572016027849)
          ·
            refine ⟨5801395618518429012020887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7735194158024572016027849 5801395618518429012020887)
            ·
              refine ⟨8702093427777643518031331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801395618518429012020887 8702093427777643518031331)
              ·
                refine ⟨13053140141666465277046997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8702093427777643518031331 13053140141666465277046997)
                ·
                  refine ⟨305932972070307779930789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13053140141666465277046997 305932972070307779930789)
                  ·
                    rfl

theorem cell23_5362221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_5362221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362221 prefixEnd_5362221 := by exact prefixLift 5362221
  have htrace : WordTrace (prefixWord ++ tailWord_5362221) baseStart_5362221 baseEnd_5362221 := by
    simpa [prefixWord, tailWord_5362221, baseEnd_5362221] using wordTrace_append hprefix tailTrace_5362221
  have hstable : (prefixWord ++ tailWord_5362221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362221).length < 2 ^ (prefixWord ++ tailWord_5362221).sum := by decide
  have hdescent : baseEnd_5362221 < baseStart_5362221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362223 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 3]
def baseStart_5362223 : Nat := 118140960795 + 5362223 * 2 ^ 59
def prefixEnd_5362223 : Nat := 4983230072969 + 3 ^ 40 * 5362223 * 2
def baseEnd_5362223 : Nat := 2753397775594079011552091

theorem tailTrace_5362223 : CollatzResearch.WordTrace tailWord_5362223 prefixEnd_5362223 2753397775594079011552091 := by
  unfold tailWord_5362223
  simp only [CollatzResearch.WordTrace]
  refine ⟨195576340052589340623363323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130384226701726227082242215 195576340052589340623363323)
  ·
    refine ⟨293364510078884010935044985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195576340052589340623363323 293364510078884010935044985)
    ·
      refine ⟨220023382559163008201283739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293364510078884010935044985 220023382559163008201283739)
      ·
        refine ⟨330035073838744512301925609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220023382559163008201283739 330035073838744512301925609)
        ·
          refine ⟨247526305379058384226444207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330035073838744512301925609 247526305379058384226444207)
          ·
            refine ⟨371289458068587576339666311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247526305379058384226444207 371289458068587576339666311)
            ·
              refine ⟨556934187102881364509499467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371289458068587576339666311 556934187102881364509499467)
              ·
                refine ⟨835401280654322046764249201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556934187102881364509499467 835401280654322046764249201)
                ·
                  refine ⟨626550960490741535073186901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 835401280654322046764249201 626550960490741535073186901)
                  ·
                    refine ⟨7342394068250877364138909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 626550960490741535073186901 7342394068250877364138909)
                    ·
                      refine ⟨2753397775594079011552091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7342394068250877364138909 2753397775594079011552091)
                      ·
                        rfl

theorem cell23_5362223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 3].length) (baseStart_5362223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362223 prefixEnd_5362223 := by exact prefixLift 5362223
  have htrace : WordTrace (prefixWord ++ tailWord_5362223) baseStart_5362223 baseEnd_5362223 := by
    simpa [prefixWord, tailWord_5362223, baseEnd_5362223] using wordTrace_append hprefix tailTrace_5362223
  have hstable : (prefixWord ++ tailWord_5362223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362223).length < 2 ^ (prefixWord ++ tailWord_5362223).sum := by decide
  have hdescent : baseEnd_5362223 < baseStart_5362223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362257 : List Nat := [1, 2, 2, 1, 3, 4, 2, 1, 2, 2, 3]
def baseStart_5362257 : Nat := 118140960795 + 5362257 * 2 ^ 59
def prefixEnd_5362257 : Nat := 4983230072969 + 3 ^ 40 * 5362257 * 2
def baseEnd_5362257 : Nat := 2753415233936331878526935

theorem tailTrace_5362257 : CollatzResearch.WordTrace tailWord_5362257 prefixEnd_5362257 2753415233936331878526935 := by
  unfold tailWord_5362257
  simp only [CollatzResearch.WordTrace]
  refine ⟨195577580134466164430101025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130385053422977442953400683 195577580134466164430101025)
  ·
    refine ⟨146683185100849623322575769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195577580134466164430101025 146683185100849623322575769)
    ·
      refine ⟨110012388825637217491931827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146683185100849623322575769 110012388825637217491931827)
      ·
        refine ⟨165018583238455826237897741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110012388825637217491931827 165018583238455826237897741)
        ·
          refine ⟨61881968714420934839211653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165018583238455826237897741 61881968714420934839211653)
          ·
            refine ⟨11602869133953925282352185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61881968714420934839211653 11602869133953925282352185)
            ·
              refine ⟨8702151850465443961764139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11602869133953925282352185 8702151850465443961764139)
              ·
                refine ⟨13053227775698165942646209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8702151850465443961764139 13053227775698165942646209)
                ·
                  refine ⟨9789920831773624456984657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13053227775698165942646209 9789920831773624456984657)
                  ·
                    refine ⟨7342440623830218342738493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9789920831773624456984657 7342440623830218342738493)
                    ·
                      refine ⟨2753415233936331878526935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7342440623830218342738493 2753415233936331878526935)
                      ·
                        rfl

theorem cell23_5362257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_5362257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362257 prefixEnd_5362257 := by exact prefixLift 5362257
  have htrace : WordTrace (prefixWord ++ tailWord_5362257) baseStart_5362257 baseEnd_5362257 := by
    simpa [prefixWord, tailWord_5362257, baseEnd_5362257] using wordTrace_append hprefix tailTrace_5362257
  have hstable : (prefixWord ++ tailWord_5362257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362257).length < 2 ^ (prefixWord ++ tailWord_5362257).sum := by decide
  have hdescent : baseEnd_5362257 < baseStart_5362257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362277 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 6]
def baseStart_5362277 : Nat := 118140960795 + 5362277 * 2 ^ 59
def prefixEnd_5362277 : Nat := 4983230072969 + 3 ^ 40 * 5362277 * 2
def baseEnd_5362277 : Nat := 305936167061046866697427

theorem tailTrace_5362277 : CollatzResearch.WordTrace tailWord_5362277 prefixEnd_5362277 305936167061046866697427 := by
  unfold tailWord_5362277
  simp only [CollatzResearch.WordTrace]
  refine ⟨195578309594393707845829085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130385539729595805230552723 195578309594393707845829085)
  ·
    refine ⟨73341866097897640442185907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195578309594393707845829085 73341866097897640442185907)
    ·
      refine ⟨110012799146846460663278861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73341866097897640442185907 110012799146846460663278861)
      ·
        refine ⟨41254799680067422748729573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110012799146846460663278861 41254799680067422748729573)
        ·
          refine ⟨7735274940012641765386795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41254799680067422748729573 7735274940012641765386795)
          ·
            refine ⟨11602912410018962648080193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7735274940012641765386795 11602912410018962648080193)
            ·
              refine ⟨8702184307514221986060145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11602912410018962648080193 8702184307514221986060145)
              ·
                refine ⟨6526638230635666489545109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8702184307514221986060145 6526638230635666489545109)
                ·
                  refine ⟨305936167061046866697427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6526638230635666489545109 305936167061046866697427)
                  ·
                    rfl

theorem cell23_5362277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_5362277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362277 prefixEnd_5362277 := by exact prefixLift 5362277
  have htrace : WordTrace (prefixWord ++ tailWord_5362277) baseStart_5362277 baseEnd_5362277 := by
    simpa [prefixWord, tailWord_5362277, baseEnd_5362277] using wordTrace_append hprefix tailTrace_5362277
  have hstable : (prefixWord ++ tailWord_5362277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362277).length < 2 ^ (prefixWord ++ tailWord_5362277).sum := by decide
  have hdescent : baseEnd_5362277 < baseStart_5362277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362314 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2]
def baseStart_5362314 : Nat := 118140960795 + 5362314 * 2 ^ 59
def prefixEnd_5362314 : Nat := 4983230072969 + 3 ^ 40 * 5362314 * 2
def baseEnd_5362314 : Nat := 2753444502333638155514173

theorem tailTrace_5362314 : CollatzResearch.WordTrace tailWord_5362314 prefixEnd_5362314 2753444502333638155514173 := by
  unfold tailWord_5362314
  simp only [CollatzResearch.WordTrace]
  refine ⟨48894914773814915791231499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130386439396839775443283997 48894914773814915791231499)
  ·
    refine ⟨73342372160722373686847249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48894914773814915791231499 73342372160722373686847249)
    ·
      refine ⟨55006779120541780265135437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73342372160722373686847249 55006779120541780265135437)
      ·
        refine ⟨20627542170203167599425789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55006779120541780265135437 20627542170203167599425789)
        ·
          refine ⟨7735328313826187849784671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20627542170203167599425789 7735328313826187849784671)
          ·
            refine ⟨11602992470739281774677007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7735328313826187849784671 11602992470739281774677007)
            ·
              refine ⟨17404488706108922662015511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11602992470739281774677007 17404488706108922662015511)
              ·
                refine ⟨26106733059163383993023267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17404488706108922662015511 26106733059163383993023267)
                ·
                  refine ⟨39160099588745075989534901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26106733059163383993023267 39160099588745075989534901)
                  ·
                    refine ⟨3671259336444850874018897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39160099588745075989534901 3671259336444850874018897)
                    ·
                      refine ⟨2753444502333638155514173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671259336444850874018897 2753444502333638155514173)
                      ·
                        rfl

theorem cell23_5362314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_5362314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362314 prefixEnd_5362314 := by exact prefixLift 5362314
  have htrace : WordTrace (prefixWord ++ tailWord_5362314) baseStart_5362314 baseEnd_5362314 := by
    simpa [prefixWord, tailWord_5362314, baseEnd_5362314] using wordTrace_append hprefix tailTrace_5362314
  have hstable : (prefixWord ++ tailWord_5362314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362314).length < 2 ^ (prefixWord ++ tailWord_5362314).sum := by decide
  have hdescent : baseEnd_5362314 < baseStart_5362314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362324 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 1, 5]
def baseStart_5362324 : Nat := 118140960795 + 5362324 * 2 ^ 59
def prefixEnd_5362324 : Nat := 4983230072969 + 3 ^ 40 * 5362324 * 2
def baseEnd_5362324 : Nat := 917816545713394372129709

theorem tailTrace_5362324 : CollatzResearch.WordTrace tailWord_5362324 prefixEnd_5362324 917816545713394372129709 := by
  unfold tailWord_5362324
  simp only [CollatzResearch.WordTrace]
  refine ⟨97790011912611717436395013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130386682550148956581860017 97790011912611717436395013)
  ·
    refine ⟨18335627233614697019324065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97790011912611717436395013 18335627233614697019324065)
    ·
      refine ⟨13751720425211022764493049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18335627233614697019324065 13751720425211022764493049)
      ·
        refine ⟨10313790318908267073369787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13751720425211022764493049 10313790318908267073369787)
        ·
          refine ⟨15470685478362400610054681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10313790318908267073369787 15470685478362400610054681)
          ·
            refine ⟨11603014108771800457541011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15470685478362400610054681 11603014108771800457541011)
            ·
              refine ⟨17404521163157700686311517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11603014108771800457541011 17404521163157700686311517)
              ·
                refine ⟨6526695436184137757366819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17404521163157700686311517 6526695436184137757366819)
                ·
                  refine ⟨9790043154276206636050229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6526695436184137757366819 9790043154276206636050229)
                  ·
                    refine ⟨917816545713394372129709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9790043154276206636050229 917816545713394372129709)
                    ·
                      rfl

theorem cell23_5362324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_5362324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362324 prefixEnd_5362324 := by exact prefixLift 5362324
  have htrace : WordTrace (prefixWord ++ tailWord_5362324) baseStart_5362324 baseEnd_5362324 := by
    simpa [prefixWord, tailWord_5362324, baseEnd_5362324] using wordTrace_append hprefix tailTrace_5362324
  have hstable : (prefixWord ++ tailWord_5362324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362324).length < 2 ^ (prefixWord ++ tailWord_5362324).sum := by decide
  have hdescent : baseEnd_5362324 < baseStart_5362324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362327 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 4]
def baseStart_5362327 : Nat := 118140960795 + 5362327 * 2 ^ 59
def prefixEnd_5362327 : Nat := 4983230072969 + 3 ^ 40 * 5362327 * 2
def baseEnd_5362327 : Nat := 2753451177582146604651613

theorem tailTrace_5362327 : CollatzResearch.WordTrace tailWord_5362327 prefixEnd_5362327 2753451177582146604651613 := by
  unfold tailWord_5362327
  simp only [CollatzResearch.WordTrace]
  refine ⟨195580133244212566385149235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130386755496141710923432823 195580133244212566385149235)
  ·
    refine ⟨293370199866318849577723853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195580133244212566385149235 293370199866318849577723853)
    ·
      refine ⟨110013824949869568591646445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293370199866318849577723853 110013824949869568591646445)
      ·
        refine ⟨41255184356201088221867417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110013824949869568591646445 41255184356201088221867417)
        ·
          refine ⟨30941388267150816166400563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41255184356201088221867417 30941388267150816166400563)
          ·
            refine ⟨46412082400726224249600845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30941388267150816166400563 46412082400726224249600845)
            ·
              refine ⟨17404530900272334093600317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46412082400726224249600845 17404530900272334093600317)
              ·
                refine ⟨6526699087602125285100119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17404530900272334093600317 6526699087602125285100119)
                ·
                  refine ⟨9790048631403187927650179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6526699087602125285100119 9790048631403187927650179)
                  ·
                    refine ⟨14685072947104781891475269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9790048631403187927650179 14685072947104781891475269)
                    ·
                      refine ⟨2753451177582146604651613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14685072947104781891475269 2753451177582146604651613)
                      ·
                        rfl

theorem cell23_5362327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_5362327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362327 prefixEnd_5362327 := by exact prefixLift 5362327
  have htrace : WordTrace (prefixWord ++ tailWord_5362327) baseStart_5362327 baseEnd_5362327 := by
    simpa [prefixWord, tailWord_5362327, baseEnd_5362327] using wordTrace_append hprefix tailTrace_5362327
  have hstable : (prefixWord ++ tailWord_5362327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362327).length < 2 ^ (prefixWord ++ tailWord_5362327).sum := by decide
  have hdescent : baseEnd_5362327 < baseStart_5362327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362340 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_5362340 : Nat := 118140960795 + 5362340 * 2 ^ 59
def prefixEnd_5362340 : Nat := 4983230072969 + 3 ^ 40 * 5362340 * 2
def baseEnd_5362340 : Nat := 2753457852830655053789053

theorem tailTrace_5362340 : CollatzResearch.WordTrace tailWord_5362340 prefixEnd_5362340 2753457852830655053789053 := by
  unfold tailWord_5362340
  simp only [CollatzResearch.WordTrace]
  refine ⟨97790303696582734802686237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130387071595443646403581649 97790303696582734802686237)
  ·
    refine ⟨36671363886218525551007339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97790303696582734802686237 36671363886218525551007339)
    ·
      refine ⟨55007045829327788326511009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36671363886218525551007339 55007045829327788326511009)
      ·
        refine ⟨41255284371995841244883257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55007045829327788326511009 41255284371995841244883257)
        ·
          refine ⟨30941463278996880933662443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41255284371995841244883257 30941463278996880933662443)
          ·
            refine ⟨46412194918495321400493665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30941463278996880933662443 46412194918495321400493665)
            ·
              refine ⟨34809146188871491050370249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46412194918495321400493665 34809146188871491050370249)
              ·
                refine ⟨26106859641653618287777687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34809146188871491050370249 26106859641653618287777687)
                ·
                  refine ⟨39160289462480427431666531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26106859641653618287777687 39160289462480427431666531)
                  ·
                    refine ⟨58740434193720641147499797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39160289462480427431666531 58740434193720641147499797)
                    ·
                      refine ⟨2753457852830655053789053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58740434193720641147499797 2753457852830655053789053)
                      ·
                        rfl

theorem cell23_5362340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_5362340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362340 prefixEnd_5362340 := by exact prefixLift 5362340
  have htrace : WordTrace (prefixWord ++ tailWord_5362340) baseStart_5362340 baseEnd_5362340 := by
    simpa [prefixWord, tailWord_5362340, baseEnd_5362340] using wordTrace_append hprefix tailTrace_5362340
  have hstable : (prefixWord ++ tailWord_5362340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362340).length < 2 ^ (prefixWord ++ tailWord_5362340).sum := by decide
  have hdescent : baseEnd_5362340 < baseStart_5362340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362357 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_5362357 : Nat := 118140960795 + 5362357 * 2 ^ 59
def prefixEnd_5362357 : Nat := 4983230072969 + 3 ^ 40 * 5362357 * 2
def baseEnd_5362357 : Nat := 2753466582001781487276475

theorem tailTrace_5362357 : CollatzResearch.WordTrace tailWord_5362357 prefixEnd_5362357 2753466582001781487276475 := by
  unfold tailWord_5362357
  simp only [CollatzResearch.WordTrace]
  refine ⟨195581227434103881508741325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130387484956069254339160883 195581227434103881508741325)
  ·
    refine ⟨73342960287788955565777997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195581227434103881508741325 73342960287788955565777997)
    ·
      refine ⟨27503610107920858337166749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73342960287788955565777997 27503610107920858337166749)
      ·
        refine ⟨10313853790470321876437531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27503610107920858337166749 10313853790470321876437531)
        ·
          refine ⟨15470780685705482814656297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10313853790470321876437531 15470780685705482814656297)
          ·
            refine ⟨11603085514279112110992223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15470780685705482814656297 11603085514279112110992223)
            ·
              refine ⟨17404628271418668166488335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11603085514279112110992223 17404628271418668166488335)
              ·
                refine ⟨26106942407128002249732503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17404628271418668166488335 26106942407128002249732503)
                ·
                  refine ⟨39160413610692003374598755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26106942407128002249732503 39160413610692003374598755)
                  ·
                    refine ⟨58740620416038005061898133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39160413610692003374598755 58740620416038005061898133)
                    ·
                      refine ⟨2753466582001781487276475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58740620416038005061898133 2753466582001781487276475)
                      ·
                        rfl

theorem cell23_5362357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_5362357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362357 prefixEnd_5362357 := by exact prefixLift 5362357
  have htrace : WordTrace (prefixWord ++ tailWord_5362357) baseStart_5362357 baseEnd_5362357 := by
    simpa [prefixWord, tailWord_5362357, baseEnd_5362357] using wordTrace_append hprefix tailTrace_5362357
  have hstable : (prefixWord ++ tailWord_5362357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362357).length < 2 ^ (prefixWord ++ tailWord_5362357).sum := by decide
  have hdescent : baseEnd_5362357 < baseStart_5362357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362364 : List Nat := [2, 2, 2, 3, 1, 1, 4, 2, 1, 2, 3]
def baseStart_5362364 : Nat := 118140960795 + 5362364 * 2 ^ 59
def prefixEnd_5362364 : Nat := 4983230072969 + 3 ^ 40 * 5362364 * 2
def baseEnd_5362364 : Nat := 2753470176366362959888943

theorem tailTrace_5362364 : CollatzResearch.WordTrace tailWord_5362364 prefixEnd_5362364 2753470176366362959888943 := by
  unfold tailWord_5362364
  simp only [CollatzResearch.WordTrace]
  refine ⟨97790741372539260852123073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130387655163385681136164097 97790741372539260852123073)
  ·
    refine ⟨73343056029404445639092305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97790741372539260852123073 73343056029404445639092305)
    ·
      refine ⟨55007292022053334229319229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73343056029404445639092305 55007292022053334229319229)
      ·
        refine ⟨20627734508270000335994711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55007292022053334229319229 20627734508270000335994711)
        ·
          refine ⟨30941601762405000503992067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20627734508270000335994711 30941601762405000503992067)
          ·
            refine ⟨46412402643607500755988101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30941601762405000503992067 46412402643607500755988101)
            ·
              refine ⟨8702325495676406391747769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46412402643607500755988101 8702325495676406391747769)
              ·
                refine ⟨6526744121757304793810827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8702325495676406391747769 6526744121757304793810827)
                ·
                  refine ⟨9790116182635957190716241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6526744121757304793810827 9790116182635957190716241)
                  ·
                    refine ⟨7342587136976967893037181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9790116182635957190716241 7342587136976967893037181)
                    ·
                      refine ⟨2753470176366362959888943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7342587136976967893037181 2753470176366362959888943)
                      ·
                        rfl

theorem cell23_5362364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_5362364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362364 prefixEnd_5362364 := by exact prefixLift 5362364
  have htrace : WordTrace (prefixWord ++ tailWord_5362364) baseStart_5362364 baseEnd_5362364 := by
    simpa [prefixWord, tailWord_5362364, baseEnd_5362364] using wordTrace_append hprefix tailTrace_5362364
  have hstable : (prefixWord ++ tailWord_5362364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362364).length < 2 ^ (prefixWord ++ tailWord_5362364).sum := by decide
  have hdescent : baseEnd_5362364 < baseStart_5362364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362367 : List Nat := [1, 1, 2, 2, 2, 6, 2, 7]
def baseStart_5362367 : Nat := 118140960795 + 5362367 * 2 ^ 59
def prefixEnd_5362367 : Nat := 4983230072969 + 3 ^ 40 * 5362367 * 2
def baseEnd_5362367 : Nat := 101980433955863942524127

theorem tailTrace_5362367 : CollatzResearch.WordTrace tailWord_5362367 prefixEnd_5362367 101980433955863942524127 := by
  unfold tailWord_5362367
  simp only [CollatzResearch.WordTrace]
  refine ⟨195581592164067653216605355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130387728109378435477736903 195581592164067653216605355)
  ·
    refine ⟨293372388246101479824908033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195581592164067653216605355 293372388246101479824908033)
    ·
      refine ⟨220029291184576109868681025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293372388246101479824908033 220029291184576109868681025)
      ·
        refine ⟨165021968388432082401510769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220029291184576109868681025 165021968388432082401510769)
        ·
          refine ⟨123766476291324061801133077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165021968388432082401510769 123766476291324061801133077)
          ·
            refine ⟨5801553576155815396928113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123766476291324061801133077 5801553576155815396928113)
            ·
              refine ⟨4351165182116861547696085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5801553576155815396928113 4351165182116861547696085)
              ·
                refine ⟨101980433955863942524127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4351165182116861547696085 101980433955863942524127)
                ·
                  rfl

theorem cell23_5362367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 7].length) (baseStart_5362367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362367 prefixEnd_5362367 := by exact prefixLift 5362367
  have htrace : WordTrace (prefixWord ++ tailWord_5362367) baseStart_5362367 baseEnd_5362367 := by
    simpa [prefixWord, tailWord_5362367, baseEnd_5362367] using wordTrace_append hprefix tailTrace_5362367
  have hstable : (prefixWord ++ tailWord_5362367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362367).length < 2 ^ (prefixWord ++ tailWord_5362367).sum := by decide
  have hdescent : baseEnd_5362367 < baseStart_5362367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362378 : List Nat := [3, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2]
def baseStart_5362378 : Nat := 118140960795 + 5362378 * 2 ^ 59
def prefixEnd_5362378 : Nat := 4983230072969 + 3 ^ 40 * 5362378 * 2
def baseEnd_5362378 : Nat := 2753477365095525905113879

theorem tailTrace_5362378 : CollatzResearch.WordTrace tailWord_5362378 prefixEnd_5362378 2753477365095525905113879 := by
  unfold tailWord_5362378
  simp only [CollatzResearch.WordTrace]
  refine ⟨48895498341756950523813947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130387995578018534730170525 48895498341756950523813947)
  ·
    refine ⟨73343247512635425785720921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48895498341756950523813947 73343247512635425785720921)
    ·
      refine ⟨55007435634476569339290691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73343247512635425785720921 55007435634476569339290691)
      ·
        refine ⟨82511153451714854008936037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55007435634476569339290691 82511153451714854008936037)
        ·
          refine ⟨15470841272196535126675507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82511153451714854008936037 15470841272196535126675507)
          ·
            refine ⟨23206261908294802690013261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15470841272196535126675507 23206261908294802690013261)
            ·
              refine ⟨8702348215610551008754973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23206261908294802690013261 8702348215610551008754973)
              ·
                refine ⟨3263380580853956628283115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8702348215610551008754973 3263380580853956628283115)
                ·
                  refine ⟨4895070871280934942424673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263380580853956628283115 4895070871280934942424673)
                  ·
                    refine ⟨3671303153460701206818505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4895070871280934942424673 3671303153460701206818505)
                    ·
                      refine ⟨2753477365095525905113879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671303153460701206818505 2753477365095525905113879)
                      ·
                        rfl

theorem cell23_5362378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_5362378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362378 prefixEnd_5362378 := by exact prefixLift 5362378
  have htrace : WordTrace (prefixWord ++ tailWord_5362378) baseStart_5362378 baseEnd_5362378 := by
    simpa [prefixWord, tailWord_5362378, baseEnd_5362378] using wordTrace_append hprefix tailTrace_5362378
  have hstable : (prefixWord ++ tailWord_5362378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362378).length < 2 ^ (prefixWord ++ tailWord_5362378).sum := by decide
  have hdescent : baseEnd_5362378 < baseStart_5362378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362381 : List Nat := [1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_5362381 : Nat := 118140960795 + 5362381 * 2 ^ 59
def prefixEnd_5362381 : Nat := 4983230072969 + 3 ^ 40 * 5362381 * 2
def baseEnd_5362381 : Nat := 2753478905537489393376365

theorem tailTrace_5362381 : CollatzResearch.WordTrace tailWord_5362381 prefixEnd_5362381 2753478905537489393376365 := by
  unfold tailWord_5362381
  simp only [CollatzResearch.WordTrace]
  refine ⟨195582102786016933607614997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130388068524011289071743331 195582102786016933607614997)
  ·
    refine ⟨9167911068094543762856953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 195582102786016933607614997 9167911068094543762856953)
    ·
      refine ⟨6875933301070907822142715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9167911068094543762856953 6875933301070907822142715)
      ·
        refine ⟨10313899951606361733214073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6875933301070907822142715 10313899951606361733214073)
        ·
          refine ⟨7735424963704771299910555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10313899951606361733214073 7735424963704771299910555)
          ·
            refine ⟨11603137445557156949865833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7735424963704771299910555 11603137445557156949865833)
            ·
              refine ⟨8702353084167867712399375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11603137445557156949865833 8702353084167867712399375)
              ·
                refine ⟨13053529626251801568599063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8702353084167867712399375 13053529626251801568599063)
                ·
                  refine ⟨19580294439377702352898595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13053529626251801568599063 19580294439377702352898595)
                  ·
                    refine ⟨29370441659066553529347893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19580294439377702352898595 29370441659066553529347893)
                    ·
                      refine ⟨2753478905537489393376365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29370441659066553529347893 2753478905537489393376365)
                      ·
                        rfl

theorem cell23_5362381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_5362381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362381 prefixEnd_5362381 := by exact prefixLift 5362381
  have htrace : WordTrace (prefixWord ++ tailWord_5362381) baseStart_5362381 baseEnd_5362381 := by
    simpa [prefixWord, tailWord_5362381, baseEnd_5362381] using wordTrace_append hprefix tailTrace_5362381
  have hstable : (prefixWord ++ tailWord_5362381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362381).length < 2 ^ (prefixWord ++ tailWord_5362381).sum := by decide
  have hdescent : baseEnd_5362381 < baseStart_5362381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362394 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3]
def baseStart_5362394 : Nat := 118140960795 + 5362394 * 2 ^ 59
def prefixEnd_5362394 : Nat := 4983230072969 + 3 ^ 40 * 5362394 * 2
def baseEnd_5362394 : Nat := 2753485580785997842513805

theorem tailTrace_5362394 : CollatzResearch.WordTrace tailWord_5362394 prefixEnd_5362394 2753485580785997842513805 := by
  unfold tailWord_5362394
  simp only [CollatzResearch.WordTrace]
  refine ⟨48895644233742459206959559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130388384623313224551892157 48895644233742459206959559)
  ·
    refine ⟨73343466350613688810439339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48895644233742459206959559 73343466350613688810439339)
    ·
      refine ⟨110015199525920533215659009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73343466350613688810439339 110015199525920533215659009)
      ·
        refine ⟨82511399644440399911744257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110015199525920533215659009 82511399644440399911744257)
        ·
          refine ⟨61883549733330299933808193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82511399644440399911744257 61883549733330299933808193)
          ·
            refine ⟨46412662299997724950356145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61883549733330299933808193 46412662299997724950356145)
            ·
              refine ⟨34809496724998293712767109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46412662299997724950356145 34809496724998293712767109)
              ·
                refine ⟨6526780635937180071143833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34809496724998293712767109 6526780635937180071143833)
                ·
                  refine ⟨4895085476952885053357875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6526780635937180071143833 4895085476952885053357875)
                  ·
                    refine ⟨7342628215429327580036813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4895085476952885053357875 7342628215429327580036813)
                    ·
                      refine ⟨2753485580785997842513805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7342628215429327580036813 2753485580785997842513805)
                      ·
                        rfl

theorem cell23_5362394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_5362394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362394 prefixEnd_5362394 := by exact prefixLift 5362394
  have htrace : WordTrace (prefixWord ++ tailWord_5362394) baseStart_5362394 baseEnd_5362394 := by
    simpa [prefixWord, tailWord_5362394, baseEnd_5362394] using wordTrace_append hprefix tailTrace_5362394
  have hstable : (prefixWord ++ tailWord_5362394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362394).length < 2 ^ (prefixWord ++ tailWord_5362394).sum := by decide
  have hdescent : baseEnd_5362394 < baseStart_5362394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362400 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_5362400 : Nat := 118140960795 + 5362400 * 2 ^ 59
def prefixEnd_5362400 : Nat := 4983230072969 + 3 ^ 40 * 5362400 * 2
def baseEnd_5362400 : Nat := 2753488661669924819038777

theorem tailTrace_5362400 : CollatzResearch.WordTrace tailWord_5362400 prefixEnd_5362400 2753488661669924819038777 := by
  unfold tailWord_5362400
  simp only [CollatzResearch.WordTrace]
  refine ⟨97791397886474049926278327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130388530515298733235037769 97791397886474049926278327)
  ·
    refine ⟨146687096829711074889417491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97791397886474049926278327 146687096829711074889417491)
    ·
      refine ⟨220030645244566612334126237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146687096829711074889417491 220030645244566612334126237)
      ·
        refine ⟨82511491966712479625297339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220030645244566612334126237 82511491966712479625297339)
        ·
          refine ⟨123767237950068719437946009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82511491966712479625297339 123767237950068719437946009)
          ·
            refine ⟨92825428462551539578459507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123767237950068719437946009 92825428462551539578459507)
            ·
              refine ⟨139238142693827309367689261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92825428462551539578459507 139238142693827309367689261)
              ·
                refine ⟨52214303510185241012883473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139238142693827309367689261 52214303510185241012883473)
                ·
                  refine ⟨39160727632638930759662605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52214303510185241012883473 39160727632638930759662605)
                  ·
                    refine ⟨14685272862239599034873477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39160727632638930759662605 14685272862239599034873477)
                    ·
                      refine ⟨2753488661669924819038777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14685272862239599034873477 2753488661669924819038777)
                      ·
                        rfl

theorem cell23_5362400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_5362400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362400 prefixEnd_5362400 := by exact prefixLift 5362400
  have htrace : WordTrace (prefixWord ++ tailWord_5362400) baseStart_5362400 baseEnd_5362400 := by
    simpa [prefixWord, tailWord_5362400, baseEnd_5362400] using wordTrace_append hprefix tailTrace_5362400
  have hstable : (prefixWord ++ tailWord_5362400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362400).length < 2 ^ (prefixWord ++ tailWord_5362400).sum := by decide
  have hdescent : baseEnd_5362400 < baseStart_5362400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362410 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 1, 8]
def baseStart_5362410 : Nat := 118140960795 + 5362410 * 2 ^ 59
def prefixEnd_5362410 : Nat := 4983230072969 + 3 ^ 40 * 5362410 * 2
def baseEnd_5362410 : Nat := 917831265492156593304577

theorem tailTrace_5362410 : CollatzResearch.WordTrace tailWord_5362410 prefixEnd_5362410 917831265492156593304577 := by
  unfold tailWord_5362410
  simp only [CollatzResearch.WordTrace]
  refine ⟨48895790125727967890105171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130388773668607914373613789 48895790125727967890105171)
  ·
    refine ⟨73343685188591951835157757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48895790125727967890105171 73343685188591951835157757)
    ·
      refine ⟨27503881945721981938184159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73343685188591951835157757 27503881945721981938184159)
      ·
        refine ⟨41255822918582972907276239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27503881945721981938184159 41255822918582972907276239)
        ·
          refine ⟨61883734377874459360914359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41255822918582972907276239 61883734377874459360914359)
          ·
            refine ⟨92825601566811689041371539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61883734377874459360914359 92825601566811689041371539)
            ·
              refine ⟨139238402350217533562057309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92825601566811689041371539 139238402350217533562057309)
              ·
                refine ⟨52214400881331575085771491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139238402350217533562057309 52214400881331575085771491)
                ·
                  refine ⟨78321601321997362628657237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52214400881331575085771491 78321601321997362628657237)
                  ·
                    refine ⟨917831265492156593304577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78321601321997362628657237 917831265492156593304577)
                    ·
                      rfl

theorem cell23_5362410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_5362410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362410 prefixEnd_5362410 := by exact prefixLift 5362410
  have htrace : WordTrace (prefixWord ++ tailWord_5362410) baseStart_5362410 baseEnd_5362410 := by
    simpa [prefixWord, tailWord_5362410, baseEnd_5362410] using wordTrace_append hprefix tailTrace_5362410
  have hstable : (prefixWord ++ tailWord_5362410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362410).length < 2 ^ (prefixWord ++ tailWord_5362410).sum := by decide
  have hdescent : baseEnd_5362410 < baseStart_5362410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362451 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 2, 2, 2]
def baseStart_5362451 : Nat := 118140960795 + 5362451 * 2 ^ 59
def prefixEnd_5362451 : Nat := 4983230072969 + 3 ^ 40 * 5362451 * 2
def baseEnd_5362451 : Nat := 2753514849183304119501043

theorem tailTrace_5362451 : CollatzResearch.WordTrace tailWord_5362451 prefixEnd_5362451 2753514849183304119501043 := by
  unfold tailWord_5362451
  simp only [CollatzResearch.WordTrace]
  refine ⟨195584655895763335562663207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130389770597175557041775471 195584655895763335562663207)
  ·
    refine ⟨293376983843645003343994811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195584655895763335562663207 293376983843645003343994811)
    ·
      refine ⟨440065475765467505015992217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293376983843645003343994811 440065475765467505015992217)
      ·
        refine ⟨330049106824100628761994163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440065475765467505015992217 330049106824100628761994163)
        ·
          refine ⟨495073660236150943142991245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330049106824100628761994163 495073660236150943142991245)
          ·
            refine ⟨185652622588556603678621717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 495073660236150943142991245 185652622588556603678621717)
            ·
              refine ⟨8702466683838590797435393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185652622588556603678621717 8702466683838590797435393)
              ·
                refine ⟨6526850012878943098076545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8702466683838590797435393 6526850012878943098076545)
                ·
                  refine ⟨4895137509659207323557409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6526850012878943098076545 4895137509659207323557409)
                  ·
                    refine ⟨3671353132244405492668057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4895137509659207323557409 3671353132244405492668057)
                    ·
                      refine ⟨2753514849183304119501043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671353132244405492668057 2753514849183304119501043)
                      ·
                        rfl

theorem cell23_5362451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 2, 2].length) (baseStart_5362451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362451 prefixEnd_5362451 := by exact prefixLift 5362451
  have htrace : WordTrace (prefixWord ++ tailWord_5362451) baseStart_5362451 baseEnd_5362451 := by
    simpa [prefixWord, tailWord_5362451, baseEnd_5362451] using wordTrace_append hprefix tailTrace_5362451
  have hstable : (prefixWord ++ tailWord_5362451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362451).length < 2 ^ (prefixWord ++ tailWord_5362451).sum := by decide
  have hdescent : baseEnd_5362451 < baseStart_5362451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362480 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_5362480 : Nat := 118140960795 + 5362480 * 2 ^ 59
def prefixEnd_5362480 : Nat := 4983230072969 + 3 ^ 40 * 5362480 * 2
def baseEnd_5362480 : Nat := 2753529740122284506038409

theorem tailTrace_5362480 : CollatzResearch.WordTrace tailWord_5362480 prefixEnd_5362480 2753529740122284506038409 := by
  unfold tailWord_5362480
  simp only [CollatzResearch.WordTrace]
  refine ⟨97792856806329136757734447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130390475741772182343645929 97792856806329136757734447)
  ·
    refine ⟨146689285209493705136601671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97792856806329136757734447 146689285209493705136601671)
    ·
      refine ⟨220033927814240557704902507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146689285209493705136601671 220033927814240557704902507)
      ·
        refine ⟨330050891721360836557353761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220033927814240557704902507 330050891721360836557353761)
        ·
          refine ⟨247538168791020627418015321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330050891721360836557353761 247538168791020627418015321)
          ·
            refine ⟨185653626593265470563511491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247538168791020627418015321 185653626593265470563511491)
            ·
              refine ⟨278480439889898205845267237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185653626593265470563511491 278480439889898205845267237)
              ·
                refine ⟨52215082479355913595987607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 278480439889898205845267237 52215082479355913595987607)
                ·
                  refine ⟨78322623719033870393981411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52215082479355913595987607 78322623719033870393981411)
                  ·
                    refine ⟨117483935578550805590972117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78322623719033870393981411 117483935578550805590972117)
                    ·
                      refine ⟨2753529740122284506038409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117483935578550805590972117 2753529740122284506038409)
                      ·
                        rfl

theorem cell23_5362480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_5362480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362480 prefixEnd_5362480 := by exact prefixLift 5362480
  have htrace : WordTrace (prefixWord ++ tailWord_5362480) baseStart_5362480 baseEnd_5362480 := by
    simpa [prefixWord, tailWord_5362480, baseEnd_5362480] using wordTrace_append hprefix tailTrace_5362480
  have hstable : (prefixWord ++ tailWord_5362480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362480).length < 2 ^ (prefixWord ++ tailWord_5362480).sum := by decide
  have hdescent : baseEnd_5362480 < baseStart_5362480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362524 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5362524 : Nat := 118140960795 + 5362524 * 2 ^ 59
def prefixEnd_5362524 : Nat := 4983230072969 + 3 ^ 40 * 5362524 * 2
def baseEnd_5362524 : Nat := 2753552333271082333888207

theorem tailTrace_5362524 : CollatzResearch.WordTrace tailWord_5362524 prefixEnd_5362524 2753552333271082333888207 := by
  unfold tailWord_5362524
  simp only [CollatzResearch.WordTrace]
  refine ⟨97793659212249434515035313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130391545616332579353380417 97793659212249434515035313)
  ·
    refine ⟨73345244409187075886276485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97793659212249434515035313 73345244409187075886276485)
    ·
      refine ⟨13752233326722576728676841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73345244409187075886276485 13752233326722576728676841)
      ·
        refine ⟨10314174995041932546507631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13752233326722576728676841 10314174995041932546507631)
        ·
          refine ⟨15471262492562898819761447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10314174995041932546507631 15471262492562898819761447)
          ·
            refine ⟨23206893738844348229642171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15471262492562898819761447 23206893738844348229642171)
            ·
              refine ⟨34810340608266522344463257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23206893738844348229642171 34810340608266522344463257)
              ·
                refine ⟨26107755456199891758347443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34810340608266522344463257 26107755456199891758347443)
                ·
                  refine ⟨39161633184299837637521165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26107755456199891758347443 39161633184299837637521165)
                  ·
                    refine ⟨14685612444112439114070437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39161633184299837637521165 14685612444112439114070437)
                    ·
                      refine ⟨2753552333271082333888207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14685612444112439114070437 2753552333271082333888207)
                      ·
                        rfl

theorem cell23_5362524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5362524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362524 prefixEnd_5362524 := by exact prefixLift 5362524
  have htrace : WordTrace (prefixWord ++ tailWord_5362524) baseStart_5362524 baseEnd_5362524 := by
    simpa [prefixWord, tailWord_5362524, baseEnd_5362524] using wordTrace_append hprefix tailTrace_5362524
  have hstable : (prefixWord ++ tailWord_5362524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362524).length < 2 ^ (prefixWord ++ tailWord_5362524).sum := by decide
  have hdescent : baseEnd_5362524 < baseStart_5362524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362527 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 3]
def baseStart_5362527 : Nat := 118140960795 + 5362527 * 2 ^ 59
def prefixEnd_5362527 : Nat := 4983230072969 + 3 ^ 40 * 5362527 * 2
def baseEnd_5362527 : Nat := 2753553873713045822150693

theorem tailTrace_5362527 : CollatzResearch.WordTrace tailWord_5362527 prefixEnd_5362527 2753553873713045822150693 := by
  unfold tailWord_5362527
  simp only [CollatzResearch.WordTrace]
  refine ⟨195587427843488000542429835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130391618562325333694953223 195587427843488000542429835)
  ·
    refine ⟨293381141765232000813644753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195587427843488000542429835 293381141765232000813644753)
    ·
      refine ⟨220035856323924000610233565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293381141765232000813644753 220035856323924000610233565)
      ·
        refine ⟨82513446121471500228837587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220035856323924000610233565 82513446121471500228837587)
        ·
          refine ⟨123770169182207250343256381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82513446121471500228837587 123770169182207250343256381)
          ·
            refine ⟨46413813443327718878721143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123770169182207250343256381 46413813443327718878721143)
            ·
              refine ⟨69620720164991578318081715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46413813443327718878721143 69620720164991578318081715)
              ·
                refine ⟨104431080247487367477122573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69620720164991578318081715 104431080247487367477122573)
                ·
                  refine ⟨39161655092807762803920965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104431080247487367477122573 39161655092807762803920965)
                  ·
                    refine ⟨7342810329901455525735181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39161655092807762803920965 7342810329901455525735181)
                    ·
                      refine ⟨2753553873713045822150693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7342810329901455525735181 2753553873713045822150693)
                      ·
                        rfl

theorem cell23_5362527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_5362527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362527 prefixEnd_5362527 := by exact prefixLift 5362527
  have htrace : WordTrace (prefixWord ++ tailWord_5362527) baseStart_5362527 baseEnd_5362527 := by
    simpa [prefixWord, tailWord_5362527, baseEnd_5362527] using wordTrace_append hprefix tailTrace_5362527
  have hstable : (prefixWord ++ tailWord_5362527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362527).length < 2 ^ (prefixWord ++ tailWord_5362527).sum := by decide
  have hdescent : baseEnd_5362527 < baseStart_5362527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362558 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_5362558 : Nat := 118140960795 + 5362558 * 2 ^ 59
def prefixEnd_5362558 : Nat := 4983230072969 + 3 ^ 40 * 5362558 * 2
def baseEnd_5362558 : Nat := 2753569791613335200863051

theorem tailTrace_5362558 : CollatzResearch.WordTrace tailWord_5362558 prefixEnd_5362558 2753569791613335200863051 := by
  unfold tailWord_5362558
  simp only [CollatzResearch.WordTrace]
  refine ⟨24448569813296961604601041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130392372337583795224538885 24448569813296961604601041)
  ·
    refine ⟨18336427359972721203450781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24448569813296961604601041 18336427359972721203450781)
    ·
      refine ⟨6876160259989770451294043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18336427359972721203450781 6876160259989770451294043)
      ·
        refine ⟨10314240389984655676941065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6876160259989770451294043 10314240389984655676941065)
        ·
          refine ⟨7735680292488491757705799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10314240389984655676941065 7735680292488491757705799)
          ·
            refine ⟨11603520438732737636558699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7735680292488491757705799 11603520438732737636558699)
            ·
              refine ⟨17405280658099106454838049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11603520438732737636558699 17405280658099106454838049)
              ·
                refine ⟨13053960493574329841128537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17405280658099106454838049 13053960493574329841128537)
                ·
                  refine ⟨9790470370180747380846403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13053960493574329841128537 9790470370180747380846403)
                  ·
                    refine ⟨14685705555271121071269605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9790470370180747380846403 14685705555271121071269605)
                    ·
                      refine ⟨2753569791613335200863051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14685705555271121071269605 2753569791613335200863051)
                      ·
                        rfl

theorem cell23_5362558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_5362558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362558 prefixEnd_5362558 := by exact prefixLift 5362558
  have htrace : WordTrace (prefixWord ++ tailWord_5362558) baseStart_5362558 baseEnd_5362558 := by
    simpa [prefixWord, tailWord_5362558, baseEnd_5362558] using wordTrace_append hprefix tailTrace_5362558
  have hstable : (prefixWord ++ tailWord_5362558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362558).length < 2 ^ (prefixWord ++ tailWord_5362558).sum := by decide
  have hdescent : baseEnd_5362558 < baseStart_5362558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362577 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 3, 5]
def baseStart_5362577 : Nat := 118140960795 + 5362577 * 2 ^ 59
def prefixEnd_5362577 : Nat := 4983230072969 + 3 ^ 40 * 5362577 * 2
def baseEnd_5362577 : Nat := 917859849248590208841821

theorem tailTrace_5362577 : CollatzResearch.WordTrace tailWord_5362577 prefixEnd_5362577 917859849248590208841821 := by
  unfold tailWord_5362577
  simp only [CollatzResearch.WordTrace]
  refine ⟨195589251493306859081749985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130392834328871239387833323 195589251493306859081749985)
  ·
    refine ⟨146691938619980144311312489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195589251493306859081749985 146691938619980144311312489)
    ·
      refine ⟨110018953964985108233484367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146691938619980144311312489 110018953964985108233484367)
      ·
        refine ⟨165028430947477662350226551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110018953964985108233484367 165028430947477662350226551)
        ·
          refine ⟨247542646421216493525339827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165028430947477662350226551 247542646421216493525339827)
          ·
            refine ⟨371313969631824740288009741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247542646421216493525339827 371313969631824740288009741)
            ·
              refine ⟨139242738611934277608003653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 371313969631824740288009741 139242738611934277608003653)
              ·
                refine ⟨26108013489737677051500685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 139242738611934277608003653 26108013489737677051500685)
                ·
                  refine ⟨9790505058651628894312757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26108013489737677051500685 9790505058651628894312757)
                  ·
                    refine ⟨917859849248590208841821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9790505058651628894312757 917859849248590208841821)
                    ·
                      rfl

theorem cell23_5362577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_5362577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362577 prefixEnd_5362577 := by exact prefixLift 5362577
  have htrace : WordTrace (prefixWord ++ tailWord_5362577) baseStart_5362577 baseEnd_5362577 := by
    simpa [prefixWord, tailWord_5362577, baseEnd_5362577] using wordTrace_append hprefix tailTrace_5362577
  have hstable : (prefixWord ++ tailWord_5362577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362577).length < 2 ^ (prefixWord ++ tailWord_5362577).sum := by decide
  have hdescent : baseEnd_5362577 < baseStart_5362577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362581 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 6]
def baseStart_5362581 : Nat := 118140960795 + 5362581 * 2 ^ 59
def prefixEnd_5362581 : Nat := 4983230072969 + 3 ^ 40 * 5362581 * 2
def baseEnd_5362581 : Nat := 305953511296487623430605

theorem tailTrace_5362581 : CollatzResearch.WordTrace tailWord_5362581 prefixEnd_5362581 305953511296487623430605 := by
  unfold tailWord_5362581
  simp only [CollatzResearch.WordTrace]
  refine ⟨195589397385292367764895597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130392931590194911843263731 195589397385292367764895597)
  ·
    refine ⟨73346024019484637911835849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195589397385292367764895597 73346024019484637911835849)
    ·
      refine ⟨55009518014613478433876887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73346024019484637911835849 55009518014613478433876887)
      ·
        refine ⟨82514277021920217650815331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55009518014613478433876887 82514277021920217650815331)
        ·
          refine ⟨123771415532880326476222997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82514277021920217650815331 123771415532880326476222997)
          ·
            refine ⟨5801785103103765303572953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123771415532880326476222997 5801785103103765303572953)
            ·
              refine ⟨4351338827327823977679715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5801785103103765303572953 4351338827327823977679715)
              ·
                refine ⟨6527008240991735966519573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4351338827327823977679715 6527008240991735966519573)
                ·
                  refine ⟨305953511296487623430605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6527008240991735966519573 305953511296487623430605)
                  ·
                    rfl

theorem cell23_5362581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_5362581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362581 prefixEnd_5362581 := by exact prefixLift 5362581
  have htrace : WordTrace (prefixWord ++ tailWord_5362581) baseStart_5362581 baseEnd_5362581 := by
    simpa [prefixWord, tailWord_5362581, baseEnd_5362581] using wordTrace_append hprefix tailTrace_5362581
  have hstable : (prefixWord ++ tailWord_5362581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362581).length < 2 ^ (prefixWord ++ tailWord_5362581).sum := by decide
  have hdescent : baseEnd_5362581 < baseStart_5362581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362601 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 2, 3, 2]
def baseStart_5362601 : Nat := 118140960795 + 5362601 * 2 ^ 59
def prefixEnd_5362601 : Nat := 4983230072969 + 3 ^ 40 * 5362601 * 2
def baseEnd_5362601 : Nat := 2753591871281478532625353

theorem tailTrace_5362601 : CollatzResearch.WordTrace tailWord_5362601 prefixEnd_5362601 2753591871281478532625353 := by
  unfold tailWord_5362601
  simp only [CollatzResearch.WordTrace]
  refine ⟨195590126845219911180623657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130393417896813274120415771 195590126845219911180623657)
  ·
    refine ⟨146692595133914933385467743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195590126845219911180623657 146692595133914933385467743)
    ·
      refine ⟨220038892700872400078201615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146692595133914933385467743 220038892700872400078201615)
      ·
        refine ⟨330058339051308600117302423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220038892700872400078201615 330058339051308600117302423)
        ·
          refine ⟨495087508576962900175953635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330058339051308600117302423 495087508576962900175953635)
          ·
            refine ⟨742631262865444350263930453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495087508576962900175953635 742631262865444350263930453)
            ·
              refine ⟨8702710111704425979655435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 742631262865444350263930453 8702710111704425979655435)
              ·
                refine ⟨13054065167556638969483153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8702710111704425979655435 13054065167556638969483153)
                ·
                  refine ⟨9790548875667479227112365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13054065167556638969483153 9790548875667479227112365)
                  ·
                    refine ⟨3671455828375304710167137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9790548875667479227112365 3671455828375304710167137)
                    ·
                      refine ⟨2753591871281478532625353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671455828375304710167137 2753591871281478532625353)
                      ·
                        rfl

theorem cell23_5362601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 3, 2].length) (baseStart_5362601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362601 prefixEnd_5362601 := by exact prefixLift 5362601
  have htrace : WordTrace (prefixWord ++ tailWord_5362601) baseStart_5362601 baseEnd_5362601 := by
    simpa [prefixWord, tailWord_5362601, baseEnd_5362601] using wordTrace_append hprefix tailTrace_5362601
  have hstable : (prefixWord ++ tailWord_5362601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362601).length < 2 ^ (prefixWord ++ tailWord_5362601).sum := by decide
  have hdescent : baseEnd_5362601 < baseStart_5362601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362648 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 3, 2, 2]
def baseStart_5362648 : Nat := 118140960795 + 5362648 * 2 ^ 59
def prefixEnd_5362648 : Nat := 4983230072969 + 3 ^ 40 * 5362648 * 2
def baseEnd_5362648 : Nat := 2753616004872239848737637

theorem tailTrace_5362648 : CollatzResearch.WordTrace tailWord_5362648 prefixEnd_5362648 2753616004872239848737637 := by
  unfold tailWord_5362648
  simp only [CollatzResearch.WordTrace]
  refine ⟨97795920538024819103792299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130394560717366425471723065 97795920538024819103792299)
  ·
    refine ⟨146693880807037228655688449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97795920538024819103792299 146693880807037228655688449)
    ·
      refine ⟨110020410605277921491766337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146693880807037228655688449 110020410605277921491766337)
      ·
        refine ⟨82515307953958441118824753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110020410605277921491766337 82515307953958441118824753)
        ·
          refine ⟨61886480965468830839118565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82515307953958441118824753 61886480965468830839118565)
          ·
            refine ⟨11603715181025405782334731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61886480965468830839118565 11603715181025405782334731)
            ·
              refine ⟨17405572771538108673502097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11603715181025405782334731 17405572771538108673502097)
              ·
                refine ⟨13054179578653581505126573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17405572771538108673502097 13054179578653581505126573)
                ·
                  refine ⟨4895317341995093064422465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13054179578653581505126573 4895317341995093064422465)
                  ·
                    refine ⟨3671488006496319798316849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4895317341995093064422465 3671488006496319798316849)
                    ·
                      refine ⟨2753616004872239848737637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671488006496319798316849 2753616004872239848737637)
                      ·
                        rfl

theorem cell23_5362648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_5362648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362648 prefixEnd_5362648 := by exact prefixLift 5362648
  have htrace : WordTrace (prefixWord ++ tailWord_5362648) baseStart_5362648 baseEnd_5362648 := by
    simpa [prefixWord, tailWord_5362648, baseEnd_5362648] using wordTrace_append hprefix tailTrace_5362648
  have hstable : (prefixWord ++ tailWord_5362648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362648).length < 2 ^ (prefixWord ++ tailWord_5362648).sum := by decide
  have hdescent : baseEnd_5362648 < baseStart_5362648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362681 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 4, 1, 3]
def baseStart_5362681 : Nat := 118140960795 + 5362681 * 2 ^ 59
def prefixEnd_5362681 : Nat := 4983230072969 + 3 ^ 40 * 5362681 * 2
def baseEnd_5362681 : Nat := 2753632949733838219624985

theorem tailTrace_5362681 : CollatzResearch.WordTrace tailWord_5362681 prefixEnd_5362681 2753632949733838219624985 := by
  unfold tailWord_5362681
  simp only [CollatzResearch.WordTrace]
  refine ⟨195593044684930084843535897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130395363123286723229023931 195593044684930084843535897)
  ·
    refine ⟨146694783513697563632651923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195593044684930084843535897 146694783513697563632651923)
    ·
      refine ⟨220042175270546345448977885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146694783513697563632651923 220042175270546345448977885)
      ·
        refine ⟨82515815726454879543366707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220042175270546345448977885 82515815726454879543366707)
        ·
          refine ⟨123773723589682319315050061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82515815726454879543366707 123773723589682319315050061)
          ·
            refine ⟨46415146346130869743143773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123773723589682319315050061 46415146346130869743143773)
            ·
              refine ⟨17405679879799076153678915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46415146346130869743143773 17405679879799076153678915)
              ·
                refine ⟨26108519819698614230518373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17405679879799076153678915 26108519819698614230518373)
                ·
                  refine ⟨4895347466193490168222195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26108519819698614230518373 4895347466193490168222195)
                  ·
                    refine ⟨7343021199290235252333293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4895347466193490168222195 7343021199290235252333293)
                    ·
                      refine ⟨2753632949733838219624985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7343021199290235252333293 2753632949733838219624985)
                      ·
                        rfl

theorem cell23_5362681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_5362681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362681 prefixEnd_5362681 := by exact prefixLift 5362681
  have htrace : WordTrace (prefixWord ++ tailWord_5362681) baseStart_5362681 baseEnd_5362681 := by
    simpa [prefixWord, tailWord_5362681, baseEnd_5362681] using wordTrace_append hprefix tailTrace_5362681
  have hstable : (prefixWord ++ tailWord_5362681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362681).length < 2 ^ (prefixWord ++ tailWord_5362681).sum := by decide
  have hdescent : baseEnd_5362681 < baseStart_5362681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362698 : List Nat := [3, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_5362698 : Nat := 118140960795 + 5362698 * 2 ^ 59
def prefixEnd_5362698 : Nat := 4983230072969 + 3 ^ 40 * 5362698 * 2
def baseEnd_5362698 : Nat := 2753641678904964653112407

theorem tailTrace_5362698 : CollatzResearch.WordTrace tailWord_5362698 prefixEnd_5362698 2753641678904964653112407 := by
  unfold tailWord_5362698
  simp only [CollatzResearch.WordTrace]
  refine ⟨48898416181467124186726187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130395776483912331164603165 48898416181467124186726187)
  ·
    refine ⟨73347624272200686280089281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48898416181467124186726187 73347624272200686280089281)
    ·
      refine ⟨55010718204150514710066961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73347624272200686280089281 55010718204150514710066961)
      ·
        refine ⟨41258038653112886032550221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55010718204150514710066961 41258038653112886032550221)
        ·
          refine ⟨15471764494917332262206333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41258038653112886032550221 15471764494917332262206333)
          ·
            refine ⟨5801911685593999598327375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15471764494917332262206333 5801911685593999598327375)
            ·
              refine ⟨8702867528390999397491063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5801911685593999598327375 8702867528390999397491063)
              ·
                refine ⟨13054301292586499096236595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8702867528390999397491063 13054301292586499096236595)
                ·
                  refine ⟨19581451938879748644354893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13054301292586499096236595 19581451938879748644354893)
                  ·
                    refine ⟨7343044477079905741633085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19581451938879748644354893 7343044477079905741633085)
                    ·
                      refine ⟨2753641678904964653112407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7343044477079905741633085 2753641678904964653112407)
                      ·
                        rfl

theorem cell23_5362698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_5362698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362698 prefixEnd_5362698 := by exact prefixLift 5362698
  have htrace : WordTrace (prefixWord ++ tailWord_5362698) baseStart_5362698 baseEnd_5362698 := by
    simpa [prefixWord, tailWord_5362698, baseEnd_5362698] using wordTrace_append hprefix tailTrace_5362698
  have hstable : (prefixWord ++ tailWord_5362698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362698).length < 2 ^ (prefixWord ++ tailWord_5362698).sum := by decide
  have hdescent : baseEnd_5362698 < baseStart_5362698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362738 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2]
def baseStart_5362738 : Nat := 118140960795 + 5362738 * 2 ^ 59
def prefixEnd_5362738 : Nat := 4983230072969 + 3 ^ 40 * 5362738 * 2
def baseEnd_5362738 : Nat := 2753662218131144496612223

theorem tailTrace_5362738 : CollatzResearch.WordTrace tailWord_5362738 prefixEnd_5362738 2753662218131144496612223 := by
  unfold tailWord_5362738
  simp only [CollatzResearch.WordTrace]
  refine ⟨48898780911430895894590217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130396749097149055718907245 48898780911430895894590217)
  ·
    refine ⟨36674085683573171920942663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48898780911430895894590217 36674085683573171920942663)
    ·
      refine ⟨55011128525359757881413995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36674085683573171920942663 55011128525359757881413995)
      ·
        refine ⟨82516692788039636822120993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55011128525359757881413995 82516692788039636822120993)
        ·
          refine ⟨61887519591029727616590745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82516692788039636822120993 61887519591029727616590745)
          ·
            refine ⟨46415639693272295712443059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61887519591029727616590745 46415639693272295712443059)
            ·
              refine ⟨69623459539908443568664589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46415639693272295712443059 69623459539908443568664589)
              ·
                refine ⟨26108797327465666338249221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69623459539908443568664589 26108797327465666338249221)
                ·
                  refine ⟨4895399498899812438421729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26108797327465666338249221 4895399498899812438421729)
                  ·
                    refine ⟨3671549624174859328816297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4895399498899812438421729 3671549624174859328816297)
                    ·
                      refine ⟨2753662218131144496612223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671549624174859328816297 2753662218131144496612223)
                      ·
                        rfl

theorem cell23_5362738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_5362738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362738 prefixEnd_5362738 := by exact prefixLift 5362738
  have htrace : WordTrace (prefixWord ++ tailWord_5362738) baseStart_5362738 baseEnd_5362738 := by
    simpa [prefixWord, tailWord_5362738, baseEnd_5362738] using wordTrace_append hprefix tailTrace_5362738
  have hstable : (prefixWord ++ tailWord_5362738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362738).length < 2 ^ (prefixWord ++ tailWord_5362738).sum := by decide
  have hdescent : baseEnd_5362738 < baseStart_5362738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362758 : List Nat := [6, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_5362758 : Nat := 118140960795 + 5362758 * 2 ^ 59
def prefixEnd_5362758 : Nat := 4983230072969 + 3 ^ 40 * 5362758 * 2
def baseEnd_5362758 : Nat := 2753672487744234418362131

theorem tailTrace_5362758 : CollatzResearch.WordTrace tailWord_5362758 prefixEnd_5362758 2753672487744234418362131 := by
  unfold tailWord_5362758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6112370409551597718565279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130397235403767417996059285 6112370409551597718565279)
  ·
    refine ⟨9168555614327396577847919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6112370409551597718565279 9168555614327396577847919)
    ·
      refine ⟨13752833421491094866771879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9168555614327396577847919 13752833421491094866771879)
      ·
        refine ⟨20629250132236642300157819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13752833421491094866771879 20629250132236642300157819)
        ·
          refine ⟨30943875198354963450236729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20629250132236642300157819 30943875198354963450236729)
          ·
            refine ⟨23207906398766222587677547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30943875198354963450236729 23207906398766222587677547)
            ·
              refine ⟨34811859598149333881516321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23207906398766222587677547 34811859598149333881516321)
              ·
                refine ⟨26108894698612000411137241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34811859598149333881516321 26108894698612000411137241)
                ·
                  refine ⟨19581671023959000308352931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26108894698612000411137241 19581671023959000308352931)
                  ·
                    refine ⟨29372506535938500462529397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19581671023959000308352931 29372506535938500462529397)
                    ·
                      refine ⟨2753672487744234418362131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29372506535938500462529397 2753672487744234418362131)
                      ·
                        rfl

theorem cell23_5362758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_5362758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362758 prefixEnd_5362758 := by exact prefixLift 5362758
  have htrace : WordTrace (prefixWord ++ tailWord_5362758) baseStart_5362758 baseEnd_5362758 := by
    simpa [prefixWord, tailWord_5362758, baseEnd_5362758] using wordTrace_append hprefix tailTrace_5362758
  have hstable : (prefixWord ++ tailWord_5362758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362758).length < 2 ^ (prefixWord ++ tailWord_5362758).sum := by decide
  have hdescent : baseEnd_5362758 < baseStart_5362758 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362784 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_5362784 : Nat := 118140960795 + 5362784 * 2 ^ 59
def prefixEnd_5362784 : Nat := 4983230072969 + 3 ^ 40 * 5362784 * 2
def baseEnd_5362784 : Nat := 2753685838241251316637011

theorem tailTrace_5362784 : CollatzResearch.WordTrace tailWord_5362784 prefixEnd_5362784 2753685838241251316637011 := by
  unfold tailWord_5362784
  simp only [CollatzResearch.WordTrace]
  refine ⟨97798400701778466717267703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130397867602371288956356937 97798400701778466717267703)
  ·
    refine ⟨146697601052667700075901555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97798400701778466717267703 146697601052667700075901555)
    ·
      refine ⟨220046401579001550113852333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146697601052667700075901555 220046401579001550113852333)
      ·
        refine ⟨82517400592125581292694625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220046401579001550113852333 82517400592125581292694625)
        ·
          refine ⟨61888050444094185969520969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82517400592125581292694625 61888050444094185969520969)
          ·
            refine ⟨46416037833070639477140727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61888050444094185969520969 46416037833070639477140727)
            ·
              refine ⟨69624056749605959215711091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46416037833070639477140727 69624056749605959215711091)
              ·
                refine ⟨104436085124408938823566637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69624056749605959215711091 104436085124408938823566637)
                ·
                  refine ⟨39163531921653352058837489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104436085124408938823566637 39163531921653352058837489)
                  ·
                    refine ⟨29372648941240014044128117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39163531921653352058837489 29372648941240014044128117)
                    ·
                      refine ⟨2753685838241251316637011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29372648941240014044128117 2753685838241251316637011)
                      ·
                        rfl

theorem cell23_5362784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_5362784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362784 prefixEnd_5362784 := by exact prefixLift 5362784
  have htrace : WordTrace (prefixWord ++ tailWord_5362784) baseStart_5362784 baseEnd_5362784 := by
    simpa [prefixWord, tailWord_5362784, baseEnd_5362784] using wordTrace_append hprefix tailTrace_5362784
  have hstable : (prefixWord ++ tailWord_5362784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362784).length < 2 ^ (prefixWord ++ tailWord_5362784).sum := by decide
  have hdescent : baseEnd_5362784 < baseStart_5362784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362791 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 2, 5]
def baseStart_5362791 : Nat := 118140960795 + 5362791 * 2 ^ 59
def prefixEnd_5362791 : Nat := 4983230072969 + 3 ^ 40 * 5362791 * 2
def baseEnd_5362791 : Nat := 917896477535277596416493

theorem tailTrace_5362791 : CollatzResearch.WordTrace tailWord_5362791 prefixEnd_5362791 917896477535277596416493 := by
  unfold tailWord_5362791
  simp only [CollatzResearch.WordTrace]
  refine ⟨195597056714531573630040227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130398037809687715753360151 195597056714531573630040227)
  ·
    refine ⟨293395585071797360445060341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195597056714531573630040227 293395585071797360445060341)
    ·
      refine ⟨27505836100481002541724407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 293395585071797360445060341 27505836100481002541724407)
      ·
        refine ⟨41258754150721503812586611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27505836100481002541724407 41258754150721503812586611)
        ·
          refine ⟨61888131226082255718879917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41258754150721503812586611 61888131226082255718879917)
          ·
            refine ⟨23208049209780845894579969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61888131226082255718879917 23208049209780845894579969)
            ·
              refine ⟨17406036907335634420934977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23208049209780845894579969 17406036907335634420934977)
              ·
                refine ⟨13054527680501725815701233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17406036907335634420934977 13054527680501725815701233)
                ·
                  refine ⟨9790895760376294361775925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13054527680501725815701233 9790895760376294361775925)
                  ·
                    refine ⟨917896477535277596416493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9790895760376294361775925 917896477535277596416493)
                    ·
                      rfl

theorem cell23_5362791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_5362791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362791 prefixEnd_5362791 := by exact prefixLift 5362791
  have htrace : WordTrace (prefixWord ++ tailWord_5362791) baseStart_5362791 baseEnd_5362791 := by
    simpa [prefixWord, tailWord_5362791, baseEnd_5362791] using wordTrace_append hprefix tailTrace_5362791
  have hstable : (prefixWord ++ tailWord_5362791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362791).length < 2 ^ (prefixWord ++ tailWord_5362791).sum := by decide
  have hdescent : baseEnd_5362791 < baseStart_5362791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362798 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_5362798 : Nat := 118140960795 + 5362798 * 2 ^ 59
def prefixEnd_5362798 : Nat := 4983230072969 + 3 ^ 40 * 5362798 * 2
def baseEnd_5362798 : Nat := 2753693026970414261861947

theorem tailTrace_5362798 : CollatzResearch.WordTrace tailWord_5362798 prefixEnd_5362798 2753693026970414261861947 := by
  unfold tailWord_5362798
  simp only [CollatzResearch.WordTrace]
  refine ⟨24449664003188276728193131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130398208017004142550363365 24449664003188276728193131)
  ·
    refine ⟨36674496004782415092289697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24449664003188276728193131 36674496004782415092289697)
    ·
      refine ⟨27505872003586811319217273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36674496004782415092289697 27505872003586811319217273)
      ·
        refine ⟨20629404002690108489412955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27505872003586811319217273 20629404002690108489412955)
        ·
          refine ⟨30944106004035162734119433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20629404002690108489412955 30944106004035162734119433)
          ·
            refine ⟨23208079503026372050589575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30944106004035162734119433 23208079503026372050589575)
            ·
              refine ⟨34812119254539558075884363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23208079503026372050589575 34812119254539558075884363)
              ·
                refine ⟨52218178881809337113826545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34812119254539558075884363 52218178881809337113826545)
                ·
                  refine ⟨39163634161357002835369909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52218178881809337113826545 39163634161357002835369909)
                  ·
                    refine ⟨3671590702627219015815929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39163634161357002835369909 3671590702627219015815929)
                    ·
                      refine ⟨2753693026970414261861947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671590702627219015815929 2753693026970414261861947)
                      ·
                        rfl

theorem cell23_5362798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_5362798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362798 prefixEnd_5362798 := by exact prefixLift 5362798
  have htrace : WordTrace (prefixWord ++ tailWord_5362798) baseStart_5362798 baseEnd_5362798 := by
    simpa [prefixWord, tailWord_5362798, baseEnd_5362798] using wordTrace_append hprefix tailTrace_5362798
  have hstable : (prefixWord ++ tailWord_5362798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362798).length < 2 ^ (prefixWord ++ tailWord_5362798).sum := by decide
  have hdescent : baseEnd_5362798 < baseStart_5362798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362805 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5362805 : Nat := 118140960795 + 5362805 * 2 ^ 59
def prefixEnd_5362805 : Nat := 4983230072969 + 3 ^ 40 * 5362805 * 2
def baseEnd_5362805 : Nat := 2753696621334995734474415

theorem tailTrace_5362805 : CollatzResearch.WordTrace tailWord_5362805 prefixEnd_5362805 2753696621334995734474415 := by
  unfold tailWord_5362805
  simp only [CollatzResearch.WordTrace]
  refine ⟨195597567336480854021049869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130398378224320569347366579 195597567336480854021049869)
  ·
    refine ⟨73349087751180320257893701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195597567336480854021049869 73349087751180320257893701)
    ·
      refine ⟨13752953953346310048355069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73349087751180320257893701 13752953953346310048355069)
      ·
        refine ⟨5157357732504866268133151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13752953953346310048355069 5157357732504866268133151)
        ·
          refine ⟨7736036598757299402199727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5157357732504866268133151 7736036598757299402199727)
          ·
            refine ⟨11604054898135949103299591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7736036598757299402199727 11604054898135949103299591)
            ·
              refine ⟨17406082347203923654949387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11604054898135949103299591 17406082347203923654949387)
              ·
                refine ⟨26109123520805885482424081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17406082347203923654949387 26109123520805885482424081)
                ·
                  refine ⟨19581842640604414111818061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26109123520805885482424081 19581842640604414111818061)
                  ·
                    refine ⟨7343190990226655291931773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19581842640604414111818061 7343190990226655291931773)
                    ·
                      refine ⟨2753696621334995734474415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7343190990226655291931773 2753696621334995734474415)
                      ·
                        rfl

theorem cell23_5362805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5362805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362805 prefixEnd_5362805 := by exact prefixLift 5362805
  have htrace : WordTrace (prefixWord ++ tailWord_5362805) baseStart_5362805 baseEnd_5362805 := by
    simpa [prefixWord, tailWord_5362805, baseEnd_5362805] using wordTrace_append hprefix tailTrace_5362805
  have hstable : (prefixWord ++ tailWord_5362805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362805).length < 2 ^ (prefixWord ++ tailWord_5362805).sum := by decide
  have hdescent : baseEnd_5362805 < baseStart_5362805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362855 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 3, 4]
def baseStart_5362855 : Nat := 118140960795 + 5362855 * 2 ^ 59
def prefixEnd_5362855 : Nat := 4983230072969 + 3 ^ 40 * 5362855 * 2
def baseEnd_5362855 : Nat := 917907431789240179616395

theorem tailTrace_5362855 : CollatzResearch.WordTrace tailWord_5362855 prefixEnd_5362855 917907431789240179616395 := by
  unfold tailWord_5362855
  simp only [CollatzResearch.WordTrace]
  refine ⟨195599390986299712560370019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130399593990866475040246679 195599390986299712560370019)
  ·
    refine ⟨293399086479449568840555029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195599390986299712560370019 293399086479449568840555029)
    ·
      refine ⟨13753082178724198539401017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 293399086479449568840555029 13753082178724198539401017)
      ·
        refine ⟨10314811634043148904550763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13753082178724198539401017 10314811634043148904550763)
        ·
          refine ⟨15472217451064723356826145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10314811634043148904550763 15472217451064723356826145)
          ·
            refine ⟨11604163088298542517619609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15472217451064723356826145 11604163088298542517619609)
            ·
              refine ⟨8703122316223906888214707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11604163088298542517619609 8703122316223906888214707)
              ·
                refine ⟨13054683474335860332322061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8703122316223906888214707 13054683474335860332322061)
                ·
                  refine ⟨4895506302875947624620773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13054683474335860332322061 4895506302875947624620773)
                  ·
                    refine ⟨917907431789240179616395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4895506302875947624620773 917907431789240179616395)
                    ·
                      rfl

theorem cell23_5362855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_5362855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362855 prefixEnd_5362855 := by exact prefixLift 5362855
  have htrace : WordTrace (prefixWord ++ tailWord_5362855) baseStart_5362855 baseEnd_5362855 := by
    simpa [prefixWord, tailWord_5362855, baseEnd_5362855] using wordTrace_append hprefix tailTrace_5362855
  have hstable : (prefixWord ++ tailWord_5362855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362855).length < 2 ^ (prefixWord ++ tailWord_5362855).sum := by decide
  have hdescent : baseEnd_5362855 < baseStart_5362855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362888 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 1, 5, 2]
def baseStart_5362888 : Nat := 118140960795 + 5362888 * 2 ^ 59
def prefixEnd_5362888 : Nat := 4983230072969 + 3 ^ 40 * 5362888 * 2
def baseEnd_5362888 : Nat := 2753739240229318909736533

theorem tailTrace_5362888 : CollatzResearch.WordTrace tailWord_5362888 prefixEnd_5362888 2753739240229318909736533 := by
  unfold tailWord_5362888
  simp only [CollatzResearch.WordTrace]
  refine ⟨97800297297590079598160659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130400396396786772797547545 97800297297590079598160659)
  ·
    refine ⟨146700445946385119397240989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97800297297590079598160659 146700445946385119397240989)
    ·
      refine ⟨55012667229894419773965371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146700445946385119397240989 55012667229894419773965371)
      ·
        refine ⟨82519000844841629660948057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55012667229894419773965371 82519000844841629660948057)
        ·
          refine ⟨61889250633631222245711043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82519000844841629660948057 61889250633631222245711043)
          ·
            refine ⟨92833875950446833368566565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61889250633631222245711043 92833875950446833368566565)
            ·
              refine ⟨17406351740708781256606231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92833875950446833368566565 17406351740708781256606231)
              ·
                refine ⟨26109527611063171884909347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17406351740708781256606231 26109527611063171884909347)
                ·
                  refine ⟨39164291416594757827364021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26109527611063171884909347 39164291416594757827364021)
                  ·
                    refine ⟨3671652320305758546315377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39164291416594757827364021 3671652320305758546315377)
                    ·
                      refine ⟨2753739240229318909736533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671652320305758546315377 2753739240229318909736533)
                      ·
                        rfl

theorem cell23_5362888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_5362888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362888 prefixEnd_5362888 := by exact prefixLift 5362888
  have htrace : WordTrace (prefixWord ++ tailWord_5362888) baseStart_5362888 baseEnd_5362888 := by
    simpa [prefixWord, tailWord_5362888, baseEnd_5362888] using wordTrace_append hprefix tailTrace_5362888
  have hstable : (prefixWord ++ tailWord_5362888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362888).length < 2 ^ (prefixWord ++ tailWord_5362888).sum := by decide
  have hdescent : baseEnd_5362888 < baseStart_5362888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362895 : List Nat := [1, 1, 2, 1, 1, 3, 2, 7, 1, 1, 3]
def baseStart_5362895 : Nat := 118140960795 + 5362895 * 2 ^ 59
def prefixEnd_5362895 : Nat := 4983230072969 + 3 ^ 40 * 5362895 * 2
def baseEnd_5362895 : Nat := 2753742834593900382349001

theorem tailTrace_5362895 : CollatzResearch.WordTrace tailWord_5362895 prefixEnd_5362895 2753742834593900382349001 := by
  unfold tailWord_5362895
  simp only [CollatzResearch.WordTrace]
  refine ⟨195600849906154799391826139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130400566604103199594550759 195600849906154799391826139)
  ·
    refine ⟨293401274859232199087739209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195600849906154799391826139 293401274859232199087739209)
    ·
      refine ⟨220050956144424149315804407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293401274859232199087739209 220050956144424149315804407)
      ·
        refine ⟨330076434216636223973706611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220050956144424149315804407 330076434216636223973706611)
        ·
          refine ⟨495114651324954335960559917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330076434216636223973706611 495114651324954335960559917)
          ·
            refine ⟨185667994246857875985209969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 495114651324954335960559917 185667994246857875985209969)
            ·
              refine ⟨139250995685143406988907477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185667994246857875985209969 139250995685143406988907477)
              ·
                refine ⟨3263695211370548601302519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 139250995685143406988907477 3263695211370548601302519)
                ·
                  refine ⟨4895542817055822901953779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3263695211370548601302519 4895542817055822901953779)
                  ·
                    refine ⟨7343314225583734352930669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4895542817055822901953779 7343314225583734352930669)
                    ·
                      refine ⟨2753742834593900382349001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7343314225583734352930669 2753742834593900382349001)
                      ·
                        rfl

theorem cell23_5362895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 1, 1, 3].length) (baseStart_5362895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362895 prefixEnd_5362895 := by exact prefixLift 5362895
  have htrace : WordTrace (prefixWord ++ tailWord_5362895) baseStart_5362895 baseEnd_5362895 := by
    simpa [prefixWord, tailWord_5362895, baseEnd_5362895] using wordTrace_append hprefix tailTrace_5362895
  have hstable : (prefixWord ++ tailWord_5362895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362895).length < 2 ^ (prefixWord ++ tailWord_5362895).sum := by decide
  have hdescent : baseEnd_5362895 < baseStart_5362895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362898 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 1, 5]
def baseStart_5362898 : Nat := 118140960795 + 5362898 * 2 ^ 59
def prefixEnd_5362898 : Nat := 4983230072969 + 3 ^ 40 * 5362898 * 2
def baseEnd_5362898 : Nat := 917914791678621290203829

theorem tailTrace_5362898 : CollatzResearch.WordTrace tailWord_5362898 prefixEnd_5362898 917914791678621290203829 := by
  unfold tailWord_5362898
  simp only [CollatzResearch.WordTrace]
  refine ⟨48900239831285982726046337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130400639550095953936123565 48900239831285982726046337)
  ·
    refine ⟨36675179873464487044534753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48900239831285982726046337 36675179873464487044534753)
    ·
      refine ⟨27506384905098365283401065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36675179873464487044534753 27506384905098365283401065)
      ·
        refine ⟨20629788678823773962550799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27506384905098365283401065 20629788678823773962550799)
        ·
          refine ⟨30944683018235660943826199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20629788678823773962550799 30944683018235660943826199)
          ·
            refine ⟨46417024527353491415739299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30944683018235660943826199 46417024527353491415739299)
            ·
              refine ⟨69625536791030237123608949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46417024527353491415739299 69625536791030237123608949)
              ·
                refine ⟨6527394074159084730338339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69625536791030237123608949 6527394074159084730338339)
                ·
                  refine ⟨9791091111238627095507509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6527394074159084730338339 9791091111238627095507509)
                  ·
                    refine ⟨917914791678621290203829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9791091111238627095507509 917914791678621290203829)
                    ·
                      rfl

theorem cell23_5362898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_5362898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362898 prefixEnd_5362898 := by exact prefixLift 5362898
  have htrace : WordTrace (prefixWord ++ tailWord_5362898) baseStart_5362898 baseEnd_5362898 := by
    simpa [prefixWord, tailWord_5362898, baseEnd_5362898] using wordTrace_append hprefix tailTrace_5362898
  have hstable : (prefixWord ++ tailWord_5362898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362898).length < 2 ^ (prefixWord ++ tailWord_5362898).sum := by decide
  have hdescent : baseEnd_5362898 < baseStart_5362898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362931 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 6]
def baseStart_5362931 : Nat := 118140960795 + 5362931 * 2 ^ 59
def prefixEnd_5362931 : Nat := 4983230072969 + 3 ^ 40 * 5362931 * 2
def baseEnd_5362931 : Nat := 2753761319897462241498835

theorem tailTrace_5362931 : CollatzResearch.WordTrace tailWord_5362931 prefixEnd_5362931 2753761319897462241498835 := by
  unfold tailWord_5362931
  simp only [CollatzResearch.WordTrace]
  refine ⟨195602162934024377540136647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130401441956016251693424431 195602162934024377540136647)
  ·
    refine ⟨293403244401036566310204971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195602162934024377540136647 293403244401036566310204971)
    ·
      refine ⟨440104866601554849465307457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293403244401036566310204971 440104866601554849465307457)
      ·
        refine ⟨330078649951166137098980593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440104866601554849465307457 330078649951166137098980593)
        ·
          refine ⟨247558987463374602824235445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330078649951166137098980593 247558987463374602824235445)
          ·
            refine ⟨23208655074691369014772073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 247558987463374602824235445 23208655074691369014772073)
            ·
              refine ⟨17406491306018526761079055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23208655074691369014772073 17406491306018526761079055)
              ·
                refine ⟨26109736959027790141618583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17406491306018526761079055 26109736959027790141618583)
                ·
                  refine ⟨39164605438541685212427875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26109736959027790141618583 39164605438541685212427875)
                  ·
                    refine ⟨58746908157812527818641813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39164605438541685212427875 58746908157812527818641813)
                    ·
                      refine ⟨2753761319897462241498835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58746908157812527818641813 2753761319897462241498835)
                      ·
                        rfl

theorem cell23_5362931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_5362931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362931 prefixEnd_5362931 := by exact prefixLift 5362931
  have htrace : WordTrace (prefixWord ++ tailWord_5362931) baseStart_5362931 baseEnd_5362931 := by
    simpa [prefixWord, tailWord_5362931, baseEnd_5362931] using wordTrace_append hprefix tailTrace_5362931
  have hstable : (prefixWord ++ tailWord_5362931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362931).length < 2 ^ (prefixWord ++ tailWord_5362931).sum := by decide
  have hdescent : baseEnd_5362931 < baseStart_5362931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362938 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3]
def baseStart_5362938 : Nat := 118140960795 + 5362938 * 2 ^ 59
def prefixEnd_5362938 : Nat := 4983230072969 + 3 ^ 40 * 5362938 * 2
def baseEnd_5362938 : Nat := 2753764914262043714111303

theorem tailTrace_5362938 : CollatzResearch.WordTrace tailWord_5362938 prefixEnd_5362938 2753764914262043714111303 := by
  unfold tailWord_5362938
  simp only [CollatzResearch.WordTrace]
  refine ⟨48900604561249754433910367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130401612163332678490427645 48900604561249754433910367)
  ·
    refine ⟨73350906841874631650865551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48900604561249754433910367 73350906841874631650865551)
    ·
      refine ⟨110026360262811947476298327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73350906841874631650865551 110026360262811947476298327)
      ·
        refine ⟨165039540394217921214447491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110026360262811947476298327 165039540394217921214447491)
        ·
          refine ⟨247559310591326881821671237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165039540394217921214447491 247559310591326881821671237)
          ·
            refine ⟨46417370735873790341563357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247559310591326881821671237 46417370735873790341563357)
            ·
              refine ⟨17406514025952671378086259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46417370735873790341563357 17406514025952671378086259)
              ·
                refine ⟨26109771038929007067129389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17406514025952671378086259 26109771038929007067129389)
                ·
                  refine ⟨9791164139598377650173521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26109771038929007067129389 9791164139598377650173521)
                  ·
                    refine ⟨7343373104698783237630141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9791164139598377650173521 7343373104698783237630141)
                    ·
                      refine ⟨2753764914262043714111303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7343373104698783237630141 2753764914262043714111303)
                      ·
                        rfl

theorem cell23_5362938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_5362938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362938 prefixEnd_5362938 := by exact prefixLift 5362938
  have htrace : WordTrace (prefixWord ++ tailWord_5362938) baseStart_5362938 baseEnd_5362938 := by
    simpa [prefixWord, tailWord_5362938, baseEnd_5362938] using wordTrace_append hprefix tailTrace_5362938
  have hstable : (prefixWord ++ tailWord_5362938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362938).length < 2 ^ (prefixWord ++ tailWord_5362938).sum := by decide
  have hdescent : baseEnd_5362938 < baseStart_5362938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362948 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_5362948 : Nat := 118140960795 + 5362948 * 2 ^ 59
def prefixEnd_5362948 : Nat := 4983230072969 + 3 ^ 40 * 5362948 * 2
def baseEnd_5362948 : Nat := 2753770049068588674986257

theorem tailTrace_5362948 : CollatzResearch.WordTrace tailWord_5362948 prefixEnd_5362948 2753770049068588674986257 := by
  unfold tailWord_5362948
  simp only [CollatzResearch.WordTrace]
  refine ⟨97801391487481394721752749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130401855316641859629003665 97801391487481394721752749)
  ·
    refine ⟨36675521807805523020657281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97801391487481394721752749 36675521807805523020657281)
    ·
      refine ⟨27506641355854142265492961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36675521807805523020657281 27506641355854142265492961)
      ·
        refine ⟨20629981016890606699119721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27506641355854142265492961 20629981016890606699119721)
        ·
          refine ⟨15472485762667955024339791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20629981016890606699119721 15472485762667955024339791)
          ·
            refine ⟨23208728644001932536509687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15472485762667955024339791 23208728644001932536509687)
            ·
              refine ⟨34813092966002898804764531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23208728644001932536509687 34813092966002898804764531)
              ·
                refine ⟨52219639449004348207146797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34813092966002898804764531 52219639449004348207146797)
                ·
                  refine ⟨19582364793376630577680049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52219639449004348207146797 19582364793376630577680049)
                  ·
                    refine ⟨14686773595032472933260037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19582364793376630577680049 14686773595032472933260037)
                    ·
                      refine ⟨2753770049068588674986257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14686773595032472933260037 2753770049068588674986257)
                      ·
                        rfl

theorem cell23_5362948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_5362948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362948 prefixEnd_5362948 := by exact prefixLift 5362948
  have htrace : WordTrace (prefixWord ++ tailWord_5362948) baseStart_5362948 baseEnd_5362948 := by
    simpa [prefixWord, tailWord_5362948, baseEnd_5362948] using wordTrace_append hprefix tailTrace_5362948
  have hstable : (prefixWord ++ tailWord_5362948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362948).length < 2 ^ (prefixWord ++ tailWord_5362948).sum := by decide
  have hdescent : baseEnd_5362948 < baseStart_5362948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362952 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 1, 1, 4]
def baseStart_5362952 : Nat := 118140960795 + 5362952 * 2 ^ 59
def prefixEnd_5362952 : Nat := 4983230072969 + 3 ^ 40 * 5362952 * 2
def baseEnd_5362952 : Nat := 2753772102991206659336239

theorem tailTrace_5362952 : CollatzResearch.WordTrace tailWord_5362952 prefixEnd_5362952 2753772102991206659336239 := by
  unfold tailWord_5362952
  simp only [CollatzResearch.WordTrace]
  refine ⟨97801464433474149063325555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130401952577965532084434073 97801464433474149063325555)
  ·
    refine ⟨146702196650211223594988333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97801464433474149063325555 146702196650211223594988333)
    ·
      refine ⟨55013323743829208848120625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146702196650211223594988333 55013323743829208848120625)
      ·
        refine ⟨41259992807871906636090469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55013323743829208848120625 41259992807871906636090469)
        ·
          refine ⟨7736248651475982494266963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41259992807871906636090469 7736248651475982494266963)
          ·
            refine ⟨11604372977213973741400445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7736248651475982494266963 11604372977213973741400445)
            ·
              refine ⟨4351639866455240153025167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11604372977213973741400445 4351639866455240153025167)
              ·
                refine ⟨6527459799682860229537751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4351639866455240153025167 6527459799682860229537751)
                ·
                  refine ⟨9791189699524290344306627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6527459799682860229537751 9791189699524290344306627)
                  ·
                    refine ⟨14686784549286435516459941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9791189699524290344306627 14686784549286435516459941)
                    ·
                      refine ⟨2753772102991206659336239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14686784549286435516459941 2753772102991206659336239)
                      ·
                        rfl

theorem cell23_5362952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_5362952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362952 prefixEnd_5362952 := by exact prefixLift 5362952
  have htrace : WordTrace (prefixWord ++ tailWord_5362952) baseStart_5362952 baseEnd_5362952 := by
    simpa [prefixWord, tailWord_5362952, baseEnd_5362952] using wordTrace_append hprefix tailTrace_5362952
  have hstable : (prefixWord ++ tailWord_5362952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362952).length < 2 ^ (prefixWord ++ tailWord_5362952).sum := by decide
  have hdescent : baseEnd_5362952 < baseStart_5362952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362975 : List Nat := [1, 1, 2, 4, 5, 1, 1, 8]
def baseStart_5362975 : Nat := 118140960795 + 5362975 * 2 ^ 59
def prefixEnd_5362975 : Nat := 4983230072969 + 3 ^ 40 * 5362975 * 2
def baseEnd_5362975 : Nat := 101991996779491113679579

theorem tailTrace_5362975 : CollatzResearch.WordTrace tailWord_5362975 prefixEnd_5362975 101991996779491113679579 := by
  unfold tailWord_5362975
  simp only [CollatzResearch.WordTrace]
  refine ⟨195603767745864973054738379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130402511830576648703158919 195603767745864973054738379)
  ·
    refine ⟨293405651618797459582107569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195603767745864973054738379 293405651618797459582107569)
    ·
      refine ⟨220054238714098094686580677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293405651618797459582107569 220054238714098094686580677)
      ·
        refine ⟨41260169758893392753733877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220054238714098094686580677 41260169758893392753733877)
        ·
          refine ⟨3868140914896255570662551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41260169758893392753733877 3868140914896255570662551)
          ·
            refine ⟨5802211372344383355993827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868140914896255570662551 5802211372344383355993827)
            ·
              refine ⟨8703317058516575033990741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5802211372344383355993827 8703317058516575033990741)
              ·
                refine ⟨101991996779491113679579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8703317058516575033990741 101991996779491113679579)
                ·
                  rfl

theorem cell23_5362975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 8].length) (baseStart_5362975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362975 prefixEnd_5362975 := by exact prefixLift 5362975
  have htrace : WordTrace (prefixWord ++ tailWord_5362975) baseStart_5362975 baseEnd_5362975 := by
    simpa [prefixWord, tailWord_5362975, baseEnd_5362975] using wordTrace_append hprefix tailTrace_5362975
  have hstable : (prefixWord ++ tailWord_5362975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362975).length < 2 ^ (prefixWord ++ tailWord_5362975).sum := by decide
  have hdescent : baseEnd_5362975 < baseStart_5362975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362991 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 4]
def baseStart_5362991 : Nat := 118140960795 + 5362991 * 2 ^ 59
def prefixEnd_5362991 : Nat := 4983230072969 + 3 ^ 40 * 5362991 * 2
def baseEnd_5362991 : Nat := 2753792128736732006748559

theorem tailTrace_5362991 : CollatzResearch.WordTrace tailWord_5362991 prefixEnd_5362991 2753792128736732006748559 := by
  unfold tailWord_5362991
  simp only [CollatzResearch.WordTrace]
  refine ⟨195604351313807007787320827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130402900875871338524880551 195604351313807007787320827)
  ·
    refine ⟨293406526970710511680981241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195604351313807007787320827 293406526970710511680981241)
    ·
      refine ⟨220054895228032883760735931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293406526970710511680981241 220054895228032883760735931)
      ·
        refine ⟨330082342842049325641103897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220054895228032883760735931 330082342842049325641103897)
        ·
          refine ⟨247561757131536994230827923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330082342842049325641103897 247561757131536994230827923)
          ·
            refine ⟨371342635697305491346241885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247561757131536994230827923 371342635697305491346241885)
            ·
              refine ⟨139253488386489559254840707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 371342635697305491346241885 139253488386489559254840707)
              ·
                refine ⟨208880232579734338882261061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139253488386489559254840707 208880232579734338882261061)
                ·
                  refine ⟨39165043608700188540423949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208880232579734338882261061 39165043608700188540423949)
                  ·
                    refine ⟨14686891353262570702658981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39165043608700188540423949 14686891353262570702658981)
                    ·
                      refine ⟨2753792128736732006748559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14686891353262570702658981 2753792128736732006748559)
                      ·
                        rfl

theorem cell23_5362991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_5362991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362991 prefixEnd_5362991 := by exact prefixLift 5362991
  have htrace : WordTrace (prefixWord ++ tailWord_5362991) baseStart_5362991 baseEnd_5362991 := by
    simpa [prefixWord, tailWord_5362991, baseEnd_5362991] using wordTrace_append hprefix tailTrace_5362991
  have hstable : (prefixWord ++ tailWord_5362991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362991).length < 2 ^ (prefixWord ++ tailWord_5362991).sum := by decide
  have hdescent : baseEnd_5362991 < baseStart_5362991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5362995 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 3, 3, 2]
def baseStart_5362995 : Nat := 118140960795 + 5362995 * 2 ^ 59
def prefixEnd_5362995 : Nat := 4983230072969 + 3 ^ 40 * 5362995 * 2
def baseEnd_5362995 : Nat := 2753794182659349991098541

theorem tailTrace_5362995 : CollatzResearch.WordTrace tailWord_5362995 prefixEnd_5362995 2753794182659349991098541 := by
  unfold tailWord_5362995
  simp only [CollatzResearch.WordTrace]
  refine ⟨195604497205792516470466439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130402998137195010980310959 195604497205792516470466439)
  ·
    refine ⟨293406745808688774705699659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195604497205792516470466439 293406745808688774705699659)
    ·
      refine ⟨440110118713033162058549489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293406745808688774705699659 440110118713033162058549489)
      ·
        refine ⟨330082589034774871543912117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440110118713033162058549489 330082589034774871543912117)
        ·
          refine ⟨30945242722010144207241761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 330082589034774871543912117 30945242722010144207241761)
          ·
            refine ⟨23208932041507608155431321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30945242722010144207241761 23208932041507608155431321)
            ·
              refine ⟨17406699031130706116573491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23208932041507608155431321 17406699031130706116573491)
              ·
                refine ⟨26110048546696059174860237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17406699031130706116573491 26110048546696059174860237)
                ·
                  refine ⟨9791268205011022190572589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26110048546696059174860237 9791268205011022190572589)
                  ·
                    refine ⟨3671725576879133321464721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9791268205011022190572589 3671725576879133321464721)
                    ·
                      refine ⟨2753794182659349991098541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671725576879133321464721 2753794182659349991098541)
                      ·
                        rfl

theorem cell23_5362995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 3, 2].length) (baseStart_5362995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5362995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5362995 prefixEnd_5362995 := by exact prefixLift 5362995
  have htrace : WordTrace (prefixWord ++ tailWord_5362995) baseStart_5362995 baseEnd_5362995 := by
    simpa [prefixWord, tailWord_5362995, baseEnd_5362995] using wordTrace_append hprefix tailTrace_5362995
  have hstable : (prefixWord ++ tailWord_5362995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5362995).length < 2 ^ (prefixWord ++ tailWord_5362995).sum := by decide
  have hdescent : baseEnd_5362995 < baseStart_5362995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5362995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363011 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 5]
def baseStart_5363011 : Nat := 118140960795 + 5363011 * 2 ^ 59
def prefixEnd_5363011 : Nat := 4983230072969 + 3 ^ 40 * 5363011 * 2
def baseEnd_5363011 : Nat := 2753802398349821928498467

theorem tailTrace_5363011 : CollatzResearch.WordTrace tailWord_5363011 prefixEnd_5363011 2753802398349821928498467 := by
  unfold tailWord_5363011
  simp only [CollatzResearch.WordTrace]
  refine ⟨195605080773734551203048887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130403387182489700802032591 195605080773734551203048887)
  ·
    refine ⟨293407621160601826804573331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195605080773734551203048887 293407621160601826804573331)
    ·
      refine ⟨440111431740902740206859997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293407621160601826804573331 440111431740902740206859997)
      ·
        refine ⟨165041786902838527577572499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 440111431740902740206859997 165041786902838527577572499)
        ·
          refine ⟨247562680354257791366358749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165041786902838527577572499 247562680354257791366358749)
          ·
            refine ⟨92836005132846671762384531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247562680354257791366358749 92836005132846671762384531)
            ·
              refine ⟨139254007699270007643576797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92836005132846671762384531 139254007699270007643576797)
              ·
                refine ⟨52220252887226252866341299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139254007699270007643576797 52220252887226252866341299)
                ·
                  refine ⟨78330379330839379299511949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52220252887226252866341299 78330379330839379299511949)
                  ·
                    refine ⟨29373892249064767237316981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78330379330839379299511949 29373892249064767237316981)
                    ·
                      refine ⟨2753802398349821928498467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29373892249064767237316981 2753802398349821928498467)
                      ·
                        rfl

theorem cell23_5363011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_5363011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363011 prefixEnd_5363011 := by exact prefixLift 5363011
  have htrace : WordTrace (prefixWord ++ tailWord_5363011) baseStart_5363011 baseEnd_5363011 := by
    simpa [prefixWord, tailWord_5363011, baseEnd_5363011] using wordTrace_append hprefix tailTrace_5363011
  have hstable : (prefixWord ++ tailWord_5363011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363011).length < 2 ^ (prefixWord ++ tailWord_5363011).sum := by decide
  have hdescent : baseEnd_5363011 < baseStart_5363011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363041 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_5363041 : Nat := 118140960795 + 5363041 * 2 ^ 59
def prefixEnd_5363041 : Nat := 4983230072969 + 3 ^ 40 * 5363041 * 2
def baseEnd_5363041 : Nat := 2753817802769456811123329

theorem tailTrace_5363041 : CollatzResearch.WordTrace tailWord_5363041 prefixEnd_5363041 2753817802769456811123329 := by
  unfold tailWord_5363041
  simp only [CollatzResearch.WordTrace]
  refine ⟨195606174963625866326640977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130404116642417244217760651 195606174963625866326640977)
  ·
    refine ⟨146704631222719399744980733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195606174963625866326640977 146704631222719399744980733)
    ·
      refine ⟨55014236708519774904367775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146704631222719399744980733 55014236708519774904367775)
      ·
        refine ⟨82521355062779662356551663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55014236708519774904367775 82521355062779662356551663)
        ·
          refine ⟨123782032594169493534827495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82521355062779662356551663 123782032594169493534827495)
          ·
            refine ⟨185673048891254240302241243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123782032594169493534827495 185673048891254240302241243)
            ·
              refine ⟨278509573336881360453361865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185673048891254240302241243 278509573336881360453361865)
              ·
                refine ⟨208882180002661020340021399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278509573336881360453361865 208882180002661020340021399)
                ·
                  refine ⟨313323270003991530510032099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208882180002661020340021399 313323270003991530510032099)
                  ·
                    refine ⟨469984905005987295765048149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 313323270003991530510032099 469984905005987295765048149)
                    ·
                      refine ⟨2753817802769456811123329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 469984905005987295765048149 2753817802769456811123329)
                      ·
                        rfl

theorem cell23_5363041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_5363041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363041 prefixEnd_5363041 := by exact prefixLift 5363041
  have htrace : WordTrace (prefixWord ++ tailWord_5363041) baseStart_5363041 baseEnd_5363041 := by
    simpa [prefixWord, tailWord_5363041, baseEnd_5363041] using wordTrace_append hprefix tailTrace_5363041
  have hstable : (prefixWord ++ tailWord_5363041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363041).length < 2 ^ (prefixWord ++ tailWord_5363041).sum := by decide
  have hdescent : baseEnd_5363041 < baseStart_5363041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363065 : List Nat := [1, 2, 1, 3, 2, 1, 5, 3, 5]
def baseStart_5363065 : Nat := 118140960795 + 5363065 * 2 ^ 59
def prefixEnd_5363065 : Nat := 4983230072969 + 3 ^ 40 * 5363065 * 2
def baseEnd_5363065 : Nat := 305981125145018301913691

theorem tailTrace_5363065 : CollatzResearch.WordTrace tailWord_5363065 prefixEnd_5363065 305981125145018301913691 := by
  unfold tailWord_5363065
  simp only [CollatzResearch.WordTrace]
  refine ⟨195607050315538918425514649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130404700210359278950343099 195607050315538918425514649)
  ·
    refine ⟨146705287736654188819135987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195607050315538918425514649 146705287736654188819135987)
    ·
      refine ⟨220057931604981283228703981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146705287736654188819135987 220057931604981283228703981)
      ·
        refine ⟨82521724351867981210763993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220057931604981283228703981 82521724351867981210763993)
        ·
          refine ⟨61891293263900985908072995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82521724351867981210763993 61891293263900985908072995)
          ·
            refine ⟨92836939895851478862109493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61891293263900985908072995 92836939895851478862109493)
            ·
              refine ⟨8703463115236076143322765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92836939895851478862109493 8703463115236076143322765)
              ·
                refine ⟨3263798668213528553746037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8703463115236076143322765 3263798668213528553746037)
                ·
                  refine ⟨305981125145018301913691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3263798668213528553746037 305981125145018301913691)
                  ·
                    rfl

theorem cell23_5363065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 5].length) (baseStart_5363065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363065 prefixEnd_5363065 := by exact prefixLift 5363065
  have htrace : WordTrace (prefixWord ++ tailWord_5363065) baseStart_5363065 baseEnd_5363065 := by
    simpa [prefixWord, tailWord_5363065, baseEnd_5363065] using wordTrace_append hprefix tailTrace_5363065
  have hstable : (prefixWord ++ tailWord_5363065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363065).length < 2 ^ (prefixWord ++ tailWord_5363065).sum := by decide
  have hdescent : baseEnd_5363065 < baseStart_5363065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363182 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_5363182 : Nat := 118140960795 + 5363182 * 2 ^ 59
def prefixEnd_5363182 : Nat := 4983230072969 + 3 ^ 40 * 5363182 * 2
def baseEnd_5363182 : Nat := 2753890203541740759460181

theorem tailTrace_5363182 : CollatzResearch.WordTrace tailWord_5363182 prefixEnd_5363182 2753890203541740759460181 := by
  unfold tailWord_5363182
  simp only [CollatzResearch.WordTrace]
  refine ⟨24451414707014380925940475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130407545104076698271682533 24451414707014380925940475)
  ·
    refine ⟨36677122060521571388910713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24451414707014380925940475 36677122060521571388910713)
    ·
      refine ⟨27507841545391178541683035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36677122060521571388910713 27507841545391178541683035)
      ·
        refine ⟨41261762318086767812524553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27507841545391178541683035 41261762318086767812524553)
        ·
          refine ⟨30946321738565075859393415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41261762318086767812524553 30946321738565075859393415)
          ·
            refine ⟨46419482607847613789090123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30946321738565075859393415 46419482607847613789090123)
            ·
              refine ⟨69629223911771420683635185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46419482607847613789090123 69629223911771420683635185)
              ·
                refine ⟨52221917933828565512726389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69629223911771420683635185 52221917933828565512726389)
                ·
                  refine ⟨4895804806296428016818099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52221917933828565512726389 4895804806296428016818099)
                  ·
                    refine ⟨7343707209444642025227149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4895804806296428016818099 7343707209444642025227149)
                    ·
                      refine ⟨2753890203541740759460181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7343707209444642025227149 2753890203541740759460181)
                      ·
                        rfl

theorem cell23_5363182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_5363182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363182 prefixEnd_5363182 := by exact prefixLift 5363182
  have htrace : WordTrace (prefixWord ++ tailWord_5363182) baseStart_5363182 baseEnd_5363182 := by
    simpa [prefixWord, tailWord_5363182, baseEnd_5363182] using wordTrace_append hprefix tailTrace_5363182
  have hstable : (prefixWord ++ tailWord_5363182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363182).length < 2 ^ (prefixWord ++ tailWord_5363182).sum := by decide
  have hdescent : baseEnd_5363182 < baseStart_5363182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363189 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 6]
def baseStart_5363189 : Nat := 118140960795 + 5363189 * 2 ^ 59
def prefixEnd_5363189 : Nat := 4983230072969 + 3 ^ 40 * 5363189 * 2
def baseEnd_5363189 : Nat := 305988199767369136896961

theorem tailTrace_5363189 : CollatzResearch.WordTrace tailWord_5363189 prefixEnd_5363189 305988199767369136896961 := by
  unfold tailWord_5363189
  simp only [CollatzResearch.WordTrace]
  refine ⟨195611572967089687603028621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130407715311393125068685747 195611572967089687603028621)
  ·
    refine ⟨73354339862658632851135733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195611572967089687603028621 73354339862658632851135733)
    ·
      refine ⟨6876969362124246829793975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73354339862658632851135733 6876969362124246829793975)
      ·
        refine ⟨10315454043186370244690963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6876969362124246829793975 10315454043186370244690963)
        ·
          refine ⟨15473181064779555367036445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10315454043186370244690963 15473181064779555367036445)
          ·
            refine ⟨5802442899292333262638667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15473181064779555367036445 5802442899292333262638667)
            ·
              refine ⟨8703664348938499893958001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5802442899292333262638667 8703664348938499893958001)
              ·
                refine ⟨6527748261703874920468501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8703664348938499893958001 6527748261703874920468501)
                ·
                  refine ⟨305988199767369136896961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6527748261703874920468501 305988199767369136896961)
                  ·
                    rfl

theorem cell23_5363189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_5363189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363189 prefixEnd_5363189 := by exact prefixLift 5363189
  have htrace : WordTrace (prefixWord ++ tailWord_5363189) baseStart_5363189 baseEnd_5363189 := by
    simpa [prefixWord, tailWord_5363189, baseEnd_5363189] using wordTrace_append hprefix tailTrace_5363189
  have hstable : (prefixWord ++ tailWord_5363189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363189).length < 2 ^ (prefixWord ++ tailWord_5363189).sum := by decide
  have hdescent : baseEnd_5363189 < baseStart_5363189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363232 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 4, 4]
def baseStart_5363232 : Nat := 118140960795 + 5363232 * 2 ^ 59
def prefixEnd_5363232 : Nat := 4983230072969 + 3 ^ 40 * 5363232 * 2
def baseEnd_5363232 : Nat := 917971959191488521278317

theorem tailTrace_5363232 : CollatzResearch.WordTrace tailWord_5363232 prefixEnd_5363232 917971959191488521278317 := by
  unfold tailWord_5363232
  simp only [CollatzResearch.WordTrace]
  refine ⟨97806570652966952973421975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130408760870622603964562633 97806570652966952973421975)
  ·
    refine ⟨146709855979450429460132963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97806570652966952973421975 146709855979450429460132963)
    ·
      refine ⟨220064783969175644190199445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146709855979450429460132963 220064783969175644190199445)
      ·
        refine ⟨10315536748555108321415599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 220064783969175644190199445 10315536748555108321415599)
        ·
          refine ⟨15473305122832662482123399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10315536748555108321415599 15473305122832662482123399)
          ·
            refine ⟨23209957684248993723185099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15473305122832662482123399 23209957684248993723185099)
            ·
              refine ⟨34814936526373490584777649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23209957684248993723185099 34814936526373490584777649)
              ·
                refine ⟨26111202394780117938583237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34814936526373490584777649 26111202394780117938583237)
                ·
                  refine ⟨4895850449021272113484357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26111202394780117938583237 4895850449021272113484357)
                  ·
                    refine ⟨917971959191488521278317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4895850449021272113484357 917971959191488521278317)
                    ·
                      rfl

theorem cell23_5363232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4, 4].length) (baseStart_5363232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363232 prefixEnd_5363232 := by exact prefixLift 5363232
  have htrace : WordTrace (prefixWord ++ tailWord_5363232) baseStart_5363232 baseEnd_5363232 := by
    simpa [prefixWord, tailWord_5363232, baseEnd_5363232] using wordTrace_append hprefix tailTrace_5363232
  have hstable : (prefixWord ++ tailWord_5363232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363232).length < 2 ^ (prefixWord ++ tailWord_5363232).sum := by decide
  have hdescent : baseEnd_5363232 < baseStart_5363232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363242 : List Nat := [3, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_5363242 : Nat := 118140960795 + 5363242 * 2 ^ 59
def prefixEnd_5363242 : Nat := 4983230072969 + 3 ^ 40 * 5363242 * 2
def baseEnd_5363242 : Nat := 2753921012381010524709905

theorem tailTrace_5363242 : CollatzResearch.WordTrace tailWord_5363242 prefixEnd_5363242 2753921012381010524709905 := by
  unfold tailWord_5363242
  simp only [CollatzResearch.WordTrace]
  refine ⟨48903376508974419413676995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130409004023931785103138653 48903376508974419413676995)
  ·
    refine ⟨73355064763461629120515493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48903376508974419413676995 73355064763461629120515493)
    ·
      refine ⟨13754074643149055460096655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73355064763461629120515493 13754074643149055460096655)
      ·
        refine ⟨20631111964723583190144983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13754074643149055460096655 20631111964723583190144983)
        ·
          refine ⟨30946667947085374785217475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20631111964723583190144983 30946667947085374785217475)
          ·
            refine ⟨46420001920628062177826213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30946667947085374785217475 46420001920628062177826213)
            ·
              refine ⟨8703750360117761658342415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46420001920628062177826213 8703750360117761658342415)
              ·
                refine ⟨13055625540176642487513623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8703750360117761658342415 13055625540176642487513623)
                ·
                  refine ⟨19583438310264963731270435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13055625540176642487513623 19583438310264963731270435)
                  ·
                    refine ⟨29375157465397445596905653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19583438310264963731270435 29375157465397445596905653)
                    ·
                      refine ⟨2753921012381010524709905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29375157465397445596905653 2753921012381010524709905)
                      ·
                        rfl

theorem cell23_5363242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_5363242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363242 prefixEnd_5363242 := by exact prefixLift 5363242
  have htrace : WordTrace (prefixWord ++ tailWord_5363242) baseStart_5363242 baseEnd_5363242 := by
    simpa [prefixWord, tailWord_5363242, baseEnd_5363242] using wordTrace_append hprefix tailTrace_5363242
  have hstable : (prefixWord ++ tailWord_5363242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363242).length < 2 ^ (prefixWord ++ tailWord_5363242).sum := by decide
  have hdescent : baseEnd_5363242 < baseStart_5363242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363256 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 3, 2, 2]
def baseStart_5363256 : Nat := 118140960795 + 5363256 * 2 ^ 59
def prefixEnd_5363256 : Nat := 4983230072969 + 3 ^ 40 * 5363256 * 2
def baseEnd_5363256 : Nat := 2753928201110173469934841

theorem tailTrace_5363256 : CollatzResearch.WordTrace tailWord_5363256 prefixEnd_5363256 2753928201110173469934841 := by
  unfold tailWord_5363256
  simp only [CollatzResearch.WordTrace]
  refine ⟨97807008328923479022858811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130409344438564638697145081 97807008328923479022858811)
  ·
    refine ⟨146710512493385218534288217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97807008328923479022858811 146710512493385218534288217)
    ·
      refine ⟨110032884370038913900716163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146710512493385218534288217 110032884370038913900716163)
      ·
        refine ⟨165049326555058370851074245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110032884370038913900716163 165049326555058370851074245)
        ·
          refine ⟨30946748729073444534576421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165049326555058370851074245 30946748729073444534576421)
          ·
            refine ⟨5802515386701270850233079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30946748729073444534576421 5802515386701270850233079)
            ·
              refine ⟨8703773080051906275349619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5802515386701270850233079 8703773080051906275349619)
              ·
                refine ⟨13055659620077859413024429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8703773080051906275349619 13055659620077859413024429)
                ·
                  refine ⟨4895872357529197279884161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13055659620077859413024429 4895872357529197279884161)
                  ·
                    refine ⟨3671904268146897959913121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4895872357529197279884161 3671904268146897959913121)
                    ·
                      refine ⟨2753928201110173469934841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671904268146897959913121 2753928201110173469934841)
                      ·
                        rfl

theorem cell23_5363256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_5363256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363256 prefixEnd_5363256 := by exact prefixLift 5363256
  have htrace : WordTrace (prefixWord ++ tailWord_5363256) baseStart_5363256 baseEnd_5363256 := by
    simpa [prefixWord, tailWord_5363256, baseEnd_5363256] using wordTrace_append hprefix tailTrace_5363256
  have hstable : (prefixWord ++ tailWord_5363256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363256).length < 2 ^ (prefixWord ++ tailWord_5363256).sum := by decide
  have hdescent : baseEnd_5363256 < baseStart_5363256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363265 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_5363265 : Nat := 118140960795 + 5363265 * 2 ^ 59
def prefixEnd_5363265 : Nat := 4983230072969 + 3 ^ 40 * 5363265 * 2
def baseEnd_5363265 : Nat := 2753932822436063934722299

theorem tailTrace_5363265 : CollatzResearch.WordTrace tailWord_5363265 prefixEnd_5363265 2753932822436063934722299 := by
  unfold tailWord_5363265
  simp only [CollatzResearch.WordTrace]
  refine ⟨195614344914814352582795249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130409563276542901721863499 195614344914814352582795249)
  ·
    refine ⟨146710758686110764437096437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195614344914814352582795249 146710758686110764437096437)
    ·
      refine ⟨13754133626822884165977791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146710758686110764437096437 13754133626822884165977791)
      ·
        refine ⟨20631200440234326248966687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13754133626822884165977791 20631200440234326248966687)
        ·
          refine ⟨30946800660351489373450031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20631200440234326248966687 30946800660351489373450031)
          ·
            refine ⟨46420200990527234060175047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30946800660351489373450031 46420200990527234060175047)
            ·
              refine ⟨69630301485790851090262571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46420200990527234060175047 69630301485790851090262571)
              ·
                refine ⟨104445452228686276635393857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69630301485790851090262571 104445452228686276635393857)
                ·
                  refine ⟨78334089171514707476545393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104445452228686276635393857 78334089171514707476545393)
                  ·
                    refine ⟨58750566878636030607409045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78334089171514707476545393 58750566878636030607409045)
                    ·
                      refine ⟨2753932822436063934722299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58750566878636030607409045 2753932822436063934722299)
                      ·
                        rfl

theorem cell23_5363265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_5363265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363265 prefixEnd_5363265 := by exact prefixLift 5363265
  have htrace : WordTrace (prefixWord ++ tailWord_5363265) baseStart_5363265 baseEnd_5363265 := by
    simpa [prefixWord, tailWord_5363265, baseEnd_5363265] using wordTrace_append hprefix tailTrace_5363265
  have hstable : (prefixWord ++ tailWord_5363265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363265).length < 2 ^ (prefixWord ++ tailWord_5363265).sum := by decide
  have hdescent : baseEnd_5363265 < baseStart_5363265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363293 : List Nat := [1, 4, 4, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5363293 : Nat := 118140960795 + 5363293 * 2 ^ 59
def prefixEnd_5363293 : Nat := 4983230072969 + 3 ^ 40 * 5363293 * 2
def baseEnd_5363293 : Nat := 2753947199894389825172171

theorem tailTrace_5363293 : CollatzResearch.WordTrace tailWord_5363293 prefixEnd_5363293 2753947199894389825172171 := by
  unfold tailWord_5363293
  simp only [CollatzResearch.WordTrace]
  refine ⟨195615366158712913364814533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130410244105808608909876355 195615366158712913364814533)
  ·
    refine ⟨36677881154758671255902725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195615366158712913364814533 36677881154758671255902725)
    ·
      refine ⟨6877102716517250860481761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36677881154758671255902725 6877102716517250860481761)
      ·
        refine ⟨5157827037387938145361321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6877102716517250860481761 5157827037387938145361321)
        ·
          refine ⟨3868370278040953609020991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5157827037387938145361321 3868370278040953609020991)
          ·
            refine ⟨5802555417061430413531487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868370278040953609020991 5802555417061430413531487)
            ·
              refine ⟨8703833125592145620297231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5802555417061430413531487 8703833125592145620297231)
              ·
                refine ⟨13055749688388218430445847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8703833125592145620297231 13055749688388218430445847)
                ·
                  refine ⟨19583624532582327645668771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13055749688388218430445847 19583624532582327645668771)
                  ·
                    refine ⟨29375436798873491468503157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19583624532582327645668771 29375436798873491468503157)
                    ·
                      refine ⟨2753947199894389825172171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29375436798873491468503157 2753947199894389825172171)
                      ·
                        rfl

theorem cell23_5363293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5363293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363293 prefixEnd_5363293 := by exact prefixLift 5363293
  have htrace : WordTrace (prefixWord ++ tailWord_5363293) baseStart_5363293 baseEnd_5363293 := by
    simpa [prefixWord, tailWord_5363293, baseEnd_5363293] using wordTrace_append hprefix tailTrace_5363293
  have hstable : (prefixWord ++ tailWord_5363293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363293).length < 2 ^ (prefixWord ++ tailWord_5363293).sum := by decide
  have hdescent : baseEnd_5363293 < baseStart_5363293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363306 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_5363306 : Nat := 118140960795 + 5363306 * 2 ^ 59
def prefixEnd_5363306 : Nat := 4983230072969 + 3 ^ 40 * 5363306 * 2
def baseEnd_5363306 : Nat := 2753953875142898274309611

theorem tailTrace_5363306 : CollatzResearch.WordTrace tailWord_5363306 prefixEnd_5363306 2753953875142898274309611 := by
  unfold tailWord_5363306
  simp only [CollatzResearch.WordTrace]
  refine ⟨48903960076916454146259443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130410560205110544390025181 48903960076916454146259443)
  ·
    refine ⟨73355940115374681219389165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48903960076916454146259443 73355940115374681219389165)
    ·
      refine ⟨27508477543265505457270937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73355940115374681219389165 27508477543265505457270937)
      ·
        refine ⟨20631358157449129092953203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27508477543265505457270937 20631358157449129092953203)
        ·
          refine ⟨30947037236173693639429805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20631358157449129092953203 30947037236173693639429805)
          ·
            refine ⟨11605138963565135114786177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30947037236173693639429805 11605138963565135114786177)
            ·
              refine ⟨8703854222673851336089633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11605138963565135114786177 8703854222673851336089633)
              ·
                refine ⟨6527890667005388502067225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8703854222673851336089633 6527890667005388502067225)
                ·
                  refine ⟨4895918000254041376550419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6527890667005388502067225 4895918000254041376550419)
                  ·
                    refine ⟨7343877000381062064825629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4895918000254041376550419 7343877000381062064825629)
                    ·
                      refine ⟨2753953875142898274309611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7343877000381062064825629 2753953875142898274309611)
                      ·
                        rfl

theorem cell23_5363306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_5363306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363306 prefixEnd_5363306 := by exact prefixLift 5363306
  have htrace : WordTrace (prefixWord ++ tailWord_5363306) baseStart_5363306 baseEnd_5363306 := by
    simpa [prefixWord, tailWord_5363306, baseEnd_5363306] using wordTrace_append hprefix tailTrace_5363306
  have hstable : (prefixWord ++ tailWord_5363306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363306).length < 2 ^ (prefixWord ++ tailWord_5363306).sum := by decide
  have hdescent : baseEnd_5363306 < baseStart_5363306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363329 : List Nat := [1, 2, 4, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_5363329 : Nat := 118140960795 + 5363329 * 2 ^ 59
def prefixEnd_5363329 : Nat := 4983230072969 + 3 ^ 40 * 5363329 * 2
def baseEnd_5363329 : Nat := 2753965685197951684322005

theorem tailTrace_5363329 : CollatzResearch.WordTrace tailWord_5363329 prefixEnd_5363329 2753965685197951684322005 := by
  unfold tailWord_5363329
  simp only [CollatzResearch.WordTrace]
  refine ⟨195616679186582491513125041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130411119457721661008750027 195616679186582491513125041)
  ·
    refine ⟨146712509389936868634843781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195616679186582491513125041 146712509389936868634843781)
    ·
      refine ⟨27508595510613162869033209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146712509389936868634843781 27508595510613162869033209)
      ·
        refine ⟨20631446632959872151774907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27508595510613162869033209 20631446632959872151774907)
        ·
          refine ⟨30947169949439808227662361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20631446632959872151774907 30947169949439808227662361)
          ·
            refine ⟨23210377462079856170746771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30947169949439808227662361 23210377462079856170746771)
            ·
              refine ⟨34815566193119784256120157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23210377462079856170746771 34815566193119784256120157)
              ·
                refine ⟨13055837322419919096045059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34815566193119784256120157 13055837322419919096045059)
                ·
                  refine ⟨19583755983629878644067589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13055837322419919096045059 19583755983629878644067589)
                  ·
                    refine ⟨3671954246930602245762673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19583755983629878644067589 3671954246930602245762673)
                    ·
                      refine ⟨2753965685197951684322005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3671954246930602245762673 2753965685197951684322005)
                      ·
                        rfl

theorem cell23_5363329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_5363329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363329 prefixEnd_5363329 := by exact prefixLift 5363329
  have htrace : WordTrace (prefixWord ++ tailWord_5363329) baseStart_5363329 baseEnd_5363329 := by
    simpa [prefixWord, tailWord_5363329, baseEnd_5363329] using wordTrace_append hprefix tailTrace_5363329
  have hstable : (prefixWord ++ tailWord_5363329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363329).length < 2 ^ (prefixWord ++ tailWord_5363329).sum := by decide
  have hdescent : baseEnd_5363329 < baseStart_5363329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363335 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 9]
def baseStart_5363335 : Nat := 118140960795 + 5363335 * 2 ^ 59
def prefixEnd_5363335 : Nat := 4983230072969 + 3 ^ 40 * 5363335 * 2
def baseEnd_5363335 : Nat := 305996529564653184538553

theorem tailTrace_5363335 : CollatzResearch.WordTrace tailWord_5363335 prefixEnd_5363335 305996529564653184538553 := by
  unfold tailWord_5363335
  simp only [CollatzResearch.WordTrace]
  refine ⟨195616898024560754537843459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130411265349707169691895639 195616898024560754537843459)
  ·
    refine ⟨293425347036841131806765189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195616898024560754537843459 293425347036841131806765189)
    ·
      refine ⟨55017252569407712213768473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293425347036841131806765189 55017252569407712213768473)
      ·
        refine ⟨41262939427055784160326355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55017252569407712213768473 41262939427055784160326355)
        ·
          refine ⟨61894409140583676240489533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41262939427055784160326355 61894409140583676240489533)
          ·
            refine ⟨23210403427718878590183575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61894409140583676240489533 23210403427718878590183575)
            ·
              refine ⟨34815605141578317885275363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23210403427718878590183575 34815605141578317885275363)
              ·
                refine ⟨52223407712367476827913045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34815605141578317885275363 52223407712367476827913045)
                ·
                  refine ⟨305996529564653184538553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52223407712367476827913045 305996529564653184538553)
                  ·
                    rfl

theorem cell23_5363335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 9].length) (baseStart_5363335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363335 prefixEnd_5363335 := by exact prefixLift 5363335
  have htrace : WordTrace (prefixWord ++ tailWord_5363335) baseStart_5363335 baseEnd_5363335 := by
    simpa [prefixWord, tailWord_5363335, baseEnd_5363335] using wordTrace_append hprefix tailTrace_5363335
  have hstable : (prefixWord ++ tailWord_5363335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363335).length < 2 ^ (prefixWord ++ tailWord_5363335).sum := by decide
  have hdescent : baseEnd_5363335 < baseStart_5363335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363375 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 7]
def baseStart_5363375 : Nat := 118140960795 + 5363375 * 2 ^ 59
def prefixEnd_5363375 : Nat := 4983230072969 + 3 ^ 40 * 5363375 * 2
def baseEnd_5363375 : Nat := 2753989305308058504346793

theorem tailTrace_5363375 : CollatzResearch.WordTrace tailWord_5363375 prefixEnd_5363375 2753989305308058504346793 := by
  unfold tailWord_5363375
  simp only [CollatzResearch.WordTrace]
  refine ⟨195618356944415841369299579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130412237962943894246199719 195618356944415841369299579)
  ·
    refine ⟨293427535416623762053949369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195618356944415841369299579 293427535416623762053949369)
    ·
      refine ⟨220070651562467821540462027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293427535416623762053949369 220070651562467821540462027)
      ·
        refine ⟨330105977343701732310693041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220070651562467821540462027 330105977343701732310693041)
        ·
          refine ⟨247579483007776299233019781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330105977343701732310693041 247579483007776299233019781)
          ·
            refine ⟨46421153063958056106191209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247579483007776299233019781 46421153063958056106191209)
            ·
              refine ⟨34815864797968542079643407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46421153063958056106191209 34815864797968542079643407)
              ·
                refine ⟨52223797196952813119465111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34815864797968542079643407 52223797196952813119465111)
                ·
                  refine ⟨78335695795429219679197667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52223797196952813119465111 78335695795429219679197667)
                  ·
                    refine ⟨117503543693143829518796501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78335695795429219679197667 117503543693143829518796501)
                    ·
                      refine ⟨2753989305308058504346793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117503543693143829518796501 2753989305308058504346793)
                      ·
                        rfl

theorem cell23_5363375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_5363375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363375 prefixEnd_5363375 := by exact prefixLift 5363375
  have htrace : WordTrace (prefixWord ++ tailWord_5363375) baseStart_5363375 baseEnd_5363375 := by
    simpa [prefixWord, tailWord_5363375, baseEnd_5363375] using wordTrace_append hprefix tailTrace_5363375
  have hstable : (prefixWord ++ tailWord_5363375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363375).length < 2 ^ (prefixWord ++ tailWord_5363375).sum := by decide
  have hdescent : baseEnd_5363375 < baseStart_5363375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363513 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5363513 : Nat := 118140960795 + 5363513 * 2 ^ 59
def prefixEnd_5363513 : Nat := 4983230072969 + 3 ^ 40 * 5363513 * 2
def baseEnd_5363513 : Nat := 2754060165638378964421159

theorem tailTrace_5363513 : CollatzResearch.WordTrace tailWord_5363513 prefixEnd_5363513 2754060165638378964421159 := by
  unfold tailWord_5363513
  simp only [CollatzResearch.WordTrace]
  refine ⟨195623390217915890937823193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130415593478610593958548795 195623390217915890937823193)
  ·
    refine ⟨146717542663436918203367395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195623390217915890937823193 146717542663436918203367395)
    ·
      refine ⟨220076313995155377305051093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146717542663436918203367395 220076313995155377305051093)
      ·
        refine ⟨5158038609261454155587135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 220076313995155377305051093 5158038609261454155587135)
        ·
          refine ⟨7737057913892181233380703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5158038609261454155587135 7737057913892181233380703)
          ·
            refine ⟨11605586870838271850071055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7737057913892181233380703 11605586870838271850071055)
            ·
              refine ⟨17408380306257407775106583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11605586870838271850071055 17408380306257407775106583)
              ·
                refine ⟨26112570459386111662659875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17408380306257407775106583 26112570459386111662659875)
                ·
                  refine ⟨39168855689079167493989813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26112570459386111662659875 39168855689079167493989813)
                  ·
                    refine ⟨3672080220851171952561545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39168855689079167493989813 3672080220851171952561545)
                    ·
                      refine ⟨2754060165638378964421159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672080220851171952561545 2754060165638378964421159)
                      ·
                        rfl

theorem cell23_5363513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5363513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363513 prefixEnd_5363513 := by exact prefixLift 5363513
  have htrace : WordTrace (prefixWord ++ tailWord_5363513) baseStart_5363513 baseEnd_5363513 := by
    simpa [prefixWord, tailWord_5363513, baseEnd_5363513] using wordTrace_append hprefix tailTrace_5363513
  have hstable : (prefixWord ++ tailWord_5363513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363513).length < 2 ^ (prefixWord ++ tailWord_5363513).sum := by decide
  have hdescent : baseEnd_5363513 < baseStart_5363513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363566 : List Nat := [4, 1, 2, 3, 1, 1, 4, 7]
def baseStart_5363566 : Nat := 118140960795 + 5363566 * 2 ^ 59
def prefixEnd_5363566 : Nat := 4983230072969 + 3 ^ 40 * 5363566 * 2
def baseEnd_5363566 : Nat := 102003236300483972483645

theorem tailTrace_5363566 : CollatzResearch.WordTrace tailWord_5363566 prefixEnd_5363566 102003236300483972483645 := by
  unfold tailWord_5363566
  simp only [CollatzResearch.WordTrace]
  refine ⟨24453165410840485123687819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130416882191149253993001701 24453165410840485123687819)
  ·
    refine ⟨36679748116260727685531729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24453165410840485123687819 36679748116260727685531729)
    ·
      refine ⟨27509811087195545764148797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36679748116260727685531729 27509811087195545764148797)
      ·
        refine ⟨10316179157698329661555799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27509811087195545764148797 10316179157698329661555799)
        ·
          refine ⟨15474268736547494492333699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10316179157698329661555799 15474268736547494492333699)
          ·
            refine ⟨23211403104821241738500549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15474268736547494492333699 23211403104821241738500549)
            ·
              refine ⟨4352138082153982825968853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23211403104821241738500549 4352138082153982825968853)
              ·
                refine ⟨102003236300483972483645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4352138082153982825968853 102003236300483972483645)
                ·
                  rfl

theorem cell23_5363566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_5363566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363566 prefixEnd_5363566 := by exact prefixLift 5363566
  have htrace : WordTrace (prefixWord ++ tailWord_5363566) baseStart_5363566 baseEnd_5363566 := by
    simpa [prefixWord, tailWord_5363566, baseEnd_5363566] using wordTrace_append hprefix tailTrace_5363566
  have hstable : (prefixWord ++ tailWord_5363566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363566).length < 2 ^ (prefixWord ++ tailWord_5363566).sum := by decide
  have hdescent : baseEnd_5363566 < baseStart_5363566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363594 : List Nat := [3, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2]
def baseStart_5363594 : Nat := 118140960795 + 5363594 * 2 ^ 59
def prefixEnd_5363594 : Nat := 4983230072969 + 3 ^ 40 * 5363594 * 2
def baseEnd_5363594 : Nat := 2754101757571393147508287

theorem tailTrace_5363594 : CollatzResearch.WordTrace tailWord_5363594 prefixEnd_5363594 2754101757571393147508287 := by
  unfold tailWord_5363594
  simp only [CollatzResearch.WordTrace]
  refine ⟨48906586132655610442880459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130417563020414961181014557 48906586132655610442880459)
  ·
    refine ⟨73359879198983415664320689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48906586132655610442880459 73359879198983415664320689)
    ·
      refine ⟨55019909399237561748240517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73359879198983415664320689 55019909399237561748240517)
      ·
        refine ⟨10316233012357042827795097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55019909399237561748240517 10316233012357042827795097)
        ·
          refine ⟨7737174759267782120846323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10316233012357042827795097 7737174759267782120846323)
          ·
            refine ⟨11605762138901673181269485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7737174759267782120846323 11605762138901673181269485)
            ·
              refine ⟨4352160802088127442976057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11605762138901673181269485 4352160802088127442976057)
              ·
                refine ⟨3264120601566095582232043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4352160802088127442976057 3264120601566095582232043)
                ·
                  refine ⟨4896180902349143373348065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264120601566095582232043 4896180902349143373348065)
                  ·
                    refine ⟨3672135676761857530011049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4896180902349143373348065 3672135676761857530011049)
                    ·
                      refine ⟨2754101757571393147508287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672135676761857530011049 2754101757571393147508287)
                      ·
                        rfl

theorem cell23_5363594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_5363594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363594 prefixEnd_5363594 := by exact prefixLift 5363594
  have htrace : WordTrace (prefixWord ++ tailWord_5363594) baseStart_5363594 baseEnd_5363594 := by
    simpa [prefixWord, tailWord_5363594, baseEnd_5363594] using wordTrace_append hprefix tailTrace_5363594
  have hstable : (prefixWord ++ tailWord_5363594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363594).length < 2 ^ (prefixWord ++ tailWord_5363594).sum := by decide
  have hdescent : baseEnd_5363594 < baseStart_5363594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363610 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3]
def baseStart_5363610 : Nat := 118140960795 + 5363610 * 2 ^ 59
def prefixEnd_5363610 : Nat := 4983230072969 + 3 ^ 40 * 5363610 * 2
def baseEnd_5363610 : Nat := 2754109973261865084908213

theorem tailTrace_5363610 : CollatzResearch.WordTrace tailWord_5363610 prefixEnd_5363610 2754109973261865084908213 := by
  unfold tailWord_5363610
  simp only [CollatzResearch.WordTrace]
  refine ⟨48906732024641119126026071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130417952065709651002736189 48906732024641119126026071)
  ·
    refine ⟨73360098036961678689039107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48906732024641119126026071 73360098036961678689039107)
    ·
      refine ⟨110040147055442518033558661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73360098036961678689039107 110040147055442518033558661)
      ·
        refine ⟨20632527572895472131292249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110040147055442518033558661 20632527572895472131292249)
        ·
          refine ⟨15474395679671604098469187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20632527572895472131292249 15474395679671604098469187)
          ·
            refine ⟨23211593519507406147703781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15474395679671604098469187 23211593519507406147703781)
            ·
              refine ⟨4352173784907638652694459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23211593519507406147703781 4352173784907638652694459)
              ·
                refine ⟨6528260677361457979041689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4352173784907638652694459 6528260677361457979041689)
                ·
                  refine ⟨4896195508021093484281267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6528260677361457979041689 4896195508021093484281267)
                  ·
                    refine ⟨7344293262031640226421901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4896195508021093484281267 7344293262031640226421901)
                    ·
                      refine ⟨2754109973261865084908213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7344293262031640226421901 2754109973261865084908213)
                      ·
                        rfl

theorem cell23_5363610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_5363610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363610 prefixEnd_5363610 := by exact prefixLift 5363610
  have htrace : WordTrace (prefixWord ++ tailWord_5363610) baseStart_5363610 baseEnd_5363610 := by
    simpa [prefixWord, tailWord_5363610, baseEnd_5363610] using wordTrace_append hprefix tailTrace_5363610
  have hstable : (prefixWord ++ tailWord_5363610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363610).length < 2 ^ (prefixWord ++ tailWord_5363610).sum := by decide
  have hdescent : baseEnd_5363610 < baseStart_5363610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363614 : List Nat := [4, 3, 1, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_5363614 : Nat := 118140960795 + 5363614 * 2 ^ 59
def prefixEnd_5363614 : Nat := 4983230072969 + 3 ^ 40 * 5363614 * 2
def baseEnd_5363614 : Nat := 2754112027184483069258195

theorem tailTrace_5363614 : CollatzResearch.WordTrace tailWord_5363614 prefixEnd_5363614 2754112027184483069258195 := by
  unfold tailWord_5363614
  simp only [CollatzResearch.WordTrace]
  refine ⟨24453384248818748148406237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130418049327033323458166597 24453384248818748148406237)
  ·
    refine ⟨9170019093307030555652339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24453384248818748148406237 9170019093307030555652339)
    ·
      refine ⟨13755028639960545833478509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9170019093307030555652339 13755028639960545833478509)
      ·
        refine ⟨5158135739985204687554441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13755028639960545833478509 5158135739985204687554441)
        ·
          refine ⟨3868601804988903515665831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5158135739985204687554441 3868601804988903515665831)
          ·
            refine ⟨5802902707483355273498747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868601804988903515665831 5802902707483355273498747)
            ·
              refine ⟨8704354061225032910248121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5802902707483355273498747 8704354061225032910248121)
              ·
                refine ⟨6528265545918774682686091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8704354061225032910248121 6528265545918774682686091)
                ·
                  refine ⟨9792398318878162024029137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6528265545918774682686091 9792398318878162024029137)
                  ·
                    refine ⟨7344298739158621518021853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9792398318878162024029137 7344298739158621518021853)
                    ·
                      refine ⟨2754112027184483069258195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7344298739158621518021853 2754112027184483069258195)
                      ·
                        rfl

theorem cell23_5363614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_5363614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363614 prefixEnd_5363614 := by exact prefixLift 5363614
  have htrace : WordTrace (prefixWord ++ tailWord_5363614) baseStart_5363614 baseEnd_5363614 := by
    simpa [prefixWord, tailWord_5363614, baseEnd_5363614] using wordTrace_append hprefix tailTrace_5363614
  have hstable : (prefixWord ++ tailWord_5363614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363614).length < 2 ^ (prefixWord ++ tailWord_5363614).sum := by decide
  have hdescent : baseEnd_5363614 < baseStart_5363614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363616 : List Nat := [2, 1, 1, 4, 1, 1, 1, 5, 1, 4, 2]
def baseStart_5363616 : Nat := 118140960795 + 5363616 * 2 ^ 59
def prefixEnd_5363616 : Nat := 4983230072969 + 3 ^ 40 * 5363616 * 2
def baseEnd_5363616 : Nat := 2754113054145792061433185

theorem tailTrace_5363616 : CollatzResearch.WordTrace tailWord_5363616 prefixEnd_5363616 2754113054145792061433185 := by
  unfold tailWord_5363616
  simp only [CollatzResearch.WordTrace]
  refine ⟨97813573468271369764411351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130418097957695159685881801 97813573468271369764411351)
  ·
    refine ⟨146720360202407054646617027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97813573468271369764411351 146720360202407054646617027)
    ·
      refine ⟨220080540303610581969925541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146720360202407054646617027 220080540303610581969925541)
      ·
        refine ⟨41265101306926984119361039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220080540303610581969925541 41265101306926984119361039)
        ·
          refine ⟨61897651960390476179041559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41265101306926984119361039 61897651960390476179041559)
          ·
            refine ⟨92846477940585714268562339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61897651960390476179041559 92846477940585714268562339)
            ·
              refine ⟨139269716910878571402843509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92846477940585714268562339 139269716910878571402843509)
              ·
                refine ⟨13056535960394866069016579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139269716910878571402843509 13056535960394866069016579)
                ·
                  refine ⟨19584803940592299103524869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13056535960394866069016579 19584803940592299103524869)
                  ·
                    refine ⟨3672150738861056081910913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19584803940592299103524869 3672150738861056081910913)
                    ·
                      refine ⟨2754113054145792061433185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672150738861056081910913 2754113054145792061433185)
                      ·
                        rfl

theorem cell23_5363616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_5363616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363616 prefixEnd_5363616 := by exact prefixLift 5363616
  have htrace : WordTrace (prefixWord ++ tailWord_5363616) baseStart_5363616 baseEnd_5363616 := by
    simpa [prefixWord, tailWord_5363616, baseEnd_5363616] using wordTrace_append hprefix tailTrace_5363616
  have hstable : (prefixWord ++ tailWord_5363616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363616).length < 2 ^ (prefixWord ++ tailWord_5363616).sum := by decide
  have hdescent : baseEnd_5363616 < baseStart_5363616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363620 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 1, 3, 2]
def baseStart_5363620 : Nat := 118140960795 + 5363620 * 2 ^ 59
def prefixEnd_5363620 : Nat := 4983230072969 + 3 ^ 40 * 5363620 * 2
def baseEnd_5363620 : Nat := 2754115108068410045783167

theorem tailTrace_5363620 : CollatzResearch.WordTrace tailWord_5363620 prefixEnd_5363620 2754115108068410045783167 := by
  unfold tailWord_5363620
  simp only [CollatzResearch.WordTrace]
  refine ⟨97813646414264124105984157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130418195219018832141312209 97813646414264124105984157)
  ·
    refine ⟨36680117405349046539744059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97813646414264124105984157 36680117405349046539744059)
    ·
      refine ⟨55020176108023569809616089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36680117405349046539744059 55020176108023569809616089)
      ·
        refine ⟨41265132081017677357212067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55020176108023569809616089 41265132081017677357212067)
        ·
          refine ⟨61897698121526516035818101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41265132081017677357212067 61897698121526516035818101)
          ·
            refine ⟨5802909198893110878357947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61897698121526516035818101 5802909198893110878357947)
            ·
              refine ⟨8704363798339666317536921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5802909198893110878357947 8704363798339666317536921)
              ·
                refine ⟨6528272848754749738152691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8704363798339666317536921 6528272848754749738152691)
                ·
                  refine ⟨9792409273132124607229037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6528272848754749738152691 9792409273132124607229037)
                  ·
                    refine ⟨3672153477424546727710889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9792409273132124607229037 3672153477424546727710889)
                    ·
                      refine ⟨2754115108068410045783167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672153477424546727710889 2754115108068410045783167)
                      ·
                        rfl

theorem cell23_5363620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_5363620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363620 prefixEnd_5363620 := by exact prefixLift 5363620
  have htrace : WordTrace (prefixWord ++ tailWord_5363620) baseStart_5363620 baseEnd_5363620 := by
    simpa [prefixWord, tailWord_5363620, baseEnd_5363620] using wordTrace_append hprefix tailTrace_5363620
  have hstable : (prefixWord ++ tailWord_5363620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363620).length < 2 ^ (prefixWord ++ tailWord_5363620).sum := by decide
  have hdescent : baseEnd_5363620 < baseStart_5363620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363633 : List Nat := [1, 2, 2, 4, 2, 2, 1, 2, 1, 4, 2]
def baseStart_5363633 : Nat := 118140960795 + 5363633 * 2 ^ 59
def prefixEnd_5363633 : Nat := 4983230072969 + 3 ^ 40 * 5363633 * 2
def baseEnd_5363633 : Nat := 2754121783316918494920607

theorem tailTrace_5363633 : CollatzResearch.WordTrace tailWord_5363633 prefixEnd_5363633 2754121783316918494920607 := by
  unfold tailWord_5363633
  simp only [CollatzResearch.WordTrace]
  refine ⟨195627766977481151432191553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130418511318320767621461035 195627766977481151432191553)
  ·
    refine ⟨146720825233110863574143665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195627766977481151432191553 146720825233110863574143665)
    ·
      refine ⟨110040618924833147680607749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146720825233110863574143665 110040618924833147680607749)
      ·
        refine ⟨20632616048406215190113953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110040618924833147680607749 20632616048406215190113953)
        ·
          refine ⟨15474462036304661392585465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20632616048406215190113953 15474462036304661392585465)
          ·
            refine ⟨11605846527228496044439099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15474462036304661392585465 11605846527228496044439099)
            ·
              refine ⟨17408769790842744066658649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11605846527228496044439099 17408769790842744066658649)
              ·
                refine ⟨13056577343132058049993987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17408769790842744066658649 13056577343132058049993987)
                ·
                  refine ⟨19584866014698087074990981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13056577343132058049993987 19584866014698087074990981)
                  ·
                    refine ⟨3672162377755891326560809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19584866014698087074990981 3672162377755891326560809)
                    ·
                      refine ⟨2754121783316918494920607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672162377755891326560809 2754121783316918494920607)
                      ·
                        rfl

theorem cell23_5363633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_5363633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363633 prefixEnd_5363633 := by exact prefixLift 5363633
  have htrace : WordTrace (prefixWord ++ tailWord_5363633) baseStart_5363633 baseEnd_5363633 := by
    simpa [prefixWord, tailWord_5363633, baseEnd_5363633] using wordTrace_append hprefix tailTrace_5363633
  have hstable : (prefixWord ++ tailWord_5363633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363633).length < 2 ^ (prefixWord ++ tailWord_5363633).sum := by decide
  have hdescent : baseEnd_5363633 < baseStart_5363633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363709 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_5363709 : Nat := 118140960795 + 5363709 * 2 ^ 59
def prefixEnd_5363709 : Nat := 4983230072969 + 3 ^ 40 * 5363709 * 2
def baseEnd_5363709 : Nat := 2754160807846660197570257

theorem tailTrace_5363709 : CollatzResearch.WordTrace tailWord_5363709 prefixEnd_5363709 2754160807846660197570257 := by
  unfold tailWord_5363709
  simp only [CollatzResearch.WordTrace]
  refine ⟨195630538925205816411958181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130420359283470544274638787 195630538925205816411958181)
  ·
    refine ⟨36680726048476090577242159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195630538925205816411958181 36680726048476090577242159)
    ·
      refine ⟨55021089072714135865863239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36680726048476090577242159 55021089072714135865863239)
      ·
        refine ⟨82531633609071203798794859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55021089072714135865863239 82531633609071203798794859)
        ·
          refine ⟨123797450413606805698192289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82531633609071203798794859 123797450413606805698192289)
          ·
            refine ⟨92848087810205104273644217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123797450413606805698192289 92848087810205104273644217)
            ·
              refine ⟨69636065857653828205233163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92848087810205104273644217 69636065857653828205233163)
              ·
                refine ⟨104454098786480742307849745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69636065857653828205233163 104454098786480742307849745)
                ·
                  refine ⟨78340574089860556730887309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104454098786480742307849745 78340574089860556730887309)
                  ·
                    refine ⟨29377715283697708774082741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78340574089860556730887309 29377715283697708774082741)
                    ·
                      refine ⟨2754160807846660197570257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29377715283697708774082741 2754160807846660197570257)
                      ·
                        rfl

theorem cell23_5363709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_5363709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363709 prefixEnd_5363709 := by exact prefixLift 5363709
  have htrace : WordTrace (prefixWord ++ tailWord_5363709) baseStart_5363709 baseEnd_5363709 := by
    simpa [prefixWord, tailWord_5363709, baseEnd_5363709] using wordTrace_append hprefix tailTrace_5363709
  have hstable : (prefixWord ++ tailWord_5363709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363709).length < 2 ^ (prefixWord ++ tailWord_5363709).sum := by decide
  have hdescent : baseEnd_5363709 < baseStart_5363709 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363718 : List Nat := [6, 2, 1, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_5363718 : Nat := 118140960795 + 5363718 * 2 ^ 59
def prefixEnd_5363718 : Nat := 4983230072969 + 3 ^ 40 * 5363718 * 2
def baseEnd_5363718 : Nat := 2754165429172550662357717

theorem tailTrace_5363718 : CollatzResearch.WordTrace tailWord_5363718 prefixEnd_5363718 2754165429172550662357717 := by
  unfold tailWord_5363718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113464599442912842157369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130420578121448807299357205 6113464599442912842157369)
  ·
    refine ⟨4585098449582184631618027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6113464599442912842157369 4585098449582184631618027)
    ·
      refine ⟨6877647674373276947427041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4585098449582184631618027 6877647674373276947427041)
      ·
        refine ⟨5158235755779957710570281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6877647674373276947427041 5158235755779957710570281)
        ·
          refine ⟨3868676816834968282927711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5158235755779957710570281 3868676816834968282927711)
          ·
            refine ⟨5803015225252452424391567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868676816834968282927711 5803015225252452424391567)
            ·
              refine ⟨8704522837878678636587351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5803015225252452424391567 8704522837878678636587351)
              ·
                refine ⟨13056784256818017954881027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8704522837878678636587351 13056784256818017954881027)
                ·
                  refine ⟨19585176385227026932321541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13056784256818017954881027 19585176385227026932321541)
                  ·
                    refine ⟨3672220572230067549810289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19585176385227026932321541 3672220572230067549810289)
                    ·
                      refine ⟨2754165429172550662357717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672220572230067549810289 2754165429172550662357717)
                      ·
                        rfl

theorem cell23_5363718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_5363718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363718 prefixEnd_5363718 := by exact prefixLift 5363718
  have htrace : WordTrace (prefixWord ++ tailWord_5363718) baseStart_5363718 baseEnd_5363718 := by
    simpa [prefixWord, tailWord_5363718, baseEnd_5363718] using wordTrace_append hprefix tailTrace_5363718
  have hstable : (prefixWord ++ tailWord_5363718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363718).length < 2 ^ (prefixWord ++ tailWord_5363718).sum := by decide
  have hdescent : baseEnd_5363718 < baseStart_5363718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363726 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_5363726 : Nat := 118140960795 + 5363726 * 2 ^ 59
def prefixEnd_5363726 : Nat := 4983230072969 + 3 ^ 40 * 5363726 * 2
def baseEnd_5363726 : Nat := 2754169537017786631057679

theorem tailTrace_5363726 : CollatzResearch.WordTrace tailWord_5363726 prefixEnd_5363726 2754169537017786631057679 := by
  unfold tailWord_5363726
  simp only [CollatzResearch.WordTrace]
  refine ⟨24453894870768028539415879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130420772644096152210218021 24453894870768028539415879)
  ·
    refine ⟨36680842306152042809123819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24453894870768028539415879 36680842306152042809123819)
    ·
      refine ⟨55021263459228064213685729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36680842306152042809123819 55021263459228064213685729)
      ·
        refine ⟨41265947594421048160264297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55021263459228064213685729 41265947594421048160264297)
        ·
          refine ⟨30949460695815786120198223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41265947594421048160264297 30949460695815786120198223)
          ·
            refine ⟨46424191043723679180297335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30949460695815786120198223 46424191043723679180297335)
            ·
              refine ⟨69636286565585518770446003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46424191043723679180297335 69636286565585518770446003)
              ·
                refine ⟨104454429848378278155669005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69636286565585518770446003 104454429848378278155669005)
                ·
                  refine ⟨39170411193141854308375877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104454429848378278155669005 39170411193141854308375877)
                  ·
                    refine ⟨7344452098714097682820477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39170411193141854308375877 7344452098714097682820477)
                    ·
                      refine ⟨2754169537017786631057679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7344452098714097682820477 2754169537017786631057679)
                      ·
                        rfl

theorem cell23_5363726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_5363726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363726 prefixEnd_5363726 := by exact prefixLift 5363726
  have htrace : WordTrace (prefixWord ++ tailWord_5363726) baseStart_5363726 baseEnd_5363726 := by
    simpa [prefixWord, tailWord_5363726, baseEnd_5363726] using wordTrace_append hprefix tailTrace_5363726
  have hstable : (prefixWord ++ tailWord_5363726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363726).length < 2 ^ (prefixWord ++ tailWord_5363726).sum := by decide
  have hdescent : baseEnd_5363726 < baseStart_5363726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363783 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 4, 3, 2]
def baseStart_5363783 : Nat := 118140960795 + 5363783 * 2 ^ 59
def prefixEnd_5363783 : Nat := 4983230072969 + 3 ^ 40 * 5363783 * 2
def baseEnd_5363783 : Nat := 2754198805415092908044917

theorem tailTrace_5363783 : CollatzResearch.WordTrace tailWord_5363783 prefixEnd_5363783 2754198805415092908044917 := by
  unfold tailWord_5363783
  simp only [CollatzResearch.WordTrace]
  refine ⟨195633237926937727050152003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130422158617958484700101335 195633237926937727050152003)
  ·
    refine ⟨293449856890406590575228005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195633237926937727050152003 293449856890406590575228005)
    ·
      refine ⟨55021848166951235732855251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293449856890406590575228005 55021848166951235732855251)
      ·
        refine ⟨82532772250426853599282877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55021848166951235732855251 82532772250426853599282877)
        ·
          refine ⟨30949789593910070099731079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82532772250426853599282877 30949789593910070099731079)
          ·
            refine ⟨46424684390865105149596619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30949789593910070099731079 46424684390865105149596619)
            ·
              refine ⟨69637026586297657724394929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46424684390865105149596619 69637026586297657724394929)
              ·
                refine ⟨52227769939723243293296197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69637026586297657724394929 52227769939723243293296197)
                ·
                  refine ⟨9792706863698108117493037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52227769939723243293296197 9792706863698108117493037)
                  ·
                    refine ⟨3672265073886790544059889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9792706863698108117493037 3672265073886790544059889)
                    ·
                      refine ⟨2754198805415092908044917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672265073886790544059889 2754198805415092908044917)
                      ·
                        rfl

theorem cell23_5363783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 3, 2].length) (baseStart_5363783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363783 prefixEnd_5363783 := by exact prefixLift 5363783
  have htrace : WordTrace (prefixWord ++ tailWord_5363783) baseStart_5363783 baseEnd_5363783 := by
    simpa [prefixWord, tailWord_5363783, baseEnd_5363783] using wordTrace_append hprefix tailTrace_5363783
  have hstable : (prefixWord ++ tailWord_5363783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363783).length < 2 ^ (prefixWord ++ tailWord_5363783).sum := by decide
  have hdescent : baseEnd_5363783 < baseStart_5363783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363800 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 2, 3, 2]
def baseStart_5363800 : Nat := 118140960795 + 5363800 * 2 ^ 59
def prefixEnd_5363800 : Nat := 4983230072969 + 3 ^ 40 * 5363800 * 2
def baseEnd_5363800 : Nat := 2754207534586219341532339

theorem tailTrace_5363800 : CollatzResearch.WordTrace tailWord_5363800 prefixEnd_5363800 2754207534586219341532339 := by
  unfold tailWord_5363800
  simp only [CollatzResearch.WordTrace]
  refine ⟨97816928983938069476760427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130422571978584092635680569 97816928983938069476760427)
  ·
    refine ⟨146725393475907104215140641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97816928983938069476760427 146725393475907104215140641)
    ·
      refine ⟨110044045106930328161355481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146725393475907104215140641 110044045106930328161355481)
      ·
        refine ⟨82533033830197746121016611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110044045106930328161355481 82533033830197746121016611)
        ·
          refine ⟨123799550745296619181524917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82533033830197746121016611 123799550745296619181524917)
          ·
            refine ⟨11606207882371558048267961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123799550745296619181524917 11606207882371558048267961)
            ·
              refine ⟨8704655911778668536200971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11606207882371558048267961 8704655911778668536200971)
              ·
                refine ⟨13056983867668002804301457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8704655911778668536200971 13056983867668002804301457)
                ·
                  refine ⟨9792737900751002103226093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13056983867668002804301457 9792737900751002103226093)
                  ·
                    refine ⟨3672276712781625788709785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9792737900751002103226093 3672276712781625788709785)
                    ·
                      refine ⟨2754207534586219341532339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672276712781625788709785 2754207534586219341532339)
                      ·
                        rfl

theorem cell23_5363800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_5363800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363800 prefixEnd_5363800 := by exact prefixLift 5363800
  have htrace : WordTrace (prefixWord ++ tailWord_5363800) baseStart_5363800 baseEnd_5363800 := by
    simpa [prefixWord, tailWord_5363800, baseEnd_5363800] using wordTrace_append hprefix tailTrace_5363800
  have hstable : (prefixWord ++ tailWord_5363800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363800).length < 2 ^ (prefixWord ++ tailWord_5363800).sum := by decide
  have hdescent : baseEnd_5363800 < baseStart_5363800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363823 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 2, 4]
def baseStart_5363823 : Nat := 118140960795 + 5363823 * 2 ^ 59
def prefixEnd_5363823 : Nat := 4983230072969 + 3 ^ 40 * 5363823 * 2
def baseEnd_5363823 : Nat := 918073114880424250514911

theorem tailTrace_5363823 : CollatzResearch.WordTrace tailWord_5363823 prefixEnd_5363823 918073114880424250514911 := by
  unfold tailWord_5363823
  simp only [CollatzResearch.WordTrace]
  refine ⟨195634696846792813881608123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130423131231195209254405415 195634696846792813881608123)
  ·
    refine ⟨293452045270189220822412185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195634696846792813881608123 293452045270189220822412185)
    ·
      refine ⟨220089033952641915616809139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293452045270189220822412185 220089033952641915616809139)
      ·
        refine ⟨330133550928962873425213709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220089033952641915616809139 330133550928962873425213709)
        ·
          refine ⟨123800081598361077534455141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 330133550928962873425213709 123800081598361077534455141)
          ·
            refine ⟨23212515299692702037710339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123800081598361077534455141 23212515299692702037710339)
            ·
              refine ⟨34818772949539053056565509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23212515299692702037710339 34818772949539053056565509)
              ·
                refine ⟨6528519928038572448106033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34818772949539053056565509 6528519928038572448106033)
                ·
                  refine ⟨4896389946028929336079525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6528519928038572448106033 4896389946028929336079525)
                  ·
                    refine ⟨918073114880424250514911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4896389946028929336079525 918073114880424250514911)
                    ·
                      rfl

theorem cell23_5363823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 4].length) (baseStart_5363823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363823 prefixEnd_5363823 := by exact prefixLift 5363823
  have htrace : WordTrace (prefixWord ++ tailWord_5363823) baseStart_5363823 baseEnd_5363823 := by
    simpa [prefixWord, tailWord_5363823, baseEnd_5363823] using wordTrace_append hprefix tailTrace_5363823
  have hstable : (prefixWord ++ tailWord_5363823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363823).length < 2 ^ (prefixWord ++ tailWord_5363823).sum := by decide
  have hdescent : baseEnd_5363823 < baseStart_5363823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363824 : List Nat := [2, 1, 1, 1, 5, 4, 2, 2, 1, 1, 3]
def baseStart_5363824 : Nat := 118140960795 + 5363824 * 2 ^ 59
def prefixEnd_5363824 : Nat := 4983230072969 + 3 ^ 40 * 5363824 * 2
def baseEnd_5363824 : Nat := 2754219858121927247632229

theorem tailTrace_5363824 : CollatzResearch.WordTrace tailWord_5363824 prefixEnd_5363824 2754219858121927247632229 := by
  unfold tailWord_5363824
  simp only [CollatzResearch.WordTrace]
  refine ⟨97817366659894595526197263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130423155546526127368263017 97817366659894595526197263)
  ·
    refine ⟨146726049989841893289295895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97817366659894595526197263 146726049989841893289295895)
    ·
      refine ⟨220089074984762839933943843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146726049989841893289295895 220089074984762839933943843)
      ·
        refine ⟨330133612477144259900915765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220089074984762839933943843 330133612477144259900915765)
        ·
          refine ⟨30950026169732274365710853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 330133612477144259900915765 30950026169732274365710853)
          ·
            refine ⟨5803129906824801443570785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30950026169732274365710853 5803129906824801443570785)
            ·
              refine ⟨4352347430118601082678089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5803129906824801443570785 4352347430118601082678089)
              ·
                refine ⟨3264260572588950812008567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4352347430118601082678089 3264260572588950812008567)
                ·
                  refine ⟨4896390858883426218012851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264260572588950812008567 4896390858883426218012851)
                  ·
                    refine ⟨7344586288325139327019277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4896390858883426218012851 7344586288325139327019277)
                    ·
                      refine ⟨2754219858121927247632229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7344586288325139327019277 2754219858121927247632229)
                      ·
                        rfl

theorem cell23_5363824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 1, 1, 3].length) (baseStart_5363824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363824 prefixEnd_5363824 := by exact prefixLift 5363824
  have htrace : WordTrace (prefixWord ++ tailWord_5363824) baseStart_5363824 baseEnd_5363824 := by
    simpa [prefixWord, tailWord_5363824, baseEnd_5363824] using wordTrace_append hprefix tailTrace_5363824
  have hstable : (prefixWord ++ tailWord_5363824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363824).length < 2 ^ (prefixWord ++ tailWord_5363824).sum := by decide
  have hdescent : baseEnd_5363824 < baseStart_5363824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363833 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 3, 2, 3]
def baseStart_5363833 : Nat := 118140960795 + 5363833 * 2 ^ 59
def prefixEnd_5363833 : Nat := 4983230072969 + 3 ^ 40 * 5363833 * 2
def baseEnd_5363833 : Nat := 2754224479447817712419687

theorem tailTrace_5363833 : CollatzResearch.WordTrace tailWord_5363833 prefixEnd_5363833 2754224479447817712419687 := by
  unfold tailWord_5363833
  simp only [CollatzResearch.WordTrace]
  refine ⟨195635061576756585589472153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130423374384504390392981435 195635061576756585589472153)
  ·
    refine ⟨146726296182567439192104115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195635061576756585589472153 146726296182567439192104115)
    ·
      refine ⟨220089444273851158788156173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146726296182567439192104115 220089444273851158788156173)
      ·
        refine ⟨82533541602694184545558565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220089444273851158788156173 82533541602694184545558565)
        ·
          refine ⟨15475039050505159602292231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82533541602694184545558565 15475039050505159602292231)
          ·
            refine ⟨23212558575757739403438347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15475039050505159602292231 23212558575757739403438347)
            ·
              refine ⟨34818837863636609105157521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23212558575757739403438347 34818837863636609105157521)
              ·
                refine ⟨26114128397727456828868141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34818837863636609105157521 26114128397727456828868141)
                ·
                  refine ⟨9792798149147796310825553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26114128397727456828868141 9792798149147796310825553)
                  ·
                    refine ⟨7344598611860847233119165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9792798149147796310825553 7344598611860847233119165)
                    ·
                      refine ⟨2754224479447817712419687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7344598611860847233119165 2754224479447817712419687)
                      ·
                        rfl

theorem cell23_5363833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_5363833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363833 prefixEnd_5363833 := by exact prefixLift 5363833
  have htrace : WordTrace (prefixWord ++ tailWord_5363833) baseStart_5363833 baseEnd_5363833 := by
    simpa [prefixWord, tailWord_5363833, baseEnd_5363833] using wordTrace_append hprefix tailTrace_5363833
  have hstable : (prefixWord ++ tailWord_5363833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363833).length < 2 ^ (prefixWord ++ tailWord_5363833).sum := by decide
  have hdescent : baseEnd_5363833 < baseStart_5363833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363836 : List Nat := [2, 2, 2, 1, 1, 4, 3, 8]
def baseStart_5363836 : Nat := 118140960795 + 5363836 * 2 ^ 59
def prefixEnd_5363836 : Nat := 4983230072969 + 3 ^ 40 * 5363836 * 2
def baseEnd_5363836 : Nat := 102008371107028933358599

theorem tailTrace_5363836 : CollatzResearch.WordTrace tailWord_5363836 prefixEnd_5363836 102008371107028933358599 := by
  unfold tailWord_5363836
  simp only [CollatzResearch.WordTrace]
  refine ⟨97817585497872858550915681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130423447330497144734554241 97817585497872858550915681)
  ·
    refine ⟨73363189123404643913186761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97817585497872858550915681 73363189123404643913186761)
    ·
      refine ⟨55022391842553482934890071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73363189123404643913186761 55022391842553482934890071)
      ·
        refine ⟨82533587763830224402335107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55022391842553482934890071 82533587763830224402335107)
        ·
          refine ⟨123800381645745336603502661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82533587763830224402335107 123800381645745336603502661)
          ·
            refine ⟨23212571558577250613156749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123800381645745336603502661 23212571558577250613156749)
            ·
              refine ⟨8704714334466468979933781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23212571558577250613156749 8704714334466468979933781)
              ·
                refine ⟨102008371107028933358599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8704714334466468979933781 102008371107028933358599)
                ·
                  rfl

theorem cell23_5363836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 8].length) (baseStart_5363836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363836 prefixEnd_5363836 := by exact prefixLift 5363836
  have htrace : WordTrace (prefixWord ++ tailWord_5363836) baseStart_5363836 baseEnd_5363836 := by
    simpa [prefixWord, tailWord_5363836, baseEnd_5363836] using wordTrace_append hprefix tailTrace_5363836
  have hstable : (prefixWord ++ tailWord_5363836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363836).length < 2 ^ (prefixWord ++ tailWord_5363836).sum := by decide
  have hdescent : baseEnd_5363836 < baseStart_5363836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363843 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 4]
def baseStart_5363843 : Nat := 118140960795 + 5363843 * 2 ^ 59
def prefixEnd_5363843 : Nat := 4983230072969 + 3 ^ 40 * 5363843 * 2
def baseEnd_5363843 : Nat := 2754229614254362673294641

theorem tailTrace_5363843 : CollatzResearch.WordTrace tailWord_5363843 prefixEnd_5363843 2754229614254362673294641 := by
  unfold tailWord_5363843
  simp only [CollatzResearch.WordTrace]
  refine ⟨195635426306720357297336183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130423617537813571531557455 195635426306720357297336183)
  ·
    refine ⟨293453139460080535946004275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195635426306720357297336183 293453139460080535946004275)
    ·
      refine ⟨440179709190120803919006413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293453139460080535946004275 440179709190120803919006413)
      ·
        refine ⟨165067390946295301469627405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 440179709190120803919006413 165067390946295301469627405)
        ·
          refine ⟨61900271604860738051110277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165067390946295301469627405 61900271604860738051110277)
          ·
            refine ⟨11606300925911388384583177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61900271604860738051110277 11606300925911388384583177)
            ·
              refine ⟨8704725694433541288437383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11606300925911388384583177 8704725694433541288437383)
              ·
                refine ⟨13057088541650311932656075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8704725694433541288437383 13057088541650311932656075)
                ·
                  refine ⟨19585632812475467898984113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13057088541650311932656075 19585632812475467898984113)
                  ·
                    refine ⟨14689224609356600924238085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19585632812475467898984113 14689224609356600924238085)
                    ·
                      refine ⟨2754229614254362673294641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14689224609356600924238085 2754229614254362673294641)
                      ·
                        rfl

theorem cell23_5363843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_5363843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363843 prefixEnd_5363843 := by exact prefixLift 5363843
  have htrace : WordTrace (prefixWord ++ tailWord_5363843) baseStart_5363843 baseEnd_5363843 := by
    simpa [prefixWord, tailWord_5363843, baseEnd_5363843] using wordTrace_append hprefix tailTrace_5363843
  have hstable : (prefixWord ++ tailWord_5363843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363843).length < 2 ^ (prefixWord ++ tailWord_5363843).sum := by decide
  have hdescent : baseEnd_5363843 < baseStart_5363843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363864 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 1, 1, 4]
def baseStart_5363864 : Nat := 118140960795 + 5363864 * 2 ^ 59
def prefixEnd_5363864 : Nat := 4983230072969 + 3 ^ 40 * 5363864 * 2
def baseEnd_5363864 : Nat := 2754240397348107091132045

theorem tailTrace_5363864 : CollatzResearch.WordTrace tailWord_5363864 prefixEnd_5363864 2754240397348107091132045 := by
  unfold tailWord_5363864
  simp only [CollatzResearch.WordTrace]
  refine ⟨97818096119822138941925323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130424128159762851922567097 97818096119822138941925323)
  ·
    refine ⟨146727144179733208412887985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97818096119822138941925323 146727144179733208412887985)
    ·
      refine ⟨110045358134799906309665989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146727144179733208412887985 110045358134799906309665989)
      ·
        refine ⟨20633504650274982433062373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110045358134799906309665989 20633504650274982433062373)
        ·
          refine ⟨3868782121926559206199195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20633504650274982433062373 3868782121926559206199195)
          ·
            refine ⟨5803173182889838809298793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3868782121926559206199195 5803173182889838809298793)
            ·
              refine ⟨4352379887167379106974095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5803173182889838809298793 4352379887167379106974095)
              ·
                refine ⟨6528569830751068660461143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4352379887167379106974095 6528569830751068660461143)
                ·
                  refine ⟨9792854746126602990691715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6528569830751068660461143 9792854746126602990691715)
                  ·
                    refine ⟨14689282119189904486037573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9792854746126602990691715 14689282119189904486037573)
                    ·
                      refine ⟨2754240397348107091132045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14689282119189904486037573 2754240397348107091132045)
                      ·
                        rfl

theorem cell23_5363864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_5363864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363864 prefixEnd_5363864 := by exact prefixLift 5363864
  have htrace : WordTrace (prefixWord ++ tailWord_5363864) baseStart_5363864 baseEnd_5363864 := by
    simpa [prefixWord, tailWord_5363864, baseEnd_5363864] using wordTrace_append hprefix tailTrace_5363864
  have hstable : (prefixWord ++ tailWord_5363864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363864).length < 2 ^ (prefixWord ++ tailWord_5363864).sum := by decide
  have hdescent : baseEnd_5363864 < baseStart_5363864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363896 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 2, 6]
def baseStart_5363896 : Nat := 118140960795 + 5363896 * 2 ^ 59
def prefixEnd_5363896 : Nat := 4983230072969 + 3 ^ 40 * 5363896 * 2
def baseEnd_5363896 : Nat := 918085609576350321977299

theorem tailTrace_5363896 : CollatzResearch.WordTrace tailWord_5363896 prefixEnd_5363896 918085609576350321977299 := by
  unfold tailWord_5363896
  simp only [CollatzResearch.WordTrace]
  refine ⟨97818679687764173674507771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130424906250352231566010361 97818679687764173674507771)
  ·
    refine ⟨146728019531646260511761657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97818679687764173674507771 146728019531646260511761657)
    ·
      refine ⟨110046014648734695383821243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146728019531646260511761657 110046014648734695383821243)
      ·
        refine ⟨165069021973102043075731865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110046014648734695383821243 165069021973102043075731865)
        ·
          refine ⟨123801766479826532306798899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165069021973102043075731865 123801766479826532306798899)
          ·
            refine ⟨185702649719739798460198349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123801766479826532306798899 185702649719739798460198349)
            ·
              refine ⟨69638493644902424422574381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185702649719739798460198349 69638493644902424422574381)
              ·
                refine ⟨26114435116838409158465393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69638493644902424422574381 26114435116838409158465393)
                ·
                  refine ⟨19585826337628806868849045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26114435116838409158465393 19585826337628806868849045)
                  ·
                    refine ⟨918085609576350321977299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19585826337628806868849045 918085609576350321977299)
                    ·
                      rfl

theorem cell23_5363896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_5363896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363896 prefixEnd_5363896 := by exact prefixLift 5363896
  have htrace : WordTrace (prefixWord ++ tailWord_5363896) baseStart_5363896 baseEnd_5363896 := by
    simpa [prefixWord, tailWord_5363896, baseEnd_5363896] using wordTrace_append hprefix tailTrace_5363896
  have hstable : (prefixWord ++ tailWord_5363896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363896).length < 2 ^ (prefixWord ++ tailWord_5363896).sum := by decide
  have hdescent : baseEnd_5363896 < baseStart_5363896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363897 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 2, 1, 3]
def baseStart_5363897 : Nat := 118140960795 + 5363897 * 2 ^ 59
def prefixEnd_5363897 : Nat := 4983230072969 + 3 ^ 40 * 5363897 * 2
def baseEnd_5363897 : Nat := 2754257342209705462019393

theorem tailTrace_5363897 : CollatzResearch.WordTrace tailWord_5363897 prefixEnd_5363897 2754257342209705462019393 := by
  unfold tailWord_5363897
  simp only [CollatzResearch.WordTrace]
  refine ⟨195637395848524724519801945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130424930565683149679867963 195637395848524724519801945)
  ·
    refine ⟨146728046886393543389851459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195637395848524724519801945 146728046886393543389851459)
    ·
      refine ⟨220092070329590315084777189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146728046886393543389851459 220092070329590315084777189)
      ·
        refine ⟨41267263186798184078395723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220092070329590315084777189 41267263186798184078395723)
        ·
          refine ⟨61900894780197276117593585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41267263186798184078395723 61900894780197276117593585)
          ·
            refine ⟨46425671085147957088195189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61900894780197276117593585 46425671085147957088195189)
            ·
              refine ⟨4352406664232620977018299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46425671085147957088195189 4352406664232620977018299)
              ·
                refine ⟨6528609996348931465527449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4352406664232620977018299 6528609996348931465527449)
                ·
                  refine ⟨4896457497261698599145587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6528609996348931465527449 4896457497261698599145587)
                  ·
                    refine ⟨7344686245892547898718381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4896457497261698599145587 7344686245892547898718381)
                    ·
                      refine ⟨2754257342209705462019393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7344686245892547898718381 2754257342209705462019393)
                      ·
                        rfl

theorem cell23_5363897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_5363897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363897 prefixEnd_5363897 := by exact prefixLift 5363897
  have htrace : WordTrace (prefixWord ++ tailWord_5363897) baseStart_5363897 baseEnd_5363897 := by
    simpa [prefixWord, tailWord_5363897, baseEnd_5363897] using wordTrace_append hprefix tailTrace_5363897
  have hstable : (prefixWord ++ tailWord_5363897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363897).length < 2 ^ (prefixWord ++ tailWord_5363897).sum := by decide
  have hdescent : baseEnd_5363897 < baseStart_5363897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363936 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_5363936 : Nat := 118140960795 + 5363936 * 2 ^ 59
def prefixEnd_5363936 : Nat := 4983230072969 + 3 ^ 40 * 5363936 * 2
def baseEnd_5363936 : Nat := 2754277367955230809431713

theorem tailTrace_5363936 : CollatzResearch.WordTrace tailWord_5363936 prefixEnd_5363936 2754277367955230809431713 := by
  unfold tailWord_5363936
  simp only [CollatzResearch.WordTrace]
  refine ⟨97819409147691717090235831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130425878863588956120314441 97819409147691717090235831)
  ·
    refine ⟨146729113721537575635353747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97819409147691717090235831 146729113721537575635353747)
    ·
      refine ⟨220093670582306363453030621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146729113721537575635353747 220093670582306363453030621)
      ·
        refine ⟨82535126468364886294886483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220093670582306363453030621 82535126468364886294886483)
        ·
          refine ⟨123802689702547329442329725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82535126468364886294886483 123802689702547329442329725)
          ·
            refine ⟨46426008638455248540873647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123802689702547329442329725 46426008638455248540873647)
            ·
              refine ⟨69639012957682872811310471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46426008638455248540873647 69639012957682872811310471)
              ·
                refine ⟨104458519436524309216965707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69639012957682872811310471 104458519436524309216965707)
                ·
                  refine ⟨156687779154786463825448561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104458519436524309216965707 156687779154786463825448561)
                  ·
                    refine ⟨117515834366089847869086421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 156687779154786463825448561 117515834366089847869086421)
                    ·
                      refine ⟨2754277367955230809431713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117515834366089847869086421 2754277367955230809431713)
                      ·
                        rfl

theorem cell23_5363936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_5363936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363936 prefixEnd_5363936 := by exact prefixLift 5363936
  have htrace : WordTrace (prefixWord ++ tailWord_5363936) baseStart_5363936 baseEnd_5363936 := by
    simpa [prefixWord, tailWord_5363936, baseEnd_5363936] using wordTrace_append hprefix tailTrace_5363936
  have hstable : (prefixWord ++ tailWord_5363936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363936).length < 2 ^ (prefixWord ++ tailWord_5363936).sum := by decide
  have hdescent : baseEnd_5363936 < baseStart_5363936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363937 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 2, 2, 2]
def baseStart_5363937 : Nat := 118140960795 + 5363937 * 2 ^ 59
def prefixEnd_5363937 : Nat := 4983230072969 + 3 ^ 40 * 5363937 * 2
def baseEnd_5363937 : Nat := 2754277881435885305519209

theorem tailTrace_5363937 : CollatzResearch.WordTrace tailWord_5363937 prefixEnd_5363937 2754277881435885305519209 := by
  unfold tailWord_5363937
  simp only [CollatzResearch.WordTrace]
  refine ⟨195638854768379811351258065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130425903178919874234172043 195638854768379811351258065)
  ·
    refine ⟨146729141076284858513443549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195638854768379811351258065 146729141076284858513443549)
    ·
      refine ⟨55023427903606821942541331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146729141076284858513443549 55023427903606821942541331)
      ·
        refine ⟨82535141855410232913811997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55023427903606821942541331 82535141855410232913811997)
        ·
          refine ⟨30950678195778837342679499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82535141855410232913811997 30950678195778837342679499)
          ·
            refine ⟨46426017293668256014019249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30950678195778837342679499 46426017293668256014019249)
            ·
              refine ⟨34819512970251192010514437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46426017293668256014019249 34819512970251192010514437)
              ·
                refine ⟨6528658681922098501971457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34819512970251192010514437 6528658681922098501971457)
                ·
                  refine ⟨4896494011441573876478593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6528658681922098501971457 4896494011441573876478593)
                  ·
                    refine ⟨3672370508581180407358945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4896494011441573876478593 3672370508581180407358945)
                    ·
                      refine ⟨2754277881435885305519209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672370508581180407358945 2754277881435885305519209)
                      ·
                        rfl

theorem cell23_5363937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_5363937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363937 prefixEnd_5363937 := by exact prefixLift 5363937
  have htrace : WordTrace (prefixWord ++ tailWord_5363937) baseStart_5363937 baseEnd_5363937 := by
    simpa [prefixWord, tailWord_5363937, baseEnd_5363937] using wordTrace_append hprefix tailTrace_5363937
  have hstable : (prefixWord ++ tailWord_5363937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363937).length < 2 ^ (prefixWord ++ tailWord_5363937).sum := by decide
  have hdescent : baseEnd_5363937 < baseStart_5363937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363953 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 2, 3, 3]
def baseStart_5363953 : Nat := 118140960795 + 5363953 * 2 ^ 59
def prefixEnd_5363953 : Nat := 4983230072969 + 3 ^ 40 * 5363953 * 2
def baseEnd_5363953 : Nat := 2754286097126357242919135

theorem tailTrace_5363953 : CollatzResearch.WordTrace tailWord_5363953 prefixEnd_5363953 2754286097126357242919135 := by
  unfold tailWord_5363953
  simp only [CollatzResearch.WordTrace]
  refine ⟨195639438336321846083840513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130426292224214564055893675 195639438336321846083840513)
  ·
    refine ⟨146729578752241384562880385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195639438336321846083840513 146729578752241384562880385)
    ·
      refine ⟨110047184064181038422160289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146729578752241384562880385 110047184064181038422160289)
      ·
        refine ⟨82535388048135778816620217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110047184064181038422160289 82535388048135778816620217)
        ·
          refine ⟨61901541036101834112465163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82535388048135778816620217 61901541036101834112465163)
          ·
            refine ⟨92852311554152751168697745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61901541036101834112465163 92852311554152751168697745)
            ·
              refine ⟨69639233665614563376523309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92852311554152751168697745 69639233665614563376523309)
              ·
                refine ⟨26114712624605461266196241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69639233665614563376523309 26114712624605461266196241)
                ·
                  refine ⟨19586034468454095949647181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26114712624605461266196241 19586034468454095949647181)
                  ·
                    refine ⟨7344762925670285981117693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19586034468454095949647181 7344762925670285981117693)
                    ·
                      refine ⟨2754286097126357242919135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7344762925670285981117693 2754286097126357242919135)
                      ·
                        rfl

theorem cell23_5363953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_5363953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363953 prefixEnd_5363953 := by exact prefixLift 5363953
  have htrace : WordTrace (prefixWord ++ tailWord_5363953) baseStart_5363953 baseEnd_5363953 := by
    simpa [prefixWord, tailWord_5363953, baseEnd_5363953] using wordTrace_append hprefix tailTrace_5363953
  have hstable : (prefixWord ++ tailWord_5363953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363953).length < 2 ^ (prefixWord ++ tailWord_5363953).sum := by decide
  have hdescent : baseEnd_5363953 < baseStart_5363953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363954 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 2, 2, 2]
def baseStart_5363954 : Nat := 118140960795 + 5363954 * 2 ^ 59
def prefixEnd_5363954 : Nat := 4983230072969 + 3 ^ 40 * 5363954 * 2
def baseEnd_5363954 : Nat := 2754286610607011739006631

theorem tailTrace_5363954 : CollatzResearch.WordTrace tailWord_5363954 prefixEnd_5363954 2754286610607011739006631 := by
  unfold tailWord_5363954
  simp only [CollatzResearch.WordTrace]
  refine ⟨48909868702329555813656729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130426316539545482169751277 48909868702329555813656729)
  ·
    refine ⟨36682401526747166860242547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48909868702329555813656729 36682401526747166860242547)
    ·
      refine ⟨55023602290120750290363821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36682401526747166860242547 55023602290120750290363821)
      ·
        refine ⟨20633850858795281358886433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55023602290120750290363821 20633850858795281358886433)
        ·
          refine ⟨15475388144096461019164825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20633850858795281358886433 15475388144096461019164825)
          ·
            refine ⟨11606541108072345764373619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15475388144096461019164825 11606541108072345764373619)
            ·
              refine ⟨17409811662108518646560429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11606541108072345764373619 17409811662108518646560429)
              ·
                refine ⟨6528679373290694492460161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17409811662108518646560429 6528679373290694492460161)
                ·
                  refine ⟨4896509529968020869345121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6528679373290694492460161 4896509529968020869345121)
                  ·
                    refine ⟨3672382147476015652008841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4896509529968020869345121 3672382147476015652008841)
                    ·
                      refine ⟨2754286610607011739006631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672382147476015652008841 2754286610607011739006631)
                      ·
                        rfl

theorem cell23_5363954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_5363954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363954 prefixEnd_5363954 := by exact prefixLift 5363954
  have htrace : WordTrace (prefixWord ++ tailWord_5363954) baseStart_5363954 baseEnd_5363954 := by
    simpa [prefixWord, tailWord_5363954, baseEnd_5363954] using wordTrace_append hprefix tailTrace_5363954
  have hstable : (prefixWord ++ tailWord_5363954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363954).length < 2 ^ (prefixWord ++ tailWord_5363954).sum := by decide
  have hdescent : baseEnd_5363954 < baseStart_5363954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5363994 : List Nat := [3, 1, 1, 3, 4, 2, 2, 2, 5]
def baseStart_5363994 : Nat := 118140960795 + 5363994 * 2 ^ 59
def prefixEnd_5363994 : Nat := 4983230072969 + 3 ^ 40 * 5363994 * 2
def baseEnd_5363994 : Nat := 306034127759243509167383

theorem tailTrace_5363994 : CollatzResearch.WordTrace tailWord_5363994 prefixEnd_5363994 306034127759243509167383 := by
  unfold tailWord_5363994
  simp only [CollatzResearch.WordTrace]
  refine ⟨48910233432293327521520759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130427289152782206724055357 48910233432293327521520759)
  ·
    refine ⟨73365350148439991282281139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48910233432293327521520759 73365350148439991282281139)
    ·
      refine ⟨110048025222659986923421709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73365350148439991282281139 110048025222659986923421709)
      ·
        refine ⟨41268009458497495096283141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110048025222659986923421709 41268009458497495096283141)
        ·
          refine ⟨7737751773468280330553089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41268009458497495096283141 7737751773468280330553089)
          ·
            refine ⟨5803313830101210247914817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7737751773468280330553089 5803313830101210247914817)
            ·
              refine ⟨4352485372575907685936113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5803313830101210247914817 4352485372575907685936113)
              ·
                refine ⟨3264364029431930764452085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4352485372575907685936113 3264364029431930764452085)
                ·
                  refine ⟨306034127759243509167383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3264364029431930764452085 306034127759243509167383)
                  ·
                    rfl

theorem cell23_5363994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 5].length) (baseStart_5363994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5363994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5363994 prefixEnd_5363994 := by exact prefixLift 5363994
  have htrace : WordTrace (prefixWord ++ tailWord_5363994) baseStart_5363994 baseEnd_5363994 := by
    simpa [prefixWord, tailWord_5363994, baseEnd_5363994] using wordTrace_append hprefix tailTrace_5363994
  have hstable : (prefixWord ++ tailWord_5363994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5363994).length < 2 ^ (prefixWord ++ tailWord_5363994).sum := by decide
  have hdescent : baseEnd_5363994 < baseStart_5363994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5363994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364050 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 6]
def baseStart_5364050 : Nat := 118140960795 + 5364050 * 2 ^ 59
def prefixEnd_5364050 : Nat := 4983230072969 + 3 ^ 40 * 5364050 * 2
def baseEnd_5364050 : Nat := 306037322749982595934021

theorem tailTrace_5364050 : CollatzResearch.WordTrace tailWord_5364050 prefixEnd_5364050 306037322749982595934021 := by
  unfold tailWord_5364050
  simp only [CollatzResearch.WordTrace]
  refine ⟨48910744054242607912530401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130428650811313621100081069 48910744054242607912530401)
  ·
    refine ⟨36683058040681955934397801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48910744054242607912530401 36683058040681955934397801)
    ·
      refine ⟨27512293530511466950798351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36683058040681955934397801 27512293530511466950798351)
      ·
        refine ⟨41268440295767200426197527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27512293530511466950798351 41268440295767200426197527)
        ·
          refine ⟨61902660443650800639296291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41268440295767200426197527 61902660443650800639296291)
          ·
            refine ⟨92853990665476200958944437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61902660443650800639296291 92853990665476200958944437)
            ·
              refine ⟨8705061624888393839901041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92853990665476200958944437 8705061624888393839901041)
              ·
                refine ⟨6528796218666295379925781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8705061624888393839901041 6528796218666295379925781)
                ·
                  refine ⟨306037322749982595934021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6528796218666295379925781 306037322749982595934021)
                  ·
                    rfl

theorem cell23_5364050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 6].length) (baseStart_5364050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364050 prefixEnd_5364050 := by exact prefixLift 5364050
  have htrace : WordTrace (prefixWord ++ tailWord_5364050) baseStart_5364050 baseEnd_5364050 := by
    simpa [prefixWord, tailWord_5364050, baseEnd_5364050] using wordTrace_append hprefix tailTrace_5364050
  have hstable : (prefixWord ++ tailWord_5364050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364050).length < 2 ^ (prefixWord ++ tailWord_5364050).sum := by decide
  have hdescent : baseEnd_5364050 < baseStart_5364050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364063 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 5, 5]
def baseStart_5364063 : Nat := 118140960795 + 5364063 * 2 ^ 59
def prefixEnd_5364063 : Nat := 4983230072969 + 3 ^ 40 * 5364063 * 2
def baseEnd_5364063 : Nat := 918114193332783937514543

theorem tailTrace_5364063 : CollatzResearch.WordTrace tailWord_5364063 prefixEnd_5364063 918114193332783937514543 := by
  unfold tailWord_5364063
  simp only [CollatzResearch.WordTrace]
  refine ⟨195643450365923334870344843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130428966910615556580229895 195643450365923334870344843)
  ·
    refine ⟨293465175548885002305517265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195643450365923334870344843 293465175548885002305517265)
    ·
      refine ⟨220098881661663751729137949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293465175548885002305517265 220098881661663751729137949)
      ·
        refine ⟨82537080623123906898426731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220098881661663751729137949 82537080623123906898426731)
        ·
          refine ⟨123805620934685860347640097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82537080623123906898426731 123805620934685860347640097)
          ·
            refine ⟨92854215701014395260730073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123805620934685860347640097 92854215701014395260730073)
            ·
              refine ⟨69640661775760796445547555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92854215701014395260730073 69640661775760796445547555)
              ·
                refine ⟨104460992663641194668321333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69640661775760796445547555 104460992663641194668321333)
                ·
                  refine ⟨9793218062216362000155125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104460992663641194668321333 9793218062216362000155125)
                  ·
                    refine ⟨918114193332783937514543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9793218062216362000155125 918114193332783937514543)
                    ·
                      rfl

theorem cell23_5364063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_5364063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364063 prefixEnd_5364063 := by exact prefixLift 5364063
  have htrace : WordTrace (prefixWord ++ tailWord_5364063) baseStart_5364063 baseEnd_5364063 := by
    simpa [prefixWord, tailWord_5364063, baseEnd_5364063] using wordTrace_append hprefix tailTrace_5364063
  have hstable : (prefixWord ++ tailWord_5364063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364063).length < 2 ^ (prefixWord ++ tailWord_5364063).sum := by decide
  have hdescent : baseEnd_5364063 < baseStart_5364063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364077 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_5364077 : Nat := 118140960795 + 5364077 * 2 ^ 59
def prefixEnd_5364077 : Nat := 4983230072969 + 3 ^ 40 * 5364077 * 2
def baseEnd_5364077 : Nat := 2754349768727514757768565

theorem tailTrace_5364077 : CollatzResearch.WordTrace tailWord_5364077 prefixEnd_5364077 2754349768727514757768565 := by
  unfold tailWord_5364077
  simp only [CollatzResearch.WordTrace]
  refine ⟨195643960987872615261354485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130429307325248410174236323 195643960987872615261354485)
  ·
    refine ⟨18341621342613057680751983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195643960987872615261354485 18341621342613057680751983)
    ·
      refine ⟨27512432013919586521127975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18341621342613057680751983 27512432013919586521127975)
      ·
        refine ⟨41268648020879379781691963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27512432013919586521127975 41268648020879379781691963)
        ·
          refine ⟨61902972031319069672537945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41268648020879379781691963 61902972031319069672537945)
          ·
            refine ⟨46427229023489302254403459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61902972031319069672537945 46427229023489302254403459)
            ·
              refine ⟨69640843535233953381605189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46427229023489302254403459 69640843535233953381605189)
              ·
                refine ⟨13057658162856366259050973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69640843535233953381605189 13057658162856366259050973)
                ·
                  refine ⟨4896621811071137347144115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13057658162856366259050973 4896621811071137347144115)
                  ·
                    refine ⟨7344932716606706020716173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4896621811071137347144115 7344932716606706020716173)
                    ·
                      refine ⟨2754349768727514757768565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7344932716606706020716173 2754349768727514757768565)
                      ·
                        rfl

theorem cell23_5364077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_5364077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364077 prefixEnd_5364077 := by exact prefixLift 5364077
  have htrace : WordTrace (prefixWord ++ tailWord_5364077) baseStart_5364077 baseEnd_5364077 := by
    simpa [prefixWord, tailWord_5364077, baseEnd_5364077] using wordTrace_append hprefix tailTrace_5364077
  have hstable : (prefixWord ++ tailWord_5364077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364077).length < 2 ^ (prefixWord ++ tailWord_5364077).sum := by decide
  have hdescent : baseEnd_5364077 < baseStart_5364077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364080 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 1, 5]
def baseStart_5364080 : Nat := 118140960795 + 5364080 * 2 ^ 59
def prefixEnd_5364080 : Nat := 4983230072969 + 3 ^ 40 * 5364080 * 2
def baseEnd_5364080 : Nat := 918117103056492748677017

theorem tailTrace_5364080 : CollatzResearch.WordTrace tailWord_5364080 prefixEnd_5364080 918117103056492748677017 := by
  unfold tailWord_5364080
  simp only [CollatzResearch.WordTrace]
  refine ⟨97822035203430873386856847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130429380271241164515809129 97822035203430873386856847)
  ·
    refine ⟨146733052805146310080285271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97822035203430873386856847 146733052805146310080285271)
    ·
      refine ⟨220099579207719465120427907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146733052805146310080285271 220099579207719465120427907)
      ·
        refine ⟨330149368811579197680641861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220099579207719465120427907 330149368811579197680641861)
        ·
          refine ⟨61903006652171099565120349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330149368811579197680641861 61903006652171099565120349)
          ·
            refine ⟨23213627494564162336920131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61903006652171099565120349 23213627494564162336920131)
            ·
              refine ⟨34820441241846243505380197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23213627494564162336920131 34820441241846243505380197)
              ·
                refine ⟨6528832732846170657258787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34820441241846243505380197 6528832732846170657258787)
                ·
                  refine ⟨9793249099269255985888181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6528832732846170657258787 9793249099269255985888181)
                  ·
                    refine ⟨918117103056492748677017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9793249099269255985888181 918117103056492748677017)
                    ·
                      rfl

theorem cell23_5364080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 5].length) (baseStart_5364080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364080 prefixEnd_5364080 := by exact prefixLift 5364080
  have htrace : WordTrace (prefixWord ++ tailWord_5364080) baseStart_5364080 baseEnd_5364080 := by
    simpa [prefixWord, tailWord_5364080, baseEnd_5364080] using wordTrace_append hprefix tailTrace_5364080
  have hstable : (prefixWord ++ tailWord_5364080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364080).length < 2 ^ (prefixWord ++ tailWord_5364080).sum := by decide
  have hdescent : baseEnd_5364080 < baseStart_5364080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364097 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 1, 5]
def baseStart_5364097 : Nat := 118140960795 + 5364097 * 2 ^ 59
def prefixEnd_5364097 : Nat := 4983230072969 + 3 ^ 40 * 5364097 * 2
def baseEnd_5364097 : Nat := 918120012780201559839491

theorem tailTrace_5364097 : CollatzResearch.WordTrace tailWord_5364097 prefixEnd_5364097 918120012780201559839491 := by
  unfold tailWord_5364097
  simp only [CollatzResearch.WordTrace]
  refine ⟨195644690447800158677082545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130429793631866772451388363 195644690447800158677082545)
  ·
    refine ⟨146733517835850119007811909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195644690447800158677082545 146733517835850119007811909)
    ·
      refine ⟨27512534594221897313964733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146733517835850119007811909 27512534594221897313964733)
      ·
        refine ⟨10317200472833211492736775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27512534594221897313964733 10317200472833211492736775)
        ·
          refine ⟨15475800709249817239105163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10317200472833211492736775 15475800709249817239105163)
          ·
            refine ⟨23213701063874725858657745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15475800709249817239105163 23213701063874725858657745)
            ·
              refine ⟨17410275797906044393993309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23213701063874725858657745 17410275797906044393993309)
              ·
                refine ⟨6528853424214766647747491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17410275797906044393993309 6528853424214766647747491)
                ·
                  refine ⟨9793280136322149971621237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6528853424214766647747491 9793280136322149971621237)
                  ·
                    refine ⟨918120012780201559839491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9793280136322149971621237 918120012780201559839491)
                    ·
                      rfl

theorem cell23_5364097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_5364097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364097 prefixEnd_5364097 := by exact prefixLift 5364097
  have htrace : WordTrace (prefixWord ++ tailWord_5364097) baseStart_5364097 baseEnd_5364097 := by
    simpa [prefixWord, tailWord_5364097, baseEnd_5364097] using wordTrace_append hprefix tailTrace_5364097
  have hstable : (prefixWord ++ tailWord_5364097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364097).length < 2 ^ (prefixWord ++ tailWord_5364097).sum := by decide
  have hdescent : baseEnd_5364097 < baseStart_5364097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364113 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_5364113 : Nat := 118140960795 + 5364113 * 2 ^ 59
def prefixEnd_5364113 : Nat := 4983230072969 + 3 ^ 40 * 5364113 * 2
def baseEnd_5364113 : Nat := 2754368254031076616918399

theorem tailTrace_5364113 : CollatzResearch.WordTrace tailWord_5364113 prefixEnd_5364113 2754368254031076616918399 := by
  unfold tailWord_5364113
  simp only [CollatzResearch.WordTrace]
  refine ⟨195645274015742193409664993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130430182677161462273109995 195645274015742193409664993)
  ·
    refine ⟨146733955511806645057248745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195645274015742193409664993 146733955511806645057248745)
    ·
      refine ⟨110050466633854983792936559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146733955511806645057248745 110050466633854983792936559)
      ·
        refine ⟨165075699950782475689404839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110050466633854983792936559 165075699950782475689404839)
        ·
          refine ⟨247613549926173713534107259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165075699950782475689404839 247613549926173713534107259)
          ·
            refine ⟨371420324889260570301160889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247613549926173713534107259 371420324889260570301160889)
            ·
              refine ⟨278565243666945427725870667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371420324889260570301160889 278565243666945427725870667)
              ·
                refine ⟨417847865500418141588806001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278565243666945427725870667 417847865500418141588806001)
                ·
                  refine ⟨313385899125313606191604501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417847865500418141588806001 313385899125313606191604501)
                  ·
                    refine ⟨14689964021499075290231461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 313385899125313606191604501 14689964021499075290231461)
                    ·
                      refine ⟨2754368254031076616918399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14689964021499075290231461 2754368254031076616918399)
                      ·
                        rfl

theorem cell23_5364113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_5364113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364113 prefixEnd_5364113 := by exact prefixLift 5364113
  have htrace : WordTrace (prefixWord ++ tailWord_5364113) baseStart_5364113 baseEnd_5364113 := by
    simpa [prefixWord, tailWord_5364113, baseEnd_5364113] using wordTrace_append hprefix tailTrace_5364113
  have hstable : (prefixWord ++ tailWord_5364113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364113).length < 2 ^ (prefixWord ++ tailWord_5364113).sum := by decide
  have hdescent : baseEnd_5364113 < baseStart_5364113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364127 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 2, 4]
def baseStart_5364127 : Nat := 118140960795 + 5364127 * 2 ^ 59
def prefixEnd_5364127 : Nat := 4983230072969 + 3 ^ 40 * 5364127 * 2
def baseEnd_5364127 : Nat := 918125147586746520714445

theorem tailTrace_5364127 : CollatzResearch.WordTrace tailWord_5364127 prefixEnd_5364127 918125147586746520714445 := by
  unfold tailWord_5364127
  simp only [CollatzResearch.WordTrace]
  refine ⟨195645784637691473800674635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130430523091794315867116423 195645784637691473800674635)
  ·
    refine ⟨293468676956537210701011953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195645784637691473800674635 293468676956537210701011953)
    ·
      refine ⟨220101507717402908025758965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293468676956537210701011953 220101507717402908025758965)
      ·
        refine ⟨20634516348506522627414903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220101507717402908025758965 20634516348506522627414903)
        ·
          refine ⟨30951774522759783941122355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20634516348506522627414903 30951774522759783941122355)
          ·
            refine ⟨46427661784139675911683533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30951774522759783941122355 46427661784139675911683533)
            ·
              refine ⟨17410373169052378466881325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46427661784139675911683533 17410373169052378466881325)
              ·
                refine ⟨6528889938394641925080497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17410373169052378466881325 6528889938394641925080497)
                ·
                  refine ⟨4896667453795981443810373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6528889938394641925080497 4896667453795981443810373)
                  ·
                    refine ⟨918125147586746520714445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4896667453795981443810373 918125147586746520714445)
                    ·
                      rfl

theorem cell23_5364127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 4].length) (baseStart_5364127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364127 prefixEnd_5364127 := by exact prefixLift 5364127
  have htrace : WordTrace (prefixWord ++ tailWord_5364127) baseStart_5364127 baseEnd_5364127 := by
    simpa [prefixWord, tailWord_5364127, baseEnd_5364127] using wordTrace_append hprefix tailTrace_5364127
  have hstable : (prefixWord ++ tailWord_5364127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364127).length < 2 ^ (prefixWord ++ tailWord_5364127).sum := by decide
  have hdescent : baseEnd_5364127 < baseStart_5364127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364130 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_5364130 : Nat := 118140960795 + 5364130 * 2 ^ 59
def prefixEnd_5364130 : Nat := 4983230072969 + 3 ^ 40 * 5364130 * 2
def baseEnd_5364130 : Nat := 2754376983202203050405821

theorem tailTrace_5364130 : CollatzResearch.WordTrace tailWord_5364130 prefixEnd_5364130 2754376983202203050405821 := by
  unfold tailWord_5364130
  simp only [CollatzResearch.WordTrace]
  refine ⟨48911473514170151328258461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130430596037787070208689229 48911473514170151328258461)
  ·
    refine ⟨18341802567813806748096923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48911473514170151328258461 18341802567813806748096923)
    ·
      refine ⟨27512703851720710122145385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18341802567813806748096923 27512703851720710122145385)
      ·
        refine ⟨20634527888790532591609039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27512703851720710122145385 20634527888790532591609039)
        ·
          refine ⟨30951791833185798887413559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20634527888790532591609039 30951791833185798887413559)
          ·
            refine ⟨46427687749778698331120339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30951791833185798887413559 46427687749778698331120339)
            ·
              refine ⟨69641531624668047496680509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46427687749778698331120339 69641531624668047496680509)
              ·
                refine ⟨26115574359250517811255191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69641531624668047496680509 26115574359250517811255191)
                ·
                  refine ⟨39173361538875776716882787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26115574359250517811255191 39173361538875776716882787)
                  ·
                    refine ⟨58760042308313665075324181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39173361538875776716882787 58760042308313665075324181)
                    ·
                      refine ⟨2754376983202203050405821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58760042308313665075324181 2754376983202203050405821)
                      ·
                        rfl

theorem cell23_5364130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_5364130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364130 prefixEnd_5364130 := by exact prefixLift 5364130
  have htrace : WordTrace (prefixWord ++ tailWord_5364130) baseStart_5364130 baseEnd_5364130 := by
    simpa [prefixWord, tailWord_5364130, baseEnd_5364130] using wordTrace_append hprefix tailTrace_5364130
  have hstable : (prefixWord ++ tailWord_5364130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364130).length < 2 ^ (prefixWord ++ tailWord_5364130).sum := by decide
  have hdescent : baseEnd_5364130 < baseStart_5364130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364148 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 1, 5]
def baseStart_5364148 : Nat := 118140960795 + 5364148 * 2 ^ 59
def prefixEnd_5364148 : Nat := 4983230072969 + 3 ^ 40 * 5364148 * 2
def baseEnd_5364148 : Nat := 918128741951327993326913

theorem tailTrace_5364148 : CollatzResearch.WordTrace tailWord_5364148 prefixEnd_5364148 918128741951327993326913 := by
  unfold tailWord_5364148
  simp only [CollatzResearch.WordTrace]
  refine ⟨97823275285307697193594549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130431033713743596258126065 97823275285307697193594549)
  ·
    refine ⟨9170932057997596611899489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97823275285307697193594549 9170932057997596611899489)
    ·
      refine ⟨6878199043498197458924617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9170932057997596611899489 6878199043498197458924617)
      ·
        refine ⟨5158649282623648094193463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6878199043498197458924617 5158649282623648094193463)
        ·
          refine ⟨7737973923935472141290195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5158649282623648094193463 7737973923935472141290195)
          ·
            refine ⟨11606960885903208211935293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7737973923935472141290195 11606960885903208211935293)
            ·
              refine ⟨4352610332213703079475735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11606960885903208211935293 4352610332213703079475735)
              ·
                refine ⟨6528915498320554619213603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4352610332213703079475735 6528915498320554619213603)
                ·
                  refine ⟨9793373247480831928820405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6528915498320554619213603 9793373247480831928820405)
                  ·
                    refine ⟨918128741951327993326913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9793373247480831928820405 918128741951327993326913)
                    ·
                      rfl

theorem cell23_5364148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_5364148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364148 prefixEnd_5364148 := by exact prefixLift 5364148
  have htrace : WordTrace (prefixWord ++ tailWord_5364148) baseStart_5364148 baseEnd_5364148 := by
    simpa [prefixWord, tailWord_5364148, baseEnd_5364148] using wordTrace_append hprefix tailTrace_5364148
  have hstable : (prefixWord ++ tailWord_5364148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364148).length < 2 ^ (prefixWord ++ tailWord_5364148).sum := by decide
  have hdescent : baseEnd_5364148 < baseStart_5364148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364168 : List Nat := [2, 1, 3, 1, 3, 2, 4, 2, 1, 2, 2]
def baseStart_5364168 : Nat := 118140960795 + 5364168 * 2 ^ 59
def prefixEnd_5364168 : Nat := 4983230072969 + 3 ^ 40 * 5364168 * 2
def baseEnd_5364168 : Nat := 2754396495467073901730647

theorem tailTrace_5364168 : CollatzResearch.WordTrace tailWord_5364168 prefixEnd_5364168 2754396495467073901730647 := by
  unfold tailWord_5364168
  simp only [CollatzResearch.WordTrace]
  refine ⟨97823640015271468901458579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130431520020361958535278105 97823640015271468901458579)
  ·
    refine ⟨146735460022907203352187869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97823640015271468901458579 146735460022907203352187869)
    ·
      refine ⟨55025797508590201257070451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146735460022907203352187869 55025797508590201257070451)
      ·
        refine ⟨82538696262885301885605677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55025797508590201257070451 82538696262885301885605677)
        ·
          refine ⟨30952011098581988207102129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82538696262885301885605677 30952011098581988207102129)
          ·
            refine ⟨23214008323936491155326597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30952011098581988207102129 23214008323936491155326597)
            ·
              refine ⟨4352626560738092091623737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23214008323936491155326597 4352626560738092091623737)
              ·
                refine ⟨3264469920553569068717803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4352626560738092091623737 3264469920553569068717803)
                ·
                  refine ⟨4896704880830353603076705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264469920553569068717803 4896704880830353603076705)
                  ·
                    refine ⟨3672528660622765202307529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4896704880830353603076705 3672528660622765202307529)
                    ·
                      refine ⟨2754396495467073901730647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672528660622765202307529 2754396495467073901730647)
                      ·
                        rfl

theorem cell23_5364168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_5364168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364168 prefixEnd_5364168 := by exact prefixLift 5364168
  have htrace : WordTrace (prefixWord ++ tailWord_5364168) baseStart_5364168 baseEnd_5364168 := by
    simpa [prefixWord, tailWord_5364168, baseEnd_5364168] using wordTrace_append hprefix tailTrace_5364168
  have hstable : (prefixWord ++ tailWord_5364168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364168).length < 2 ^ (prefixWord ++ tailWord_5364168).sum := by decide
  have hdescent : baseEnd_5364168 < baseStart_5364168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364240 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 3]
def baseStart_5364240 : Nat := 118140960795 + 5364240 * 2 ^ 59
def prefixEnd_5364240 : Nat := 4983230072969 + 3 ^ 40 * 5364240 * 2
def baseEnd_5364240 : Nat := 2754433466074197620030315

theorem tailTrace_5364240 : CollatzResearch.WordTrace tailWord_5364240 prefixEnd_5364240 2754433466074197620030315 := by
  unfold tailWord_5364240
  simp only [CollatzResearch.WordTrace]
  refine ⟨97824953043141047049769087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130433270724188062733025449 97824953043141047049769087)
  ·
    refine ⟨146737429564711570574653631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97824953043141047049769087 146737429564711570574653631)
    ·
      refine ⟨220106144347067355861980447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146737429564711570574653631 220106144347067355861980447)
      ·
        refine ⟨330159216520601033792970671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220106144347067355861980447 330159216520601033792970671)
        ·
          refine ⟨495238824780901550689456007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330159216520601033792970671 495238824780901550689456007)
          ·
            refine ⟨742858237171352326034184011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495238824780901550689456007 742858237171352326034184011)
            ·
              refine ⟨1114287355757028489051276017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742858237171352326034184011 1114287355757028489051276017)
              ·
                refine ⟨835715516817771366788457013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114287355757028489051276017 835715516817771366788457013)
                ·
                  refine ⟨78348329701666065636417845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 835715516817771366788457013 78348329701666065636417845)
                  ·
                    refine ⟨7345155909531193653414173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78348329701666065636417845 7345155909531193653414173)
                    ·
                      refine ⟨2754433466074197620030315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7345155909531193653414173 2754433466074197620030315)
                      ·
                        rfl

theorem cell23_5364240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 3].length) (baseStart_5364240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364240 prefixEnd_5364240 := by exact prefixLift 5364240
  have htrace : WordTrace (prefixWord ++ tailWord_5364240) baseStart_5364240 baseEnd_5364240 := by
    simpa [prefixWord, tailWord_5364240, baseEnd_5364240] using wordTrace_append hprefix tailTrace_5364240
  have hstable : (prefixWord ++ tailWord_5364240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364240).length < 2 ^ (prefixWord ++ tailWord_5364240).sum := by decide
  have hdescent : baseEnd_5364240 < baseStart_5364240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364277 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_5364277 : Nat := 118140960795 + 5364277 * 2 ^ 59
def prefixEnd_5364277 : Nat := 4983230072969 + 3 ^ 40 * 5364277 * 2
def baseEnd_5364277 : Nat := 918150821619471325089215

theorem tailTrace_5364277 : CollatzResearch.WordTrace tailWord_5364277 prefixEnd_5364277 918150821619471325089215 := by
  unfold tailWord_5364277
  simp only [CollatzResearch.WordTrace]
  refine ⟨195651255587148049418635085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130434170391432032945756723 195651255587148049418635085)
  ·
    refine ⟨73369220845180518531988157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195651255587148049418635085 73369220845180518531988157)
    ·
      refine ⟨27513457816942694449495559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73369220845180518531988157 27513457816942694449495559)
      ·
        refine ⟨41270186725414041674243339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27513457816942694449495559 41270186725414041674243339)
        ·
          refine ⟨61905280088121062511365009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41270186725414041674243339 61905280088121062511365009)
          ·
            refine ⟨46428960066090796883523757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61905280088121062511365009 46428960066090796883523757)
            ·
              refine ⟨17410860024784048831321409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46428960066090796883523757 17410860024784048831321409)
              ·
                refine ⟨13058145018588036623491057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17410860024784048831321409 13058145018588036623491057)
                ·
                  refine ⟨9793608763941027467618293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13058145018588036623491057 9793608763941027467618293)
                  ·
                    refine ⟨918150821619471325089215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9793608763941027467618293 918150821619471325089215)
                    ·
                      rfl

theorem cell23_5364277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_5364277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364277 prefixEnd_5364277 := by exact prefixLift 5364277
  have htrace : WordTrace (prefixWord ++ tailWord_5364277) baseStart_5364277 baseEnd_5364277 := by
    simpa [prefixWord, tailWord_5364277, baseEnd_5364277] using wordTrace_append hprefix tailTrace_5364277
  have hstable : (prefixWord ++ tailWord_5364277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364277).length < 2 ^ (prefixWord ++ tailWord_5364277).sum := by decide
  have hdescent : baseEnd_5364277 < baseStart_5364277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364292 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5364292 : Nat := 118140960795 + 5364292 * 2 ^ 59
def prefixEnd_5364292 : Nat := 4983230072969 + 3 ^ 40 * 5364292 * 2
def baseEnd_5364292 : Nat := 2754460167068231416580077

theorem tailTrace_5364292 : CollatzResearch.WordTrace tailWord_5364292 prefixEnd_5364292 2754460167068231416580077 := by
  unfold tailWord_5364292
  simp only [CollatzResearch.WordTrace]
  refine ⟨97825901341046853490215565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130434535121395804653620753 97825901341046853490215565)
  ·
    refine ⟨36684713002892570058830837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97825901341046853490215565 36684713002892570058830837)
    ·
      refine ⟨3439191844021178443015391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36684713002892570058830837 3439191844021178443015391)
      ·
        refine ⟨5158787766031767664523087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3439191844021178443015391 5158787766031767664523087)
        ·
          refine ⟨7738181649047651496784631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5158787766031767664523087 7738181649047651496784631)
          ·
            refine ⟨11607272473571477245176947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7738181649047651496784631 11607272473571477245176947)
            ·
              refine ⟨17410908710357215867765421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11607272473571477245176947 17410908710357215867765421)
              ·
                refine ⟨6529090766383955950412033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17410908710357215867765421 6529090766383955950412033)
                ·
                  refine ⟨4896818074787966962809025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6529090766383955950412033 4896818074787966962809025)
                  ·
                    refine ⟨3672613556090975222106769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4896818074787966962809025 3672613556090975222106769)
                    ·
                      refine ⟨2754460167068231416580077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672613556090975222106769 2754460167068231416580077)
                      ·
                        rfl

theorem cell23_5364292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5364292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364292 prefixEnd_5364292 := by exact prefixLift 5364292
  have htrace : WordTrace (prefixWord ++ tailWord_5364292) baseStart_5364292 baseEnd_5364292 := by
    simpa [prefixWord, tailWord_5364292, baseEnd_5364292] using wordTrace_append hprefix tailTrace_5364292
  have hstable : (prefixWord ++ tailWord_5364292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364292).length < 2 ^ (prefixWord ++ tailWord_5364292).sum := by decide
  have hdescent : baseEnd_5364292 < baseStart_5364292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364320 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 10]
def baseStart_5364320 : Nat := 118140960795 + 5364320 * 2 ^ 59
def prefixEnd_5364320 : Nat := 4983230072969 + 3 ^ 40 * 5364320 * 2
def baseEnd_5364320 : Nat := 306052727169617478558883

theorem tailTrace_5364320 : CollatzResearch.WordTrace tailWord_5364320 prefixEnd_5364320 306052727169617478558883 := by
  unfold tailWord_5364320
  simp only [CollatzResearch.WordTrace]
  refine ⟨97826411962996133881225207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130435215950661511841633609 97826411962996133881225207)
  ·
    refine ⟨146739617944494200821837811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97826411962996133881225207 146739617944494200821837811)
    ·
      refine ⟨220109426916741301232756717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146739617944494200821837811 220109426916741301232756717)
      ·
        refine ⟨82541035093777987962283769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220109426916741301232756717 82541035093777987962283769)
        ·
          refine ⟨61905776320333490971712827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82541035093777987962283769 61905776320333490971712827)
          ·
            refine ⟨92858664480500236457569241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61905776320333490971712827 92858664480500236457569241)
            ·
              refine ⟨69643998360375177343176931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92858664480500236457569241 69643998360375177343176931)
              ·
                refine ⟨104465997540562766014765397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69643998360375177343176931 104465997540562766014765397)
                ·
                  refine ⟨306052727169617478558883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 104465997540562766014765397 306052727169617478558883)
                  ·
                    rfl

theorem cell23_5364320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 10].length) (baseStart_5364320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364320 prefixEnd_5364320 := by exact prefixLift 5364320
  have htrace : WordTrace (prefixWord ++ tailWord_5364320) baseStart_5364320 baseEnd_5364320 := by
    simpa [prefixWord, tailWord_5364320, baseEnd_5364320] using wordTrace_append hprefix tailTrace_5364320
  have hstable : (prefixWord ++ tailWord_5364320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364320).length < 2 ^ (prefixWord ++ tailWord_5364320).sum := by decide
  have hdescent : baseEnd_5364320 < baseStart_5364320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364387 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 4]
def baseStart_5364387 : Nat := 118140960795 + 5364387 * 2 ^ 59
def prefixEnd_5364387 : Nat := 4983230072969 + 3 ^ 40 * 5364387 * 2
def baseEnd_5364387 : Nat := 2754508947730408544892139

theorem tailTrace_5364387 : CollatzResearch.WordTrace tailWord_5364387 prefixEnd_5364387 2754508947730408544892139 := by
  unfold tailWord_5364387
  simp only [CollatzResearch.WordTrace]
  refine ⟨195655267616749538205139415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130436845077833025470092943 195655267616749538205139415)
  ·
    refine ⟨293482901425124307307709123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195655267616749538205139415 293482901425124307307709123)
    ·
      refine ⟨440224352137686460961563685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293482901425124307307709123 440224352137686460961563685)
      ·
        refine ⟨82542066025816211430293191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 440224352137686460961563685 82542066025816211430293191)
        ·
          refine ⟨123813099038724317145439787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82542066025816211430293191 123813099038724317145439787)
          ·
            refine ⟨185719648558086475718159681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123813099038724317145439787 185719648558086475718159681)
            ·
              refine ⟨139289736418564856788619761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185719648558086475718159681 139289736418564856788619761)
              ·
                refine ⟨104467302313923642591464821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139289736418564856788619761 104467302313923642591464821)
                ·
                  refine ⟨9793809591930341492949827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104467302313923642591464821 9793809591930341492949827)
                  ·
                    refine ⟨14690714387895512239424741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9793809591930341492949827 14690714387895512239424741)
                    ·
                      refine ⟨2754508947730408544892139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14690714387895512239424741 2754508947730408544892139)
                      ·
                        rfl

theorem cell23_5364387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_5364387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364387 prefixEnd_5364387 := by exact prefixLift 5364387
  have htrace : WordTrace (prefixWord ++ tailWord_5364387) baseStart_5364387 baseEnd_5364387 := by
    simpa [prefixWord, tailWord_5364387, baseEnd_5364387] using wordTrace_append hprefix tailTrace_5364387
  have hstable : (prefixWord ++ tailWord_5364387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364387).length < 2 ^ (prefixWord ++ tailWord_5364387).sum := by decide
  have hdescent : baseEnd_5364387 < baseStart_5364387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364398 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_5364398 : Nat := 118140960795 + 5364398 * 2 ^ 59
def prefixEnd_5364398 : Nat := 4983230072969 + 3 ^ 40 * 5364398 * 2
def baseEnd_5364398 : Nat := 2754514596017608001854589

theorem tailTrace_5364398 : CollatzResearch.WordTrace tailWord_5364398 prefixEnd_5364398 2754514596017608001854589 := by
  unfold tailWord_5364398
  simp only [CollatzResearch.WordTrace]
  refine ⟨24456958602463710885473731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130437112546473124722526565 24456958602463710885473731)
  ·
    refine ⟨36685437903695566328210597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24456958602463710885473731 36685437903695566328210597)
    ·
      refine ⟨6878519606942918686539487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36685437903695566328210597 6878519606942918686539487)
      ·
        refine ⟨10317779410414378029809231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6878519606942918686539487 10317779410414378029809231)
        ·
          refine ⟨15476669115621567044713847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10317779410414378029809231 15476669115621567044713847)
          ·
            refine ⟨23215003673432350567070771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15476669115621567044713847 23215003673432350567070771)
            ·
              refine ⟨34822505510148525850606157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23215003673432350567070771 34822505510148525850606157)
              ·
                refine ⟨13058439566305697193977309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34822505510148525850606157 13058439566305697193977309)
                ·
                  refine ⟨4896914837364636447741491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13058439566305697193977309 4896914837364636447741491)
                  ·
                    refine ⟨7345372256046954671612237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4896914837364636447741491 7345372256046954671612237)
                    ·
                      refine ⟨2754514596017608001854589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7345372256046954671612237 2754514596017608001854589)
                      ·
                        rfl

theorem cell23_5364398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_5364398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364398 prefixEnd_5364398 := by exact prefixLift 5364398
  have htrace : WordTrace (prefixWord ++ tailWord_5364398) baseStart_5364398 baseEnd_5364398 := by
    simpa [prefixWord, tailWord_5364398, baseEnd_5364398] using wordTrace_append hprefix tailTrace_5364398
  have hstable : (prefixWord ++ tailWord_5364398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364398).length < 2 ^ (prefixWord ++ tailWord_5364398).sum := by decide
  have hdescent : baseEnd_5364398 < baseStart_5364398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364444 : List Nat := [2, 2, 5, 1, 1, 1, 11]
def baseStart_5364444 : Nat := 118140960795 + 5364444 * 2 ^ 59
def prefixEnd_5364444 : Nat := 4983230072969 + 3 ^ 40 * 5364444 * 2
def baseEnd_5364444 : Nat := 34006644643552034838017

theorem tailTrace_5364444 : CollatzResearch.WordTrace tailWord_5364444 prefixEnd_5364444 34006644643552034838017 := by
  unfold tailWord_5364444
  simp only [CollatzResearch.WordTrace]
  refine ⟨97828673288771518469982193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130438231051695357959976257 97828673288771518469982193)
  ·
    refine ⟨73371504966578638852486645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97828673288771518469982193 73371504966578638852486645)
    ·
      refine ⟨6878578590616747392420623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73371504966578638852486645 6878578590616747392420623)
      ·
        refine ⟨10317867885925121088630935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6878578590616747392420623 10317867885925121088630935)
        ·
          refine ⟨15476801828887681632946403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10317867885925121088630935 15476801828887681632946403)
          ·
            refine ⟨23215202743331522449419605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15476801828887681632946403 23215202743331522449419605)
            ·
              refine ⟨34006644643552034838017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23215202743331522449419605 34006644643552034838017)
              ·
                rfl

theorem cell23_5364444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 11].length) (baseStart_5364444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364444 prefixEnd_5364444 := by exact prefixLift 5364444
  have htrace : WordTrace (prefixWord ++ tailWord_5364444) baseStart_5364444 baseEnd_5364444 := by
    simpa [prefixWord, tailWord_5364444, baseEnd_5364444] using wordTrace_append hprefix tailTrace_5364444
  have hstable : (prefixWord ++ tailWord_5364444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364444).length < 2 ^ (prefixWord ++ tailWord_5364444).sum := by decide
  have hdescent : baseEnd_5364444 < baseStart_5364444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364524 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 4]
def baseStart_5364524 : Nat := 118140960795 + 5364524 * 2 ^ 59
def prefixEnd_5364524 : Nat := 4983230072969 + 3 ^ 40 * 5364524 * 2
def baseEnd_5364524 : Nat := 2754579294580074508879009

theorem tailTrace_5364524 : CollatzResearch.WordTrace tailWord_5364524 prefixEnd_5364524 2754579294580074508879009 := by
  unfold tailWord_5364524
  simp only [CollatzResearch.WordTrace]
  refine ⟨97830132208626605301438313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130440176278168807068584417 97830132208626605301438313)
  ·
    refine ⟨73372599156469953976078735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97830132208626605301438313 73372599156469953976078735)
    ·
      refine ⟨110058898734704930964118103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73372599156469953976078735 110058898734704930964118103)
      ·
        refine ⟨165088348102057396446177155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110058898734704930964118103 165088348102057396446177155)
        ·
          refine ⟨247632522153086094669265733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165088348102057396446177155 247632522153086094669265733)
          ·
            refine ⟨46431097903703642750487325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 247632522153086094669265733 46431097903703642750487325)
            ·
              refine ⟨17411661713888866031432747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46431097903703642750487325 17411661713888866031432747)
              ·
                refine ⟨26117492570833299047149121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17411661713888866031432747 26117492570833299047149121)
                ·
                  refine ⟨19588119428124974285361841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26117492570833299047149121 19588119428124974285361841)
                  ·
                    refine ⟨14691089571093730714021381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19588119428124974285361841 14691089571093730714021381)
                    ·
                      refine ⟨2754579294580074508879009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14691089571093730714021381 2754579294580074508879009)
                      ·
                        rfl

theorem cell23_5364524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_5364524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364524 prefixEnd_5364524 := by exact prefixLift 5364524
  have htrace : WordTrace (prefixWord ++ tailWord_5364524) baseStart_5364524 baseEnd_5364524 := by
    simpa [prefixWord, tailWord_5364524, baseEnd_5364524] using wordTrace_append hprefix tailTrace_5364524
  have hstable : (prefixWord ++ tailWord_5364524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364524).length < 2 ^ (prefixWord ++ tailWord_5364524).sum := by decide
  have hdescent : baseEnd_5364524 < baseStart_5364524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364618 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5364618 : Nat := 118140960795 + 5364618 * 2 ^ 59
def prefixEnd_5364618 : Nat := 4983230072969 + 3 ^ 40 * 5364618 * 2
def baseEnd_5364618 : Nat := 2754627561761597141103577

theorem tailTrace_5364618 : CollatzResearch.WordTrace tailWord_5364618 prefixEnd_5364618 2754627561761597141103577 := by
  unfold tailWord_5364618
  simp only [CollatzResearch.WordTrace]
  refine ⟨48915923219728166164199627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130442461919275109771199005 48915923219728166164199627)
  ·
    refine ⟨73373884829592249246299441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48915923219728166164199627 73373884829592249246299441)
    ·
      refine ⟨55030413622194186934724581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73373884829592249246299441 55030413622194186934724581)
      ·
        refine ⟨10318202554161410050260859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55030413622194186934724581 10318202554161410050260859)
        ·
          refine ⟨15477303831242115075391289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10318202554161410050260859 15477303831242115075391289)
          ·
            refine ⟨11607977873431586306543467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15477303831242115075391289 11607977873431586306543467)
            ·
              refine ⟨17411966810147379459815201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11607977873431586306543467 17411966810147379459815201)
              ·
                refine ⟨13058975107610534594861401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17411966810147379459815201 13058975107610534594861401)
                ·
                  refine ⟨9794231330707900946146051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13058975107610534594861401 9794231330707900946146051)
                  ·
                    refine ⟨14691346996061851419219077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9794231330707900946146051 14691346996061851419219077)
                    ·
                      refine ⟨2754627561761597141103577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14691346996061851419219077 2754627561761597141103577)
                      ·
                        rfl

theorem cell23_5364618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5364618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364618 prefixEnd_5364618 := by exact prefixLift 5364618
  have htrace : WordTrace (prefixWord ++ tailWord_5364618) baseStart_5364618 baseEnd_5364618 := by
    simpa [prefixWord, tailWord_5364618, baseEnd_5364618] using wordTrace_append hprefix tailTrace_5364618
  have hstable : (prefixWord ++ tailWord_5364618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364618).length < 2 ^ (prefixWord ++ tailWord_5364618).sum := by decide
  have hdescent : baseEnd_5364618 < baseStart_5364618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364765 : List Nat := [1, 4, 2, 2, 3, 2, 2, 7]
def baseStart_5364765 : Nat := 118140960795 + 5364765 * 2 ^ 59
def prefixEnd_5364765 : Nat := 4983230072969 + 3 ^ 40 * 5364765 * 2
def baseEnd_5364765 : Nat := 102026038645104002443163

theorem tailTrace_5364765 : CollatzResearch.WordTrace tailWord_5364765 prefixEnd_5364765 102026038645104002443163 := by
  unfold tailWord_5364765
  simp only [CollatzResearch.WordTrace]
  refine ⟨195669054409380108762399749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130446036272920072508266499 195669054409380108762399749)
  ·
    refine ⟨36687947701758770392949953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195669054409380108762399749 36687947701758770392949953)
    ·
      refine ⟨27515960776319077794712465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36687947701758770392949953 27515960776319077794712465)
      ·
        refine ⟨20636970582239308346034349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27515960776319077794712465 20636970582239308346034349)
        ·
          refine ⟨7738863968339740629762881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20636970582239308346034349 7738863968339740629762881)
          ·
            refine ⟨5804147976254805472322161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7738863968339740629762881 5804147976254805472322161)
            ·
              refine ⟨4353110982191104104241621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5804147976254805472322161 4353110982191104104241621)
              ·
                refine ⟨102026038645104002443163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4353110982191104104241621 102026038645104002443163)
                ·
                  rfl

theorem cell23_5364765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 7].length) (baseStart_5364765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364765 prefixEnd_5364765 := by exact prefixLift 5364765
  have htrace : WordTrace (prefixWord ++ tailWord_5364765) baseStart_5364765 baseEnd_5364765 := by
    simpa [prefixWord, tailWord_5364765, baseEnd_5364765] using wordTrace_append hprefix tailTrace_5364765
  have hstable : (prefixWord ++ tailWord_5364765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364765).length < 2 ^ (prefixWord ++ tailWord_5364765).sum := by decide
  have hdescent : baseEnd_5364765 < baseStart_5364765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364771 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 5]
def baseStart_5364771 : Nat := 118140960795 + 5364771 * 2 ^ 59
def prefixEnd_5364771 : Nat := 4983230072969 + 3 ^ 40 * 5364771 * 2
def baseEnd_5364771 : Nat := 2754706124301735042490373

theorem tailTrace_5364771 : CollatzResearch.WordTrace tailWord_5364771 prefixEnd_5364771 2754706124301735042490373 := by
  unfold tailWord_5364771
  simp only [CollatzResearch.WordTrace]
  refine ⟨195669273247358371787118167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130446182164905581191412111 195669273247358371787118167)
  ·
    refine ⟨293503909871037557680677251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195669273247358371787118167 293503909871037557680677251)
    ·
      refine ⟨440255864806556336521015877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293503909871037557680677251 440255864806556336521015877)
      ·
        refine ⟨82547974651229313097690477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 440255864806556336521015877 82547974651229313097690477)
        ·
          refine ⟨30955490494210992411633929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82547974651229313097690477 30955490494210992411633929)
          ·
            refine ⟨23216617870658244308725447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30955490494210992411633929 23216617870658244308725447)
            ·
              refine ⟨34824926805987366463088171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23216617870658244308725447 34824926805987366463088171)
              ·
                refine ⟨52237390208981049694632257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34824926805987366463088171 52237390208981049694632257)
                ·
                  refine ⟨39178042656735787270974193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52237390208981049694632257 39178042656735787270974193)
                  ·
                    refine ⟨29383531992551840453230645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39178042656735787270974193 29383531992551840453230645)
                    ·
                      refine ⟨2754706124301735042490373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29383531992551840453230645 2754706124301735042490373)
                      ·
                        rfl

theorem cell23_5364771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_5364771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364771 prefixEnd_5364771 := by exact prefixLift 5364771
  have htrace : WordTrace (prefixWord ++ tailWord_5364771) baseStart_5364771 baseEnd_5364771 := by
    simpa [prefixWord, tailWord_5364771, baseEnd_5364771] using wordTrace_append hprefix tailTrace_5364771
  have hstable : (prefixWord ++ tailWord_5364771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364771).length < 2 ^ (prefixWord ++ tailWord_5364771).sum := by decide
  have hdescent : baseEnd_5364771 < baseStart_5364771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364785 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 1, 3, 2]
def baseStart_5364785 : Nat := 118140960795 + 5364785 * 2 ^ 59
def prefixEnd_5364785 : Nat := 4983230072969 + 3 ^ 40 * 5364785 * 2
def baseEnd_5364785 : Nat := 2754713313030897987715309

theorem tailTrace_5364785 : CollatzResearch.WordTrace tailWord_5364785 prefixEnd_5364785 2754713313030897987715309 := by
  unfold tailWord_5364785
  simp only [CollatzResearch.WordTrace]
  refine ⟨195669783869307652178127809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130446522579538434785418539 195669783869307652178127809)
  ·
    refine ⟨146752337901980739133595857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195669783869307652178127809 146752337901980739133595857)
    ·
      refine ⟨110064253426485554350196893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146752337901980739133595857 110064253426485554350196893)
      ·
        refine ⟨41274095034932082881323835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110064253426485554350196893 41274095034932082881323835)
        ·
          refine ⟨61911142552398124321985753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41274095034932082881323835 61911142552398124321985753)
          ·
            refine ⟨46433356914298593241489315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61911142552398124321985753 46433356914298593241489315)
            ·
              refine ⟨69650035371447889862233973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46433356914298593241489315 69650035371447889862233973)
              ·
                refine ⟨6529690816073239674584435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69650035371447889862233973 6529690816073239674584435)
                ·
                  refine ⟨9794536224109859511876653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6529690816073239674584435 9794536224109859511876653)
                  ·
                    refine ⟨3672951084041197316953745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9794536224109859511876653 3672951084041197316953745)
                    ·
                      refine ⟨2754713313030897987715309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3672951084041197316953745 2754713313030897987715309)
                      ·
                        rfl

theorem cell23_5364785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_5364785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364785 prefixEnd_5364785 := by exact prefixLift 5364785
  have htrace : WordTrace (prefixWord ++ tailWord_5364785) baseStart_5364785 baseEnd_5364785 := by
    simpa [prefixWord, tailWord_5364785, baseEnd_5364785] using wordTrace_append hprefix tailTrace_5364785
  have hstable : (prefixWord ++ tailWord_5364785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364785).length < 2 ^ (prefixWord ++ tailWord_5364785).sum := by decide
  have hdescent : baseEnd_5364785 < baseStart_5364785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364818 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_5364818 : Nat := 118140960795 + 5364818 * 2 ^ 59
def prefixEnd_5364818 : Nat := 4983230072969 + 3 ^ 40 * 5364818 * 2
def baseEnd_5364818 : Nat := 2754730257892496358602657

theorem tailTrace_5364818 : CollatzResearch.WordTrace tailWord_5364818 prefixEnd_5364818 2754730257892496358602657 := by
  unfold tailWord_5364818
  simp only [CollatzResearch.WordTrace]
  refine ⟨48917746869547024703519777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130447324985458732542719405 48917746869547024703519777)
  ·
    refine ⟨36688310152160268527639833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48917746869547024703519777 36688310152160268527639833)
    ·
      refine ⟨27516232614120201395729875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36688310152160268527639833 27516232614120201395729875)
      ·
        refine ⟨41274348921180302093594813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27516232614120201395729875 41274348921180302093594813)
        ·
          refine ⟨15477880845442613285098055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41274348921180302093594813 15477880845442613285098055)
          ·
            refine ⟨23216821268163919927647083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15477880845442613285098055 23216821268163919927647083)
            ·
              refine ⟨34825231902245879891470625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23216821268163919927647083 34825231902245879891470625)
              ·
                refine ⟨26118923926684409918602969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34825231902245879891470625 26118923926684409918602969)
                ·
                  refine ⟨19589192945013307438952227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26118923926684409918602969 19589192945013307438952227)
                  ·
                    refine ⟨29383789417519961158428341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19589192945013307438952227 29383789417519961158428341)
                    ·
                      refine ⟨2754730257892496358602657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29383789417519961158428341 2754730257892496358602657)
                      ·
                        rfl

theorem cell23_5364818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_5364818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364818 prefixEnd_5364818 := by exact prefixLift 5364818
  have htrace : WordTrace (prefixWord ++ tailWord_5364818) baseStart_5364818 baseEnd_5364818 := by
    simpa [prefixWord, tailWord_5364818, baseEnd_5364818] using wordTrace_append hprefix tailTrace_5364818
  have hstable : (prefixWord ++ tailWord_5364818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364818).length < 2 ^ (prefixWord ++ tailWord_5364818).sum := by decide
  have hdescent : baseEnd_5364818 < baseStart_5364818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364821 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 9]
def baseStart_5364821 : Nat := 118140960795 + 5364821 * 2 ^ 59
def prefixEnd_5364821 : Nat := 4983230072969 + 3 ^ 40 * 5364821 * 2
def baseEnd_5364821 : Nat := 306081310926051094096127

theorem tailTrace_5364821 : CollatzResearch.WordTrace tailWord_5364821 prefixEnd_5364821 306081310926051094096127 := by
  unfold tailWord_5364821
  simp only [CollatzResearch.WordTrace]
  refine ⟨195671096897177230326438317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130447397931451486884292211 195671096897177230326438317)
  ·
    refine ⟨73376661336441461372414369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195671096897177230326438317 73376661336441461372414369)
    ·
      refine ⟨55032496002331096029310777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73376661336441461372414369 55032496002331096029310777)
      ·
        refine ⟨41274372001748322021983083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55032496002331096029310777 41274372001748322021983083)
        ·
          refine ⟨61911558002622483032974625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41274372001748322021983083 61911558002622483032974625)
          ·
            refine ⟨46433668501966862274730969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61911558002622483032974625 46433668501966862274730969)
            ·
              refine ⟨34825251376475146706048227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46433668501966862274730969 34825251376475146706048227)
              ·
                refine ⟨52237877064712720059072341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34825251376475146706048227 52237877064712720059072341)
                ·
                  refine ⟨306081310926051094096127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52237877064712720059072341 306081310926051094096127)
                  ·
                    rfl

theorem cell23_5364821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_5364821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364821 prefixEnd_5364821 := by exact prefixLift 5364821
  have htrace : WordTrace (prefixWord ++ tailWord_5364821) baseStart_5364821 baseEnd_5364821 := by
    simpa [prefixWord, tailWord_5364821, baseEnd_5364821] using wordTrace_append hprefix tailTrace_5364821
  have hstable : (prefixWord ++ tailWord_5364821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364821).length < 2 ^ (prefixWord ++ tailWord_5364821).sum := by decide
  have hdescent : baseEnd_5364821 < baseStart_5364821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364848 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 3]
def baseStart_5364848 : Nat := 118140960795 + 5364848 * 2 ^ 59
def prefixEnd_5364848 : Nat := 4983230072969 + 3 ^ 40 * 5364848 * 2
def baseEnd_5364848 : Nat := 2754745662312131241227519

theorem tailTrace_5364848 : CollatzResearch.WordTrace tailWord_5364848 prefixEnd_5364848 2754745662312131241227519 := by
  unfold tailWord_5364848
  simp only [CollatzResearch.WordTrace]
  refine ⟨97836040834039706968835599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130448054445386275958447465 97836040834039706968835599)
  ·
    refine ⟨146754061251059560453253399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97836040834039706968835599 146754061251059560453253399)
    ·
      refine ⟨220131091876589340679880099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146754061251059560453253399 220131091876589340679880099)
      ·
        refine ⟨330196637814884011019820149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220131091876589340679880099 330196637814884011019820149)
        ·
          refine ⟨30955934795145376033108139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 330196637814884011019820149 30955934795145376033108139)
          ·
            refine ⟨46433902192718064049662209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30955934795145376033108139 46433902192718064049662209)
            ·
              refine ⟨34825426644538548037246657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46433902192718064049662209 34825426644538548037246657)
              ·
                refine ⟨26119069983403911027934993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34825426644538548037246657 26119069983403911027934993)
                ·
                  refine ⟨19589302487552933270951245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26119069983403911027934993 19589302487552933270951245)
                  ·
                    refine ⟨7345988432832349976606717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19589302487552933270951245 7345988432832349976606717)
                    ·
                      refine ⟨2754745662312131241227519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7345988432832349976606717 2754745662312131241227519)
                      ·
                        rfl

theorem cell23_5364848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 3].length) (baseStart_5364848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364848 prefixEnd_5364848 := by exact prefixLift 5364848
  have htrace : WordTrace (prefixWord ++ tailWord_5364848) baseStart_5364848 baseEnd_5364848 := by
    simpa [prefixWord, tailWord_5364848, baseEnd_5364848] using wordTrace_append hprefix tailTrace_5364848
  have hstable : (prefixWord ++ tailWord_5364848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364848).length < 2 ^ (prefixWord ++ tailWord_5364848).sum := by decide
  have hdescent : baseEnd_5364848 < baseStart_5364848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364865 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_5364865 : Nat := 118140960795 + 5364865 * 2 ^ 59
def prefixEnd_5364865 : Nat := 4983230072969 + 3 ^ 40 * 5364865 * 2
def baseEnd_5364865 : Nat := 2754754391483257674714941

theorem tailTrace_5364865 : CollatzResearch.WordTrace tailWord_5364865 prefixEnd_5364865 2754754391483257674714941 := by
  unfold tailWord_5364865
  simp only [CollatzResearch.WordTrace]
  refine ⟨195672701709017825841040049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130448467806011883894026699 195672701709017825841040049)
  ·
    refine ⟨146754526281763369380780037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195672701709017825841040049 146754526281763369380780037)
    ·
      refine ⟨27516473677830631758896257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146754526281763369380780037 27516473677830631758896257)
      ·
        refine ⟨20637355258372973819172193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27516473677830631758896257 20637355258372973819172193)
        ·
          refine ⟨15478016443779730364379145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20637355258372973819172193 15478016443779730364379145)
          ·
            refine ⟨11608512332834797773284359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15478016443779730364379145 11608512332834797773284359)
            ·
              refine ⟨17412768499252196659926539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11608512332834797773284359 17412768499252196659926539)
              ·
                refine ⟨26119152748878294989889809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17412768499252196659926539 26119152748878294989889809)
                ·
                  refine ⟨19589364561658721242417357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26119152748878294989889809 19589364561658721242417357)
                  ·
                    refine ⟨7346011710622020465906509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19589364561658721242417357 7346011710622020465906509)
                    ·
                      refine ⟨2754754391483257674714941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346011710622020465906509 2754754391483257674714941)
                      ·
                        rfl

theorem cell23_5364865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_5364865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364865 prefixEnd_5364865 := by exact prefixLift 5364865
  have htrace : WordTrace (prefixWord ++ tailWord_5364865) baseStart_5364865 baseEnd_5364865 := by
    simpa [prefixWord, tailWord_5364865, baseEnd_5364865] using wordTrace_append hprefix tailTrace_5364865
  have hstable : (prefixWord ++ tailWord_5364865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364865).length < 2 ^ (prefixWord ++ tailWord_5364865).sum := by decide
  have hdescent : baseEnd_5364865 < baseStart_5364865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364891 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 5]
def baseStart_5364891 : Nat := 118140960795 + 5364891 * 2 ^ 59
def prefixEnd_5364891 : Nat := 4983230072969 + 3 ^ 40 * 5364891 * 2
def baseEnd_5364891 : Nat := 2754767741980274572989821

theorem tailTrace_5364891 : CollatzResearch.WordTrace tailWord_5364891 prefixEnd_5364891 2754767741980274572989821 := by
  unfold tailWord_5364891
  simp only [CollatzResearch.WordTrace]
  refine ⟨195673650006923632281486527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130449100004615754854324351 195673650006923632281486527)
  ·
    refine ⟨293510475010385448422229791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195673650006923632281486527 293510475010385448422229791)
    ·
      refine ⟨440265712515578172633344687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293510475010385448422229791 440265712515578172633344687)
      ·
        refine ⟨660398568773367258950017031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440265712515578172633344687 660398568773367258950017031)
        ·
          refine ⟨990597853160050888425025547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660398568773367258950017031 990597853160050888425025547)
          ·
            refine ⟨1485896779740076332637538321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990597853160050888425025547 1485896779740076332637538321)
            ·
              refine ⟨1114422584805057249478153741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485896779740076332637538321 1114422584805057249478153741)
              ·
                refine ⟨417908469301896468554307653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1114422584805057249478153741 417908469301896468554307653)
                ·
                  refine ⟨78357837994105587853932685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417908469301896468554307653 78357837994105587853932685)
                  ·
                    refine ⟨29384189247789595445224757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78357837994105587853932685 29384189247789595445224757)
                    ·
                      refine ⟨2754767741980274572989821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29384189247789595445224757 2754767741980274572989821)
                      ·
                        rfl

theorem cell23_5364891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_5364891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364891 prefixEnd_5364891 := by exact prefixLift 5364891
  have htrace : WordTrace (prefixWord ++ tailWord_5364891) baseStart_5364891 baseEnd_5364891 := by
    simpa [prefixWord, tailWord_5364891, baseEnd_5364891] using wordTrace_append hprefix tailTrace_5364891
  have hstable : (prefixWord ++ tailWord_5364891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364891).length < 2 ^ (prefixWord ++ tailWord_5364891).sum := by decide
  have hdescent : baseEnd_5364891 < baseStart_5364891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364949 : List Nat := [1, 3, 2, 4, 1, 1, 3, 3, 1, 4]
def baseStart_5364949 : Nat := 118140960795 + 5364949 * 2 ^ 59
def prefixEnd_5364949 : Nat := 4983230072969 + 3 ^ 40 * 5364949 * 2
def baseEnd_5364949 : Nat := 918265841286078448688185

theorem tailTrace_5364949 : CollatzResearch.WordTrace tailWord_5364949 prefixEnd_5364949 918265841286078448688185 := by
  unfold tailWord_5364949
  simp only [CollatzResearch.WordTrace]
  refine ⟨195675765440713508187097901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130450510293809005458065267 195675765440713508187097901)
  ·
    refine ⟨73378412040267565570161713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195675765440713508187097901 73378412040267565570161713)
    ·
      refine ⟨55033809030200674177621285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73378412040267565570161713 55033809030200674177621285)
      ·
        refine ⟨10318839193162626408303991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55033809030200674177621285 10318839193162626408303991)
        ·
          refine ⟨15478258789743939612455987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10318839193162626408303991 15478258789743939612455987)
          ·
            refine ⟨23217388184615909418683981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15478258789743939612455987 23217388184615909418683981)
            ·
              refine ⟨8706520569230966032006493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23217388184615909418683981 8706520569230966032006493)
              ·
                refine ⟨3264945213461612262002435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8706520569230966032006493 3264945213461612262002435)
                ·
                  refine ⟨4897417820192418393003653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264945213461612262002435 4897417820192418393003653)
                  ·
                    refine ⟨918265841286078448688185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4897417820192418393003653 918265841286078448688185)
                    ·
                      rfl

theorem cell23_5364949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_5364949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364949 prefixEnd_5364949 := by exact prefixLift 5364949
  have htrace : WordTrace (prefixWord ++ tailWord_5364949) baseStart_5364949 baseEnd_5364949 := by
    simpa [prefixWord, tailWord_5364949, baseEnd_5364949] using wordTrace_append hprefix tailTrace_5364949
  have hstable : (prefixWord ++ tailWord_5364949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364949).length < 2 ^ (prefixWord ++ tailWord_5364949).sum := by decide
  have hdescent : baseEnd_5364949 < baseStart_5364949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364972 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 3]
def baseStart_5364972 : Nat := 118140960795 + 5364972 * 2 ^ 59
def prefixEnd_5364972 : Nat := 4983230072969 + 3 ^ 40 * 5364972 * 2
def baseEnd_5364972 : Nat := 2754809333913288756076949

theorem tailTrace_5364972 : CollatzResearch.WordTrace tailWord_5364972 prefixEnd_5364972 2754809333913288756076949 := by
  unfold tailWord_5364972
  simp only [CollatzResearch.WordTrace]
  refine ⟨97838302159815091557592585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130451069546420122076790113 97838302159815091557592585)
  ·
    refine ⟨73378726619861318668194439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97838302159815091557592585 73378726619861318668194439)
    ·
      refine ⟨110068089929791978002291659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73378726619861318668194439 110068089929791978002291659)
      ·
        refine ⟨165102134894687967003437489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110068089929791978002291659 165102134894687967003437489)
        ·
          refine ⟨123826601171015975252578117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165102134894687967003437489 123826601171015975252578117)
          ·
            refine ⟨23217487719565495359858397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123826601171015975252578117 23217487719565495359858397)
            ·
              refine ⟨8706557894837060759946899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23217487719565495359858397 8706557894837060759946899)
              ·
                refine ⟨13059836842255591139920349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8706557894837060759946899 13059836842255591139920349)
                ·
                  refine ⟨4897438815845846677470131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13059836842255591139920349 4897438815845846677470131)
                  ·
                    refine ⟨7346158223768770016205197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4897438815845846677470131 7346158223768770016205197)
                    ·
                      refine ⟨2754809333913288756076949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346158223768770016205197 2754809333913288756076949)
                      ·
                        rfl

theorem cell23_5364972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 3].length) (baseStart_5364972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364972 prefixEnd_5364972 := by exact prefixLift 5364972
  have htrace : WordTrace (prefixWord ++ tailWord_5364972) baseStart_5364972 baseEnd_5364972 := by
    simpa [prefixWord, tailWord_5364972, baseEnd_5364972] using wordTrace_append hprefix tailTrace_5364972
  have hstable : (prefixWord ++ tailWord_5364972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364972).length < 2 ^ (prefixWord ++ tailWord_5364972).sum := by decide
  have hdescent : baseEnd_5364972 < baseStart_5364972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364982 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_5364982 : Nat := 118140960795 + 5364982 * 2 ^ 59
def prefixEnd_5364982 : Nat := 4983230072969 + 3 ^ 40 * 5364982 * 2
def baseEnd_5364982 : Nat := 2754814468719833716951903

theorem tailTrace_5364982 : CollatzResearch.WordTrace tailWord_5364982 prefixEnd_5364982 2754814468719833716951903 := by
  unfold tailWord_5364982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12229810565599622176440575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130451312699729303215366133 12229810565599622176440575)
  ·
    refine ⟨18344715848399433264660863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12229810565599622176440575 18344715848399433264660863)
    ·
      refine ⟨27517073772599149896991295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18344715848399433264660863 27517073772599149896991295)
      ·
        refine ⟨41275610658898724845486943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27517073772599149896991295 41275610658898724845486943)
        ·
          refine ⟨61913415988348087268230415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41275610658898724845486943 61913415988348087268230415)
          ·
            refine ⟨92870123982522130902345623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61913415988348087268230415 92870123982522130902345623)
            ·
              refine ⟨139305185973783196353518435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92870123982522130902345623 139305185973783196353518435)
              ·
                refine ⟨208957778960674794530277653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139305185973783196353518435 208957778960674794530277653)
                ·
                  refine ⟨9794895888781630993606765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 208957778960674794530277653 9794895888781630993606765)
                  ·
                    refine ⟨3673085958293111622602537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9794895888781630993606765 3673085958293111622602537)
                    ·
                      refine ⟨2754814468719833716951903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3673085958293111622602537 2754814468719833716951903)
                      ·
                        rfl

theorem cell23_5364982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_5364982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364982 prefixEnd_5364982 := by exact prefixLift 5364982
  have htrace : WordTrace (prefixWord ++ tailWord_5364982) baseStart_5364982 baseEnd_5364982 := by
    simpa [prefixWord, tailWord_5364982, baseEnd_5364982] using wordTrace_append hprefix tailTrace_5364982
  have hstable : (prefixWord ++ tailWord_5364982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364982).length < 2 ^ (prefixWord ++ tailWord_5364982).sum := by decide
  have hdescent : baseEnd_5364982 < baseStart_5364982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5364995 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 4]
def baseStart_5364995 : Nat := 118140960795 + 5364995 * 2 ^ 59
def prefixEnd_5364995 : Nat := 4983230072969 + 3 ^ 40 * 5364995 * 2
def baseEnd_5364995 : Nat := 2754821143968342166089343

theorem tailTrace_5364995 : CollatzResearch.WordTrace tailWord_5364995 prefixEnd_5364995 2754821143968342166089343 := by
  unfold tailWord_5364995
  simp only [CollatzResearch.WordTrace]
  refine ⟨195677443198546858043272439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130451628799031238695514959 195677443198546858043272439)
  ·
    refine ⟨293516164797820287064908659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195677443198546858043272439 293516164797820287064908659)
    ·
      refine ⟨440274247196730430597362989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293516164797820287064908659 440274247196730430597362989)
      ·
        refine ⟨165102842698773911474011121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 440274247196730430597362989 165102842698773911474011121)
        ·
          refine ⟨123827132024080433605508341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165102842698773911474011121 123827132024080433605508341)
          ·
            refine ⟨11608793627257540650516407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123827132024080433605508341 11608793627257540650516407)
            ·
              refine ⟨17413190440886310975774611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11608793627257540650516407 17413190440886310975774611)
              ·
                refine ⟨26119785661329466463661917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17413190440886310975774611 26119785661329466463661917)
                ·
                  refine ⟨9794919622998549923873219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26119785661329466463661917 9794919622998549923873219)
                  ·
                    refine ⟨14692379434497824885809829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9794919622998549923873219 14692379434497824885809829)
                    ·
                      refine ⟨2754821143968342166089343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14692379434497824885809829 2754821143968342166089343)
                      ·
                        rfl

theorem cell23_5364995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_5364995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5364995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5364995 prefixEnd_5364995 := by exact prefixLift 5364995
  have htrace : WordTrace (prefixWord ++ tailWord_5364995) baseStart_5364995 baseEnd_5364995 := by
    simpa [prefixWord, tailWord_5364995, baseEnd_5364995] using wordTrace_append hprefix tailTrace_5364995
  have hstable : (prefixWord ++ tailWord_5364995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5364995).length < 2 ^ (prefixWord ++ tailWord_5364995).sum := by decide
  have hdescent : baseEnd_5364995 < baseStart_5364995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5364995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365018 : List Nat := [3, 1, 1, 3, 3, 12]
def baseStart_5365018 : Nat := 118140960795 + 5365018 * 2 ^ 59
def prefixEnd_5365018 : Nat := 4983230072969 + 3 ^ 40 * 5365018 * 2
def baseEnd_5365018 : Nat := 11336761127668294551859

theorem tailTrace_5365018 : CollatzResearch.WordTrace tailWord_5365018 prefixEnd_5365018 11336761127668294551859 := by
  unfold tailWord_5365018
  simp only [CollatzResearch.WordTrace]
  refine ⟨48919570519365883242839927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130452188051642355314239805 48919570519365883242839927)
  ·
    refine ⟨73379355779048824864259891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48919570519365883242839927 73379355779048824864259891)
    ·
      refine ⟨110069033668573237296389837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73379355779048824864259891 110069033668573237296389837)
      ·
        refine ⟨41275887625714963986146189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110069033668573237296389837 41275887625714963986146189)
        ·
          refine ⟨15478457859643111494804821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41275887625714963986146189 15478457859643111494804821)
          ·
            refine ⟨11336761127668294551859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 15478457859643111494804821 11336761127668294551859)
            ·
              rfl

theorem cell23_5365018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 12].length) (baseStart_5365018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365018 prefixEnd_5365018 := by exact prefixLift 5365018
  have htrace : WordTrace (prefixWord ++ tailWord_5365018) baseStart_5365018 baseEnd_5365018 := by
    simpa [prefixWord, tailWord_5365018, baseEnd_5365018] using wordTrace_append hprefix tailTrace_5365018
  have hstable : (prefixWord ++ tailWord_5365018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365018).length < 2 ^ (prefixWord ++ tailWord_5365018).sum := by decide
  have hdescent : baseEnd_5365018 < baseStart_5365018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365023 : List Nat := [1, 1, 2, 4, 4, 2, 2, 2, 1, 1, 3]
def baseStart_5365023 : Nat := 118140960795 + 5365023 * 2 ^ 59
def prefixEnd_5365023 : Nat := 4983230072969 + 3 ^ 40 * 5365023 * 2
def baseEnd_5365023 : Nat := 2754835521426668056539215

theorem tailTrace_5365023 : CollatzResearch.WordTrace tailWord_5365023 prefixEnd_5365023 2754835521426668056539215 := by
  unfold tailWord_5365023
  simp only [CollatzResearch.WordTrace]
  refine ⟨195678464442445418825291723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130452309628296945883527815 195678464442445418825291723)
  ·
    refine ⟨293517696663668128237937585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195678464442445418825291723 293517696663668128237937585)
    ·
      refine ⟨220138272497751096178453189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293517696663668128237937585 220138272497751096178453189)
      ·
        refine ⟨41275926093328330533459973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220138272497751096178453189 41275926093328330533459973)
        ·
          refine ⟨7739236142499061975023745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41275926093328330533459973 7739236142499061975023745)
          ·
            refine ⟨5804427106874296481267809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7739236142499061975023745 5804427106874296481267809)
            ·
              refine ⟨4353320330155722360950857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5804427106874296481267809 4353320330155722360950857)
              ·
                refine ⟨3264990247616791770713143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4353320330155722360950857 3264990247616791770713143)
                ·
                  refine ⟨4897485371425187656069715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3264990247616791770713143 4897485371425187656069715)
                  ·
                    refine ⟨7346228057137781484104573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4897485371425187656069715 7346228057137781484104573)
                    ·
                      refine ⟨2754835521426668056539215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346228057137781484104573 2754835521426668056539215)
                      ·
                        rfl

theorem cell23_5365023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_5365023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365023 prefixEnd_5365023 := by exact prefixLift 5365023
  have htrace : WordTrace (prefixWord ++ tailWord_5365023) baseStart_5365023 baseEnd_5365023 := by
    simpa [prefixWord, tailWord_5365023, baseEnd_5365023] using wordTrace_append hprefix tailTrace_5365023
  have hstable : (prefixWord ++ tailWord_5365023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365023).length < 2 ^ (prefixWord ++ tailWord_5365023).sum := by decide
  have hdescent : baseEnd_5365023 < baseStart_5365023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365032 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_5365032 : Nat := 118140960795 + 5365032 * 2 ^ 59
def prefixEnd_5365032 : Nat := 4983230072969 + 3 ^ 40 * 5365032 * 2
def baseEnd_5365032 : Nat := 2754840142752558521326673

theorem tailTrace_5365032 : CollatzResearch.WordTrace tailWord_5365032 prefixEnd_5365032 2754840142752558521326673 := by
  unfold tailWord_5365032
  simp only [CollatzResearch.WordTrace]
  refine ⟨97839396349706406681184675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130452528466275208908246233 97839396349706406681184675)
  ·
    refine ⟨146759094524559610021777013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97839396349706406681184675 146759094524559610021777013)
    ·
      refine ⟨13758665111677463439541595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146759094524559610021777013 13758665111677463439541595)
      ·
        refine ⟨20637997667516195159312393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13758665111677463439541595 20637997667516195159312393)
        ·
          refine ⟨15478498250637146369484295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20637997667516195159312393 15478498250637146369484295)
          ·
            refine ⟨23217747375955719554226443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15478498250637146369484295 23217747375955719554226443)
            ·
              refine ⟨34826621063933579331339665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23217747375955719554226443 34826621063933579331339665)
              ·
                refine ⟨26119965797950184498504749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34826621063933579331339665 26119965797950184498504749)
                ·
                  refine ⟨9794987174231319186939281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26119965797950184498504749 9794987174231319186939281)
                  ·
                    refine ⟨7346240380673489390204461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9794987174231319186939281 7346240380673489390204461)
                    ·
                      refine ⟨2754840142752558521326673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346240380673489390204461 2754840142752558521326673)
                      ·
                        rfl

theorem cell23_5365032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_5365032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365032 prefixEnd_5365032 := by exact prefixLift 5365032
  have htrace : WordTrace (prefixWord ++ tailWord_5365032) baseStart_5365032 baseEnd_5365032 := by
    simpa [prefixWord, tailWord_5365032, baseEnd_5365032] using wordTrace_append hprefix tailTrace_5365032
  have hstable : (prefixWord ++ tailWord_5365032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365032).length < 2 ^ (prefixWord ++ tailWord_5365032).sum := by decide
  have hdescent : baseEnd_5365032 < baseStart_5365032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365042 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_5365042 : Nat := 118140960795 + 5365042 * 2 ^ 59
def prefixEnd_5365042 : Nat := 4983230072969 + 3 ^ 40 * 5365042 * 2
def baseEnd_5365042 : Nat := 2754845277559103482201627

theorem tailTrace_5365042 : CollatzResearch.WordTrace tailWord_5365042 prefixEnd_5365042 2754845277559103482201627 := by
  unfold tailWord_5365042
  simp only [CollatzResearch.WordTrace]
  refine ⟨48919789357344146267558345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130452771619584390046822253 48919789357344146267558345)
  ·
    refine ⟨36689842018008109700668759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48919789357344146267558345 36689842018008109700668759)
    ·
      refine ⟨55034763027012164551003139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36689842018008109700668759 55034763027012164551003139)
      ·
        refine ⟨82552144540518246826504709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55034763027012164551003139 82552144540518246826504709)
        ·
          refine ⟨15478527101347171279969633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82552144540518246826504709 15478527101347171279969633)
          ·
            refine ⟨11608895326010378459977225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15478527101347171279969633 11608895326010378459977225)
            ·
              refine ⟨8706671494507783844982919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11608895326010378459977225 8706671494507783844982919)
              ·
                refine ⟨13060007241761675767474379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8706671494507783844982919 13060007241761675767474379)
                ·
                  refine ⟨19590010862642513651211569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13060007241761675767474379 19590010862642513651211569)
                  ·
                    refine ⟨14692508146981885238408677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19590010862642513651211569 14692508146981885238408677)
                    ·
                      refine ⟨2754845277559103482201627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14692508146981885238408677 2754845277559103482201627)
                      ·
                        rfl

theorem cell23_5365042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_5365042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365042 prefixEnd_5365042 := by exact prefixLift 5365042
  have htrace : WordTrace (prefixWord ++ tailWord_5365042) baseStart_5365042 baseEnd_5365042 := by
    simpa [prefixWord, tailWord_5365042, baseEnd_5365042] using wordTrace_append hprefix tailTrace_5365042
  have hstable : (prefixWord ++ tailWord_5365042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365042).length < 2 ^ (prefixWord ++ tailWord_5365042).sum := by decide
  have hdescent : baseEnd_5365042 < baseStart_5365042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365048 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 4, 7]
def baseStart_5365048 : Nat := 118140960795 + 5365048 * 2 ^ 59
def prefixEnd_5365048 : Nat := 4983230072969 + 3 ^ 40 * 5365048 * 2
def baseEnd_5365048 : Nat := 918282786147676819575533

theorem tailTrace_5365048 : CollatzResearch.WordTrace tailWord_5365048 prefixEnd_5365048 918282786147676819575533 := by
  unfold tailWord_5365048
  simp only [CollatzResearch.WordTrace]
  refine ⟨97839688133677424047475899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130452917511569898729967865 97839688133677424047475899)
  ·
    refine ⟨146759532200516136071213849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97839688133677424047475899 146759532200516136071213849)
    ·
      refine ⟨110069649150387102053410387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146759532200516136071213849 110069649150387102053410387)
      ·
        refine ⟨165104473725580653080115581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110069649150387102053410387 165104473725580653080115581)
        ·
          refine ⟨61914177647092744905043343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165104473725580653080115581 61914177647092744905043343)
          ·
            refine ⟨92871266470639117357565015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61914177647092744905043343 92871266470639117357565015)
            ·
              refine ⟨139306899705958676036347523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92871266470639117357565015 139306899705958676036347523)
              ·
                refine ⟨208960349558938014054521285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139306899705958676036347523 208960349558938014054521285)
                ·
                  refine ⟨39180065542300877635222741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 208960349558938014054521285 39180065542300877635222741)
                  ·
                    refine ⟨918282786147676819575533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39180065542300877635222741 918282786147676819575533)
                    ·
                      rfl

theorem cell23_5365048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_5365048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365048 prefixEnd_5365048 := by exact prefixLift 5365048
  have htrace : WordTrace (prefixWord ++ tailWord_5365048) baseStart_5365048 baseEnd_5365048 := by
    simpa [prefixWord, tailWord_5365048, baseEnd_5365048] using wordTrace_append hprefix tailTrace_5365048
  have hstable : (prefixWord ++ tailWord_5365048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365048).length < 2 ^ (prefixWord ++ tailWord_5365048).sum := by decide
  have hdescent : baseEnd_5365048 < baseStart_5365048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365079 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 2, 1, 3]
def baseStart_5365079 : Nat := 118140960795 + 5365079 * 2 ^ 59
def prefixEnd_5365079 : Nat := 4983230072969 + 3 ^ 40 * 5365079 * 2
def baseEnd_5365079 : Nat := 2754864276343319837438957

theorem tailTrace_5365079 : CollatzResearch.WordTrace tailWord_5365079 prefixEnd_5365079 2754864276343319837438957 := by
  unfold tailWord_5365079
  simp only [CollatzResearch.WordTrace]
  refine ⟨195680506930242540389330291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130453671286828360259553527 195680506930242540389330291)
  ·
    refine ⟨293520760395363810583995437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195680506930242540389330291 293520760395363810583995437)
    ·
      refine ⟨110070285148261428968998289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293520760395363810583995437 110070285148261428968998289)
      ·
        refine ⟨82552713861196071726748717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110070285148261428968998289 82552713861196071726748717)
        ·
          refine ⟨30957267697948526897530769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82552713861196071726748717 30957267697948526897530769)
          ·
            refine ⟨23217950773461395173148077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30957267697948526897530769 23217950773461395173148077)
            ·
              refine ⟨8706731540048023189930529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23217950773461395173148077 8706731540048023189930529)
              ·
                refine ⟨6530048655036017392447897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8706731540048023189930529 6530048655036017392447897)
                ·
                  refine ⟨4897536491277013044335923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6530048655036017392447897 4897536491277013044335923)
                  ·
                    refine ⟨7346304736915519566503885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4897536491277013044335923 7346304736915519566503885)
                    ·
                      refine ⟨2754864276343319837438957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346304736915519566503885 2754864276343319837438957)
                      ·
                        rfl

theorem cell23_5365079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_5365079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365079 prefixEnd_5365079 := by exact prefixLift 5365079
  have htrace : WordTrace (prefixWord ++ tailWord_5365079) baseStart_5365079 baseEnd_5365079 := by
    simpa [prefixWord, tailWord_5365079, baseEnd_5365079] using wordTrace_append hprefix tailTrace_5365079
  have hstable : (prefixWord ++ tailWord_5365079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365079).length < 2 ^ (prefixWord ++ tailWord_5365079).sum := by decide
  have hdescent : baseEnd_5365079 < baseStart_5365079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365096 : List Nat := [2, 1, 4, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_5365096 : Nat := 118140960795 + 5365096 * 2 ^ 59
def prefixEnd_5365096 : Nat := 4983230072969 + 3 ^ 40 * 5365096 * 2
def baseEnd_5365096 : Nat := 2754873005514446270926379

theorem tailTrace_5365096 : CollatzResearch.WordTrace tailWord_5365096 prefixEnd_5365096 2754873005514446270926379 := by
  unfold tailWord_5365096
  simp only [CollatzResearch.WordTrace]
  refine ⟨97840563485590476146349571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130454084647453968195132761 97840563485590476146349571)
  ·
    refine ⟨146760845228385714219524357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97840563485590476146349571 146760845228385714219524357)
    ·
      refine ⟨27517658480322321416160817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146760845228385714219524357 27517658480322321416160817)
      ·
        refine ⟨20638243860241741062120613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27517658480322321416160817 20638243860241741062120613)
        ·
          refine ⟨3869670723795326449147615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20638243860241741062120613 3869670723795326449147615)
          ·
            refine ⟨5804506085692989673721423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3869670723795326449147615 5804506085692989673721423)
            ·
              refine ⟨8706759128539484510582135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5804506085692989673721423 8706759128539484510582135)
              ·
                refine ⟨13060138692809226765873203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8706759128539484510582135 13060138692809226765873203)
                ·
                  refine ⟨19590208039213840148809805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13060138692809226765873203 19590208039213840148809805)
                  ·
                    refine ⟨7346328014705190055803677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19590208039213840148809805 7346328014705190055803677)
                    ·
                      refine ⟨2754873005514446270926379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346328014705190055803677 2754873005514446270926379)
                      ·
                        rfl

theorem cell23_5365096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_5365096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365096 prefixEnd_5365096 := by exact prefixLift 5365096
  have htrace : WordTrace (prefixWord ++ tailWord_5365096) baseStart_5365096 baseEnd_5365096 := by
    simpa [prefixWord, tailWord_5365096, baseEnd_5365096] using wordTrace_append hprefix tailTrace_5365096
  have hstable : (prefixWord ++ tailWord_5365096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365096).length < 2 ^ (prefixWord ++ tailWord_5365096).sum := by decide
  have hdescent : baseEnd_5365096 < baseStart_5365096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365105 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 3]
def baseStart_5365105 : Nat := 118140960795 + 5365105 * 2 ^ 59
def prefixEnd_5365105 : Nat := 4983230072969 + 3 ^ 40 * 5365105 * 2
def baseEnd_5365105 : Nat := 2754877626840336735713837

theorem tailTrace_5365105 : CollatzResearch.WordTrace tailWord_5365105 prefixEnd_5365105 2754877626840336735713837 := by
  unfold tailWord_5365105
  simp only [CollatzResearch.WordTrace]
  refine ⟨195681455228148346829776769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130454303485432231219851179 195681455228148346829776769)
  ·
    refine ⟨146761091421111260122332577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195681455228148346829776769 146761091421111260122332577)
    ·
      refine ⟨110070818565833445091749433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146761091421111260122332577 110070818565833445091749433)
      ·
        refine ⟨82553113924375083818812075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110070818565833445091749433 82553113924375083818812075)
        ·
          refine ⟨123829670886562625728218113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82553113924375083818812075 123829670886562625728218113)
          ·
            refine ⟨92872253164921969296163585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123829670886562625728218113 92872253164921969296163585)
            ·
              refine ⟨69654189873691476972122689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92872253164921969296163585 69654189873691476972122689)
              ·
                refine ⟨52240642405268607729092017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69654189873691476972122689 52240642405268607729092017)
                ·
                  refine ⟨39180481803951455796819013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52240642405268607729092017 39180481803951455796819013)
                  ·
                    refine ⟨7346340338240897961903565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39180481803951455796819013 7346340338240897961903565)
                    ·
                      refine ⟨2754877626840336735713837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346340338240897961903565 2754877626840336735713837)
                      ·
                        rfl

theorem cell23_5365105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_5365105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365105 prefixEnd_5365105 := by exact prefixLift 5365105
  have htrace : WordTrace (prefixWord ++ tailWord_5365105) baseStart_5365105 baseEnd_5365105 := by
    simpa [prefixWord, tailWord_5365105, baseEnd_5365105] using wordTrace_append hprefix tailTrace_5365105
  have hstable : (prefixWord ++ tailWord_5365105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365105).length < 2 ^ (prefixWord ++ tailWord_5365105).sum := by decide
  have hdescent : baseEnd_5365105 < baseStart_5365105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365155 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 4, 5]
def baseStart_5365155 : Nat := 118140960795 + 5365155 * 2 ^ 59
def prefixEnd_5365155 : Nat := 4983230072969 + 3 ^ 40 * 5365155 * 2
def baseEnd_5365155 : Nat := 918301100291020513362869

theorem tailTrace_5365155 : CollatzResearch.WordTrace tailWord_5365155 prefixEnd_5365155 918301100291020513362869 := by
  unfold tailWord_5365155
  simp only [CollatzResearch.WordTrace]
  refine ⟨195683278877967205369096919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130455519251978136912731279 195683278877967205369096919)
  ·
    refine ⟨293524918316950808053645379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195683278877967205369096919 293524918316950808053645379)
    ·
      refine ⟨440287377475426212080468069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293524918316950808053645379 440287377475426212080468069)
      ·
        refine ⟨82553883276642414765087763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 440287377475426212080468069 82553883276642414765087763)
        ·
          refine ⟨123830824914963622147631645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82553883276642414765087763 123830824914963622147631645)
          ·
            refine ⟨46436559343111358305361867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123830824914963622147631645 46436559343111358305361867)
            ·
              refine ⟨69654839014667037458042801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46436559343111358305361867 69654839014667037458042801)
              ·
                refine ⟨52241129261000278093532101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69654839014667037458042801 52241129261000278093532101)
                ·
                  refine ⟨9795211736437552142537269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52241129261000278093532101 9795211736437552142537269)
                  ·
                    refine ⟨918301100291020513362869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9795211736437552142537269 918301100291020513362869)
                    ·
                      rfl

theorem cell23_5365155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 5].length) (baseStart_5365155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365155 prefixEnd_5365155 := by exact prefixLift 5365155
  have htrace : WordTrace (prefixWord ++ tailWord_5365155) baseStart_5365155 baseEnd_5365155 := by
    simpa [prefixWord, tailWord_5365155, baseEnd_5365155] using wordTrace_append hprefix tailTrace_5365155
  have hstable : (prefixWord ++ tailWord_5365155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365155).length < 2 ^ (prefixWord ++ tailWord_5365155).sum := by decide
  have hdescent : baseEnd_5365155 < baseStart_5365155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365192 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_5365192 : Nat := 118140960795 + 5365192 * 2 ^ 59
def prefixEnd_5365192 : Nat := 4983230072969 + 3 ^ 40 * 5365192 * 2
def baseEnd_5365192 : Nat := 2754922299657277895325937

theorem tailTrace_5365192 : CollatzResearch.WordTrace tailWord_5365192 prefixEnd_5365192 2754922299657277895325937 := by
  unfold tailWord_5365192
  simp only [CollatzResearch.WordTrace]
  refine ⟨97842314189416580344096915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130456418919222107125462553 97842314189416580344096915)
  ·
    refine ⟨146763471284124870516145373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97842314189416580344096915 146763471284124870516145373)
    ·
      refine ⟨55036301731546826443554515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146763471284124870516145373 55036301731546826443554515)
      ·
        refine ⟨82554452597320239665331773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55036301731546826443554515 82554452597320239665331773)
        ·
          refine ⟨30957919723995089874499415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82554452597320239665331773 30957919723995089874499415)
          ·
            refine ⟨46436879585992634811749123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30957919723995089874499415 46436879585992634811749123)
            ·
              refine ⟨69655319378988952217623685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46436879585992634811749123 69655319378988952217623685)
              ·
                refine ⟨13060372383560428540804441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69655319378988952217623685 13060372383560428540804441)
                ·
                  refine ⟨9795279287670321405603331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13060372383560428540804441 9795279287670321405603331)
                  ·
                    refine ⟨14692918931505482108404997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9795279287670321405603331 14692918931505482108404997)
                    ·
                      refine ⟨2754922299657277895325937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14692918931505482108404997 2754922299657277895325937)
                      ·
                        rfl

theorem cell23_5365192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_5365192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365192 prefixEnd_5365192 := by exact prefixLift 5365192
  have htrace : WordTrace (prefixWord ++ tailWord_5365192) baseStart_5365192 baseEnd_5365192 := by
    simpa [prefixWord, tailWord_5365192, baseEnd_5365192] using wordTrace_append hprefix tailTrace_5365192
  have hstable : (prefixWord ++ tailWord_5365192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365192).length < 2 ^ (prefixWord ++ tailWord_5365192).sum := by decide
  have hdescent : baseEnd_5365192 < baseStart_5365192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365209 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 2, 4, 2]
def baseStart_5365209 : Nat := 118140960795 + 5365209 * 2 ^ 59
def prefixEnd_5365209 : Nat := 4983230072969 + 3 ^ 40 * 5365209 * 2
def baseEnd_5365209 : Nat := 2754931028828404328813359

theorem tailTrace_5365209 : CollatzResearch.WordTrace tailWord_5365209 prefixEnd_5365209 2754931028828404328813359 := by
  unfold tailWord_5365209
  simp only [CollatzResearch.WordTrace]
  refine ⟨195685248419771572591562681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130456832279847715061041787 195685248419771572591562681)
  ·
    refine ⟨146763936314828679443672011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195685248419771572591562681 146763936314828679443672011)
    ·
      refine ⟨220145904472243019165508017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146763936314828679443672011 220145904472243019165508017)
      ·
        refine ⟨165109428354182264374131013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220145904472243019165508017 165109428354182264374131013)
        ·
          refine ⟨30958017816409174570149565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165109428354182264374131013 30958017816409174570149565)
          ·
            refine ⟨11609256681153440463806087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30958017816409174570149565 11609256681153440463806087)
            ·
              refine ⟨17413885021730160695709131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11609256681153440463806087 17413885021730160695709131)
              ·
                refine ⟨26120827532595241043563697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17413885021730160695709131 26120827532595241043563697)
                ·
                  refine ⟨19590620649446430782672773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26120827532595241043563697 19590620649446430782672773)
                  ·
                    refine ⟨3673241371771205771751145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19590620649446430782672773 3673241371771205771751145)
                    ·
                      refine ⟨2754931028828404328813359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3673241371771205771751145 2754931028828404328813359)
                      ·
                        rfl

theorem cell23_5365209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_5365209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365209 prefixEnd_5365209 := by exact prefixLift 5365209
  have htrace : WordTrace (prefixWord ++ tailWord_5365209) baseStart_5365209 baseEnd_5365209 := by
    simpa [prefixWord, tailWord_5365209, baseEnd_5365209] using wordTrace_append hprefix tailTrace_5365209
  have hstable : (prefixWord ++ tailWord_5365209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365209).length < 2 ^ (prefixWord ++ tailWord_5365209).sum := by decide
  have hdescent : baseEnd_5365209 < baseStart_5365209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365219 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 3, 4]
def baseStart_5365219 : Nat := 118140960795 + 5365219 * 2 ^ 59
def prefixEnd_5365219 : Nat := 4983230072969 + 3 ^ 40 * 5365219 * 2
def baseEnd_5365219 : Nat := 918312054544983096562771

theorem tailTrace_5365219 : CollatzResearch.WordTrace tailWord_5365219 prefixEnd_5365219 918312054544983096562771 := by
  unfold tailWord_5365219
  simp only [CollatzResearch.WordTrace]
  refine ⟨195685613149735344299426711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130457075433156896199617807 195685613149735344299426711)
  ·
    refine ⟨293528419724603016449140067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195685613149735344299426711 293528419724603016449140067)
    ·
      refine ⟨440292629586904524673710101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293528419724603016449140067 440292629586904524673710101)
      ·
        refine ⟨20638717011886149594080161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 440292629586904524673710101 20638717011886149594080161)
        ·
          refine ⟨15479037758914612195560121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20638717011886149594080161 15479037758914612195560121)
          ·
            refine ⟨11609278319185959146670091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15479037758914612195560121 11609278319185959146670091)
            ·
              refine ⟨17413917478778938720005137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11609278319185959146670091 17413917478778938720005137)
              ·
                refine ⟨13060438109084204040003853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17413917478778938720005137 13060438109084204040003853)
                ·
                  refine ⟨4897664290906576515001445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13060438109084204040003853 4897664290906576515001445)
                  ·
                    refine ⟨918312054544983096562771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4897664290906576515001445 918312054544983096562771)
                    ·
                      rfl

theorem cell23_5365219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 4].length) (baseStart_5365219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365219 prefixEnd_5365219 := by exact prefixLift 5365219
  have htrace : WordTrace (prefixWord ++ tailWord_5365219) baseStart_5365219 baseEnd_5365219 := by
    simpa [prefixWord, tailWord_5365219, baseEnd_5365219] using wordTrace_append hprefix tailTrace_5365219
  have hstable : (prefixWord ++ tailWord_5365219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365219).length < 2 ^ (prefixWord ++ tailWord_5365219).sum := by decide
  have hdescent : baseEnd_5365219 < baseStart_5365219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365226 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_5365226 : Nat := 118140960795 + 5365226 * 2 ^ 59
def prefixEnd_5365226 : Nat := 4983230072969 + 3 ^ 40 * 5365226 * 2
def baseEnd_5365226 : Nat := 2754939757999530762300781

theorem tailTrace_5365226 : CollatzResearch.WordTrace tailWord_5365226 prefixEnd_5365226 2754939757999530762300781 := by
  unfold tailWord_5365226
  simp only [CollatzResearch.WordTrace]
  refine ⟨48921467115177496123732883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130457245640473322996621021 48921467115177496123732883)
  ·
    refine ⟨73382200672766244185599325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48921467115177496123732883 73382200672766244185599325)
    ·
      refine ⟨27518325252287341569599747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73382200672766244185599325 27518325252287341569599747)
      ·
        refine ⟨41277487878431012354399621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27518325252287341569599747 41277487878431012354399621)
        ·
          refine ⟨7739528977205814816449929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41277487878431012354399621 7739528977205814816449929)
          ·
            refine ⟨5804646732904361112337447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7739528977205814816449929 5804646732904361112337447)
            ·
              refine ⟨8706970099356541668506171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5804646732904361112337447 8706970099356541668506171)
              ·
                refine ⟨13060455149034812502759257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8706970099356541668506171 13060455149034812502759257)
                ·
                  refine ⟨9795341361776109377069443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13060455149034812502759257 9795341361776109377069443)
                  ·
                    refine ⟨14693012042664164065604165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9795341361776109377069443 14693012042664164065604165)
                    ·
                      refine ⟨2754939757999530762300781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14693012042664164065604165 2754939757999530762300781)
                      ·
                        rfl

theorem cell23_5365226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_5365226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365226 prefixEnd_5365226 := by exact prefixLift 5365226
  have htrace : WordTrace (prefixWord ++ tailWord_5365226) baseStart_5365226 baseEnd_5365226 := by
    simpa [prefixWord, tailWord_5365226, baseEnd_5365226] using wordTrace_append hprefix tailTrace_5365226
  have hstable : (prefixWord ++ tailWord_5365226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365226).length < 2 ^ (prefixWord ++ tailWord_5365226).sum := by decide
  have hdescent : baseEnd_5365226 < baseStart_5365226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365269 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 1, 5, 2]
def baseStart_5365269 : Nat := 118140960795 + 5365269 * 2 ^ 59
def prefixEnd_5365269 : Nat := 4983230072969 + 3 ^ 40 * 5365269 * 2
def baseEnd_5365269 : Nat := 2754961837667674094063083

theorem tailTrace_5365269 : CollatzResearch.WordTrace tailWord_5365269 prefixEnd_5365269 2754961837667674094063083 := by
  unfold tailWord_5365269
  simp only [CollatzResearch.WordTrace]
  refine ⟨195687436799554202838746861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130458291199702801892497907 195687436799554202838746861)
  ·
    refine ⟨73382788799832826064530073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195687436799554202838746861 73382788799832826064530073)
    ·
      refine ⟨55037091599874619548397555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73382788799832826064530073 55037091599874619548397555)
      ·
        refine ⟨82555637399811929322596333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55037091599874619548397555 82555637399811929322596333)
        ·
          refine ⟨30958364024929473495973625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82555637399811929322596333 30958364024929473495973625)
          ·
            refine ⟨23218773018697105121980219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30958364024929473495973625 23218773018697105121980219)
            ·
              refine ⟨34828159528045657682970329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23218773018697105121980219 34828159528045657682970329)
              ·
                refine ⟨26121119646034243262227747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34828159528045657682970329 26121119646034243262227747)
                ·
                  refine ⟨39181679469051364893341621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26121119646034243262227747 39181679469051364893341621)
                  ·
                    refine ⟨3673282450223565458750777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39181679469051364893341621 3673282450223565458750777)
                    ·
                      refine ⟨2754961837667674094063083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3673282450223565458750777 2754961837667674094063083)
                      ·
                        rfl

theorem cell23_5365269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_5365269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365269 prefixEnd_5365269 := by exact prefixLift 5365269
  have htrace : WordTrace (prefixWord ++ tailWord_5365269) baseStart_5365269 baseEnd_5365269 := by
    simpa [prefixWord, tailWord_5365269, baseEnd_5365269] using wordTrace_append hprefix tailTrace_5365269
  have hstable : (prefixWord ++ tailWord_5365269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365269).length < 2 ^ (prefixWord ++ tailWord_5365269).sum := by decide
  have hdescent : baseEnd_5365269 < baseStart_5365269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365299 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 4]
def baseStart_5365299 : Nat := 118140960795 + 5365299 * 2 ^ 59
def prefixEnd_5365299 : Nat := 4983230072969 + 3 ^ 40 * 5365299 * 2
def baseEnd_5365299 : Nat := 2754977242087308976687945

theorem tailTrace_5365299 : CollatzResearch.WordTrace tailWord_5365299 prefixEnd_5365299 2754977242087308976687945 := by
  unfold tailWord_5365299
  simp only [CollatzResearch.WordTrace]
  refine ⟨195688530989445517962338951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130459020659630345308225967 195688530989445517962338951)
  ·
    refine ⟨293532796484168276943508427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195688530989445517962338951 293532796484168276943508427)
    ·
      refine ⟨440299194726252415415262641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293532796484168276943508427 440299194726252415415262641)
      ·
        refine ⟨330224396044689311561446981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440299194726252415415262641 330224396044689311561446981)
        ·
          refine ⟨61917074258379245917771309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330224396044689311561446981 61917074258379245917771309)
          ·
            refine ⟨23218902846892217219164241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61917074258379245917771309 23218902846892217219164241)
            ·
              refine ⟨17414177135169162914373181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23218902846892217219164241 17414177135169162914373181)
              ·
                refine ⟨6530316425688436092889943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17414177135169162914373181 6530316425688436092889943)
                ·
                  refine ⟨9795474638532654139334915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6530316425688436092889943 9795474638532654139334915)
                  ·
                    refine ⟨14693211957798981209002373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9795474638532654139334915 14693211957798981209002373)
                    ·
                      refine ⟨2754977242087308976687945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14693211957798981209002373 2754977242087308976687945)
                      ·
                        rfl

theorem cell23_5365299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 4].length) (baseStart_5365299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365299 prefixEnd_5365299 := by exact prefixLift 5365299
  have htrace : WordTrace (prefixWord ++ tailWord_5365299) baseStart_5365299 baseEnd_5365299 := by
    simpa [prefixWord, tailWord_5365299, baseEnd_5365299] using wordTrace_append hprefix tailTrace_5365299
  have hstable : (prefixWord ++ tailWord_5365299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365299).length < 2 ^ (prefixWord ++ tailWord_5365299).sum := by decide
  have hdescent : baseEnd_5365299 < baseStart_5365299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365322 : List Nat := [3, 1, 2, 1, 1, 3, 4, 8]
def baseStart_5365322 : Nat := 118140960795 + 5365322 * 2 ^ 59
def prefixEnd_5365322 : Nat := 4983230072969 + 3 ^ 40 * 5365322 * 2
def baseEnd_5365322 : Nat := 102036631560828236544457

theorem tailTrace_5365322 : CollatzResearch.WordTrace tailWord_5365322 prefixEnd_5365322 102036631560828236544457 := by
  unfold tailWord_5365322
  simp only [CollatzResearch.WordTrace]
  refine ⟨48922342467090548222606555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130459579912241461926950813 48922342467090548222606555)
  ·
    refine ⟨73383513700635822333909833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48922342467090548222606555 73383513700635822333909833)
    ·
      refine ⟨55037635275476866750432375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73383513700635822333909833 55037635275476866750432375)
      ·
        refine ⟨82556452913215300125648563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55037635275476866750432375 82556452913215300125648563)
        ·
          refine ⟨123834679369822950188472845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82556452913215300125648563 123834679369822950188472845)
          ·
            refine ⟨46438004763683606320677317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123834679369822950188472845 46438004763683606320677317)
            ·
              refine ⟨8707125893190676185126997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46438004763683606320677317 8707125893190676185126997)
              ·
                refine ⟨102036631560828236544457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8707125893190676185126997 102036631560828236544457)
                ·
                  rfl

theorem cell23_5365322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 8].length) (baseStart_5365322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365322 prefixEnd_5365322 := by exact prefixLift 5365322
  have htrace : WordTrace (prefixWord ++ tailWord_5365322) baseStart_5365322 baseEnd_5365322 := by
    simpa [prefixWord, tailWord_5365322, baseEnd_5365322] using wordTrace_append hprefix tailTrace_5365322
  have hstable : (prefixWord ++ tailWord_5365322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365322).length < 2 ^ (prefixWord ++ tailWord_5365322).sum := by decide
  have hdescent : baseEnd_5365322 < baseStart_5365322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365349 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 3, 3, 3]
def baseStart_5365349 : Nat := 118140960795 + 5365349 * 2 ^ 59
def prefixEnd_5365349 : Nat := 4983230072969 + 3 ^ 40 * 5365349 * 2
def baseEnd_5365349 : Nat := 2755002916120033781062715

theorem tailTrace_5365349 : CollatzResearch.WordTrace tailWord_5365349 prefixEnd_5365349 2755002916120033781062715 := by
  unfold tailWord_5365349
  simp only [CollatzResearch.WordTrace]
  refine ⟨195690354639264376501659101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130460236426176251001106067 195690354639264376501659101)
  ·
    refine ⟨73383882989724141188122163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195690354639264376501659101 73383882989724141188122163)
    ·
      refine ⟨110075824484586211782183245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73383882989724141188122163 110075824484586211782183245)
      ·
        refine ⟨41278434181719829418318717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110075824484586211782183245 41278434181719829418318717)
        ·
          refine ⟨15479412818144936031869519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41278434181719829418318717 15479412818144936031869519)
          ·
            refine ⟨23219119227217404047804279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15479412818144936031869519 23219119227217404047804279)
            ·
              refine ⟨34828678840826106071706419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23219119227217404047804279 34828678840826106071706419)
              ·
                refine ⟨52243018261239159107559629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34828678840826106071706419 52243018261239159107559629)
                ·
                  refine ⟨19591131847964684665334861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52243018261239159107559629 19591131847964684665334861)
                  ·
                    refine ⟨7346674442986756749500573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19591131847964684665334861 7346674442986756749500573)
                    ·
                      refine ⟨2755002916120033781062715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346674442986756749500573 2755002916120033781062715)
                      ·
                        rfl

theorem cell23_5365349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_5365349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365349 prefixEnd_5365349 := by exact prefixLift 5365349
  have htrace : WordTrace (prefixWord ++ tailWord_5365349) baseStart_5365349 baseEnd_5365349 := by
    simpa [prefixWord, tailWord_5365349, baseEnd_5365349] using wordTrace_append hprefix tailTrace_5365349
  have hstable : (prefixWord ++ tailWord_5365349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365349).length < 2 ^ (prefixWord ++ tailWord_5365349).sum := by decide
  have hdescent : baseEnd_5365349 < baseStart_5365349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365392 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_5365392 : Nat := 118140960795 + 5365392 * 2 ^ 59
def prefixEnd_5365392 : Nat := 4983230072969 + 3 ^ 40 * 5365392 * 2
def baseEnd_5365392 : Nat := 2755024995788177112825017

theorem tailTrace_5365392 : CollatzResearch.WordTrace tailWord_5365392 prefixEnd_5365392 2755024995788177112825017 := by
  unfold tailWord_5365392
  simp only [CollatzResearch.WordTrace]
  refine ⟨97845961489054297422737215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130461281985405729896982953 97845961489054297422737215)
  ·
    refine ⟨146768942233581446134105823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97845961489054297422737215 146768942233581446134105823)
    ·
      refine ⟨220153413350372169201158735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146768942233581446134105823 220153413350372169201158735)
      ·
        refine ⟨330230120025558253801738103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220153413350372169201158735 330230120025558253801738103)
        ·
          refine ⟨495345180038337380702607155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330230120025558253801738103 495345180038337380702607155)
          ·
            refine ⟨743017770057506071053910733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495345180038337380702607155 743017770057506071053910733)
            ·
              refine ⟨278631663771564776645216525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 743017770057506071053910733 278631663771564776645216525)
              ·
                refine ⟨104486873914336791241956197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278631663771564776645216525 104486873914336791241956197)
                ·
                  refine ⟨19591288858938148357866787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104486873914336791241956197 19591288858938148357866787)
                  ·
                    refine ⟨29386933288407222536800181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19591288858938148357866787 29386933288407222536800181)
                    ·
                      refine ⟨2755024995788177112825017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29386933288407222536800181 2755024995788177112825017)
                      ·
                        rfl

theorem cell23_5365392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_5365392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365392 prefixEnd_5365392 := by exact prefixLift 5365392
  have htrace : WordTrace (prefixWord ++ tailWord_5365392) baseStart_5365392 baseEnd_5365392 := by
    simpa [prefixWord, tailWord_5365392, baseEnd_5365392] using wordTrace_append hprefix tailTrace_5365392
  have hstable : (prefixWord ++ tailWord_5365392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365392).length < 2 ^ (prefixWord ++ tailWord_5365392).sum := by decide
  have hdescent : baseEnd_5365392 < baseStart_5365392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365439 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 3]
def baseStart_5365439 : Nat := 118140960795 + 5365439 * 2 ^ 59
def prefixEnd_5365439 : Nat := 4983230072969 + 3 ^ 40 * 5365439 * 2
def baseEnd_5365439 : Nat := 2755049129378938428937301

theorem tailTrace_5365439 : CollatzResearch.WordTrace tailWord_5365439 prefixEnd_5365439 2755049129378938428937301 := by
  unfold tailWord_5365439
  simp only [CollatzResearch.WordTrace]
  refine ⟨195693637208938321872435371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130462424805958881248290247 195693637208938321872435371)
  ·
    refine ⟨293540455813407482808653057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195693637208938321872435371 293540455813407482808653057)
    ·
      refine ⟨220155341860055612106489793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293540455813407482808653057 220155341860055612106489793)
      ·
        refine ⟨165116506395041709079867345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220155341860055612106489793 165116506395041709079867345)
        ·
          refine ⟨123837379796281281809900509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165116506395041709079867345 123837379796281281809900509)
          ·
            refine ⟨46439017423605480678712691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123837379796281281809900509 46439017423605480678712691)
            ·
              refine ⟨69658526135408221018069037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46439017423605480678712691 69658526135408221018069037)
              ·
                refine ⟨26121947300778082881775889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69658526135408221018069037 26121947300778082881775889)
                ·
                  refine ⟨19591460475583562161331917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26121947300778082881775889 19591460475583562161331917)
                  ·
                    refine ⟨7346797678343835810499469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19591460475583562161331917 7346797678343835810499469)
                    ·
                      refine ⟨2755049129378938428937301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346797678343835810499469 2755049129378938428937301)
                      ·
                        rfl

theorem cell23_5365439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_5365439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365439 prefixEnd_5365439 := by exact prefixLift 5365439
  have htrace : WordTrace (prefixWord ++ tailWord_5365439) baseStart_5365439 baseEnd_5365439 := by
    simpa [prefixWord, tailWord_5365439, baseEnd_5365439] using wordTrace_append hprefix tailTrace_5365439
  have hstable : (prefixWord ++ tailWord_5365439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365439).length < 2 ^ (prefixWord ++ tailWord_5365439).sum := by decide
  have hdescent : baseEnd_5365439 < baseStart_5365439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365440 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 2, 2, 2]
def baseStart_5365440 : Nat := 118140960795 + 5365440 * 2 ^ 59
def prefixEnd_5365440 : Nat := 4983230072969 + 3 ^ 40 * 5365440 * 2
def baseEnd_5365440 : Nat := 2755049642859592925024797

theorem tailTrace_5365440 : CollatzResearch.WordTrace tailWord_5365440 prefixEnd_5365440 2755049642859592925024797 := by
  unfold tailWord_5365440
  simp only [CollatzResearch.WordTrace]
  refine ⟨97846836840967349521610887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130462449121289799362147849 97846836840967349521610887)
  ·
    refine ⟨146770255261451024282416331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97846836840967349521610887 146770255261451024282416331)
    ·
      refine ⟨220155382892176536423624497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146770255261451024282416331 220155382892176536423624497)
      ·
        refine ⟨165116537169132402317718373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220155382892176536423624497 165116537169132402317718373)
        ·
          refine ⟨30959350719212325434572195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165116537169132402317718373 30959350719212325434572195)
          ·
            refine ⟨46439026078818488151858293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30959350719212325434572195 46439026078818488151858293)
            ·
              refine ⟨4353658694889233264236715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46439026078818488151858293 4353658694889233264236715)
              ·
                refine ⟨6530488042333849896355073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4353658694889233264236715 6530488042333849896355073)
                ·
                  refine ⟨4897866031750387422266305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6530488042333849896355073 4897866031750387422266305)
                  ·
                    refine ⟨3673399523812790566699729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4897866031750387422266305 3673399523812790566699729)
                    ·
                      refine ⟨2755049642859592925024797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3673399523812790566699729 2755049642859592925024797)
                      ·
                        rfl

theorem cell23_5365440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_5365440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365440 prefixEnd_5365440 := by exact prefixLift 5365440
  have htrace : WordTrace (prefixWord ++ tailWord_5365440) baseStart_5365440 baseEnd_5365440 := by
    simpa [prefixWord, tailWord_5365440, baseEnd_5365440] using wordTrace_append hprefix tailTrace_5365440
  have hstable : (prefixWord ++ tailWord_5365440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365440).length < 2 ^ (prefixWord ++ tailWord_5365440).sum := by decide
  have hdescent : baseEnd_5365440 < baseStart_5365440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365499 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 3]
def baseStart_5365499 : Nat := 118140960795 + 5365499 * 2 ^ 59
def prefixEnd_5365499 : Nat := 4983230072969 + 3 ^ 40 * 5365499 * 2
def baseEnd_5365499 : Nat := 2755079938218208194187025

theorem tailTrace_5365499 : CollatzResearch.WordTrace tailWord_5365499 prefixEnd_5365499 2755079938218208194187025 := by
  unfold tailWord_5365499
  simp only [CollatzResearch.WordTrace]
  refine ⟨195695825588720952119619551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130463883725813968079746367 195695825588720952119619551)
  ·
    refine ⟨293543738383081428179429327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195695825588720952119619551 293543738383081428179429327)
    ·
      refine ⟨440315607574622142269143991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293543738383081428179429327 440315607574622142269143991)
      ·
        refine ⟨660473411361933213403715987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440315607574622142269143991 660473411361933213403715987)
        ·
          refine ⟨990710117042899820105573981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660473411361933213403715987 990710117042899820105573981)
          ·
            refine ⟨371516293891087432539590243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 990710117042899820105573981 371516293891087432539590243)
            ·
              refine ⟨557274440836631148809385365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371516293891087432539590243 557274440836631148809385365)
              ·
                refine ⟨26122239414217085100439939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 557274440836631148809385365 26122239414217085100439939)
                ·
                  refine ⟨39183359121325627650659909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26122239414217085100439939 39183359121325627650659909)
                  ·
                    refine ⟨7346879835248555184498733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39183359121325627650659909 7346879835248555184498733)
                    ·
                      refine ⟨2755079938218208194187025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346879835248555184498733 2755079938218208194187025)
                      ·
                        rfl

theorem cell23_5365499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 3].length) (baseStart_5365499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365499 prefixEnd_5365499 := by exact prefixLift 5365499
  have htrace : WordTrace (prefixWord ++ tailWord_5365499) baseStart_5365499 baseEnd_5365499 := by
    simpa [prefixWord, tailWord_5365499, baseEnd_5365499] using wordTrace_append hprefix tailTrace_5365499
  have hstable : (prefixWord ++ tailWord_5365499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365499).length < 2 ^ (prefixWord ++ tailWord_5365499).sum := by decide
  have hdescent : baseEnd_5365499 < baseStart_5365499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365516 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 2, 2, 3]
def baseStart_5365516 : Nat := 118140960795 + 5365516 * 2 ^ 59
def prefixEnd_5365516 : Nat := 4983230072969 + 3 ^ 40 * 5365516 * 2
def baseEnd_5365516 : Nat := 2755088667389334627674447

theorem tailTrace_5365516 : CollatzResearch.WordTrace tailWord_5365516 prefixEnd_5365516 2755088667389334627674447 := by
  unfold tailWord_5365516
  simp only [CollatzResearch.WordTrace]
  refine ⟨97848222814829682011494201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130464297086439576015325601 97848222814829682011494201)
  ·
    refine ⟨73386167111122261508620651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97848222814829682011494201 73386167111122261508620651)
    ·
      refine ⟨110079250666683392262930977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73386167111122261508620651 110079250666683392262930977)
      ·
        refine ⟨82559438000012544197198233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110079250666683392262930977 82559438000012544197198233)
        ·
          refine ⟨61919578500009408147898675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82559438000012544197198233 61919578500009408147898675)
          ·
            refine ⟨92879367750014112221848013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61919578500009408147898675 92879367750014112221848013)
            ·
              refine ⟨34829762906255292083193005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92879367750014112221848013 34829762906255292083193005)
              ·
                refine ⟨13061161089845734531197377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34829762906255292083193005 13061161089845734531197377)
                ·
                  refine ⟨9795870817384300898398033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13061161089845734531197377 9795870817384300898398033)
                  ·
                    refine ⟨7346903113038225673798525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9795870817384300898398033 7346903113038225673798525)
                    ·
                      refine ⟨2755088667389334627674447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346903113038225673798525 2755088667389334627674447)
                      ·
                        rfl

theorem cell23_5365516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_5365516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365516 prefixEnd_5365516 := by exact prefixLift 5365516
  have htrace : WordTrace (prefixWord ++ tailWord_5365516) baseStart_5365516 baseEnd_5365516 := by
    simpa [prefixWord, tailWord_5365516, baseEnd_5365516] using wordTrace_append hprefix tailTrace_5365516
  have hstable : (prefixWord ++ tailWord_5365516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365516).length < 2 ^ (prefixWord ++ tailWord_5365516).sum := by decide
  have hdescent : baseEnd_5365516 < baseStart_5365516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365529 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 4, 5, 3]
def baseStart_5365529 : Nat := 118140960795 + 5365529 * 2 ^ 59
def prefixEnd_5365529 : Nat := 4983230072969 + 3 ^ 40 * 5365529 * 2
def baseEnd_5365529 : Nat := 2755095342637843076811887

theorem tailTrace_5365529 : CollatzResearch.WordTrace tailWord_5365529 prefixEnd_5365529 2755095342637843076811887 := by
  unfold tailWord_5365529
  simp only [CollatzResearch.WordTrace]
  refine ⟨195696919778612267243211641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130464613185741511495474427 195696919778612267243211641)
  ·
    refine ⟨146772689833959200432408731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195696919778612267243211641 146772689833959200432408731)
    ·
      refine ⟨220159034750938800648613097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146772689833959200432408731 220159034750938800648613097)
      ·
        refine ⟨165119276063204100486459823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220159034750938800648613097 165119276063204100486459823)
        ·
          refine ⟨247678914094806150729689735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165119276063204100486459823 247678914094806150729689735)
          ·
            refine ⟨371518371142209226094534603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247678914094806150729689735 371518371142209226094534603)
            ·
              refine ⟨557277556713313839141801905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371518371142209226094534603 557277556713313839141801905)
              ·
                refine ⟨417958167534985379356351429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557277556713313839141801905 417958167534985379356351429)
                ·
                  refine ⟨78367156412809758629315893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417958167534985379356351429 78367156412809758629315893)
                  ·
                    refine ⟨7346920913700914871498365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78367156412809758629315893 7346920913700914871498365)
                    ·
                      refine ⟨2755095342637843076811887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7346920913700914871498365 2755095342637843076811887)
                      ·
                        rfl

theorem cell23_5365529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_5365529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365529 prefixEnd_5365529 := by exact prefixLift 5365529
  have htrace : WordTrace (prefixWord ++ tailWord_5365529) baseStart_5365529 baseEnd_5365529 := by
    simpa [prefixWord, tailWord_5365529, baseEnd_5365529] using wordTrace_append hprefix tailTrace_5365529
  have hstable : (prefixWord ++ tailWord_5365529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365529).length < 2 ^ (prefixWord ++ tailWord_5365529).sum := by decide
  have hdescent : baseEnd_5365529 < baseStart_5365529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365536 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 6]
def baseStart_5365536 : Nat := 118140960795 + 5365536 * 2 ^ 59
def prefixEnd_5365536 : Nat := 4983230072969 + 3 ^ 40 * 5365536 * 2
def baseEnd_5365536 : Nat := 306122104111380505491595

theorem tailTrace_5365536 : CollatzResearch.WordTrace tailWord_5365536 prefixEnd_5365536 306122104111380505491595 := by
  unfold tailWord_5365536
  simp only [CollatzResearch.WordTrace]
  refine ⟨97848587544793453719358231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130464783393057938292477641 97848587544793453719358231)
  ·
    refine ⟨146772881317190180579037347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97848587544793453719358231 146772881317190180579037347)
    ·
      refine ⟨220159321975785270868556021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146772881317190180579037347 220159321975785270868556021)
      ·
        refine ⟨20639936435229869143927127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 220159321975785270868556021 20639936435229869143927127)
        ·
          refine ⟨30959904652844803715890691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20639936435229869143927127 30959904652844803715890691)
          ·
            refine ⟨46439856979267205573836037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30959904652844803715890691 46439856979267205573836037)
            ·
              refine ⟨8707473183612601045094257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46439856979267205573836037 8707473183612601045094257)
              ·
                refine ⟨6530604887709450783820693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8707473183612601045094257 6530604887709450783820693)
                ·
                  refine ⟨306122104111380505491595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6530604887709450783820693 306122104111380505491595)
                  ·
                    rfl

theorem cell23_5365536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 6].length) (baseStart_5365536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365536 prefixEnd_5365536 := by exact prefixLift 5365536
  have htrace : WordTrace (prefixWord ++ tailWord_5365536) baseStart_5365536 baseEnd_5365536 := by
    simpa [prefixWord, tailWord_5365536, baseEnd_5365536] using wordTrace_append hprefix tailTrace_5365536
  have hstable : (prefixWord ++ tailWord_5365536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365536).length < 2 ^ (prefixWord ++ tailWord_5365536).sum := by decide
  have hdescent : baseEnd_5365536 < baseStart_5365536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365540 : List Nat := [2, 3, 1, 3, 2, 2, 1, 4, 1, 4]
def baseStart_5365540 : Nat := 118140960795 + 5365540 * 2 ^ 59
def prefixEnd_5365540 : Nat := 4983230072969 + 3 ^ 40 * 5365540 * 2
def baseEnd_5365540 : Nat := 918366996975014177924779

theorem tailTrace_5365540 : CollatzResearch.WordTrace tailWord_5365540 prefixEnd_5365540 918366996975014177924779 := by
  unfold tailWord_5365540
  simp only [CollatzResearch.WordTrace]
  refine ⟨97848660490786208060931037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130464880654381610747908049 97848660490786208060931037)
  ·
    refine ⟨36693247684044828022849139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97848660490786208060931037 36693247684044828022849139)
    ·
      refine ⟨55039871526067242034273709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36693247684044828022849139 55039871526067242034273709)
      ·
        refine ⟨20639951822275215762852641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55039871526067242034273709 20639951822275215762852641)
        ·
          refine ⟨15479963866706411822139481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20639951822275215762852641 15479963866706411822139481)
          ·
            refine ⟨11609972900029808866604611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15479963866706411822139481 11609972900029808866604611)
            ·
              refine ⟨17414959350044713299906917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11609972900029808866604611 17414959350044713299906917)
              ·
                refine ⟨3265304878133383743732547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17414959350044713299906917 3265304878133383743732547)
                ·
                  refine ⟨4897957317200075615598821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3265304878133383743732547 4897957317200075615598821)
                  ·
                    refine ⟨918366996975014177924779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4897957317200075615598821 918366996975014177924779)
                    ·
                      rfl

theorem cell23_5365540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_5365540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365540 prefixEnd_5365540 := by exact prefixLift 5365540
  have htrace : WordTrace (prefixWord ++ tailWord_5365540) baseStart_5365540 baseEnd_5365540 := by
    simpa [prefixWord, tailWord_5365540, baseEnd_5365540] using wordTrace_append hprefix tailTrace_5365540
  have hstable : (prefixWord ++ tailWord_5365540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365540).length < 2 ^ (prefixWord ++ tailWord_5365540).sum := by decide
  have hdescent : baseEnd_5365540 < baseStart_5365540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365574 : List Nat := [6, 1, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_5365574 : Nat := 118140960795 + 5365574 * 2 ^ 59
def prefixEnd_5365574 : Nat := 4983230072969 + 3 ^ 40 * 5365574 * 2
def baseEnd_5365574 : Nat := 918372816422431800249727

theorem tailTrace_5365574 : CollatzResearch.WordTrace tailWord_5365574 prefixEnd_5365574 918372816422431800249727 := by
  unfold tailWord_5365574
  simp only [CollatzResearch.WordTrace]
  refine ⟨6115580033232788747768743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130465707375632826619066517 6115580033232788747768743)
  ·
    refine ⟨9173370049849183121653115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6115580033232788747768743 9173370049849183121653115)
    ·
      refine ⟨13760055074773774682479673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9173370049849183121653115 13760055074773774682479673)
      ·
        refine ⟨10320041306080331011859755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13760055074773774682479673 10320041306080331011859755)
        ·
          refine ⟨15480061959120496517789633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10320041306080331011859755 15480061959120496517789633)
          ·
            refine ⟨11610046469340372388342225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15480061959120496517789633 11610046469340372388342225)
            ·
              refine ⟨8707534852005279291256669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11610046469340372388342225 8707534852005279291256669)
              ·
                refine ⟨3265325569501979734221251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8707534852005279291256669 3265325569501979734221251)
                ·
                  refine ⟨4897988354252969601331877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3265325569501979734221251 4897988354252969601331877)
                  ·
                    refine ⟨918372816422431800249727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4897988354252969601331877 918372816422431800249727)
                    ·
                      rfl

theorem cell23_5365574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_5365574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365574 prefixEnd_5365574 := by exact prefixLift 5365574
  have htrace : WordTrace (prefixWord ++ tailWord_5365574) baseStart_5365574 baseEnd_5365574 := by
    simpa [prefixWord, tailWord_5365574, baseEnd_5365574] using wordTrace_append hprefix tailTrace_5365574
  have hstable : (prefixWord ++ tailWord_5365574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365574).length < 2 ^ (prefixWord ++ tailWord_5365574).sum := by decide
  have hdescent : baseEnd_5365574 < baseStart_5365574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365613 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_5365613 : Nat := 118140960795 + 5365613 * 2 ^ 59
def prefixEnd_5365613 : Nat := 4983230072969 + 3 ^ 40 * 5365613 * 2
def baseEnd_5365613 : Nat := 918379491670940249387167

theorem tailTrace_5365613 : CollatzResearch.WordTrace tailWord_5365613 prefixEnd_5365613 918379491670940249387167 := by
  unfold tailWord_5365613
  simp only [CollatzResearch.WordTrace]
  refine ⟨195699983510307949589269493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130466655673538633059512995 195699983510307949589269493)
  ·
    refine ⟨18346873454091370273994015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195699983510307949589269493 18346873454091370273994015)
    ·
      refine ⟨27520310181137055410991023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18346873454091370273994015 27520310181137055410991023)
      ·
        refine ⟨41280465271705583116486535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27520310181137055410991023 41280465271705583116486535)
        ·
          refine ⟨61920697907558374674729803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41280465271705583116486535 61920697907558374674729803)
          ·
            refine ⟨92881046861337562012094705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61920697907558374674729803 92881046861337562012094705)
            ·
              refine ⟨69660785146003171509071029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92881046861337562012094705 69660785146003171509071029)
              ·
                refine ⟨6530698607437797328975409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69660785146003171509071029 6530698607437797328975409)
                ·
                  refine ⟨4898023955578347996731557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6530698607437797328975409 4898023955578347996731557)
                  ·
                    refine ⟨918379491670940249387167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4898023955578347996731557 918379491670940249387167)
                    ·
                      rfl

theorem cell23_5365613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_5365613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365613 prefixEnd_5365613 := by exact prefixLift 5365613
  have htrace : WordTrace (prefixWord ++ tailWord_5365613) baseStart_5365613 baseEnd_5365613 := by
    simpa [prefixWord, tailWord_5365613, baseEnd_5365613] using wordTrace_append hprefix tailTrace_5365613
  have hstable : (prefixWord ++ tailWord_5365613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365613).length < 2 ^ (prefixWord ++ tailWord_5365613).sum := by decide
  have hdescent : baseEnd_5365613 < baseStart_5365613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365626 : List Nat := [3, 1, 1, 1, 1, 1, 8, 7]
def baseStart_5365626 : Nat := 118140960795 + 5365626 * 2 ^ 59
def prefixEnd_5365626 : Nat := 4983230072969 + 3 ^ 40 * 5365626 * 2
def baseEnd_5365626 : Nat := 102042412972641822122183

theorem tailTrace_5365626 : CollatzResearch.WordTrace tailWord_5365626 prefixEnd_5365626 102042412972641822122183 := by
  unfold tailWord_5365626
  simp only [CollatzResearch.WordTrace]
  refine ⟨48925114414815213202373183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130466971772840568539661821 48925114414815213202373183)
  ·
    refine ⟨73387671622222819803559775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48925114414815213202373183 73387671622222819803559775)
    ·
      refine ⟨110081507433334229705339663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73387671622222819803559775 110081507433334229705339663)
      ·
        refine ⟨165122261150001344558009495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110081507433334229705339663 165122261150001344558009495)
        ·
          refine ⟨247683391725002016837014243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165122261150001344558009495 247683391725002016837014243)
          ·
            refine ⟨371525087587503025255521365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247683391725002016837014243 371525087587503025255521365)
            ·
              refine ⟨4353809620166051077213141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 371525087587503025255521365 4353809620166051077213141)
              ·
                refine ⟨102042412972641822122183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4353809620166051077213141 102042412972641822122183)
                ·
                  rfl

theorem cell23_5365626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 7].length) (baseStart_5365626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365626 prefixEnd_5365626 := by exact prefixLift 5365626
  have htrace : WordTrace (prefixWord ++ tailWord_5365626) baseStart_5365626 baseEnd_5365626 := by
    simpa [prefixWord, tailWord_5365626, baseEnd_5365626] using wordTrace_append hprefix tailTrace_5365626
  have hstable : (prefixWord ++ tailWord_5365626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365626).length < 2 ^ (prefixWord ++ tailWord_5365626).sum := by decide
  have hdescent : baseEnd_5365626 < baseStart_5365626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365630 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_5365630 : Nat := 118140960795 + 5365630 * 2 ^ 59
def prefixEnd_5365630 : Nat := 4983230072969 + 3 ^ 40 * 5365630 * 2
def baseEnd_5365630 : Nat := 918382401394649060549641

theorem tailTrace_5365630 : CollatzResearch.WordTrace tailWord_5365630 prefixEnd_5365630 918382401394649060549641 := by
  unfold tailWord_5365630
  simp only [CollatzResearch.WordTrace]
  refine ⟨24462575443905795186579793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130467069034164240995092229 24462575443905795186579793)
  ·
    refine ⟨18346931582929346389934845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24462575443905795186579793 18346931582929346389934845)
    ·
      refine ⟨6880099343598504896225567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18346931582929346389934845 6880099343598504896225567)
      ·
        refine ⟨10320149015397757344338351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6880099343598504896225567 10320149015397757344338351)
        ·
          refine ⟨15480223523096636016507527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10320149015397757344338351 15480223523096636016507527)
          ·
            refine ⟨23220335284644954024761291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15480223523096636016507527 23220335284644954024761291)
            ·
              refine ⟨34830502926967431037141937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23220335284644954024761291 34830502926967431037141937)
              ·
                refine ⟨26122877195225573277856453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34830502926967431037141937 26122877195225573277856453)
                ·
                  refine ⟨4898039474104794989598085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26122877195225573277856453 4898039474104794989598085)
                  ·
                    refine ⟨918382401394649060549641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4898039474104794989598085 918382401394649060549641)
                    ·
                      rfl

theorem cell23_5365630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_5365630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365630 prefixEnd_5365630 := by exact prefixLift 5365630
  have htrace : WordTrace (prefixWord ++ tailWord_5365630) baseStart_5365630 baseEnd_5365630 := by
    simpa [prefixWord, tailWord_5365630, baseEnd_5365630] using wordTrace_append hprefix tailTrace_5365630
  have hstable : (prefixWord ++ tailWord_5365630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365630).length < 2 ^ (prefixWord ++ tailWord_5365630).sum := by decide
  have hdescent : baseEnd_5365630 < baseStart_5365630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365653 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_5365653 : Nat := 118140960795 + 5365653 * 2 ^ 59
def prefixEnd_5365653 : Nat := 4983230072969 + 3 ^ 40 * 5365653 * 2
def baseEnd_5365653 : Nat := 2755159014239000591661317

theorem tailTrace_5365653 : CollatzResearch.WordTrace tailWord_5365653 prefixEnd_5365653 2755159014239000591661317 := by
  unfold tailWord_5365653
  simp only [CollatzResearch.WordTrace]
  refine ⟨195701442430163036420725613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130467628286775357613817075 195701442430163036420725613)
  ·
    refine ⟨73388040911311138657772105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195701442430163036420725613 73388040911311138657772105)
    ·
      refine ⟨55041030683483353993329079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73388040911311138657772105 55041030683483353993329079)
      ·
        refine ⟨82561546025225030989993619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55041030683483353993329079 82561546025225030989993619)
        ·
          refine ⟨123842319037837546484990429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82561546025225030989993619 123842319037837546484990429)
          ·
            refine ⟨46440869639189079931871411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123842319037837546484990429 46440869639189079931871411)
            ·
              refine ⟨69661304458783619897807117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46440869639189079931871411 69661304458783619897807117)
              ·
                refine ⟨26122989172043857461677669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69661304458783619897807117 26122989172043857461677669)
                ·
                  refine ⟨4898060469758223274064563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26122989172043857461677669 4898060469758223274064563)
                  ·
                    refine ⟨7347090704637334911096845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4898060469758223274064563 7347090704637334911096845)
                    ·
                      refine ⟨2755159014239000591661317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7347090704637334911096845 2755159014239000591661317)
                      ·
                        rfl

theorem cell23_5365653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_5365653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365653 prefixEnd_5365653 := by exact prefixLift 5365653
  have htrace : WordTrace (prefixWord ++ tailWord_5365653) baseStart_5365653 baseEnd_5365653 := by
    simpa [prefixWord, tailWord_5365653, baseEnd_5365653] using wordTrace_append hprefix tailTrace_5365653
  have hstable : (prefixWord ++ tailWord_5365653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365653).length < 2 ^ (prefixWord ++ tailWord_5365653).sum := by decide
  have hdescent : baseEnd_5365653 < baseStart_5365653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365696 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_5365696 : Nat := 118140960795 + 5365696 * 2 ^ 59
def prefixEnd_5365696 : Nat := 4983230072969 + 3 ^ 40 * 5365696 * 2
def baseEnd_5365696 : Nat := 2755181093907143923423619

theorem tailTrace_5365696 : CollatzResearch.WordTrace tailWord_5365696 prefixEnd_5365696 2755181093907143923423619 := by
  unfold tailWord_5365696
  simp only [CollatzResearch.WordTrace]
  refine ⟨97851505384503627382270471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130468673846004836509693961 97851505384503627382270471)
  ·
    refine ⟨146777258076755441073405707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97851505384503627382270471 146777258076755441073405707)
    ·
      refine ⟨220165887115133161610108561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146777258076755441073405707 220165887115133161610108561)
      ·
        refine ⟨165124415336349871207581421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220165887115133161610108561 165124415336349871207581421)
        ·
          refine ⟨61921655751131201702843033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165124415336349871207581421 61921655751131201702843033)
          ·
            refine ⟨46441241813348401277132275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61921655751131201702843033 46441241813348401277132275)
            ·
              refine ⟨69661862720022601915698413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46441241813348401277132275 69661862720022601915698413)
              ·
                refine ⟨26123198520008475718386905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69661862720022601915698413 26123198520008475718386905)
                ·
                  refine ⟨19592398890006356788790179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26123198520008475718386905 19592398890006356788790179)
                  ·
                    refine ⟨29388598335009535183185269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19592398890006356788790179 29388598335009535183185269)
                    ·
                      refine ⟨2755181093907143923423619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29388598335009535183185269 2755181093907143923423619)
                      ·
                        rfl

theorem cell23_5365696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_5365696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365696 prefixEnd_5365696 := by exact prefixLift 5365696
  have htrace : WordTrace (prefixWord ++ tailWord_5365696) baseStart_5365696 baseEnd_5365696 := by
    simpa [prefixWord, tailWord_5365696, baseEnd_5365696] using wordTrace_append hprefix tailTrace_5365696
  have hstable : (prefixWord ++ tailWord_5365696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365696).length < 2 ^ (prefixWord ++ tailWord_5365696).sum := by decide
  have hdescent : baseEnd_5365696 < baseStart_5365696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365727 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 2, 2, 2]
def baseStart_5365727 : Nat := 118140960795 + 5365727 * 2 ^ 59
def prefixEnd_5365727 : Nat := 4983230072969 + 3 ^ 40 * 5365727 * 2
def baseEnd_5365727 : Nat := 2755197011807433302135977

theorem tailTrace_5365727 : CollatzResearch.WordTrace tailWord_5365727 prefixEnd_5365727 2755197011807433302135977 := by
  unfold tailWord_5365727
  simp only [CollatzResearch.WordTrace]
  refine ⟨195704141431894947058919435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130469427621263298039279623 195704141431894947058919435)
  ·
    refine ⟨293556212147842420588379153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195704141431894947058919435 293556212147842420588379153)
    ·
      refine ⟨220167159110881815441284365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293556212147842420588379153 220167159110881815441284365)
      ·
        refine ⟨82562684666580680790481637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220167159110881815441284365 82562684666580680790481637)
        ·
          refine ⟨15480503374983877648215307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82562684666580680790481637 15480503374983877648215307)
          ·
            refine ⟨23220755062475816472322961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15480503374983877648215307 23220755062475816472322961)
            ·
              refine ⟨17415566296856862354242221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23220755062475816472322961 17415566296856862354242221)
              ·
                refine ⟨6530837361321323382840833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17415566296856862354242221 6530837361321323382840833)
                ·
                  refine ⟨4898128020990992537130625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6530837361321323382840833 4898128020990992537130625)
                  ·
                    refine ⟨3673596015743244402847969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4898128020990992537130625 3673596015743244402847969)
                    ·
                      refine ⟨2755197011807433302135977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3673596015743244402847969 2755197011807433302135977)
                      ·
                        rfl

theorem cell23_5365727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_5365727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365727 prefixEnd_5365727 := by exact prefixLift 5365727
  have htrace : WordTrace (prefixWord ++ tailWord_5365727) baseStart_5365727 baseEnd_5365727 := by
    simpa [prefixWord, tailWord_5365727, baseEnd_5365727] using wordTrace_append hprefix tailTrace_5365727
  have hstable : (prefixWord ++ tailWord_5365727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365727).length < 2 ^ (prefixWord ++ tailWord_5365727).sum := by decide
  have hdescent : baseEnd_5365727 < baseStart_5365727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365820 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 2, 2, 3]
def baseStart_5365820 : Nat := 118140960795 + 5365820 * 2 ^ 59
def prefixEnd_5365820 : Nat := 4983230072969 + 3 ^ 40 * 5365820 * 2
def baseEnd_5365820 : Nat := 2755244765508301438273049

theorem tailTrace_5365820 : CollatzResearch.WordTrace tailWord_5365820 prefixEnd_5365820 2755244765508301438273049 := by
  unfold tailWord_5365820
  simp only [CollatzResearch.WordTrace]
  refine ⟨97853766710279011971027457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130471688947038682628036609 97853766710279011971027457)
  ·
    refine ⟨73390325032709258978270593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97853766710279011971027457 73390325032709258978270593)
    ·
      refine ⟨55042743774531944233702945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73390325032709258978270593 55042743774531944233702945)
      ·
        refine ⟨41282057830898958175277209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55042743774531944233702945 41282057830898958175277209)
        ·
          refine ⟨30961543373174218631457907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41282057830898958175277209 30961543373174218631457907)
          ·
            refine ⟨46442315059761327947186861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30961543373174218631457907 46442315059761327947186861)
            ·
              refine ⟨17415868147410497980195073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46442315059761327947186861 17415868147410497980195073)
              ·
                refine ⟨13061901110557873485146305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17415868147410497980195073 13061901110557873485146305)
                ·
                  refine ⟨9796425832918405113859729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13061901110557873485146305 9796425832918405113859729)
                  ·
                    refine ⟨7347319374688803835394797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9796425832918405113859729 7347319374688803835394797)
                    ·
                      refine ⟨2755244765508301438273049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7347319374688803835394797 2755244765508301438273049)
                      ·
                        rfl

theorem cell23_5365820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2, 3].length) (baseStart_5365820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365820 prefixEnd_5365820 := by exact prefixLift 5365820
  have htrace : WordTrace (prefixWord ++ tailWord_5365820) baseStart_5365820 baseEnd_5365820 := by
    simpa [prefixWord, tailWord_5365820, baseEnd_5365820] using wordTrace_append hprefix tailTrace_5365820
  have hstable : (prefixWord ++ tailWord_5365820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365820).length < 2 ^ (prefixWord ++ tailWord_5365820).sum := by decide
  have hdescent : baseEnd_5365820 < baseStart_5365820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365850 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3]
def baseStart_5365850 : Nat := 118140960795 + 5365850 * 2 ^ 59
def prefixEnd_5365850 : Nat := 4983230072969 + 3 ^ 40 * 5365850 * 2
def baseEnd_5365850 : Nat := 2755260169927936320897911

theorem tailTrace_5365850 : CollatzResearch.WordTrace tailWord_5365850 prefixEnd_5365850 2755260169927936320897911 := by
  unfold tailWord_5365850
  simp only [CollatzResearch.WordTrace]
  refine ⟨48927156902612334766411751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130472418406966226043764669 48927156902612334766411751)
  ·
    refine ⟨73390735353918502149617627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48927156902612334766411751 73390735353918502149617627)
    ·
      refine ⟨110086103030877753224426441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73390735353918502149617627 110086103030877753224426441)
      ·
        refine ⟨82564577273158314918319831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110086103030877753224426441 82564577273158314918319831)
        ·
          refine ⟨123846865909737472377479747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82564577273158314918319831 123846865909737472377479747)
          ·
            refine ⟨185770298864606208566219621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123846865909737472377479747 185770298864606208566219621)
            ·
              refine ⟨34831931037113664106166179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185770298864606208566219621 34831931037113664106166179)
              ·
                refine ⟨52247896555670496159249269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34831931037113664106166179 52247896555670496159249269)
                ·
                  refine ⟨4898240302094109014929619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52247896555670496159249269 4898240302094109014929619)
                  ·
                    refine ⟨7347360453141163522394429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4898240302094109014929619 7347360453141163522394429)
                    ·
                      refine ⟨2755260169927936320897911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7347360453141163522394429 2755260169927936320897911)
                      ·
                        rfl

theorem cell23_5365850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_5365850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365850 prefixEnd_5365850 := by exact prefixLift 5365850
  have htrace : WordTrace (prefixWord ++ tailWord_5365850) baseStart_5365850 baseEnd_5365850 := by
    simpa [prefixWord, tailWord_5365850, baseEnd_5365850] using wordTrace_append hprefix tailTrace_5365850
  have hstable : (prefixWord ++ tailWord_5365850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365850).length < 2 ^ (prefixWord ++ tailWord_5365850).sum := by decide
  have hdescent : baseEnd_5365850 < baseStart_5365850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365860 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 1, 5, 2]
def baseStart_5365860 : Nat := 118140960795 + 5365860 * 2 ^ 59
def prefixEnd_5365860 : Nat := 4983230072969 + 3 ^ 40 * 5365860 * 2
def baseEnd_5365860 : Nat := 2755265304734481281772865

theorem tailTrace_5365860 : CollatzResearch.WordTrace tailWord_5365860 prefixEnd_5365860 2755265304734481281772865 := by
  unfold tailWord_5365860
  simp only [CollatzResearch.WordTrace]
  refine ⟨97854496170206555386755517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130472661560275407182340689 97854496170206555386755517)
  ·
    refine ⟨36695436063827458270033319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97854496170206555386755517 36695436063827458270033319)
    ·
      refine ⟨55043154095741187405049979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36695436063827458270033319 55043154095741187405049979)
      ·
        refine ⟨82564731143611781107574969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55043154095741187405049979 82564731143611781107574969)
        ·
          refine ⟨61923548357708835830681227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82564731143611781107574969 61923548357708835830681227)
          ·
            refine ⟨92885322536563253746021841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61923548357708835830681227 92885322536563253746021841)
            ·
              refine ⟨69663991902422440309516381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92885322536563253746021841 69663991902422440309516381)
              ·
                refine ⟨26123996963408415116068643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69663991902422440309516381 26123996963408415116068643)
                ·
                  refine ⟨39185995445112622674102965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26123996963408415116068643 39185995445112622674102965)
                  ·
                    refine ⟨3673687072979308375697153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39185995445112622674102965 3673687072979308375697153)
                    ·
                      refine ⟨2755265304734481281772865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3673687072979308375697153 2755265304734481281772865)
                      ·
                        rfl

theorem cell23_5365860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_5365860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365860 prefixEnd_5365860 := by exact prefixLift 5365860
  have htrace : WordTrace (prefixWord ++ tailWord_5365860) baseStart_5365860 baseEnd_5365860 := by
    simpa [prefixWord, tailWord_5365860, baseEnd_5365860] using wordTrace_append hprefix tailTrace_5365860
  have hstable : (prefixWord ++ tailWord_5365860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365860).length < 2 ^ (prefixWord ++ tailWord_5365860).sum := by decide
  have hdescent : baseEnd_5365860 < baseStart_5365860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365884 : List Nat := [2, 2, 2, 1, 1, 5, 1, 4, 1, 1, 3]
def baseStart_5365884 : Nat := 118140960795 + 5365884 * 2 ^ 59
def prefixEnd_5365884 : Nat := 4983230072969 + 3 ^ 40 * 5365884 * 2
def baseEnd_5365884 : Nat := 2755277628270189187872755

theorem tailTrace_5365884 : CollatzResearch.WordTrace tailWord_5365884 prefixEnd_5365884 2755277628270189187872755 := by
  unfold tailWord_5365884
  simp only [CollatzResearch.WordTrace]
  refine ⟨97854933846163081436192353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130473245128217441914923137 97854933846163081436192353)
  ·
    refine ⟨73391200384622311077144265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97854933846163081436192353 73391200384622311077144265)
    ·
      refine ⟨55043400288466733307858199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73391200384622311077144265 55043400288466733307858199)
      ·
        refine ⟨82565100432700099961787299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55043400288466733307858199 82565100432700099961787299)
        ·
          refine ⟨123847650649050149942680949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82565100432700099961787299 123847650649050149942680949)
          ·
            refine ⟨11610717248348451557126339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123847650649050149942680949 11610717248348451557126339)
            ·
              refine ⟨17416075872522677335689509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11610717248348451557126339 17416075872522677335689509)
              ·
                refine ⟨3265514226098002000441783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17416075872522677335689509 3265514226098002000441783)
                ·
                  refine ⟨4898271339147003000662675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3265514226098002000441783 4898271339147003000662675)
                  ·
                    refine ⟨7347407008720504500994013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4898271339147003000662675 7347407008720504500994013)
                    ·
                      refine ⟨2755277628270189187872755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7347407008720504500994013 2755277628270189187872755)
                      ·
                        rfl

theorem cell23_5365884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 1, 1, 3].length) (baseStart_5365884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365884 prefixEnd_5365884 := by exact prefixLift 5365884
  have htrace : WordTrace (prefixWord ++ tailWord_5365884) baseStart_5365884 baseEnd_5365884 := by
    simpa [prefixWord, tailWord_5365884, baseEnd_5365884] using wordTrace_append hprefix tailTrace_5365884
  have hstable : (prefixWord ++ tailWord_5365884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365884).length < 2 ^ (prefixWord ++ tailWord_5365884).sum := by decide
  have hdescent : baseEnd_5365884 < baseStart_5365884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365911 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 2, 3, 2]
def baseStart_5365911 : Nat := 118140960795 + 5365911 * 2 ^ 59
def prefixEnd_5365911 : Nat := 4983230072969 + 3 ^ 40 * 5365911 * 2
def baseEnd_5365911 : Nat := 2755291492247860582235131

theorem tailTrace_5365911 : CollatzResearch.WordTrace tailWord_5365911 prefixEnd_5365911 2755291492247860582235131 := by
  unfold tailWord_5365911
  simp only [CollatzResearch.WordTrace]
  refine ⟨195710852463228346483617587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130473901642152230989078391 195710852463228346483617587)
  ·
    refine ⟨293566278694842519725426381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195710852463228346483617587 293566278694842519725426381)
    ·
      refine ⟨110087354510565944897034893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293566278694842519725426381 110087354510565944897034893)
      ·
        refine ⟨41282757941462229336388085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110087354510565944897034893 41282757941462229336388085)
        ·
          refine ⟨3870258557012084000286383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41282757941462229336388085 3870258557012084000286383)
          ·
            refine ⟨5805387835518126000429575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3870258557012084000286383 5805387835518126000429575)
            ·
              refine ⟨8708081753277189000644363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5805387835518126000429575 8708081753277189000644363)
              ·
                refine ⟨13062122629915783500966545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8708081753277189000644363 13062122629915783500966545)
                ·
                  refine ⟨9796591972436837625724909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13062122629915783500966545 9796591972436837625724909)
                  ·
                    refine ⟨3673721989663814109646841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9796591972436837625724909 3673721989663814109646841)
                    ·
                      refine ⟨2755291492247860582235131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3673721989663814109646841 2755291492247860582235131)
                      ·
                        rfl

theorem cell23_5365911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 3, 2].length) (baseStart_5365911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365911 prefixEnd_5365911 := by exact prefixLift 5365911
  have htrace : WordTrace (prefixWord ++ tailWord_5365911) baseStart_5365911 baseEnd_5365911 := by
    simpa [prefixWord, tailWord_5365911, baseEnd_5365911] using wordTrace_append hprefix tailTrace_5365911
  have hstable : (prefixWord ++ tailWord_5365911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365911).length < 2 ^ (prefixWord ++ tailWord_5365911).sum := by decide
  have hdescent : baseEnd_5365911 < baseStart_5365911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365918 : List Nat := [4, 3, 1, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_5365918 : Nat := 118140960795 + 5365918 * 2 ^ 59
def prefixEnd_5365918 : Nat := 4983230072969 + 3 ^ 40 * 5365918 * 2
def baseEnd_5365918 : Nat := 2755295086612442054847599

theorem tailTrace_5365918 : CollatzResearch.WordTrace tailWord_5365918 prefixEnd_5365918 2755295086612442054847599 := by
  unfold tailWord_5365918
  simp only [CollatzResearch.WordTrace]
  refine ⟨24463888471775373334890301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130474071849468657786081605 24463888471775373334890301)
  ·
    refine ⟨9173958176915765000583863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24463888471775373334890301 9173958176915765000583863)
    ·
      refine ⟨13760937265373647500875795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9173958176915765000583863 13760937265373647500875795)
      ·
        refine ⟨20641405898060471251313693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13760937265373647500875795 20641405898060471251313693)
        ·
          refine ⟨7740527211772676719242635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20641405898060471251313693 7740527211772676719242635)
          ·
            refine ⟨11610790817659015078863953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7740527211772676719242635 11610790817659015078863953)
            ·
              refine ⟨8708093113244261309147965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11610790817659015078863953 8708093113244261309147965)
              ·
                refine ⟨3265534917466597990930487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8708093113244261309147965 3265534917466597990930487)
                ·
                  refine ⟨4898302376199896986395731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3265534917466597990930487 4898302376199896986395731)
                  ·
                    refine ⟨7347453564299845479593597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4898302376199896986395731 7347453564299845479593597)
                    ·
                      refine ⟨2755295086612442054847599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7347453564299845479593597 2755295086612442054847599)
                      ·
                        rfl

theorem cell23_5365918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_5365918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365918 prefixEnd_5365918 := by exact prefixLift 5365918
  have htrace : WordTrace (prefixWord ++ tailWord_5365918) baseStart_5365918 baseEnd_5365918 := by
    simpa [prefixWord, tailWord_5365918, baseEnd_5365918] using wordTrace_append hprefix tailTrace_5365918
  have hstable : (prefixWord ++ tailWord_5365918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365918).length < 2 ^ (prefixWord ++ tailWord_5365918).sum := by decide
  have hdescent : baseEnd_5365918 < baseStart_5365918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365920 : List Nat := [2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 4]
def baseStart_5365920 : Nat := 118140960795 + 5365920 * 2 ^ 59
def prefixEnd_5365920 : Nat := 4983230072969 + 3 ^ 40 * 5365920 * 2
def baseEnd_5365920 : Nat := 2755296113573751047022589

theorem tailTrace_5365920 : CollatzResearch.WordTrace tailWord_5365920 prefixEnd_5365920 2755296113573751047022589 := by
  unfold tailWord_5365920
  simp only [CollatzResearch.WordTrace]
  refine ⟨97855590360097870510347607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130474120480130494013796809 97855590360097870510347607)
  ·
    refine ⟨146783385540146805765521411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97855590360097870510347607 146783385540146805765521411)
    ·
      refine ⟨220175078310220208648282117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146783385540146805765521411 220175078310220208648282117)
      ·
        refine ⟨41282827183166289121552897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220175078310220208648282117 41282827183166289121552897)
        ·
          refine ⟨30962120387374716841164673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41282827183166289121552897 30962120387374716841164673)
          ·
            refine ⟨23221590290531037630873505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30962120387374716841164673 23221590290531037630873505)
            ·
              refine ⟨17416192717898278223155129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23221590290531037630873505 17416192717898278223155129)
              ·
                refine ⟨13062144538423708667366347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17416192717898278223155129 13062144538423708667366347)
                ·
                  refine ⟨19593216807635563001049521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13062144538423708667366347 19593216807635563001049521)
                  ·
                    refine ⟨14694912605726672250787141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19593216807635563001049521 14694912605726672250787141)
                    ·
                      refine ⟨2755296113573751047022589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14694912605726672250787141 2755296113573751047022589)
                      ·
                        rfl

theorem cell23_5365920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_5365920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365920 prefixEnd_5365920 := by exact prefixLift 5365920
  have htrace : WordTrace (prefixWord ++ tailWord_5365920) baseStart_5365920 baseEnd_5365920 := by
    simpa [prefixWord, tailWord_5365920, baseEnd_5365920] using wordTrace_append hprefix tailTrace_5365920
  have hstable : (prefixWord ++ tailWord_5365920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365920).length < 2 ^ (prefixWord ++ tailWord_5365920).sum := by decide
  have hdescent : baseEnd_5365920 < baseStart_5365920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365954 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_5365954 : Nat := 118140960795 + 5365954 * 2 ^ 59
def prefixEnd_5365954 : Nat := 4983230072969 + 3 ^ 40 * 5365954 * 2
def baseEnd_5365954 : Nat := 2755313571916003913997433

theorem tailTrace_5365954 : CollatzResearch.WordTrace tailWord_5365954 prefixEnd_5365954 2755313571916003913997433 := by
  unfold tailWord_5365954
  simp only [CollatzResearch.WordTrace]
  refine ⟨48928105200518141206858229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130474947201381709884955277 48928105200518141206858229)
  ·
    refine ⟨4587009862548575738142959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48928105200518141206858229 4587009862548575738142959)
    ·
      refine ⟨6880514793822863607214439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4587009862548575738142959 6880514793822863607214439)
      ·
        refine ⟨10320772190734295410821659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6880514793822863607214439 10320772190734295410821659)
        ·
          refine ⟨15481158286101443116232489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10320772190734295410821659 15481158286101443116232489)
          ·
            refine ⟨11610868714576082337174367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15481158286101443116232489 11610868714576082337174367)
            ·
              refine ⟨17416303071864123505761551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11610868714576082337174367 17416303071864123505761551)
              ·
                refine ⟨26124454607796185258642327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17416303071864123505761551 26124454607796185258642327)
                ·
                  refine ⟨39186681911694277887963491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26124454607796185258642327 39186681911694277887963491)
                  ·
                    refine ⟨58780022867541416831945237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39186681911694277887963491 58780022867541416831945237)
                    ·
                      refine ⟨2755313571916003913997433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58780022867541416831945237 2755313571916003913997433)
                      ·
                        rfl

theorem cell23_5365954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_5365954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365954 prefixEnd_5365954 := by exact prefixLift 5365954
  have htrace : WordTrace (prefixWord ++ tailWord_5365954) baseStart_5365954 baseEnd_5365954 := by
    simpa [prefixWord, tailWord_5365954, baseEnd_5365954] using wordTrace_append hprefix tailTrace_5365954
  have hstable : (prefixWord ++ tailWord_5365954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365954).length < 2 ^ (prefixWord ++ tailWord_5365954).sum := by decide
  have hdescent : baseEnd_5365954 < baseStart_5365954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365957 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 2, 1, 3]
def baseStart_5365957 : Nat := 118140960795 + 5365957 * 2 ^ 59
def prefixEnd_5365957 : Nat := 4983230072969 + 3 ^ 40 * 5365957 * 2
def baseEnd_5365957 : Nat := 2755315112357967402259919

theorem tailTrace_5365957 : CollatzResearch.WordTrace tailWord_5365957 prefixEnd_5365957 2755315112357967402259919 := by
  unfold tailWord_5365957
  simp only [CollatzResearch.WordTrace]
  refine ⟨195712530221061696339792125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130475020147374464226528083 195712530221061696339792125)
  ·
    refine ⟨73392198832898136127422047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195712530221061696339792125 73392198832898136127422047)
    ·
      refine ⟨110088298249347204191133071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73392198832898136127422047 110088298249347204191133071)
      ·
        refine ⟨165132447374020806286699607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110088298249347204191133071 165132447374020806286699607)
        ·
          refine ⟨247698671061031209430049411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165132447374020806286699607 247698671061031209430049411)
          ·
            refine ⟨371548006591546814145074117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247698671061031209430049411 371548006591546814145074117)
            ·
              refine ⟨69665251235915027652201397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 371548006591546814145074117 69665251235915027652201397)
              ·
                refine ⟨6531117303367033842393881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69665251235915027652201397 6531117303367033842393881)
                ·
                  refine ⟨4898337977525275381795411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6531117303367033842393881 4898337977525275381795411)
                  ·
                    refine ⟨7347506966287913072693117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4898337977525275381795411 7347506966287913072693117)
                    ·
                      refine ⟨2755315112357967402259919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7347506966287913072693117 2755315112357967402259919)
                      ·
                        rfl

theorem cell23_5365957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 1, 3].length) (baseStart_5365957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365957 prefixEnd_5365957 := by exact prefixLift 5365957
  have htrace : WordTrace (prefixWord ++ tailWord_5365957) baseStart_5365957 baseEnd_5365957 := by
    simpa [prefixWord, tailWord_5365957, baseEnd_5365957] using wordTrace_append hprefix tailTrace_5365957
  have hstable : (prefixWord ++ tailWord_5365957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365957).length < 2 ^ (prefixWord ++ tailWord_5365957).sum := by decide
  have hdescent : baseEnd_5365957 < baseStart_5365957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365964 : List Nat := [2, 2, 1, 6, 1, 2, 2, 7]
def baseStart_5365964 : Nat := 118140960795 + 5365964 * 2 ^ 59
def prefixEnd_5365964 : Nat := 4983230072969 + 3 ^ 40 * 5365964 * 2
def baseEnd_5365964 : Nat := 102048840989724032402681

theorem tailTrace_5365964 : CollatzResearch.WordTrace tailWord_5365964 prefixEnd_5365964 102048840989724032402681 := by
  unfold tailWord_5365964
  simp only [CollatzResearch.WordTrace]
  refine ⟨97856392766018168267648473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130475190354690891023531297 97856392766018168267648473)
  ·
    refine ⟨73392294574513626200736355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97856392766018168267648473 73392294574513626200736355)
    ·
      refine ⟨110088441861770439301104533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73392294574513626200736355 110088441861770439301104533)
      ·
        refine ⟨5160395712270489342239275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110088441861770439301104533 5160395712270489342239275)
        ·
          refine ⟨7740593568405734013358913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5160395712270489342239275 7740593568405734013358913)
          ·
            refine ⟨5805445176304300510019185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7740593568405734013358913 5805445176304300510019185)
            ·
              refine ⟨4354083882228225382514389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5805445176304300510019185 4354083882228225382514389)
              ·
                refine ⟨102048840989724032402681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4354083882228225382514389 102048840989724032402681)
                ·
                  rfl

theorem cell23_5365964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 7].length) (baseStart_5365964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365964 prefixEnd_5365964 := by exact prefixLift 5365964
  have htrace : WordTrace (prefixWord ++ tailWord_5365964) baseStart_5365964 baseEnd_5365964 := by
    simpa [prefixWord, tailWord_5365964, baseEnd_5365964] using wordTrace_append hprefix tailTrace_5365964
  have hstable : (prefixWord ++ tailWord_5365964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365964).length < 2 ^ (prefixWord ++ tailWord_5365964).sum := by decide
  have hdescent : baseEnd_5365964 < baseStart_5365964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5365970 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_5365970 : Nat := 118140960795 + 5365970 * 2 ^ 59
def prefixEnd_5365970 : Nat := 4983230072969 + 3 ^ 40 * 5365970 * 2
def baseEnd_5365970 : Nat := 2755321787606475851397359

theorem tailTrace_5365970 : CollatzResearch.WordTrace tailWord_5365970 prefixEnd_5365970 2755321787606475851397359 := by
  unfold tailWord_5365970
  simp only [CollatzResearch.WordTrace]
  refine ⟨48928251092503649890003841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130475336246676399706676909 48928251092503649890003841)
  ·
    refine ⟨36696188319377737417502881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48928251092503649890003841 36696188319377737417502881)
    ·
      refine ⟨27522141239533303063127161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36696188319377737417502881 27522141239533303063127161)
      ·
        refine ⟨20641605929649977297345371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27522141239533303063127161 20641605929649977297345371)
        ·
          refine ⟨30962408894474965946018057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20641605929649977297345371 30962408894474965946018057)
          ·
            refine ⟨23221806670856224459513543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30962408894474965946018057 23221806670856224459513543)
            ·
              refine ⟨34832710006284336689270315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23221806670856224459513543 34832710006284336689270315)
              ·
                refine ⟨52249065009426505033905473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34832710006284336689270315 52249065009426505033905473)
                ·
                  refine ⟨39186798757069878775429105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52249065009426505033905473 39186798757069878775429105)
                  ·
                    refine ⟨29390099067802409081571829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39186798757069878775429105 29390099067802409081571829)
                    ·
                      refine ⟨2755321787606475851397359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29390099067802409081571829 2755321787606475851397359)
                      ·
                        rfl

theorem cell23_5365970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_5365970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5365970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5365970 prefixEnd_5365970 := by exact prefixLift 5365970
  have htrace : WordTrace (prefixWord ++ tailWord_5365970) baseStart_5365970 baseEnd_5365970 := by
    simpa [prefixWord, tailWord_5365970, baseEnd_5365970] using wordTrace_append hprefix tailTrace_5365970
  have hstable : (prefixWord ++ tailWord_5365970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5365970).length < 2 ^ (prefixWord ++ tailWord_5365970).sum := by decide
  have hdescent : baseEnd_5365970 < baseStart_5365970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5365970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366014 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_5366014 : Nat := 118140960795 + 5366014 * 2 ^ 59
def prefixEnd_5366014 : Nat := 4983230072969 + 3 ^ 40 * 5366014 * 2
def baseEnd_5366014 : Nat := 2755344380755273679247157

theorem tailTrace_5366014 : CollatzResearch.WordTrace tailWord_5366014 prefixEnd_5366014 2755344380755273679247157 := by
  unfold tailWord_5366014
  simp only [CollatzResearch.WordTrace]
  refine ⟨24464326147731899384327137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130476406121236796716411397 24464326147731899384327137)
  ·
    refine ⟨18348244610798924538245353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24464326147731899384327137 18348244610798924538245353)
    ·
      refine ⟨13761183458099193403684015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18348244610798924538245353 13761183458099193403684015)
      ·
        refine ⟨20641775187148790105526023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13761183458099193403684015 20641775187148790105526023)
        ·
          refine ⟨30962662780723185158289035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20641775187148790105526023 30962662780723185158289035)
          ·
            refine ⟨46443994171084777737433553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30962662780723185158289035 46443994171084777737433553)
            ·
              refine ⟨34832995628313583303075165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46443994171084777737433553 34832995628313583303075165)
              ·
                refine ⟨13062373360617593738653187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34832995628313583303075165 13062373360617593738653187)
                ·
                  refine ⟨19593560040926390607979781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13062373360617593738653187 19593560040926390607979781)
                  ·
                    refine ⟨3673792507673698238996209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19593560040926390607979781 3673792507673698238996209)
                    ·
                      refine ⟨2755344380755273679247157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3673792507673698238996209 2755344380755273679247157)
                      ·
                        rfl

theorem cell23_5366014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_5366014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366014 prefixEnd_5366014 := by exact prefixLift 5366014
  have htrace : WordTrace (prefixWord ++ tailWord_5366014) baseStart_5366014 baseEnd_5366014 := by
    simpa [prefixWord, tailWord_5366014, baseEnd_5366014] using wordTrace_append hprefix tailTrace_5366014
  have hstable : (prefixWord ++ tailWord_5366014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366014).length < 2 ^ (prefixWord ++ tailWord_5366014).sum := by decide
  have hdescent : baseEnd_5366014 < baseStart_5366014 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366018 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 1, 3, 2]
def baseStart_5366018 : Nat := 118140960795 + 5366018 * 2 ^ 59
def prefixEnd_5366018 : Nat := 4983230072969 + 3 ^ 40 * 5366018 * 2
def baseEnd_5366018 : Nat := 2755346434677891663597139

theorem tailTrace_5366018 : CollatzResearch.WordTrace tailWord_5366018 prefixEnd_5366018 2755346434677891663597139 := by
  unfold tailWord_5366018
  simp only [CollatzResearch.WordTrace]
  refine ⟨48928688768460175939440677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130476503382560469171841805 48928688768460175939440677)
  ·
    refine ⟨9174129144086282988645127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48928688768460175939440677 9174129144086282988645127)
    ·
      refine ⟨13761193716129424482967691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9174129144086282988645127 13761193716129424482967691)
      ·
        refine ⟨20641790574194136724451537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13761193716129424482967691 20641790574194136724451537)
        ·
          refine ⟨15481342930645602543338653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20641790574194136724451537 15481342930645602543338653)
          ·
            refine ⟨5805503598992100953751995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15481342930645602543338653 5805503598992100953751995)
            ·
              refine ⟨8708255398488151430627993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5805503598992100953751995 8708255398488151430627993)
              ·
                refine ⟨6531191548866113572970995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8708255398488151430627993 6531191548866113572970995)
                ·
                  refine ⟨9796787323299170359456493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6531191548866113572970995 9796787323299170359456493)
                  ·
                    refine ⟨3673795246237188884796185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9796787323299170359456493 3673795246237188884796185)
                    ·
                      refine ⟨2755346434677891663597139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3673795246237188884796185 2755346434677891663597139)
                      ·
                        rfl

theorem cell23_5366018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_5366018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366018 prefixEnd_5366018 := by exact prefixLift 5366018
  have htrace : WordTrace (prefixWord ++ tailWord_5366018) baseStart_5366018 baseEnd_5366018 := by
    simpa [prefixWord, tailWord_5366018, baseEnd_5366018] using wordTrace_append hprefix tailTrace_5366018
  have hstable : (prefixWord ++ tailWord_5366018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366018).length < 2 ^ (prefixWord ++ tailWord_5366018).sum := by decide
  have hdescent : baseEnd_5366018 < baseStart_5366018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366060 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 5]
def baseStart_5366060 : Nat := 118140960795 + 5366060 * 2 ^ 59
def prefixEnd_5366060 : Nat := 4983230072969 + 3 ^ 40 * 5366060 * 2
def baseEnd_5366060 : Nat := 2755368000865380499271945

theorem tailTrace_5366060 : CollatzResearch.WordTrace tailWord_5366060 prefixEnd_5366060 2755368000865380499271945 := by
  unfold tailWord_5366060
  simp only [CollatzResearch.WordTrace]
  refine ⟨97858143469844272465395817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130477524626459029953861089 97858143469844272465395817)
  ·
    refine ⟨73393607602383204349046863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97858143469844272465395817 73393607602383204349046863)
    ·
      refine ⟨110090411403574806523570295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73393607602383204349046863 110090411403574806523570295)
      ·
        refine ⟨165135617105362209785355443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110090411403574806523570295 165135617105362209785355443)
        ·
          refine ⟨247703425658043314678033165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165135617105362209785355443 247703425658043314678033165)
          ·
            refine ⟨92888784621766243004262437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247703425658043314678033165 92888784621766243004262437)
            ·
              refine ⟨17416647116581170563299207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92888784621766243004262437 17416647116581170563299207)
              ·
                refine ⟨26124970674871755844948811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17416647116581170563299207 26124970674871755844948811)
                ·
                  refine ⟨39187456012307633767423217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26124970674871755844948811 39187456012307633767423217)
                  ·
                    refine ⟨29390592009230725325567413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39187456012307633767423217 29390592009230725325567413)
                    ·
                      refine ⟨2755368000865380499271945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29390592009230725325567413 2755368000865380499271945)
                      ·
                        rfl

theorem cell23_5366060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_5366060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366060 prefixEnd_5366060 := by exact prefixLift 5366060
  have htrace : WordTrace (prefixWord ++ tailWord_5366060) baseStart_5366060 baseEnd_5366060 := by
    simpa [prefixWord, tailWord_5366060, baseEnd_5366060] using wordTrace_append hprefix tailTrace_5366060
  have hstable : (prefixWord ++ tailWord_5366060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366060).length < 2 ^ (prefixWord ++ tailWord_5366060).sum := by decide
  have hdescent : baseEnd_5366060 < baseStart_5366060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366084 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 1, 7]
def baseStart_5366084 : Nat := 118140960795 + 5366084 * 2 ^ 59
def prefixEnd_5366084 : Nat := 4983230072969 + 3 ^ 40 * 5366084 * 2
def baseEnd_5366084 : Nat := 918460108133696135123945

theorem tailTrace_5366084 : CollatzResearch.WordTrace tailWord_5366084 prefixEnd_5366084 918460108133696135123945 := by
  unfold tailWord_5366084
  simp only [CollatzResearch.WordTrace]
  refine ⟨97858581145800798514832653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130478108194401064686443537 97858581145800798514832653)
  ·
    refine ⟨36696967929675299443062245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97858581145800798514832653 36696967929675299443062245)
    ·
      refine ⟨6880681486814118645574171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36696967929675299443062245 6880681486814118645574171)
      ·
        refine ⟨10321022230221177968361257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6880681486814118645574171 10321022230221177968361257)
        ·
          refine ⟨7740766672665883476270943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10321022230221177968361257 7740766672665883476270943)
          ·
            refine ⟨11611150008998825214406415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7740766672665883476270943 11611150008998825214406415)
            ·
              refine ⟨17416725013498237821609623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11611150008998825214406415 17416725013498237821609623)
              ·
                refine ⟨26125087520247356732414435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17416725013498237821609623 26125087520247356732414435)
                ·
                  refine ⟨39187631280371035098621653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26125087520247356732414435 39187631280371035098621653)
                  ·
                    refine ⟨918460108133696135123945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39187631280371035098621653 918460108133696135123945)
                    ·
                      rfl

theorem cell23_5366084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_5366084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366084 prefixEnd_5366084 := by exact prefixLift 5366084
  have htrace : WordTrace (prefixWord ++ tailWord_5366084) baseStart_5366084 baseEnd_5366084 := by
    simpa [prefixWord, tailWord_5366084, baseEnd_5366084] using wordTrace_append hprefix tailTrace_5366084
  have hstable : (prefixWord ++ tailWord_5366084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366084).length < 2 ^ (prefixWord ++ tailWord_5366084).sum := by decide
  have hdescent : baseEnd_5366084 < baseStart_5366084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366087 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 1, 6, 2]
def baseStart_5366087 : Nat := 118140960795 + 5366087 * 2 ^ 59
def prefixEnd_5366087 : Nat := 4983230072969 + 3 ^ 40 * 5366087 * 2
def baseEnd_5366087 : Nat := 2755381864843051893634321

theorem tailTrace_5366087 : CollatzResearch.WordTrace tailWord_5366087 prefixEnd_5366087 2755381864843051893634321 := by
  unfold tailWord_5366087
  simp only [CollatzResearch.WordTrace]
  refine ⟨195717271710590728542024515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130478181140393819028016343 195717271710590728542024515)
  ·
    refine ⟨293575907565886092813036773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195717271710590728542024515 293575907565886092813036773)
    ·
      refine ⟨55045482668603642402444395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293575907565886092813036773 55045482668603642402444395)
      ·
        refine ⟨82568224002905463603666593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55045482668603642402444395 82568224002905463603666593)
        ·
          refine ⟨61926168002179097702749945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82568224002905463603666593 61926168002179097702749945)
          ·
            refine ⟨46444626001634323277062459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61926168002179097702749945 46444626001634323277062459)
            ·
              refine ⟨69666939002451484915593689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46444626001634323277062459 69666939002451484915593689)
              ·
                refine ⟨52250204251838613686695267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69666939002451484915593689 52250204251838613686695267)
                ·
                  refine ⟨78375306377757920530042901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52250204251838613686695267 78375306377757920530042901)
                  ·
                    refine ⟨3673842486457402524845761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78375306377757920530042901 3673842486457402524845761)
                    ·
                      refine ⟨2755381864843051893634321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3673842486457402524845761 2755381864843051893634321)
                      ·
                        rfl

theorem cell23_5366087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_5366087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366087 prefixEnd_5366087 := by exact prefixLift 5366087
  have htrace : WordTrace (prefixWord ++ tailWord_5366087) baseStart_5366087 baseEnd_5366087 := by
    simpa [prefixWord, tailWord_5366087, baseEnd_5366087] using wordTrace_append hprefix tailTrace_5366087
  have hstable : (prefixWord ++ tailWord_5366087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366087).length < 2 ^ (prefixWord ++ tailWord_5366087).sum := by decide
  have hdescent : baseEnd_5366087 < baseStart_5366087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366114 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_5366114 : Nat := 118140960795 + 5366114 * 2 ^ 59
def prefixEnd_5366114 : Nat := 4983230072969 + 3 ^ 40 * 5366114 * 2
def baseEnd_5366114 : Nat := 918465242940241095998899

theorem tailTrace_5366114 : CollatzResearch.WordTrace tailWord_5366114 prefixEnd_5366114 918465242940241095998899 := by
  unfold tailWord_5366114
  simp only [CollatzResearch.WordTrace]
  refine ⟨48929564120373228038314349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130478837654328608102171597 48929564120373228038314349)
  ·
    refine ⟨18348586545139960514367881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48929564120373228038314349 18348586545139960514367881)
    ·
      refine ⟨13761439908854970385775911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18348586545139960514367881 13761439908854970385775911)
      ·
        refine ⟨20642159863282455578663867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13761439908854970385775911 20642159863282455578663867)
        ·
          refine ⟨30963239794923683367995801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20642159863282455578663867 30963239794923683367995801)
          ·
            refine ⟨23222429846192762525996851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30963239794923683367995801 23222429846192762525996851)
            ·
              refine ⟨34833644769289143788995277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23222429846192762525996851 34833644769289143788995277)
              ·
                refine ⟨13062616788483428920873229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34833644769289143788995277 13062616788483428920873229)
                ·
                  refine ⟨4898481295681285845327461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13062616788483428920873229 4898481295681285845327461)
                  ·
                    refine ⟨918465242940241095998899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4898481295681285845327461 918465242940241095998899)
                    ·
                      rfl

theorem cell23_5366114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_5366114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366114 prefixEnd_5366114 := by exact prefixLift 5366114
  have htrace : WordTrace (prefixWord ++ tailWord_5366114) baseStart_5366114 baseEnd_5366114 := by
    simpa [prefixWord, tailWord_5366114, baseEnd_5366114] using wordTrace_append hprefix tailTrace_5366114
  have hstable : (prefixWord ++ tailWord_5366114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366114).length < 2 ^ (prefixWord ++ tailWord_5366114).sum := by decide
  have hdescent : baseEnd_5366114 < baseStart_5366114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366204 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 1, 6]
def baseStart_5366204 : Nat := 118140960795 + 5366204 * 2 ^ 59
def prefixEnd_5366204 : Nat := 4983230072969 + 3 ^ 40 * 5366204 * 2
def baseEnd_5366204 : Nat := 918480647359875978623761

theorem tailTrace_5366204 : CollatzResearch.WordTrace tailWord_5366204 prefixEnd_5366204 918480647359875978623761 := by
  unfold tailWord_5366204
  simp only [CollatzResearch.WordTrace]
  refine ⟨97860769525583428762016833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130481026034111238349355777 97860769525583428762016833)
  ·
    refine ⟨73395577144187571571512625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97860769525583428762016833 73395577144187571571512625)
    ·
      refine ⟨55046682858140678678634469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73395577144187571571512625 55046682858140678678634469)
      ·
        refine ⟨10321253035901377252243963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55046682858140678678634469 10321253035901377252243963)
        ·
          refine ⟨15481879553852065878365945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10321253035901377252243963 15481879553852065878365945)
          ·
            refine ⟨11611409665389049408774459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15481879553852065878365945 11611409665389049408774459)
            ·
              refine ⟨17417114498083574113161689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11611409665389049408774459 17417114498083574113161689)
              ·
                refine ⟨13062835873562680584871267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17417114498083574113161689 13062835873562680584871267)
                ·
                  refine ⟨19594253810344020877306901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13062835873562680584871267 19594253810344020877306901)
                  ·
                    refine ⟨918480647359875978623761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19594253810344020877306901 918480647359875978623761)
                    ·
                      rfl

theorem cell23_5366204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_5366204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366204 prefixEnd_5366204 := by exact prefixLift 5366204
  have htrace : WordTrace (prefixWord ++ tailWord_5366204) baseStart_5366204 baseEnd_5366204 := by
    simpa [prefixWord, tailWord_5366204, baseEnd_5366204] using wordTrace_append hprefix tailTrace_5366204
  have hstable : (prefixWord ++ tailWord_5366204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366204).length < 2 ^ (prefixWord ++ tailWord_5366204).sum := by decide
  have hdescent : baseEnd_5366204 < baseStart_5366204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366244 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 8, 1, 3]
def baseStart_5366244 : Nat := 118140960795 + 5366244 * 2 ^ 59
def prefixEnd_5366244 : Nat := 4983230072969 + 3 ^ 40 * 5366244 * 2
def baseEnd_5366244 : Nat := 2755462481305807779371099

theorem tailTrace_5366244 : CollatzResearch.WordTrace tailWord_5366244 prefixEnd_5366244 2755462481305807779371099 := by
  unfold tailWord_5366244
  simp only [CollatzResearch.WordTrace]
  refine ⟨97861498985510972177744893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130481998647347962903659857 97861498985510972177744893)
  ·
    refine ⟨36698062119566614566654335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97861498985510972177744893 36698062119566614566654335)
    ·
      refine ⟨55047093179349921849981503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36698062119566614566654335 55047093179349921849981503)
      ·
        refine ⟨82570639769024882774972255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55047093179349921849981503 82570639769024882774972255)
        ·
          refine ⟨123855959653537324162458383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82570639769024882774972255 123855959653537324162458383)
          ·
            refine ⟨185783939480305986243687575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123855959653537324162458383 185783939480305986243687575)
            ·
              refine ⟨278675909220458979365531363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185783939480305986243687575 278675909220458979365531363)
              ·
                refine ⟨418013863830688469048297045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278675909220458979365531363 418013863830688469048297045)
                ·
                  refine ⟨4898599966765880496659731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 418013863830688469048297045 4898599966765880496659731)
                  ·
                    refine ⟨7347899950148820744989597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4898599966765880496659731 7347899950148820744989597)
                    ·
                      refine ⟨2755462481305807779371099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7347899950148820744989597 2755462481305807779371099)
                      ·
                        rfl

theorem cell23_5366244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_5366244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366244 prefixEnd_5366244 := by exact prefixLift 5366244
  have htrace : WordTrace (prefixWord ++ tailWord_5366244) baseStart_5366244 baseEnd_5366244 := by
    simpa [prefixWord, tailWord_5366244, baseEnd_5366244] using wordTrace_append hprefix tailTrace_5366244
  have hstable : (prefixWord ++ tailWord_5366244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366244).length < 2 ^ (prefixWord ++ tailWord_5366244).sum := by decide
  have hdescent : baseEnd_5366244 < baseStart_5366244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366247 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 2, 7]
def baseStart_5366247 : Nat := 118140960795 + 5366247 * 2 ^ 59
def prefixEnd_5366247 : Nat := 4983230072969 + 3 ^ 40 * 5366247 * 2
def baseEnd_5366247 : Nat := 918488007249257089211195

theorem tailTrace_5366247 : CollatzResearch.WordTrace tailWord_5366247 prefixEnd_5366247 918488007249257089211195 := by
  unfold tailWord_5366247
  simp only [CollatzResearch.WordTrace]
  refine ⟨195723107390011075867848995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130482071593340717245232663 195723107390011075867848995)
  ·
    refine ⟨293584661085016613801773493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195723107390011075867848995 293584661085016613801773493)
    ·
      refine ⟨27523561976720307543916265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 293584661085016613801773493 27523561976720307543916265)
      ·
        refine ⟨20642671482540230657937199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27523561976720307543916265 20642671482540230657937199)
        ·
          refine ⟨30964007223810345986905799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20642671482540230657937199 30964007223810345986905799)
          ·
            refine ⟨46446010835715518980358699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30964007223810345986905799 46446010835715518980358699)
            ·
              refine ⟨69669016253573278470538049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46446010835715518980358699 69669016253573278470538049)
              ·
                refine ⟨52251762190179958852903537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69669016253573278470538049 52251762190179958852903537)
                ·
                  refine ⟨39188821642634969139677653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52251762190179958852903537 39188821642634969139677653)
                  ·
                    refine ⟨918488007249257089211195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39188821642634969139677653 918488007249257089211195)
                    ·
                      rfl

theorem cell23_5366247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_5366247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366247 prefixEnd_5366247 := by exact prefixLift 5366247
  have htrace : WordTrace (prefixWord ++ tailWord_5366247) baseStart_5366247 baseEnd_5366247 := by
    simpa [prefixWord, tailWord_5366247, baseEnd_5366247] using wordTrace_append hprefix tailTrace_5366247
  have hstable : (prefixWord ++ tailWord_5366247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366247).length < 2 ^ (prefixWord ++ tailWord_5366247).sum := by decide
  have hdescent : baseEnd_5366247 < baseStart_5366247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366257 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_5366257 : Nat := 118140960795 + 5366257 * 2 ^ 59
def prefixEnd_5366257 : Nat := 4983230072969 + 3 ^ 40 * 5366257 * 2
def baseEnd_5366257 : Nat := 2755469156554316228508539

theorem tailTrace_5366257 : CollatzResearch.WordTrace tailWord_5366257 prefixEnd_5366257 2755469156554316228508539 := by
  unfold tailWord_5366257
  simp only [CollatzResearch.WordTrace]
  refine ⟨195723472119974847575713025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130482314746649898383808683 195723472119974847575713025)
  ·
    refine ⟨146792604089981135681784769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195723472119974847575713025 146792604089981135681784769)
    ·
      refine ⟨110094453067485851761338577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146792604089981135681784769 110094453067485851761338577)
      ·
        refine ⟨82570839800614388821003933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110094453067485851761338577 82570839800614388821003933)
        ·
          refine ⟨30964064925230395807876475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82570839800614388821003933 30964064925230395807876475)
          ·
            refine ⟨46446097387845593711814713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30964064925230395807876475 46446097387845593711814713)
            ·
              refine ⟨34834573040884195283861035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46446097387845593711814713 34834573040884195283861035)
              ·
                refine ⟨52251859561326292925791553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34834573040884195283861035 52251859561326292925791553)
                ·
                  refine ⟨39188894670994719694343665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52251859561326292925791553 39188894670994719694343665)
                  ·
                    refine ⟨29391671003246039770757749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39188894670994719694343665 29391671003246039770757749)
                    ·
                      refine ⟨2755469156554316228508539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29391671003246039770757749 2755469156554316228508539)
                      ·
                        rfl

theorem cell23_5366257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_5366257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366257 prefixEnd_5366257 := by exact prefixLift 5366257
  have htrace : WordTrace (prefixWord ++ tailWord_5366257) baseStart_5366257 baseEnd_5366257 := by
    simpa [prefixWord, tailWord_5366257, baseEnd_5366257] using wordTrace_append hprefix tailTrace_5366257
  have hstable : (prefixWord ++ tailWord_5366257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366257).length < 2 ^ (prefixWord ++ tailWord_5366257).sum := by decide
  have hdescent : baseEnd_5366257 < baseStart_5366257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366271 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 1, 3, 2]
def baseStart_5366271 : Nat := 118140960795 + 5366271 * 2 ^ 59
def prefixEnd_5366271 : Nat := 4983230072969 + 3 ^ 40 * 5366271 * 2
def baseEnd_5366271 : Nat := 2755476345283479173733475

theorem tailTrace_5366271 : CollatzResearch.WordTrace tailWord_5366271 prefixEnd_5366271 2755476345283479173733475 := by
  unfold tailWord_5366271
  simp only [CollatzResearch.WordTrace]
  refine ⟨195723982741924127966722667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130482655161282751977815111 195723982741924127966722667)
  ·
    refine ⟨293585974112886191950084001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195723982741924127966722667 293585974112886191950084001)
    ·
      refine ⟨220189480584664643962563001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293585974112886191950084001 220189480584664643962563001)
      ·
        refine ⟨165142110438498482971922251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220189480584664643962563001 165142110438498482971922251)
        ·
          refine ⟨247713165657747724457883377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165142110438498482971922251 247713165657747724457883377)
          ·
            refine ⟨185784874243310793343412533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247713165657747724457883377 185784874243310793343412533)
            ·
              refine ⟨17417331960310386875944925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185784874243310793343412533 17417331960310386875944925)
              ·
                refine ⟨6531499485116395078479347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17417331960310386875944925 6531499485116395078479347)
                ·
                  refine ⟨9797249227674592617719021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6531499485116395078479347 9797249227674592617719021)
                  ·
                    refine ⟨3673968460377972231644633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9797249227674592617719021 3673968460377972231644633)
                    ·
                      refine ⟨2755476345283479173733475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3673968460377972231644633 2755476345283479173733475)
                      ·
                        rfl

theorem cell23_5366271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_5366271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366271 prefixEnd_5366271 := by exact prefixLift 5366271
  have htrace : WordTrace (prefixWord ++ tailWord_5366271) baseStart_5366271 baseEnd_5366271 := by
    simpa [prefixWord, tailWord_5366271, baseEnd_5366271] using wordTrace_append hprefix tailTrace_5366271
  have hstable : (prefixWord ++ tailWord_5366271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366271).length < 2 ^ (prefixWord ++ tailWord_5366271).sum := by decide
  have hdescent : baseEnd_5366271 < baseStart_5366271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366277 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_5366277 : Nat := 118140960795 + 5366277 * 2 ^ 59
def prefixEnd_5366277 : Nat := 4983230072969 + 3 ^ 40 * 5366277 * 2
def baseEnd_5366277 : Nat := 918493142055802050086149

theorem tailTrace_5366277 : CollatzResearch.WordTrace tailWord_5366277 prefixEnd_5366277 918493142055802050086149 := by
  unfold tailWord_5366277
  simp only [CollatzResearch.WordTrace]
  refine ⟨195724201579902390991441085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130482801053268260660960723 195724201579902390991441085)
  ·
    refine ⟨73396575592463396621790407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195724201579902390991441085 73396575592463396621790407)
    ·
      refine ⟨110094863388695094932685611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73396575592463396621790407 110094863388695094932685611)
      ·
        refine ⟨165142295083042642399028417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110094863388695094932685611 165142295083042642399028417)
        ·
          refine ⟨123856721312281981799271313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165142295083042642399028417 123856721312281981799271313)
          ·
            refine ⟨92892540984211486349453485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123856721312281981799271313 92892540984211486349453485)
            ·
              refine ⟨34834702869079307381045057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92892540984211486349453485 34834702869079307381045057)
              ·
                refine ⟨26126027151809480535783793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34834702869079307381045057 26126027151809480535783793)
                ·
                  refine ⟨19594520363857110401837845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26126027151809480535783793 19594520363857110401837845)
                  ·
                    refine ⟨918493142055802050086149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19594520363857110401837845 918493142055802050086149)
                    ·
                      rfl

theorem cell23_5366277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_5366277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366277 prefixEnd_5366277 := by exact prefixLift 5366277
  have htrace : WordTrace (prefixWord ++ tailWord_5366277) baseStart_5366277 baseEnd_5366277 := by
    simpa [prefixWord, tailWord_5366277, baseEnd_5366277] using wordTrace_append hprefix tailTrace_5366277
  have hstable : (prefixWord ++ tailWord_5366277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366277).length < 2 ^ (prefixWord ++ tailWord_5366277).sum := by decide
  have hdescent : baseEnd_5366277 < baseStart_5366277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366295 : List Nat := [1, 1, 3, 6, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5366295 : Nat := 118140960795 + 5366295 * 2 ^ 59
def prefixEnd_5366295 : Nat := 4983230072969 + 3 ^ 40 * 5366295 * 2
def baseEnd_5366295 : Nat := 2755488668819187079833365

theorem tailTrace_5366295 : CollatzResearch.WordTrace tailWord_5366295 prefixEnd_5366295 2755488668819187079833365 := by
  unfold tailWord_5366295
  simp only [CollatzResearch.WordTrace]
  refine ⟨195724858093837180065596339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130483238729224786710397559 195724858093837180065596339)
  ·
    refine ⟨293587287140755770098394509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195724858093837180065596339 293587287140755770098394509)
    ·
      refine ⟨110095232677783413786897941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293587287140755770098394509 110095232677783413786897941)
      ·
        refine ⟨5160714031771097521260841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110095232677783413786897941 5160714031771097521260841)
        ·
          refine ⟨3870535523828323140945631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5160714031771097521260841 3870535523828323140945631)
          ·
            refine ⟨5805803285742484711418447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3870535523828323140945631 5805803285742484711418447)
            ·
              refine ⟨8708704928613727067127671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5805803285742484711418447 8708704928613727067127671)
              ·
                refine ⟨13063057392920590600691507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8708704928613727067127671 13063057392920590600691507)
                ·
                  refine ⟨19594586089380885901037261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13063057392920590600691507 19594586089380885901037261)
                  ·
                    refine ⟨7347969783517832212888973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19594586089380885901037261 7347969783517832212888973)
                    ·
                      refine ⟨2755488668819187079833365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7347969783517832212888973 2755488668819187079833365)
                      ·
                        rfl

theorem cell23_5366295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5366295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366295 prefixEnd_5366295 := by exact prefixLift 5366295
  have htrace : WordTrace (prefixWord ++ tailWord_5366295) baseStart_5366295 baseEnd_5366295 := by
    simpa [prefixWord, tailWord_5366295, baseEnd_5366295] using wordTrace_append hprefix tailTrace_5366295
  have hstable : (prefixWord ++ tailWord_5366295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366295).length < 2 ^ (prefixWord ++ tailWord_5366295).sum := by decide
  have hdescent : baseEnd_5366295 < baseStart_5366295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366347 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 7]
def baseStart_5366347 : Nat := 118140960795 + 5366347 * 2 ^ 59
def prefixEnd_5366347 : Nat := 4983230072969 + 3 ^ 40 * 5366347 * 2
def baseEnd_5366347 : Nat := 2755515369813220876383125

theorem tailTrace_5366347 : CollatzResearch.WordTrace tailWord_5366347 prefixEnd_5366347 2755515369813220876383125 := by
  unfold tailWord_5366347
  simp only [CollatzResearch.WordTrace]
  refine ⟨195726754689648792946489295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130484503126432528630992863 195726754689648792946489295)
  ·
    refine ⟨293590132034473189419733943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195726754689648792946489295 293590132034473189419733943)
    ·
      refine ⟨440385198051709784129600915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293590132034473189419733943 440385198051709784129600915)
      ·
        refine ⟨660577797077564676194401373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440385198051709784129600915 660577797077564676194401373)
        ·
          refine ⟨247716673904086753572900515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 660577797077564676194401373 247716673904086753572900515)
          ·
            refine ⟨371575010856130130359350773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247716673904086753572900515 371575010856130130359350773)
            ·
              refine ⟨34835157267762199721189135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 371575010856130130359350773 34835157267762199721189135)
              ·
                refine ⟨52252735901643299581783703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34835157267762199721189135 52252735901643299581783703)
                ·
                  refine ⟨78379103852464949372675555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52252735901643299581783703 78379103852464949372675555)
                  ·
                    refine ⟨117568655778697424059013333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78379103852464949372675555 117568655778697424059013333)
                    ·
                      refine ⟨2755515369813220876383125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117568655778697424059013333 2755515369813220876383125)
                      ·
                        rfl

theorem cell23_5366347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_5366347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366347 prefixEnd_5366347 := by exact prefixLift 5366347
  have htrace : WordTrace (prefixWord ++ tailWord_5366347) baseStart_5366347 baseEnd_5366347 := by
    simpa [prefixWord, tailWord_5366347, baseEnd_5366347] using wordTrace_append hprefix tailTrace_5366347
  have hstable : (prefixWord ++ tailWord_5366347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366347).length < 2 ^ (prefixWord ++ tailWord_5366347).sum := by decide
  have hdescent : baseEnd_5366347 < baseStart_5366347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366354 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 4, 5]
def baseStart_5366354 : Nat := 118140960795 + 5366354 * 2 ^ 59
def prefixEnd_5366354 : Nat := 4983230072969 + 3 ^ 40 * 5366354 * 2
def baseEnd_5366354 : Nat := 918506321392600782998531

theorem tailTrace_5366354 : CollatzResearch.WordTrace tailWord_5366354 prefixEnd_5366354 918506321392600782998531 := by
  unfold tailWord_5366354
  simp only [CollatzResearch.WordTrace]
  refine ⟨48931752500155858285498529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130484673333748955427996077 48931752500155858285498529)
  ·
    refine ⟨36698814375116893714123897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48931752500155858285498529 36698814375116893714123897)
    ·
      refine ⟨27524110781337670285592923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36698814375116893714123897 27524110781337670285592923)
      ·
        refine ⟨41286166172006505428389385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27524110781337670285592923 41286166172006505428389385)
        ·
          refine ⟨30964624629004879071292039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41286166172006505428389385 30964624629004879071292039)
          ·
            refine ⟨46446936943507318606938059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30964624629004879071292039 46446936943507318606938059)
            ·
              refine ⟨69670405415260977910407089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46446936943507318606938059 69670405415260977910407089)
              ·
                refine ⟨52252804061445733432805317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69670405415260977910407089 52252804061445733432805317)
                ·
                  refine ⟨9797400761521075018650997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52252804061445733432805317 9797400761521075018650997)
                  ·
                    refine ⟨918506321392600782998531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9797400761521075018650997 918506321392600782998531)
                    ·
                      rfl

theorem cell23_5366354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_5366354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366354 prefixEnd_5366354 := by exact prefixLift 5366354
  have htrace : WordTrace (prefixWord ++ tailWord_5366354) baseStart_5366354 baseEnd_5366354 := by
    simpa [prefixWord, tailWord_5366354, baseEnd_5366354] using wordTrace_append hprefix tailTrace_5366354
  have hstable : (prefixWord ++ tailWord_5366354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366354).length < 2 ^ (prefixWord ++ tailWord_5366354).sum := by decide
  have hdescent : baseEnd_5366354 < baseStart_5366354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366367 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 2, 8]
def baseStart_5366367 : Nat := 118140960795 + 5366367 * 2 ^ 59
def prefixEnd_5366367 : Nat := 4983230072969 + 3 ^ 40 * 5366367 * 2
def baseEnd_5366367 : Nat := 918508546475436932711011

theorem tailTrace_5366367 : CollatzResearch.WordTrace tailWord_5366367 prefixEnd_5366367 918508546475436932711011 := by
  unfold tailWord_5366367
  simp only [CollatzResearch.WordTrace]
  refine ⟨195727484149576336362217355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130484989433050890908144903 195727484149576336362217355)
  ·
    refine ⟨293591226224364504543326033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195727484149576336362217355 293591226224364504543326033)
    ·
      refine ⟨220193419668273378407494525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293591226224364504543326033 220193419668273378407494525)
      ·
        refine ⟨82572532375602516902810447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 220193419668273378407494525 82572532375602516902810447)
        ·
          refine ⟨123858798563403775354215671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82572532375602516902810447 123858798563403775354215671)
          ·
            refine ⟨185788197845105663031323507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123858798563403775354215671 185788197845105663031323507)
            ·
              refine ⟨278682296767658494546985261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185788197845105663031323507 278682296767658494546985261)
              ·
                refine ⟨104505861287871935455119473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 278682296767658494546985261 104505861287871935455119473)
                ·
                  refine ⟨78379395965903951591339605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104505861287871935455119473 78379395965903951591339605)
                  ·
                    refine ⟨918508546475436932711011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78379395965903951591339605 918508546475436932711011)
                    ·
                      rfl

theorem cell23_5366367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_5366367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366367 prefixEnd_5366367 := by exact prefixLift 5366367
  have htrace : WordTrace (prefixWord ++ tailWord_5366367) baseStart_5366367 baseEnd_5366367 := by
    simpa [prefixWord, tailWord_5366367, baseEnd_5366367] using wordTrace_append hprefix tailTrace_5366367
  have hstable : (prefixWord ++ tailWord_5366367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366367).length < 2 ^ (prefixWord ++ tailWord_5366367).sum := by decide
  have hdescent : baseEnd_5366367 < baseStart_5366367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366401 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 3, 4]
def baseStart_5366401 : Nat := 118140960795 + 5366401 * 2 ^ 59
def prefixEnd_5366401 : Nat := 4983230072969 + 3 ^ 40 * 5366401 * 2
def baseEnd_5366401 : Nat := 918514365922854555035959

theorem tailTrace_5366401 : CollatzResearch.WordTrace tailWord_5366401 prefixEnd_5366401 918514365922854555035959 := by
  unfold tailWord_5366401
  simp only [CollatzResearch.WordTrace]
  refine ⟨195728724231453160168955057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130485816154302106779303371 195728724231453160168955057)
  ·
    refine ⟨146796543173589870126716293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195728724231453160168955057 146796543173589870126716293)
    ·
      refine ⟨27524351845048100648759305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146796543173589870126716293 27524351845048100648759305)
      ·
        refine ⟨20643263883786075486569479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27524351845048100648759305 20643263883786075486569479)
        ·
          refine ⟨30964895825679113229854219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20643263883786075486569479 30964895825679113229854219)
          ·
            refine ⟨46447343738518669844781329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30964895825679113229854219 46447343738518669844781329)
            ·
              refine ⟨34835507803889002383585997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46447343738518669844781329 34835507803889002383585997)
              ·
                refine ⟨13063315426458375893844749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34835507803889002383585997 13063315426458375893844749)
                ·
                  refine ⟨4898743284921890960191781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13063315426458375893844749 4898743284921890960191781)
                  ·
                    refine ⟨918514365922854555035959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4898743284921890960191781 918514365922854555035959)
                    ·
                      rfl

theorem cell23_5366401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_5366401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366401 prefixEnd_5366401 := by exact prefixLift 5366401
  have htrace : WordTrace (prefixWord ++ tailWord_5366401) baseStart_5366401 baseEnd_5366401 := by
    simpa [prefixWord, tailWord_5366401, baseEnd_5366401] using wordTrace_append hprefix tailTrace_5366401
  have hstable : (prefixWord ++ tailWord_5366401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366401).length < 2 ^ (prefixWord ++ tailWord_5366401).sum := by decide
  have hdescent : baseEnd_5366401 < baseStart_5366401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366402 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5366402 : Nat := 118140960795 + 5366402 * 2 ^ 59
def prefixEnd_5366402 : Nat := 4983230072969 + 3 ^ 40 * 5366402 * 2
def baseEnd_5366402 : Nat := 2755543611249218161195373

theorem tailTrace_5366402 : CollatzResearch.WordTrace tailWord_5366402 prefixEnd_5366402 2755543611249218161195373 := by
  unfold tailWord_5366402
  simp only [CollatzResearch.WordTrace]
  refine ⟨48932190176112384334935365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130485840469633024893160973 48932190176112384334935365)
  ·
    refine ⟨9174785658021072062800381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48932190176112384334935365 9174785658021072062800381)
    ·
      refine ⟨3440544621757902023550143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9174785658021072062800381 3440544621757902023550143)
      ·
        refine ⟨5160816932636853035325215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3440544621757902023550143 5160816932636853035325215)
        ·
          refine ⟨7741225398955279552987823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5160816932636853035325215 7741225398955279552987823)
          ·
            refine ⟨11611838098432919329481735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7741225398955279552987823 11611838098432919329481735)
            ·
              refine ⟨17417757147649378994222603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11611838098432919329481735 17417757147649378994222603)
              ·
                refine ⟨26126635721474068491333905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17417757147649378994222603 26126635721474068491333905)
                ·
                  refine ⟨19594976791105551368500429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26126635721474068491333905 19594976791105551368500429)
                  ·
                    refine ⟨7348116296664581763187661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19594976791105551368500429 7348116296664581763187661)
                    ·
                      refine ⟨2755543611249218161195373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7348116296664581763187661 2755543611249218161195373)
                      ·
                        rfl

theorem cell23_5366402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5366402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366402 prefixEnd_5366402 := by exact prefixLift 5366402
  have htrace : WordTrace (prefixWord ++ tailWord_5366402) baseStart_5366402 baseEnd_5366402 := by
    simpa [prefixWord, tailWord_5366402, baseEnd_5366402] using wordTrace_append hprefix tailTrace_5366402
  have hstable : (prefixWord ++ tailWord_5366402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366402).length < 2 ^ (prefixWord ++ tailWord_5366402).sum := by decide
  have hdescent : baseEnd_5366402 < baseStart_5366402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366418 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 3, 4]
def baseStart_5366418 : Nat := 118140960795 + 5366418 * 2 ^ 59
def prefixEnd_5366418 : Nat := 4983230072969 + 3 ^ 40 * 5366418 * 2
def baseEnd_5366418 : Nat := 918517275646563366198433

theorem tailTrace_5366418 : CollatzResearch.WordTrace tailWord_5366418 prefixEnd_5366418 918517275646563366198433 := by
  unfold tailWord_5366418
  simp only [CollatzResearch.WordTrace]
  refine ⟨48932336068097893018080977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130486229514927714714882605 48932336068097893018080977)
  ·
    refine ⟨36699252051073419763560733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48932336068097893018080977 36699252051073419763560733)
    ·
      refine ⟨13762219519152532411335275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36699252051073419763560733 13762219519152532411335275)
      ·
        refine ⟨20643329278728798617002913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13762219519152532411335275 20643329278728798617002913)
        ·
          refine ⟨15482496959046598962752185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20643329278728798617002913 15482496959046598962752185)
          ·
            refine ⟨11611872719284949222064139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15482496959046598962752185 11611872719284949222064139)
            ·
              refine ⟨17417809078927423833096209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11611872719284949222064139 17417809078927423833096209)
              ·
                refine ⟨13063356809195567874822157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17417809078927423833096209 13063356809195567874822157)
                ·
                  refine ⟨4898758803448337953058309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13063356809195567874822157 4898758803448337953058309)
                  ·
                    refine ⟨918517275646563366198433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4898758803448337953058309 918517275646563366198433)
                    ·
                      rfl

theorem cell23_5366418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_5366418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366418 prefixEnd_5366418 := by exact prefixLift 5366418
  have htrace : WordTrace (prefixWord ++ tailWord_5366418) baseStart_5366418 baseEnd_5366418 := by
    simpa [prefixWord, tailWord_5366418, baseEnd_5366418] using wordTrace_append hprefix tailTrace_5366418
  have hstable : (prefixWord ++ tailWord_5366418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366418).length < 2 ^ (prefixWord ++ tailWord_5366418).sum := by decide
  have hdescent : baseEnd_5366418 < baseStart_5366418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366428 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 2, 2, 3]
def baseStart_5366428 : Nat := 118140960795 + 5366428 * 2 ^ 59
def prefixEnd_5366428 : Nat := 4983230072969 + 3 ^ 40 * 5366428 * 2
def baseEnd_5366428 : Nat := 2755556961746235059470253

theorem tailTrace_5366428 : CollatzResearch.WordTrace tailWord_5366428 prefixEnd_5366428 2755556961746235059470253 := by
  unfold tailWord_5366428
  simp only [CollatzResearch.WordTrace]
  refine ⟨97864854501177671890093969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130486472668236895853458625 97864854501177671890093969)
  ·
    refine ⟨73398640875883253917570477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97864854501177671890093969 73398640875883253917570477)
    ·
      refine ⟨27524490328456220219088929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73398640875883253917570477 27524490328456220219088929)
      ·
        refine ⟨20643367746342165164316697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27524490328456220219088929 20643367746342165164316697)
        ·
          refine ⟨15482525809756623873237523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20643367746342165164316697 15482525809756623873237523)
          ·
            refine ⟨23223788714634935809856285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15482525809756623873237523 23223788714634935809856285)
            ·
              refine ⟨8708920767988100928696107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23223788714634935809856285 8708920767988100928696107)
              ·
                refine ⟨13063381151982151393044161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8708920767988100928696107 13063381151982151393044161)
                ·
                  refine ⟨9797535863986613544783121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13063381151982151393044161 9797535863986613544783121)
                  ·
                    refine ⟨7348151897989960158587341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9797535863986613544783121 7348151897989960158587341)
                    ·
                      refine ⟨2755556961746235059470253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7348151897989960158587341 2755556961746235059470253)
                      ·
                        rfl

theorem cell23_5366428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_5366428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366428 prefixEnd_5366428 := by exact prefixLift 5366428
  have htrace : WordTrace (prefixWord ++ tailWord_5366428) baseStart_5366428 baseEnd_5366428 := by
    simpa [prefixWord, tailWord_5366428, baseEnd_5366428] using wordTrace_append hprefix tailTrace_5366428
  have hstable : (prefixWord ++ tailWord_5366428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366428).length < 2 ^ (prefixWord ++ tailWord_5366428).sum := by decide
  have hdescent : baseEnd_5366428 < baseStart_5366428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366458 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3]
def baseStart_5366458 : Nat := 118140960795 + 5366458 * 2 ^ 59
def prefixEnd_5366458 : Nat := 4983230072969 + 3 ^ 40 * 5366458 * 2
def baseEnd_5366458 : Nat := 2755572366165869942095115

theorem tailTrace_5366458 : CollatzResearch.WordTrace tailWord_5366458 prefixEnd_5366458 2755572366165869942095115 := by
  unfold tailWord_5366458
  simp only [CollatzResearch.WordTrace]
  refine ⟨48932700798061664725945007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130487202128164439269186685 48932700798061664725945007)
  ·
    refine ⟨73399051197092497088917511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48932700798061664725945007 73399051197092497088917511)
    ·
      refine ⟨110098576795638745633376267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73399051197092497088917511 110098576795638745633376267)
      ·
        refine ⟨165147865193458118450064401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110098576795638745633376267 165147865193458118450064401)
        ·
          refine ⟨123860898895093588837548301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165147865193458118450064401 123860898895093588837548301)
          ·
            refine ⟨46447837085660095814080613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123860898895093588837548301 46447837085660095814080613)
            ·
              refine ⟨8708969453561267965140115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46447837085660095814080613 8708969453561267965140115)
              ·
                refine ⟨13063454180341901947710173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8708969453561267965140115 13063454180341901947710173)
                ·
                  refine ⟨4898795317628213230391315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13063454180341901947710173 4898795317628213230391315)
                  ·
                    refine ⟨7348192976442319845586973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4898795317628213230391315 7348192976442319845586973)
                    ·
                      refine ⟨2755572366165869942095115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7348192976442319845586973 2755572366165869942095115)
                      ·
                        rfl

theorem cell23_5366458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_5366458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366458 prefixEnd_5366458 := by exact prefixLift 5366458
  have htrace : WordTrace (prefixWord ++ tailWord_5366458) baseStart_5366458 baseEnd_5366458 := by
    simpa [prefixWord, tailWord_5366458, baseEnd_5366458] using wordTrace_append hprefix tailTrace_5366458
  have hstable : (prefixWord ++ tailWord_5366458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366458).length < 2 ^ (prefixWord ++ tailWord_5366458).sum := by decide
  have hdescent : baseEnd_5366458 < baseStart_5366458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366468 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 1, 5, 2]
def baseStart_5366468 : Nat := 118140960795 + 5366468 * 2 ^ 59
def prefixEnd_5366468 : Nat := 4983230072969 + 3 ^ 40 * 5366468 * 2
def baseEnd_5366468 : Nat := 2755577500972414902970069

theorem tailTrace_5366468 : CollatzResearch.WordTrace tailWord_5366468 prefixEnd_5366468 2755577500972414902970069 := by
  unfold tailWord_5366468
  simp only [CollatzResearch.WordTrace]
  refine ⟨97865583961105215305822029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130487445281473620407762705 97865583961105215305822029)
  ·
    refine ⟨36699593985414455739683261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97865583961105215305822029 36699593985414455739683261)
    ·
      refine ⟨13762347744530420902381223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36699593985414455739683261 13762347744530420902381223)
      ·
        refine ⟨20643521616795631353571835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13762347744530420902381223 20643521616795631353571835)
        ·
          refine ⟨30965282425193447030357753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20643521616795631353571835 30965282425193447030357753)
          ·
            refine ⟨23223961818895085272768315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30965282425193447030357753 23223961818895085272768315)
            ·
              refine ⟨34835942728342627909152473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23223961818895085272768315 34835942728342627909152473)
              ·
                refine ⟨26126957046256970931864355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34835942728342627909152473 26126957046256970931864355)
                ·
                  refine ⟨39190435569385456397796533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26126957046256970931864355 39190435569385456397796533)
                  ·
                    refine ⟨3674103334629886537293425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39190435569385456397796533 3674103334629886537293425)
                    ·
                      refine ⟨2755577500972414902970069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3674103334629886537293425 2755577500972414902970069)
                      ·
                        rfl

theorem cell23_5366468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_5366468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366468 prefixEnd_5366468 := by exact prefixLift 5366468
  have htrace : WordTrace (prefixWord ++ tailWord_5366468) baseStart_5366468 baseEnd_5366468 := by
    simpa [prefixWord, tailWord_5366468, baseEnd_5366468] using wordTrace_append hprefix tailTrace_5366468
  have hstable : (prefixWord ++ tailWord_5366468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366468).length < 2 ^ (prefixWord ++ tailWord_5366468).sum := by decide
  have hdescent : baseEnd_5366468 < baseStart_5366468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366478 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_5366478 : Nat := 118140960795 + 5366478 * 2 ^ 59
def prefixEnd_5366478 : Nat := 4983230072969 + 3 ^ 40 * 5366478 * 2
def baseEnd_5366478 : Nat := 918527545259653287948341

theorem tailTrace_5366478 : CollatzResearch.WordTrace tailWord_5366478 prefixEnd_5366478 918527545259653287948341 := by
  unfold tailWord_5366478
  simp only [CollatzResearch.WordTrace]
  refine ⟨24466441581521775289938511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130487688434782801546338725 24466441581521775289938511)
  ·
    refine ⟨36699662372282662934907767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24466441581521775289938511 36699662372282662934907767)
    ·
      refine ⟨55049493558423994402361651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36699662372282662934907767 55049493558423994402361651)
      ·
        refine ⟨82574240337635991603542477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55049493558423994402361651 82574240337635991603542477)
        ·
          refine ⟨30965340126613496851328429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82574240337635991603542477 30965340126613496851328429)
          ·
            refine ⟨11612002547480061319248161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30965340126613496851328429 11612002547480061319248161)
            ·
              refine ⟨8709001910610045989436121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11612002547480061319248161 8709001910610045989436121)
              ·
                refine ⟨6531751432957534492077091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8709001910610045989436121 6531751432957534492077091)
                ·
                  refine ⟨9797627149436301738115637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6531751432957534492077091 9797627149436301738115637)
                  ·
                    refine ⟨918527545259653287948341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9797627149436301738115637 918527545259653287948341)
                    ·
                      rfl

theorem cell23_5366478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_5366478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366478 prefixEnd_5366478 := by exact prefixLift 5366478
  have htrace : WordTrace (prefixWord ++ tailWord_5366478) baseStart_5366478 baseEnd_5366478 := by
    simpa [prefixWord, tailWord_5366478, baseEnd_5366478] using wordTrace_append hprefix tailTrace_5366478
  have hstable : (prefixWord ++ tailWord_5366478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366478).length < 2 ^ (prefixWord ++ tailWord_5366478).sum := by decide
  have hdescent : baseEnd_5366478 < baseStart_5366478 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366481 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 2, 6, 2]
def baseStart_5366481 : Nat := 118140960795 + 5366481 * 2 ^ 59
def prefixEnd_5366481 : Nat := 4983230072969 + 3 ^ 40 * 5366481 * 2
def baseEnd_5366481 : Nat := 2755584176220923352107509

theorem tailTrace_5366481 : CollatzResearch.WordTrace tailWord_5366481 prefixEnd_5366481 2755584176220923352107509 := by
  unfold tailWord_5366481
  simp only [CollatzResearch.WordTrace]
  refine ⟨195731642071163333831867297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130487761380775555887911531 195731642071163333831867297)
  ·
    refine ⟨146798731553372500373900473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195731642071163333831867297 146798731553372500373900473)
    ·
      refine ⟨110099048665029375280425355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146798731553372500373900473 110099048665029375280425355)
      ·
        refine ⟨165148572997544062920638033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110099048665029375280425355 165148572997544062920638033)
        ·
          refine ⟨123861429748158047190478525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165148572997544062920638033 123861429748158047190478525)
          ·
            refine ⟨46448036155559267696429447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123861429748158047190478525 46448036155559267696429447)
            ·
              refine ⟨69672054233338901544644171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46448036155559267696429447 69672054233338901544644171)
              ·
                refine ⟨104508081350008352316966257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69672054233338901544644171 104508081350008352316966257)
                ·
                  refine ⟨78381061012506264237724693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104508081350008352316966257 78381061012506264237724693)
                  ·
                    refine ⟨3674112234961231136143345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78381061012506264237724693 3674112234961231136143345)
                    ·
                      refine ⟨2755584176220923352107509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3674112234961231136143345 2755584176220923352107509)
                      ·
                        rfl

theorem cell23_5366481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_5366481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366481 prefixEnd_5366481 := by exact prefixLift 5366481
  have htrace : WordTrace (prefixWord ++ tailWord_5366481) baseStart_5366481 baseEnd_5366481 := by
    simpa [prefixWord, tailWord_5366481, baseEnd_5366481] using wordTrace_append hprefix tailTrace_5366481
  have hstable : (prefixWord ++ tailWord_5366481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366481).length < 2 ^ (prefixWord ++ tailWord_5366481).sum := by decide
  have hdescent : baseEnd_5366481 < baseStart_5366481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366501 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_5366501 : Nat := 118140960795 + 5366501 * 2 ^ 59
def prefixEnd_5366501 : Nat := 4983230072969 + 3 ^ 40 * 5366501 * 2
def baseEnd_5366501 : Nat := 2755594445834013273857417

theorem tailTrace_5366501 : CollatzResearch.WordTrace tailWord_5366501 prefixEnd_5366501 2755594445834013273857417 := by
  unfold tailWord_5366501
  simp only [CollatzResearch.WordTrace]
  refine ⟨195732371531090877247595357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130488247687393918165063571 195732371531090877247595357)
  ·
    refine ⟨73399639324159078967848259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195732371531090877247595357 73399639324159078967848259)
    ·
      refine ⟨110099458986238618451772389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73399639324159078967848259 110099458986238618451772389)
      ·
        refine ⟨20643648559919740959707323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110099458986238618451772389 20643648559919740959707323)
        ·
          refine ⟨30965472839879611439560985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20643648559919740959707323 30965472839879611439560985)
          ·
            refine ⟨23224104629909708579670739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30965472839879611439560985 23224104629909708579670739)
            ·
              refine ⟨34836156944864562869506109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23224104629909708579670739 34836156944864562869506109)
              ·
                refine ⟨13063558854324211076064791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34836156944864562869506109 13063558854324211076064791)
                ·
                  refine ⟨19595338281486316614097187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13063558854324211076064791 19595338281486316614097187)
                  ·
                    refine ⟨29393007422229474921145781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19595338281486316614097187 29393007422229474921145781)
                    ·
                      refine ⟨2755594445834013273857417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29393007422229474921145781 2755594445834013273857417)
                      ·
                        rfl

theorem cell23_5366501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_5366501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366501 prefixEnd_5366501 := by exact prefixLift 5366501
  have htrace : WordTrace (prefixWord ++ tailWord_5366501) baseStart_5366501 baseEnd_5366501 := by
    simpa [prefixWord, tailWord_5366501, baseEnd_5366501] using wordTrace_append hprefix tailTrace_5366501
  have hstable : (prefixWord ++ tailWord_5366501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366501).length < 2 ^ (prefixWord ++ tailWord_5366501).sum := by decide
  have hdescent : baseEnd_5366501 < baseStart_5366501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366518 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_5366518 : Nat := 118140960795 + 5366518 * 2 ^ 59
def prefixEnd_5366518 : Nat := 4983230072969 + 3 ^ 40 * 5366518 * 2
def baseEnd_5366518 : Nat := 2755603175005139707344839

theorem tailTrace_5366518 : CollatzResearch.WordTrace tailWord_5366518 prefixEnd_5366518 2755603175005139707344839 := by
  unfold tailWord_5366518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12233311973251830571935263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130488661048019526100642805 12233311973251830571935263)
  ·
    refine ⟨18349967959877745857902895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12233311973251830571935263 18349967959877745857902895)
    ·
      refine ⟨27524951939816618786854343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18349967959877745857902895 27524951939816618786854343)
      ·
        refine ⟨41287427909724928180281515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27524951939816618786854343 41287427909724928180281515)
        ·
          refine ⟨61931141864587392270422273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41287427909724928180281515 61931141864587392270422273)
          ·
            refine ⟨46448356398440544202816705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61931141864587392270422273 46448356398440544202816705)
            ·
              refine ⟨34836267298830408152112529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46448356398440544202816705 34836267298830408152112529)
              ·
                refine ⟨26127200474122806114084397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34836267298830408152112529 26127200474122806114084397)
                ·
                  refine ⟨9797700177796052292781649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26127200474122806114084397 9797700177796052292781649)
                  ·
                    refine ⟨7348275133347039219586237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9797700177796052292781649 7348275133347039219586237)
                    ·
                      refine ⟨2755603175005139707344839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7348275133347039219586237 2755603175005139707344839)
                      ·
                        rfl

theorem cell23_5366518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_5366518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366518 prefixEnd_5366518 := by exact prefixLift 5366518
  have htrace : WordTrace (prefixWord ++ tailWord_5366518) baseStart_5366518 baseEnd_5366518 := by
    simpa [prefixWord, tailWord_5366518, baseEnd_5366518] using wordTrace_append hprefix tailTrace_5366518
  have hstable : (prefixWord ++ tailWord_5366518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366518).length < 2 ^ (prefixWord ++ tailWord_5366518).sum := by decide
  have hdescent : baseEnd_5366518 < baseStart_5366518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366531 : List Nat := [1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 3]
def baseStart_5366531 : Nat := 118140960795 + 5366531 * 2 ^ 59
def prefixEnd_5366531 : Nat := 4983230072969 + 3 ^ 40 * 5366531 * 2
def baseEnd_5366531 : Nat := 2755609850253648156482279

theorem tailTrace_5366531 : CollatzResearch.WordTrace tailWord_5366531 prefixEnd_5366531 2755609850253648156482279 := by
  unfold tailWord_5366531
  simp only [CollatzResearch.WordTrace]
  refine ⟨195733465720982192371187447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130488977147321461580791631 195733465720982192371187447)
  ·
    refine ⟨293600198581473288556781171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195733465720982192371187447 293600198581473288556781171)
    ·
      refine ⟨440400297872209932835171757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293600198581473288556781171 440400297872209932835171757)
      ·
        refine ⟨165150111702078724813189409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 440400297872209932835171757 165150111702078724813189409)
        ·
          refine ⟨123862583776559043609892057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165150111702078724813189409 123862583776559043609892057)
          ·
            refine ⟨92896937832419282707419043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123862583776559043609892057 92896937832419282707419043)
            ·
              refine ⟨139345406748628924061128565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92896937832419282707419043 139345406748628924061128565)
              ·
                refine ⟨13063631882683961630730803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139345406748628924061128565 13063631882683961630730803)
                ·
                  refine ⟨19595447824025942446096205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13063631882683961630730803 19595447824025942446096205)
                  ·
                    refine ⟨7348292934009728417286077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19595447824025942446096205 7348292934009728417286077)
                    ·
                      refine ⟨2755609850253648156482279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7348292934009728417286077 2755609850253648156482279)
                      ·
                        rfl

theorem cell23_5366531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_5366531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366531 prefixEnd_5366531 := by exact prefixLift 5366531
  have htrace : WordTrace (prefixWord ++ tailWord_5366531) baseStart_5366531 baseEnd_5366531 := by
    simpa [prefixWord, tailWord_5366531, baseEnd_5366531] using wordTrace_append hprefix tailTrace_5366531
  have hstable : (prefixWord ++ tailWord_5366531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366531).length < 2 ^ (prefixWord ++ tailWord_5366531).sum := by decide
  have hdescent : baseEnd_5366531 < baseStart_5366531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366535 : List Nat := [1, 1, 4, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_5366535 : Nat := 118140960795 + 5366535 * 2 ^ 59
def prefixEnd_5366535 : Nat := 4983230072969 + 3 ^ 40 * 5366535 * 2
def baseEnd_5366535 : Nat := 2755611904176266140832261

theorem tailTrace_5366535 : CollatzResearch.WordTrace tailWord_5366535 prefixEnd_5366535 2755611904176266140832261 := by
  unfold tailWord_5366535
  simp only [CollatzResearch.WordTrace]
  refine ⟨195733611612967701054333059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130489074408645134036222039 195733611612967701054333059)
  ·
    refine ⟨293600417419451551581499589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195733611612967701054333059 293600417419451551581499589)
    ·
      refine ⟨55050078266147165921531173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 293600417419451551581499589 55050078266147165921531173)
      ·
        refine ⟨10321889674902593610287095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55050078266147165921531173 10321889674902593610287095)
        ·
          refine ⟨15482834512353890415430643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10321889674902593610287095 15482834512353890415430643)
          ·
            refine ⟨23224251768530835623145965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15482834512353890415430643 23224251768530835623145965)
            ·
              refine ⟨8709094413199063358679737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23224251768530835623145965 8709094413199063358679737)
              ·
                refine ⟨6531820809899297519009803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8709094413199063358679737 6531820809899297519009803)
                ·
                  refine ⟨9797731214848946278514705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6531820809899297519009803 9797731214848946278514705)
                  ·
                    refine ⟨7348298411136709708886029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9797731214848946278514705 7348298411136709708886029)
                    ·
                      refine ⟨2755611904176266140832261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7348298411136709708886029 2755611904176266140832261)
                      ·
                        rfl

theorem cell23_5366535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_5366535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366535 prefixEnd_5366535 := by exact prefixLift 5366535
  have htrace : WordTrace (prefixWord ++ tailWord_5366535) baseStart_5366535 baseEnd_5366535 := by
    simpa [prefixWord, tailWord_5366535, baseEnd_5366535] using wordTrace_append hprefix tailTrace_5366535
  have hstable : (prefixWord ++ tailWord_5366535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366535).length < 2 ^ (prefixWord ++ tailWord_5366535).sum := by decide
  have hdescent : baseEnd_5366535 < baseStart_5366535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366565 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 2, 1, 3]
def baseStart_5366565 : Nat := 118140960795 + 5366565 * 2 ^ 59
def prefixEnd_5366565 : Nat := 4983230072969 + 3 ^ 40 * 5366565 * 2
def baseEnd_5366565 : Nat := 2755627308595901023457123

theorem tailTrace_5366565 : CollatzResearch.WordTrace tailWord_5366565 prefixEnd_5366565 2755627308595901023457123 := by
  unfold tailWord_5366565
  simp only [CollatzResearch.WordTrace]
  refine ⟨195734705802859016177925149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130489803868572677451950099 195734705802859016177925149)
  ·
    refine ⟨73400514676072131066721931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195734705802859016177925149 73400514676072131066721931)
    ·
      refine ⟨110100772014108196600082897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73400514676072131066721931 110100772014108196600082897)
      ·
        refine ⟨82575579010581147450062173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110100772014108196600082897 82575579010581147450062173)
        ·
          refine ⟨30965842128967930293773315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82575579010581147450062173 30965842128967930293773315)
          ·
            refine ⟨46448763193451895440659973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30965842128967930293773315 46448763193451895440659973)
            ·
              refine ⟨8709143098772230395123745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46448763193451895440659973 8709143098772230395123745)
              ·
                refine ⟨6531857324079172796342809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8709143098772230395123745 6531857324079172796342809)
                ·
                  refine ⟨4898892993059379597257107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6531857324079172796342809 4898892993059379597257107)
                  ·
                    refine ⟨7348339489589069395885661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4898892993059379597257107 7348339489589069395885661)
                    ·
                      refine ⟨2755627308595901023457123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7348339489589069395885661 2755627308595901023457123)
                      ·
                        rfl

theorem cell23_5366565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_5366565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366565 prefixEnd_5366565 := by exact prefixLift 5366565
  have htrace : WordTrace (prefixWord ++ tailWord_5366565) baseStart_5366565 baseEnd_5366565 := by
    simpa [prefixWord, tailWord_5366565, baseEnd_5366565] using wordTrace_append hprefix tailTrace_5366565
  have hstable : (prefixWord ++ tailWord_5366565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366565).length < 2 ^ (prefixWord ++ tailWord_5366565).sum := by decide
  have hdescent : baseEnd_5366565 < baseStart_5366565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366581 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_5366581 : Nat := 118140960795 + 5366581 * 2 ^ 59
def prefixEnd_5366581 : Nat := 4983230072969 + 3 ^ 40 * 5366581 * 2
def baseEnd_5366581 : Nat := 918545174762124320285683

theorem tailTrace_5366581 : CollatzResearch.WordTrace tailWord_5366581 prefixEnd_5366581 918545174762124320285683 := by
  unfold tailWord_5366581
  simp only [CollatzResearch.WordTrace]
  refine ⟨195735289370801050910507597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130490192913867367273671731 195735289370801050910507597)
  ·
    refine ⟨73400733514050394091440349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195735289370801050910507597 73400733514050394091440349)
    ·
      refine ⟨27525275067768897784290131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73400733514050394091440349 27525275067768897784290131)
      ·
        refine ⟨41287912601653346676435197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27525275067768897784290131 41287912601653346676435197)
        ·
          refine ⟨15482967225620005003663199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41287912601653346676435197 15482967225620005003663199)
          ·
            refine ⟨23224450838430007505494799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15482967225620005003663199 23224450838430007505494799)
            ·
              refine ⟨34836676257645011258242199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23224450838430007505494799 34836676257645011258242199)
              ·
                refine ⟨52255014386467516887363299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34836676257645011258242199 52255014386467516887363299)
                ·
                  refine ⟨78382521579701275331044949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52255014386467516887363299 78382521579701275331044949)
                  ·
                    refine ⟨918545174762124320285683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78382521579701275331044949 918545174762124320285683)
                    ·
                      rfl

theorem cell23_5366581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_5366581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366581 prefixEnd_5366581 := by exact prefixLift 5366581
  have htrace : WordTrace (prefixWord ++ tailWord_5366581) baseStart_5366581 baseEnd_5366581 := by
    simpa [prefixWord, tailWord_5366581, baseEnd_5366581] using wordTrace_append hprefix tailTrace_5366581
  have hstable : (prefixWord ++ tailWord_5366581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366581).length < 2 ^ (prefixWord ++ tailWord_5366581).sum := by decide
  have hdescent : baseEnd_5366581 < baseStart_5366581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366582 : List Nat := [5, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5366582 : Nat := 118140960795 + 5366582 * 2 ^ 59
def prefixEnd_5366582 : Nat := 4983230072969 + 3 ^ 40 * 5366582 * 2
def baseEnd_5366582 : Nat := 2755636037767027456944545

theorem tailTrace_5366582 : CollatzResearch.WordTrace tailWord_5366582 prefixEnd_5366582 2755636037767027456944545 := by
  unfold tailWord_5366582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12233457865237339255080875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130490217229198285387529333 12233457865237339255080875)
  ·
    refine ⟨18350186797856008882621313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12233457865237339255080875 18350186797856008882621313)
    ·
      refine ⟨13762640098392006661965985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18350186797856008882621313 13762640098392006661965985)
      ·
        refine ⟨10321980073794004996474489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13762640098392006661965985 10321980073794004996474489)
        ·
          refine ⟨7741485055345503747355867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10321980073794004996474489 7741485055345503747355867)
          ·
            refine ⟨11612227583018255621033801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7741485055345503747355867 11612227583018255621033801)
            ·
              refine ⟨8709170687263691715775351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11612227583018255621033801 8709170687263691715775351)
              ·
                refine ⟨13063756030895537573663027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8709170687263691715775351 13063756030895537573663027)
                ·
                  refine ⟨19595634046343306360494541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13063756030895537573663027 19595634046343306360494541)
                  ·
                    refine ⟨7348362767378739885185453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19595634046343306360494541 7348362767378739885185453)
                    ·
                      refine ⟨2755636037767027456944545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7348362767378739885185453 2755636037767027456944545)
                      ·
                        rfl

theorem cell23_5366582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5366582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366582 prefixEnd_5366582 := by exact prefixLift 5366582
  have htrace : WordTrace (prefixWord ++ tailWord_5366582) baseStart_5366582 baseEnd_5366582 := by
    simpa [prefixWord, tailWord_5366582, baseEnd_5366582] using wordTrace_append hprefix tailTrace_5366582
  have hstable : (prefixWord ++ tailWord_5366582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366582).length < 2 ^ (prefixWord ++ tailWord_5366582).sum := by decide
  have hdescent : baseEnd_5366582 < baseStart_5366582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366609 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 1, 3, 2]
def baseStart_5366609 : Nat := 118140960795 + 5366609 * 2 ^ 59
def prefixEnd_5366609 : Nat := 4983230072969 + 3 ^ 40 * 5366609 * 2
def baseEnd_5366609 : Nat := 2755649901744698851306921

theorem tailTrace_5366609 : CollatzResearch.WordTrace tailWord_5366609 prefixEnd_5366609 2755649901744698851306921 := by
  unfold tailWord_5366609
  simp only [CollatzResearch.WordTrace]
  refine ⟨195736310614699611692526881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130490873743133074461684587 195736310614699611692526881)
  ·
    refine ⟨146802232961024708769395161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195736310614699611692526881 146802232961024708769395161)
    ·
      refine ⟨110101674720768531577046371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146802232961024708769395161 110101674720768531577046371)
      ·
        refine ⟨165152512081152797365569557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110101674720768531577046371 165152512081152797365569557)
        ·
          refine ⟨7741524003804037376511073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 165152512081152797365569557 7741524003804037376511073)
          ·
            refine ⟨5806143002853028032383305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7741524003804037376511073 5806143002853028032383305)
            ·
              refine ⟨4354607252139771024287479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5806143002853028032383305 4354607252139771024287479)
              ·
                refine ⟨6531910878209656536431219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4354607252139771024287479 6531910878209656536431219)
                ·
                  refine ⟨9797866317314484804646829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6531910878209656536431219 9797866317314484804646829)
                  ·
                    refine ⟨3674199868992931801742561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9797866317314484804646829 3674199868992931801742561)
                    ·
                      refine ⟨2755649901744698851306921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3674199868992931801742561 2755649901744698851306921)
                      ·
                        rfl

theorem cell23_5366609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_5366609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366609 prefixEnd_5366609 := by exact prefixLift 5366609
  have htrace : WordTrace (prefixWord ++ tailWord_5366609) baseStart_5366609 baseEnd_5366609 := by
    simpa [prefixWord, tailWord_5366609, baseEnd_5366609] using wordTrace_append hprefix tailTrace_5366609
  have hstable : (prefixWord ++ tailWord_5366609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366609).length < 2 ^ (prefixWord ++ tailWord_5366609).sum := by decide
  have hdescent : baseEnd_5366609 < baseStart_5366609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366628 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 7]
def baseStart_5366628 : Nat := 118140960795 + 5366628 * 2 ^ 59
def prefixEnd_5366628 : Nat := 4983230072969 + 3 ^ 40 * 5366628 * 2
def baseEnd_5366628 : Nat := 306184406430792697441037

theorem tailTrace_5366628 : CollatzResearch.WordTrace tailWord_5366628 prefixEnd_5366628 306184406430792697441037 := by
  unfold tailWord_5366628
  simp only [CollatzResearch.WordTrace]
  refine ⟨97868501800815388968734269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130491335734420518624979025 97868501800815388968734269)
  ·
    refine ⟨36700688175305770863275351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97868501800815388968734269 36700688175305770863275351)
    ·
      refine ⟨55051032262958656294913027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36700688175305770863275351 55051032262958656294913027)
      ·
        refine ⟨82576548394437984442369541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55051032262958656294913027 82576548394437984442369541)
        ·
          refine ⟨15483102823957122082944289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82576548394437984442369541 15483102823957122082944289)
          ·
            refine ⟨11612327117967841562208217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15483102823957122082944289 11612327117967841562208217)
            ·
              refine ⟨8709245338475881171656163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11612327117967841562208217 8709245338475881171656163)
              ·
                refine ⟨13063868007713821757484245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8709245338475881171656163 13063868007713821757484245)
                ·
                  refine ⟨306184406430792697441037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13063868007713821757484245 306184406430792697441037)
                  ·
                    rfl

theorem cell23_5366628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_5366628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366628 prefixEnd_5366628 := by exact prefixLift 5366628
  have htrace : WordTrace (prefixWord ++ tailWord_5366628) baseStart_5366628 baseEnd_5366628 := by
    simpa [prefixWord, tailWord_5366628, baseEnd_5366628] using wordTrace_append hprefix tailTrace_5366628
  have hstable : (prefixWord ++ tailWord_5366628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366628).length < 2 ^ (prefixWord ++ tailWord_5366628).sum := by decide
  have hdescent : baseEnd_5366628 < baseStart_5366628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366641 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 1, 7]
def baseStart_5366641 : Nat := 118140960795 + 5366641 * 2 ^ 59
def prefixEnd_5366641 : Nat := 4983230072969 + 3 ^ 40 * 5366641 * 2
def baseEnd_5366641 : Nat := 918555444375214242035591

theorem tailTrace_5366641 : CollatzResearch.WordTrace tailWord_5366641 prefixEnd_5366641 918555444375214242035591 := by
  unfold tailWord_5366641
  simp only [CollatzResearch.WordTrace]
  refine ⟨195737477750583681157691777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130491651833722454105127851 195737477750583681157691777)
  ·
    refine ⟨146803108312937760868268833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195737477750583681157691777 146803108312937760868268833)
    ·
      refine ⟨110102331234703320651201625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146803108312937760868268833 110102331234703320651201625)
      ·
        refine ⟨82576748426027490488401219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110102331234703320651201625 82576748426027490488401219)
        ·
          refine ⟨123865122639041235732601829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82576748426027490488401219 123865122639041235732601829)
          ·
            refine ⟨23224710494820231699862843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123865122639041235732601829 23224710494820231699862843)
            ·
              refine ⟨34837065742230347549794265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23224710494820231699862843 34837065742230347549794265)
              ·
                refine ⟨26127799306672760662345699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34837065742230347549794265 26127799306672760662345699)
                ·
                  refine ⟨39191698960009140993518549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26127799306672760662345699 39191698960009140993518549)
                  ·
                    refine ⟨918555444375214242035591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39191698960009140993518549 918555444375214242035591)
                    ·
                      rfl

theorem cell23_5366641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_5366641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366641 prefixEnd_5366641 := by exact prefixLift 5366641
  have htrace : WordTrace (prefixWord ++ tailWord_5366641) baseStart_5366641 baseEnd_5366641 := by
    simpa [prefixWord, tailWord_5366641, baseEnd_5366641] using wordTrace_append hprefix tailTrace_5366641
  have hstable : (prefixWord ++ tailWord_5366641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366641).length < 2 ^ (prefixWord ++ tailWord_5366641).sum := by decide
  have hdescent : baseEnd_5366641 < baseStart_5366641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366691 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 6]
def baseStart_5366691 : Nat := 118140960795 + 5366691 * 2 ^ 59
def prefixEnd_5366691 : Nat := 4983230072969 + 3 ^ 40 * 5366691 * 2
def baseEnd_5366691 : Nat := 2755692007158367530481543

theorem tailTrace_5366691 : CollatzResearch.WordTrace tailWord_5366691 prefixEnd_5366691 2755692007158367530481543 := by
  unfold tailWord_5366691
  simp only [CollatzResearch.WordTrace]
  refine ⟨195739301400402539697011927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130492867600268359798007951 195739301400402539697011927)
  ·
    refine ⟨293608952100603809545517891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195739301400402539697011927 293608952100603809545517891)
    ·
      refine ⟨440413428150905714318276837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293608952100603809545517891 440413428150905714318276837)
      ·
        refine ⟨82577517778294821434676907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 440413428150905714318276837 82577517778294821434676907)
        ·
          refine ⟨123866276667442232152015361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82577517778294821434676907 123866276667442232152015361)
          ·
            refine ⟨92899707500581674114011521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123866276667442232152015361 92899707500581674114011521)
            ·
              refine ⟨69674780625436255585508641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92899707500581674114011521 69674780625436255585508641)
              ·
                refine ⟨52256085469077191689131481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69674780625436255585508641 52256085469077191689131481)
                ·
                  refine ⟨39192064101807893766848611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52256085469077191689131481 39192064101807893766848611)
                  ·
                    refine ⟨58788096152711840650272917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39192064101807893766848611 58788096152711840650272917)
                    ·
                      refine ⟨2755692007158367530481543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58788096152711840650272917 2755692007158367530481543)
                      ·
                        rfl

theorem cell23_5366691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_5366691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366691 prefixEnd_5366691 := by exact prefixLift 5366691
  have htrace : WordTrace (prefixWord ++ tailWord_5366691) baseStart_5366691 baseEnd_5366691 := by
    simpa [prefixWord, tailWord_5366691, baseEnd_5366691] using wordTrace_append hprefix tailTrace_5366691
  have hstable : (prefixWord ++ tailWord_5366691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366691).length < 2 ^ (prefixWord ++ tailWord_5366691).sum := by decide
  have hdescent : baseEnd_5366691 < baseStart_5366691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366755 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 1, 5, 2]
def baseStart_5366755 : Nat := 118140960795 + 5366755 * 2 ^ 59
def prefixEnd_5366755 : Nat := 4983230072969 + 3 ^ 40 * 5366755 * 2
def baseEnd_5366755 : Nat := 2755724869920255280081249

theorem tailTrace_5366755 : CollatzResearch.WordTrace tailWord_5366755 prefixEnd_5366755 2755724869920255280081249 := by
  unfold tailWord_5366755
  simp only [CollatzResearch.WordTrace]
  refine ⟨195741635672170678627341719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130494423781447119084894479 195741635672170678627341719)
  ·
    refine ⟨293612453508256017941012579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195741635672170678627341719 293612453508256017941012579)
    ·
      refine ⟨440418680262384026911518869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293612453508256017941012579 440418680262384026911518869)
      ·
        refine ⟨20644625637299251261477447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 440418680262384026911518869 20644625637299251261477447)
        ·
          refine ⟨30966938455948876892216171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20644625637299251261477447 30966938455948876892216171)
          ·
            refine ⟨46450407683923315338324257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30966938455948876892216171 46450407683923315338324257)
            ·
              refine ⟨34837805762942486503743193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46450407683923315338324257 34837805762942486503743193)
              ·
                refine ⟨26128354322206864877807395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34837805762942486503743193 26128354322206864877807395)
                ·
                  refine ⟨39192531483310297316711093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26128354322206864877807395 39192531483310297316711093)
                  ·
                    refine ⟨3674299826560340373441665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39192531483310297316711093 3674299826560340373441665)
                    ·
                      refine ⟨2755724869920255280081249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3674299826560340373441665 2755724869920255280081249)
                      ·
                        rfl

theorem cell23_5366755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_5366755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366755 prefixEnd_5366755 := by exact prefixLift 5366755
  have htrace : WordTrace (prefixWord ++ tailWord_5366755) baseStart_5366755 baseEnd_5366755 := by
    simpa [prefixWord, tailWord_5366755, baseEnd_5366755] using wordTrace_append hprefix tailTrace_5366755
  have hstable : (prefixWord ++ tailWord_5366755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366755).length < 2 ^ (prefixWord ++ tailWord_5366755).sum := by decide
  have hdescent : baseEnd_5366755 < baseStart_5366755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366762 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3]
def baseStart_5366762 : Nat := 118140960795 + 5366762 * 2 ^ 59
def prefixEnd_5366762 : Nat := 4983230072969 + 3 ^ 40 * 5366762 * 2
def baseEnd_5366762 : Nat := 2755728464284836752693717

theorem tailTrace_5366762 : CollatzResearch.WordTrace tailWord_5366762 prefixEnd_5366762 2755728464284836752693717 := by
  unfold tailWord_5366762
  simp only [CollatzResearch.WordTrace]
  refine ⟨48935472745786329705711635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130494593988763545881897693 48935472745786329705711635)
  ·
    refine ⟨73403209118679494558567453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48935472745786329705711635 73403209118679494558567453)
    ·
      refine ⟨27526203419504810459462795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73403209118679494558567453 27526203419504810459462795)
      ·
        refine ⟨41289305129257215689194193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27526203419504810459462795 41289305129257215689194193)
        ·
          refine ⟨30966978846942911766895645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41289305129257215689194193 30966978846942911766895645)
          ·
            refine ⟨11612617067603591912585867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30966978846942911766895645 11612617067603591912585867)
            ·
              refine ⟨17418925601405387868878801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11612617067603591912585867 17418925601405387868878801)
              ·
                refine ⟨13064194201054040901659101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17418925601405387868878801 13064194201054040901659101)
                ·
                  refine ⟨4899072825395265338122163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13064194201054040901659101 4899072825395265338122163)
                  ·
                    refine ⟨7348609238092898007183245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4899072825395265338122163 7348609238092898007183245)
                    ·
                      refine ⟨2755728464284836752693717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7348609238092898007183245 2755728464284836752693717)
                      ·
                        rfl

theorem cell23_5366762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_5366762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366762 prefixEnd_5366762 := by exact prefixLift 5366762
  have htrace : WordTrace (prefixWord ++ tailWord_5366762) baseStart_5366762 baseEnd_5366762 := by
    simpa [prefixWord, tailWord_5366762, baseEnd_5366762] using wordTrace_append hprefix tailTrace_5366762
  have hstable : (prefixWord ++ tailWord_5366762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366762).length < 2 ^ (prefixWord ++ tailWord_5366762).sum := by decide
  have hdescent : baseEnd_5366762 < baseStart_5366762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366786 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 6]
def baseStart_5366786 : Nat := 118140960795 + 5366786 * 2 ^ 59
def prefixEnd_5366786 : Nat := 4983230072969 + 3 ^ 40 * 5366786 * 2
def baseEnd_5366786 : Nat := 306193420868949406532623

theorem tailTrace_5366786 : CollatzResearch.WordTrace tailWord_5366786 prefixEnd_5366786 306193420868949406532623 := by
  unfold tailWord_5366786
  simp only [CollatzResearch.WordTrace]
  refine ⟨48935691583764592730430053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130495177556705580614480141 48935691583764592730430053)
  ·
    refine ⟨9175442171955861136955635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48935691583764592730430053 9175442171955861136955635)
    ·
      refine ⟨13763163257933791705433453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9175442171955861136955635 13763163257933791705433453)
      ·
        refine ⟨5161186221725171889537545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13763163257933791705433453 5161186221725171889537545)
        ·
          refine ⟨3870889666293878917153159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5161186221725171889537545 3870889666293878917153159)
          ·
            refine ⟨5806334499440818375729739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3870889666293878917153159 5806334499440818375729739)
            ·
              refine ⟨8709501749161227563594609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5806334499440818375729739 8709501749161227563594609)
              ·
                refine ⟨6532126311870920672695957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8709501749161227563594609 6532126311870920672695957)
                ·
                  refine ⟨306193420868949406532623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6532126311870920672695957 306193420868949406532623)
                  ·
                    rfl

theorem cell23_5366786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_5366786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366786 prefixEnd_5366786 := by exact prefixLift 5366786
  have htrace : WordTrace (prefixWord ++ tailWord_5366786) baseStart_5366786 baseEnd_5366786 := by
    simpa [prefixWord, tailWord_5366786, baseEnd_5366786] using wordTrace_append hprefix tailTrace_5366786
  have hstable : (prefixWord ++ tailWord_5366786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366786).length < 2 ^ (prefixWord ++ tailWord_5366786).sum := by decide
  have hdescent : baseEnd_5366786 < baseStart_5366786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366795 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 4, 4]
def baseStart_5366795 : Nat := 118140960795 + 5366795 * 2 ^ 59
def prefixEnd_5366795 : Nat := 4983230072969 + 3 ^ 40 * 5366795 * 2
def baseEnd_5366795 : Nat := 918581803048811707860355

theorem tailTrace_5366795 : CollatzResearch.WordTrace tailWord_5366795 prefixEnd_5366795 918581803048811707860355 := by
  unfold tailWord_5366795
  simp only [CollatzResearch.WordTrace]
  refine ⟨195743094592025765458797839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130495396394683843639198559 195743094592025765458797839)
  ·
    refine ⟨293614641888038648188196759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195743094592025765458797839 293614641888038648188196759)
    ·
      refine ⟨440421962832057972282295139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293614641888038648188196759 440421962832057972282295139)
      ·
        refine ⟨660632944248086958423442709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440421962832057972282295139 660632944248086958423442709)
        ·
          refine ⟨30967169261629076176098877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 660632944248086958423442709 30967169261629076176098877)
          ·
            refine ⟨11612688473110903566037079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30967169261629076176098877 11612688473110903566037079)
            ·
              refine ⟨17419032709666355349055619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11612688473110903566037079 17419032709666355349055619)
              ·
                refine ⟨26128549064499533023583429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17419032709666355349055619 26128549064499533023583429)
                ·
                  refine ⟨4899102949593662441921893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26128549064499533023583429 4899102949593662441921893)
                  ·
                    refine ⟨918581803048811707860355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4899102949593662441921893 918581803048811707860355)
                    ·
                      rfl

theorem cell23_5366795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 4].length) (baseStart_5366795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366795 prefixEnd_5366795 := by exact prefixLift 5366795
  have htrace : WordTrace (prefixWord ++ tailWord_5366795) baseStart_5366795 baseEnd_5366795 := by
    simpa [prefixWord, tailWord_5366795, baseEnd_5366795] using wordTrace_append hprefix tailTrace_5366795
  have hstable : (prefixWord ++ tailWord_5366795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366795).length < 2 ^ (prefixWord ++ tailWord_5366795).sum := by decide
  have hdescent : baseEnd_5366795 < baseStart_5366795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366805 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_5366805 : Nat := 118140960795 + 5366805 * 2 ^ 59
def prefixEnd_5366805 : Nat := 4983230072969 + 3 ^ 40 * 5366805 * 2
def baseEnd_5366805 : Nat := 2755750543952980084456019

theorem tailTrace_5366805 : CollatzResearch.WordTrace tailWord_5366805 prefixEnd_5366805 2755750543952980084456019 := by
  unfold tailWord_5366805
  simp only [CollatzResearch.WordTrace]
  refine ⟨195743459321989537166661869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130495639547993024777774579 195743459321989537166661869)
  ·
    refine ⟨73403797245746076437498201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195743459321989537166661869 73403797245746076437498201)
    ·
      refine ⟨55052847934309557328123651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73403797245746076437498201 55052847934309557328123651)
      ·
        refine ⟨82579271901464335992185477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55052847934309557328123651 82579271901464335992185477)
        ·
          refine ⟨15483613481524562998534777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82579271901464335992185477 15483613481524562998534777)
          ·
            refine ⟨11612710111143422248901083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15483613481524562998534777 11612710111143422248901083)
            ·
              refine ⟨17419065166715133373351625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11612710111143422248901083 17419065166715133373351625)
              ·
                refine ⟨13064298875036350030013719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17419065166715133373351625 13064298875036350030013719)
                ·
                  refine ⟨19596448312554525045020579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13064298875036350030013719 19596448312554525045020579)
                  ·
                    refine ⟨29394672468831787567530869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19596448312554525045020579 29394672468831787567530869)
                    ·
                      refine ⟨2755750543952980084456019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29394672468831787567530869 2755750543952980084456019)
                      ·
                        rfl

theorem cell23_5366805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_5366805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366805 prefixEnd_5366805 := by exact prefixLift 5366805
  have htrace : WordTrace (prefixWord ++ tailWord_5366805) baseStart_5366805 baseEnd_5366805 := by
    simpa [prefixWord, tailWord_5366805, baseEnd_5366805] using wordTrace_append hprefix tailTrace_5366805
  have hstable : (prefixWord ++ tailWord_5366805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366805).length < 2 ^ (prefixWord ++ tailWord_5366805).sum := by decide
  have hdescent : baseEnd_5366805 < baseStart_5366805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366812 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_5366812 : Nat := 118140960795 + 5366812 * 2 ^ 59
def prefixEnd_5366812 : Nat := 4983230072969 + 3 ^ 40 * 5366812 * 2
def baseEnd_5366812 : Nat := 918584712772520519022829

theorem tailTrace_5366812 : CollatzResearch.WordTrace tailWord_5366812 prefixEnd_5366812 918584712772520519022829 := by
  unfold tailWord_5366812
  simp only [CollatzResearch.WordTrace]
  refine ⟨97871857316482088681083345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130495809755309451574777793 97871857316482088681083345)
  ·
    refine ⟨73403892987361566510812509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97871857316482088681083345 73403892987361566510812509)
    ·
      refine ⟨27526459870260587441554691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73403892987361566510812509 27526459870260587441554691)
      ·
        refine ⟨41289689805390881162332037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27526459870260587441554691 41289689805390881162332037)
        ·
          refine ⟨7741816838510790217937257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41289689805390881162332037 7741816838510790217937257)
          ·
            refine ⟨5806362628883092663452943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7741816838510790217937257 5806362628883092663452943)
            ·
              refine ⟨8709543943324638995179415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5806362628883092663452943 8709543943324638995179415)
              ·
                refine ⟨13064315914986958492769123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8709543943324638995179415 13064315914986958492769123)
                ·
                  refine ⟨19596473872480437739153685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13064315914986958492769123 19596473872480437739153685)
                  ·
                    refine ⟨918584712772520519022829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19596473872480437739153685 918584712772520519022829)
                    ·
                      rfl

theorem cell23_5366812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_5366812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366812 prefixEnd_5366812 := by exact prefixLift 5366812
  have htrace : WordTrace (prefixWord ++ tailWord_5366812) baseStart_5366812 baseEnd_5366812 := by
    simpa [prefixWord, tailWord_5366812, baseEnd_5366812] using wordTrace_append hprefix tailTrace_5366812
  have hstable : (prefixWord ++ tailWord_5366812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366812).length < 2 ^ (prefixWord ++ tailWord_5366812).sum := by decide
  have hdescent : baseEnd_5366812 < baseStart_5366812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366815 : List Nat := [1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 4]
def baseStart_5366815 : Nat := 118140960795 + 5366815 * 2 ^ 59
def prefixEnd_5366815 : Nat := 4983230072969 + 3 ^ 40 * 5366815 * 2
def baseEnd_5366815 : Nat := 2755755678759525045330973

theorem tailTrace_5366815 : CollatzResearch.WordTrace tailWord_5366815 prefixEnd_5366815 2755755678759525045330973 := by
  unfold tailWord_5366815
  simp only [CollatzResearch.WordTrace]
  refine ⟨195743824051953308874525899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130495882701302205916350599 195743824051953308874525899)
  ·
    refine ⟨293615736077929963311788849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195743824051953308874525899 293615736077929963311788849)
    ·
      refine ⟨220211802058447472483841637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293615736077929963311788849 220211802058447472483841637)
      ·
        refine ⟨41289712885958901090720307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 220211802058447472483841637 41289712885958901090720307)
        ·
          refine ⟨61934569328938351636080461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41289712885958901090720307 61934569328938351636080461)
          ·
            refine ⟨23225463498351881863530173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61934569328938351636080461 23225463498351881863530173)
            ·
              refine ⟨8709548811881955698823815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23225463498351881863530173 8709548811881955698823815)
              ·
                refine ⟨13064323217822933548235723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8709548811881955698823815 13064323217822933548235723)
                ·
                  refine ⟨19596484826734400322353585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13064323217822933548235723 19596484826734400322353585)
                  ·
                    refine ⟨14697363620050800241765189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19596484826734400322353585 14697363620050800241765189)
                    ·
                      refine ⟨2755755678759525045330973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14697363620050800241765189 2755755678759525045330973)
                      ·
                        rfl

theorem cell23_5366815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_5366815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366815 prefixEnd_5366815 := by exact prefixLift 5366815
  have htrace : WordTrace (prefixWord ++ tailWord_5366815) baseStart_5366815 baseEnd_5366815 := by
    simpa [prefixWord, tailWord_5366815, baseEnd_5366815] using wordTrace_append hprefix tailTrace_5366815
  have hstable : (prefixWord ++ tailWord_5366815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366815).length < 2 ^ (prefixWord ++ tailWord_5366815).sum := by decide
  have hdescent : baseEnd_5366815 < baseStart_5366815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366848 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_5366848 : Nat := 118140960795 + 5366848 * 2 ^ 59
def prefixEnd_5366848 : Nat := 4983230072969 + 3 ^ 40 * 5366848 * 2
def baseEnd_5366848 : Nat := 2755772623621123416218321

theorem tailTrace_5366848 : CollatzResearch.WordTrace tailWord_5366848 prefixEnd_5366848 2755772623621123416218321 := by
  unfold tailWord_5366848
  simp only [CollatzResearch.WordTrace]
  refine ⟨97872513830416877755238599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130496685107222503673651465 97872513830416877755238599)
  ·
    refine ⟨146808770745625316632857899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97872513830416877755238599 146808770745625316632857899)
    ·
      refine ⟨220213156118437974949286849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146808770745625316632857899 220213156118437974949286849)
      ·
        refine ⟨165159867088828481211965137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220213156118437974949286849 165159867088828481211965137)
        ·
          refine ⟨123869900316621360908973853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165159867088828481211965137 123869900316621360908973853)
          ·
            refine ⟨46451212618733010340865195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123869900316621360908973853 46451212618733010340865195)
            ·
              refine ⟨69676818928099515511297793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46451212618733010340865195 69676818928099515511297793)
              ·
                refine ⟨52257614196074636633473345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69676818928099515511297793 52257614196074636633473345)
                ·
                  refine ⟨39193210647055977475105009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52257614196074636633473345 39193210647055977475105009)
                  ·
                    refine ⟨29394907985291983106328757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39193210647055977475105009 29394907985291983106328757)
                    ·
                      refine ⟨2755772623621123416218321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29394907985291983106328757 2755772623621123416218321)
                      ·
                        rfl

theorem cell23_5366848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_5366848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366848 prefixEnd_5366848 := by exact prefixLift 5366848
  have htrace : WordTrace (prefixWord ++ tailWord_5366848) baseStart_5366848 baseEnd_5366848 := by
    simpa [prefixWord, tailWord_5366848, baseEnd_5366848] using wordTrace_append hprefix tailTrace_5366848
  have hstable : (prefixWord ++ tailWord_5366848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366848).length < 2 ^ (prefixWord ++ tailWord_5366848).sum := by decide
  have hdescent : baseEnd_5366848 < baseStart_5366848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366862 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2]
def baseStart_5366862 : Nat := 118140960795 + 5366862 * 2 ^ 59
def prefixEnd_5366862 : Nat := 4983230072969 + 3 ^ 40 * 5366862 * 2
def baseEnd_5366862 : Nat := 2755779812350286361443257

theorem tailTrace_5366862 : CollatzResearch.WordTrace tailWord_5366862 prefixEnd_5366862 2755779812350286361443257 := by
  unfold tailWord_5366862
  simp only [CollatzResearch.WordTrace]
  refine ⟨24468192285347879487685855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130497025521855357267657893 24468192285347879487685855)
  ·
    refine ⟨36702288428021819231528783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24468192285347879487685855 36702288428021819231528783)
    ·
      refine ⟨55053432642032728847293175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36702288428021819231528783 55053432642032728847293175)
      ·
        refine ⟨82580148963049093270939763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55053432642032728847293175 82580148963049093270939763)
        ·
          refine ⟨123870223444573639906409645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82580148963049093270939763 123870223444573639906409645)
          ·
            refine ⟨46451333791715114964903617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123870223444573639906409645 46451333791715114964903617)
            ·
              refine ⟨34838500343786336223677713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46451333791715114964903617 34838500343786336223677713)
              ·
                refine ⟨26128875257839752167758285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34838500343786336223677713 26128875257839752167758285)
                ·
                  refine ⟨9798328221689907062909357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26128875257839752167758285 9798328221689907062909357)
                  ·
                    refine ⟨3674373083133715148591009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9798328221689907062909357 3674373083133715148591009)
                    ·
                      refine ⟨2755779812350286361443257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3674373083133715148591009 2755779812350286361443257)
                      ·
                        rfl

theorem cell23_5366862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_5366862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366862 prefixEnd_5366862 := by exact prefixLift 5366862
  have htrace : WordTrace (prefixWord ++ tailWord_5366862) baseStart_5366862 baseEnd_5366862 := by
    simpa [prefixWord, tailWord_5366862, baseEnd_5366862] using wordTrace_append hprefix tailTrace_5366862
  have hstable : (prefixWord ++ tailWord_5366862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366862).length < 2 ^ (prefixWord ++ tailWord_5366862).sum := by decide
  have hdescent : baseEnd_5366862 < baseStart_5366862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366892 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 1, 4, 2]
def baseStart_5366892 : Nat := 118140960795 + 5366892 * 2 ^ 59
def prefixEnd_5366892 : Nat := 4983230072969 + 3 ^ 40 * 5366892 * 2
def baseEnd_5366892 : Nat := 2755795216769921244068119

theorem tailTrace_5366892 : CollatzResearch.WordTrace tailWord_5366892 prefixEnd_5366892 2755795216769921244068119 := by
  unfold tailWord_5366892
  simp only [CollatzResearch.WordTrace]
  refine ⟨97873316236337175512539465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130497754981782900683385953 97873316236337175512539465)
  ·
    refine ⟨73404987177252881634404599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97873316236337175512539465 73404987177252881634404599)
    ·
      refine ⟨110107480765879322451606899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73404987177252881634404599 110107480765879322451606899)
      ·
        refine ⟨165161221148818983677410349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110107480765879322451606899 165161221148818983677410349)
        ·
          refine ⟨61935457930807118879028881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165161221148818983677410349 61935457930807118879028881)
          ·
            refine ⟨46451593448105339159271661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61935457930807118879028881 46451593448105339159271661)
            ·
              refine ⟨17419347543039502184726873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46451593448105339159271661 17419347543039502184726873)
              ·
                refine ⟨13064510657279626638545155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17419347543039502184726873 13064510657279626638545155)
                ·
                  refine ⟨19596765985919439957817733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13064510657279626638545155 19596765985919439957817733)
                  ·
                    refine ⟨3674393622359894992090825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19596765985919439957817733 3674393622359894992090825)
                    ·
                      refine ⟨2755795216769921244068119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3674393622359894992090825 2755795216769921244068119)
                      ·
                        rfl

theorem cell23_5366892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_5366892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366892 prefixEnd_5366892 := by exact prefixLift 5366892
  have htrace : WordTrace (prefixWord ++ tailWord_5366892) baseStart_5366892 baseEnd_5366892 := by
    simpa [prefixWord, tailWord_5366892, baseEnd_5366892] using wordTrace_append hprefix tailTrace_5366892
  have hstable : (prefixWord ++ tailWord_5366892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366892).length < 2 ^ (prefixWord ++ tailWord_5366892).sum := by decide
  have hdescent : baseEnd_5366892 < baseStart_5366892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366926 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2]
def baseStart_5366926 : Nat := 118140960795 + 5366926 * 2 ^ 59
def prefixEnd_5366926 : Nat := 4983230072969 + 3 ^ 40 * 5366926 * 2
def baseEnd_5366926 : Nat := 2755812675112174111042963

theorem tailTrace_5366926 : CollatzResearch.WordTrace tailWord_5366926 prefixEnd_5366926 2755812675112174111042963 := by
  unfold tailWord_5366926
  simp only [CollatzResearch.WordTrace]
  refine ⟨24468484069318896853977079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130498581703034116554544421 24468484069318896853977079)
  ·
    refine ⟨36702726103978345280965619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24468484069318896853977079 36702726103978345280965619)
    ·
      refine ⟨55054089155967517921448429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36702726103978345280965619 55054089155967517921448429)
      ·
        refine ⟨20645283433487819220543161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55054089155967517921448429 20645283433487819220543161)
        ·
          refine ⟨15483962575115864415407371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20645283433487819220543161 15483962575115864415407371)
          ·
            refine ⟨23225943862673796623111057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15483962575115864415407371 23225943862673796623111057)
            ·
              refine ⟨17419457897005347467333293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23225943862673796623111057 17419457897005347467333293)
              ·
                refine ⟨6532296711377005300249985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17419457897005347467333293 6532296711377005300249985)
                ·
                  refine ⟨4899222533532753975187489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6532296711377005300249985 4899222533532753975187489)
                  ·
                    refine ⟨3674416900149565481390617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4899222533532753975187489 3674416900149565481390617)
                    ·
                      refine ⟨2755812675112174111042963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3674416900149565481390617 2755812675112174111042963)
                      ·
                        rfl

theorem cell23_5366926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_5366926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366926 prefixEnd_5366926 := by exact prefixLift 5366926
  have htrace : WordTrace (prefixWord ++ tailWord_5366926) baseStart_5366926 baseEnd_5366926 := by
    simpa [prefixWord, tailWord_5366926, baseEnd_5366926] using wordTrace_append hprefix tailTrace_5366926
  have hstable : (prefixWord ++ tailWord_5366926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366926).length < 2 ^ (prefixWord ++ tailWord_5366926).sum := by decide
  have hdescent : baseEnd_5366926 < baseStart_5366926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366945 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 1, 7]
def baseStart_5366945 : Nat := 118140960795 + 5366945 * 2 ^ 59
def prefixEnd_5366945 : Nat := 4983230072969 + 3 ^ 40 * 5366945 * 2
def baseEnd_5366945 : Nat := 918607477081536512235125

theorem tailTrace_5366945 : CollatzResearch.WordTrace tailWord_5366945 prefixEnd_5366945 918607477081536512235125 := by
  unfold tailWord_5366945
  simp only [CollatzResearch.WordTrace]
  refine ⟨195748565541482341076758289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130499043694321560717838859 195748565541482341076758289)
  ·
    refine ⟨146811424156111755807568717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195748565541482341076758289 146811424156111755807568717)
    ·
      refine ⟨55054284058541908427838269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146811424156111755807568717 55054284058541908427838269)
      ·
        refine ⟨20645356521953215660439351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55054284058541908427838269 20645356521953215660439351)
        ·
          refine ⟨30968034782929823490659027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20645356521953215660439351 30968034782929823490659027)
          ·
            refine ⟨46452052174394735235988541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30968034782929823490659027 46452052174394735235988541)
            ·
              refine ⟨17419519565398025713495703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46452052174394735235988541 17419519565398025713495703)
              ·
                refine ⟨26129279348097038570243555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17419519565398025713495703 26129279348097038570243555)
                ·
                  refine ⟨39193919022145557855365333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26129279348097038570243555 39193919022145557855365333)
                  ·
                    refine ⟨918607477081536512235125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39193919022145557855365333 918607477081536512235125)
                    ·
                      rfl

theorem cell23_5366945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_5366945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366945 prefixEnd_5366945 := by exact prefixLift 5366945
  have htrace : WordTrace (prefixWord ++ tailWord_5366945) baseStart_5366945 baseEnd_5366945 := by
    simpa [prefixWord, tailWord_5366945, baseEnd_5366945] using wordTrace_append hprefix tailTrace_5366945
  have hstable : (prefixWord ++ tailWord_5366945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366945).length < 2 ^ (prefixWord ++ tailWord_5366945).sum := by decide
  have hdescent : baseEnd_5366945 < baseStart_5366945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5366966 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_5366966 : Nat := 118140960795 + 5366966 * 2 ^ 59
def prefixEnd_5366966 : Nat := 4983230072969 + 3 ^ 40 * 5366966 * 2
def baseEnd_5366966 : Nat := 306203690482039328282531

theorem tailTrace_5366966 : CollatzResearch.WordTrace tailWord_5366966 prefixEnd_5366966 306203690482039328282531 := by
  unfold tailWord_5366966
  simp only [CollatzResearch.WordTrace]
  refine ⟨12234333217150391353954547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130499554316270841108848501 12234333217150391353954547)
  ·
    refine ⟨18351499825725587030931821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12234333217150391353954547 18351499825725587030931821)
    ·
      refine ⟨6881812434647095136599433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18351499825725587030931821 6881812434647095136599433)
      ·
        refine ⟨5161359325985321352449575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6881812434647095136599433 5161359325985321352449575)
        ·
          refine ⟨7742038988977982028674363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5161359325985321352449575 7742038988977982028674363)
          ·
            refine ⟨11613058483466973043011545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7742038988977982028674363 11613058483466973043011545)
            ·
              refine ⟨8709793862600229782258659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11613058483466973043011545 8709793862600229782258659)
              ·
                refine ⟨13064690793900344673387989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8709793862600229782258659 13064690793900344673387989)
                ·
                  refine ⟨306203690482039328282531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13064690793900344673387989 306203690482039328282531)
                  ·
                    rfl

theorem cell23_5366966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_5366966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5366966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5366966 prefixEnd_5366966 := by exact prefixLift 5366966
  have htrace : WordTrace (prefixWord ++ tailWord_5366966) baseStart_5366966 baseEnd_5366966 := by
    simpa [prefixWord, tailWord_5366966, baseEnd_5366966] using wordTrace_append hprefix tailTrace_5366966
  have hstable : (prefixWord ++ tailWord_5366966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5366966).length < 2 ^ (prefixWord ++ tailWord_5366966).sum := by decide
  have hdescent : baseEnd_5366966 < baseStart_5366966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5366966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367002 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3]
def baseStart_5367002 : Nat := 118140960795 + 5367002 * 2 ^ 59
def prefixEnd_5367002 : Nat := 4983230072969 + 3 ^ 40 * 5367002 * 2
def baseEnd_5367002 : Nat := 2755851699641915813692613

theorem tailTrace_5367002 : CollatzResearch.WordTrace tailWord_5367002 prefixEnd_5367002 2755851699641915813692613 := by
  unfold tailWord_5367002
  simp only [CollatzResearch.WordTrace]
  refine ⟨48937661125568959952895815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130500429668183893207722173 48937661125568959952895815)
  ·
    refine ⟨73406491688353439929343723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48937661125568959952895815 73406491688353439929343723)
    ·
      refine ⟨110109737532530159894015585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73406491688353439929343723 110109737532530159894015585)
      ·
        refine ⟨82582303149397619920511689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110109737532530159894015585 82582303149397619920511689)
        ·
          refine ⟨61936727362048214940383767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82582303149397619920511689 61936727362048214940383767)
          ·
            refine ⟨92905091043072322410575651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61936727362048214940383767 92905091043072322410575651)
            ·
              refine ⟨139357636564608483615863477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92905091043072322410575651 139357636564608483615863477)
              ·
                refine ⟨13064778427932045338987201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 139357636564608483615863477 13064778427932045338987201)
                ·
                  refine ⟨9798583820949034004240401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13064778427932045338987201 9798583820949034004240401)
                  ·
                    refine ⟨7348937865711775503180301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9798583820949034004240401 7348937865711775503180301)
                    ·
                      refine ⟨2755851699641915813692613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7348937865711775503180301 2755851699641915813692613)
                      ·
                        rfl

theorem cell23_5367002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_5367002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367002 prefixEnd_5367002 := by exact prefixLift 5367002
  have htrace : WordTrace (prefixWord ++ tailWord_5367002) baseStart_5367002 baseEnd_5367002 := by
    simpa [prefixWord, tailWord_5367002, baseEnd_5367002] using wordTrace_append hprefix tailTrace_5367002
  have hstable : (prefixWord ++ tailWord_5367002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367002).length < 2 ^ (prefixWord ++ tailWord_5367002).sum := by decide
  have hdescent : baseEnd_5367002 < baseStart_5367002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367026 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 3, 4]
def baseStart_5367026 : Nat := 118140960795 + 5367026 * 2 ^ 59
def prefixEnd_5367026 : Nat := 4983230072969 + 3 ^ 40 * 5367026 * 2
def baseEnd_5367026 : Nat := 918621341059207906597501

theorem tailTrace_5367026 : CollatzResearch.WordTrace tailWord_5367026 prefixEnd_5367026 918621341059207906597501 := by
  unfold tailWord_5367026
  simp only [CollatzResearch.WordTrace]
  refine ⟨48937879963547222977614233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130501013236125927940304621 48937879963547222977614233)
  ·
    refine ⟨36703409972660417233210675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48937879963547222977614233 36703409972660417233210675)
    ·
      refine ⟨55055114958990625849816013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36703409972660417233210675 55055114958990625849816013)
      ·
        refine ⟨20645668109621484693681005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55055114958990625849816013 20645668109621484693681005)
        ·
          refine ⟨7742125541108056760130377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20645668109621484693681005 7742125541108056760130377)
          ·
            refine ⟨5806594155831042570097783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7742125541108056760130377 5806594155831042570097783)
            ·
              refine ⟨8709891233746563855146675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5806594155831042570097783 8709891233746563855146675)
              ·
                refine ⟨13064836850619845782720013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8709891233746563855146675 13064836850619845782720013)
                ·
                  refine ⟨4899313818982442168520005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13064836850619845782720013 4899313818982442168520005)
                  ·
                    refine ⟨918621341059207906597501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4899313818982442168520005 918621341059207906597501)
                    ·
                      rfl

theorem cell23_5367026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_5367026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367026 prefixEnd_5367026 := by exact prefixLift 5367026
  have htrace : WordTrace (prefixWord ++ tailWord_5367026) baseStart_5367026 baseEnd_5367026 := by
    simpa [prefixWord, tailWord_5367026, baseEnd_5367026] using wordTrace_append hprefix tailTrace_5367026
  have hstable : (prefixWord ++ tailWord_5367026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367026).length < 2 ^ (prefixWord ++ tailWord_5367026).sum := by decide
  have hdescent : baseEnd_5367026 < baseStart_5367026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367039 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 6]
def baseStart_5367039 : Nat := 118140960795 + 5367039 * 2 ^ 59
def prefixEnd_5367039 : Nat := 4983230072969 + 3 ^ 40 * 5367039 * 2
def baseEnd_5367039 : Nat := 306207855380681352103327

theorem tailTrace_5367039 : CollatzResearch.WordTrace tailWord_5367039 prefixEnd_5367039 306207855380681352103327 := by
  unfold tailWord_5367039
  simp only [CollatzResearch.WordTrace]
  refine ⟨195751994003141795130680171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130501329335427863420453447 195751994003141795130680171)
  ·
    refine ⟨293627991004712692696020257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195751994003141795130680171 293627991004712692696020257)
    ·
      refine ⟨220220993253534519522015193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293627991004712692696020257 220220993253534519522015193)
      ·
        refine ⟨165165744940150889641511395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220220993253534519522015193 165165744940150889641511395)
        ·
          refine ⟨247748617410226334462267093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165165744940150889641511395 247748617410226334462267093)
          ·
            refine ⟨5806608220552179713959385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 247748617410226334462267093 5806608220552179713959385)
            ·
              refine ⟨4354956165414134785469539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5806608220552179713959385 4354956165414134785469539)
              ·
                refine ⟨6532434248121202178204309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4354956165414134785469539 6532434248121202178204309)
                ·
                  refine ⟨306207855380681352103327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6532434248121202178204309 306207855380681352103327)
                  ·
                    rfl

theorem cell23_5367039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 6].length) (baseStart_5367039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367039 prefixEnd_5367039 := by exact prefixLift 5367039
  have htrace : WordTrace (prefixWord ++ tailWord_5367039) baseStart_5367039 baseEnd_5367039 := by
    simpa [prefixWord, tailWord_5367039, baseEnd_5367039] using wordTrace_append hprefix tailTrace_5367039
  have hstable : (prefixWord ++ tailWord_5367039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367039).length < 2 ^ (prefixWord ++ tailWord_5367039).sum := by decide
  have hdescent : baseEnd_5367039 < baseStart_5367039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367052 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_5367052 : Nat := 118140960795 + 5367052 * 2 ^ 59
def prefixEnd_5367052 : Nat := 4983230072969 + 3 ^ 40 * 5367052 * 2
def baseEnd_5367052 : Nat := 918625791224880206022461

theorem tailTrace_5367052 : CollatzResearch.WordTrace tailWord_5367052 prefixEnd_5367052 918625791224880206022461 := by
  unfold tailWord_5367052
  simp only [CollatzResearch.WordTrace]
  refine ⟨97876234076047349175451705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130501645434729798900602273 97876234076047349175451705)
  ·
    refine ⟨73407175557035511881588779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97876234076047349175451705 73407175557035511881588779)
    ·
      refine ⟨110110763335553267822383169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73407175557035511881588779 110110763335553267822383169)
      ·
        refine ⟨82583072501664950866787377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110110763335553267822383169 82583072501664950866787377)
        ·
          refine ⟨61937304376248713150090533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82583072501664950866787377 61937304376248713150090533)
          ·
            refine ⟨11613244570546633715641975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61937304376248713150090533 11613244570546633715641975)
            ·
              refine ⟨17419866855819950573462963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11613244570546633715641975 17419866855819950573462963)
              ·
                refine ⟨26129800283729925860194445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17419866855819950573462963 26129800283729925860194445)
                ·
                  refine ⟨9798675106398722197572917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26129800283729925860194445 9798675106398722197572917)
                  ·
                    refine ⟨918625791224880206022461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9798675106398722197572917 918625791224880206022461)
                    ·
                      rfl

theorem cell23_5367052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_5367052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367052 prefixEnd_5367052 := by exact prefixLift 5367052
  have htrace : WordTrace (prefixWord ++ tailWord_5367052) baseStart_5367052 baseEnd_5367052 := by
    simpa [prefixWord, tailWord_5367052, baseEnd_5367052] using wordTrace_append hprefix tailTrace_5367052
  have hstable : (prefixWord ++ tailWord_5367052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367052).length < 2 ^ (prefixWord ++ tailWord_5367052).sum := by decide
  have hdescent : baseEnd_5367052 < baseStart_5367052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367110 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5367110 : Nat := 118140960795 + 5367110 * 2 ^ 59
def prefixEnd_5367110 : Nat := 4983230072969 + 3 ^ 40 * 5367110 * 2
def baseEnd_5367110 : Nat := 2755907155552601391142117

theorem tailTrace_5367110 : CollatzResearch.WordTrace tailWord_5367110 prefixEnd_5367110 2755907155552601391142117 := by
  unfold tailWord_5367110
  simp only [CollatzResearch.WordTrace]
  refine ⟨6117330737058892945516087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130503055723923049504343189 6117330737058892945516087)
  ·
    refine ⟨9175996105588339418274131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6117330737058892945516087 9175996105588339418274131)
    ·
      refine ⟨13763994158382509127411197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9175996105588339418274131 13763994158382509127411197)
      ·
        refine ⟨5161497809393440922779199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13763994158382509127411197 5161497809393440922779199)
        ·
          refine ⟨7742246714090161384168799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5161497809393440922779199 7742246714090161384168799)
          ·
            refine ⟨11613370071135242076253199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7742246714090161384168799 11613370071135242076253199)
            ·
              refine ⟨17420055106702863114379799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11613370071135242076253199 17420055106702863114379799)
              ·
                refine ⟨26130082660054294671569699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17420055106702863114379799 26130082660054294671569699)
                ·
                  refine ⟨39195123990081442007354549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26130082660054294671569699 39195123990081442007354549)
                  ·
                    refine ⟨3674542874070135188189489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39195123990081442007354549 3674542874070135188189489)
                    ·
                      refine ⟨2755907155552601391142117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3674542874070135188189489 2755907155552601391142117)
                      ·
                        rfl

theorem cell23_5367110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5367110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367110 prefixEnd_5367110 := by exact prefixLift 5367110
  have htrace : WordTrace (prefixWord ++ tailWord_5367110) baseStart_5367110 baseEnd_5367110 := by
    simpa [prefixWord, tailWord_5367110, baseEnd_5367110] using wordTrace_append hprefix tailTrace_5367110
  have hstable : (prefixWord ++ tailWord_5367110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367110).length < 2 ^ (prefixWord ++ tailWord_5367110).sum := by decide
  have hdescent : baseEnd_5367110 < baseStart_5367110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367115 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 6]
def baseStart_5367115 : Nat := 118140960795 + 5367115 * 2 ^ 59
def prefixEnd_5367115 : Nat := 4983230072969 + 3 ^ 40 * 5367115 * 2
def baseEnd_5367115 : Nat := 2755909722955873871579593

theorem tailTrace_5367115 : CollatzResearch.WordTrace tailWord_5367115 prefixEnd_5367115 2755909722955873871579593 := by
  unfold tailWord_5367115
  simp only [CollatzResearch.WordTrace]
  refine ⟨195754765950866460110446799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130503177300577640073631199 195754765950866460110446799)
  ·
    refine ⟨293632148926299690165670199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195754765950866460110446799 293632148926299690165670199)
    ·
      refine ⟨440448223389449535248505299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293632148926299690165670199 440448223389449535248505299)
      ·
        refine ⟨660672335084174302872757949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440448223389449535248505299 660672335084174302872757949)
        ·
          refine ⟨247752125656565363577284231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 660672335084174302872757949 247752125656565363577284231)
          ·
            refine ⟨371628188484848045365926347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247752125656565363577284231 371628188484848045365926347)
            ·
              refine ⟨557442282727272068048889521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371628188484848045365926347 557442282727272068048889521)
              ·
                refine ⟨418081712045454051036667141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557442282727272068048889521 418081712045454051036667141)
                ·
                  refine ⟨78390321008522634569375089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418081712045454051036667141 78390321008522634569375089)
                  ·
                    refine ⟨58792740756391975927031317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78390321008522634569375089 58792740756391975927031317)
                    ·
                      refine ⟨2755909722955873871579593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58792740756391975927031317 2755909722955873871579593)
                      ·
                        rfl

theorem cell23_5367115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_5367115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367115 prefixEnd_5367115 := by exact prefixLift 5367115
  have htrace : WordTrace (prefixWord ++ tailWord_5367115) baseStart_5367115 baseEnd_5367115 := by
    simpa [prefixWord, tailWord_5367115, baseEnd_5367115] using wordTrace_append hprefix tailTrace_5367115
  have hstable : (prefixWord ++ tailWord_5367115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367115).length < 2 ^ (prefixWord ++ tailWord_5367115).sum := by decide
  have hdescent : baseEnd_5367115 < baseStart_5367115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367117 : List Nat := [1, 6, 1, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5367117 : Nat := 118140960795 + 5367117 * 2 ^ 59
def prefixEnd_5367117 : Nat := 4983230072969 + 3 ^ 40 * 5367117 * 2
def baseEnd_5367117 : Nat := 2755910749917182863754585

theorem tailTrace_5367117 : CollatzResearch.WordTrace tailWord_5367117 prefixEnd_5367117 2755910749917182863754585 := by
  unfold tailWord_5367117
  simp only [CollatzResearch.WordTrace]
  refine ⟨195754838896859214452019605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130503225931239476301346403 195754838896859214452019605)
  ·
    refine ⟨9176008073290275677438419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 195754838896859214452019605 9176008073290275677438419)
    ·
      refine ⟨13764012109935413516157629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9176008073290275677438419 13764012109935413516157629)
      ·
        refine ⟨5161504541225780068559111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13764012109935413516157629 5161504541225780068559111)
        ·
          refine ⟨7742256811838670102838667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5161504541225780068559111 7742256811838670102838667)
          ·
            refine ⟨11613385217758005154258001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7742256811838670102838667 11613385217758005154258001)
            ·
              refine ⟨8710038913318503865693501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11613385217758005154258001 8710038913318503865693501)
              ·
                refine ⟨3266264592494438949635063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8710038913318503865693501 3266264592494438949635063)
                ·
                  refine ⟨4899396888741658424452595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3266264592494438949635063 4899396888741658424452595)
                  ·
                    refine ⟨7349095333112487636678893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4899396888741658424452595 7349095333112487636678893)
                    ·
                      refine ⟨2755910749917182863754585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7349095333112487636678893 2755910749917182863754585)
                      ·
                        rfl

theorem cell23_5367117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5367117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367117 prefixEnd_5367117 := by exact prefixLift 5367117
  have htrace : WordTrace (prefixWord ++ tailWord_5367117) baseStart_5367117 baseEnd_5367117 := by
    simpa [prefixWord, tailWord_5367117, baseEnd_5367117] using wordTrace_append hprefix tailTrace_5367117
  have hstable : (prefixWord ++ tailWord_5367117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367117).length < 2 ^ (prefixWord ++ tailWord_5367117).sum := by decide
  have hdescent : baseEnd_5367117 < baseStart_5367117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367123 : List Nat := [1, 1, 1, 2, 1, 1, 8, 3, 1, 2, 2]
def baseStart_5367123 : Nat := 118140960795 + 5367123 * 2 ^ 59
def prefixEnd_5367123 : Nat := 4983230072969 + 3 ^ 40 * 5367123 * 2
def baseEnd_5367123 : Nat := 2755913830801109840279557

theorem tailTrace_5367123 : CollatzResearch.WordTrace tailWord_5367123 prefixEnd_5367123 2755913830801109840279557 := by
  unfold tailWord_5367123
  simp only [CollatzResearch.WordTrace]
  refine ⟨195755057734837477476738023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130503371823224984984492015 195755057734837477476738023)
  ·
    refine ⟨293632586602256216215107035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195755057734837477476738023 293632586602256216215107035)
    ·
      refine ⟨440448879903384324322660553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293632586602256216215107035 440448879903384324322660553)
      ·
        refine ⟨330336659927538243241995415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 440448879903384324322660553 330336659927538243241995415)
        ·
          refine ⟨495504989891307364862993123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330336659927538243241995415 495504989891307364862993123)
          ·
            refine ⟨743257484836961047294489685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495504989891307364862993123 743257484836961047294489685)
            ·
              refine ⟨8710048650433137272982301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 743257484836961047294489685 8710048650433137272982301)
              ·
                refine ⟨3266268243912426477368363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8710048650433137272982301 3266268243912426477368363)
                ·
                  refine ⟨4899402365868639716052545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3266268243912426477368363 4899402365868639716052545)
                  ·
                    refine ⟨3674551774401479787039409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4899402365868639716052545 3674551774401479787039409)
                    ·
                      refine ⟨2755913830801109840279557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3674551774401479787039409 2755913830801109840279557)
                      ·
                        rfl

theorem cell23_5367123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 1, 2, 2].length) (baseStart_5367123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367123 prefixEnd_5367123 := by exact prefixLift 5367123
  have htrace : WordTrace (prefixWord ++ tailWord_5367123) baseStart_5367123 baseEnd_5367123 := by
    simpa [prefixWord, tailWord_5367123, baseEnd_5367123] using wordTrace_append hprefix tailTrace_5367123
  have hstable : (prefixWord ++ tailWord_5367123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367123).length < 2 ^ (prefixWord ++ tailWord_5367123).sum := by decide
  have hdescent : baseEnd_5367123 < baseStart_5367123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367150 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_5367150 : Nat := 118140960795 + 5367150 * 2 ^ 59
def prefixEnd_5367150 : Nat := 4983230072969 + 3 ^ 40 * 5367150 * 2
def baseEnd_5367150 : Nat := 918642564926260411547311

theorem tailTrace_5367150 : CollatzResearch.WordTrace tailWord_5367150 prefixEnd_5367150 918642564926260411547311 := by
  unfold tailWord_5367150
  simp only [CollatzResearch.WordTrace]
  refine ⟨24469505313217457635996363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130504028337159774058647269 24469505313217457635996363)
  ·
    refine ⟨36704257969826186453994545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24469505313217457635996363 36704257969826186453994545)
    ·
      refine ⟨27528193477369639840495909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36704257969826186453994545 27528193477369639840495909)
      ·
        refine ⟨5161536277006807470092983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27528193477369639840495909 5161536277006807470092983)
        ·
          refine ⟨7742304415510211205139475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5161536277006807470092983 7742304415510211205139475)
          ·
            refine ⟨11613456623265316807709213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7742304415510211205139475 11613456623265316807709213)
            ·
              refine ⟨4355046233724493802890955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11613456623265316807709213 4355046233724493802890955)
              ·
                refine ⟨6532569350586740704336433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4355046233724493802890955 6532569350586740704336433)
                ·
                  refine ⟨4899427012940055528252325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6532569350586740704336433 4899427012940055528252325)
                  ·
                    refine ⟨918642564926260411547311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4899427012940055528252325 918642564926260411547311)
                    ·
                      rfl

theorem cell23_5367150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_5367150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367150 prefixEnd_5367150 := by exact prefixLift 5367150
  have htrace : WordTrace (prefixWord ++ tailWord_5367150) baseStart_5367150 baseEnd_5367150 := by
    simpa [prefixWord, tailWord_5367150, baseEnd_5367150] using wordTrace_append hprefix tailTrace_5367150
  have hstable : (prefixWord ++ tailWord_5367150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367150).length < 2 ^ (prefixWord ++ tailWord_5367150).sum := by decide
  have hdescent : baseEnd_5367150 < baseStart_5367150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367179 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 3, 4, 2]
def baseStart_5367179 : Nat := 118140960795 + 5367179 * 2 ^ 59
def prefixEnd_5367179 : Nat := 4983230072969 + 3 ^ 40 * 5367179 * 2
def baseEnd_5367179 : Nat := 2755942585717761621179299

theorem tailTrace_5367179 : CollatzResearch.WordTrace tailWord_5367179 prefixEnd_5367179 2755942585717761621179299 := by
  unfold tailWord_5367179
  simp only [CollatzResearch.WordTrace]
  refine ⟨195757100222634599040776591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130504733481756399360517727 195757100222634599040776591)
  ·
    refine ⟨293635650333951898561164887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195757100222634599040776591 293635650333951898561164887)
    ·
      refine ⟨440453475500927847841747331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293635650333951898561164887 440453475500927847841747331)
      ·
        refine ⟨660680213251391771762620997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440453475500927847841747331 660680213251391771762620997)
        ·
          refine ⟨123877539984635957205491437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 660680213251391771762620997 123877539984635957205491437)
          ·
            refine ⟨46454077494238483952059289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123877539984635957205491437 46454077494238483952059289)
            ·
              refine ⟨34840558120678862964044467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46454077494238483952059289 34840558120678862964044467)
              ·
                refine ⟨52260837181018294446066701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34840558120678862964044467 52260837181018294446066701)
                ·
                  refine ⟨19597813942881860417275013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52260837181018294446066701 19597813942881860417275013)
                  ·
                    refine ⟨3674590114290348828239065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19597813942881860417275013 3674590114290348828239065)
                    ·
                      refine ⟨2755942585717761621179299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3674590114290348828239065 2755942585717761621179299)
                      ·
                        rfl

theorem cell23_5367179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 4, 2].length) (baseStart_5367179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367179 prefixEnd_5367179 := by exact prefixLift 5367179
  have htrace : WordTrace (prefixWord ++ tailWord_5367179) baseStart_5367179 baseEnd_5367179 := by
    simpa [prefixWord, tailWord_5367179, baseEnd_5367179] using wordTrace_append hprefix tailTrace_5367179
  have hstable : (prefixWord ++ tailWord_5367179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367179).length < 2 ^ (prefixWord ++ tailWord_5367179).sum := by decide
  have hdescent : baseEnd_5367179 < baseStart_5367179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367232 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 1, 7]
def baseStart_5367232 : Nat := 118140960795 + 5367232 * 2 ^ 59
def prefixEnd_5367232 : Nat := 4983230072969 + 3 ^ 40 * 5367232 * 2
def baseEnd_5367232 : Nat := 918656600064149971272185

theorem tailTrace_5367232 : CollatzResearch.WordTrace tailWord_5367232 prefixEnd_5367232 918656600064149971272185 := by
  unfold tailWord_5367232
  simp only [CollatzResearch.WordTrace]
  refine ⟨97879516645721294546227975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130506022194295059394970633 97879516645721294546227975)
  ·
    refine ⟨146819274968581941819341963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97879516645721294546227975 146819274968581941819341963)
    ·
      refine ⟨220228912452872912729012945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146819274968581941819341963 220228912452872912729012945)
      ·
        refine ⟨165171684339654684546759709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220228912452872912729012945 165171684339654684546759709)
        ·
          refine ⟨61939381627370506705034891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 165171684339654684546759709 61939381627370506705034891)
          ·
            refine ⟨92909072441055760057552337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61939381627370506705034891 92909072441055760057552337)
            ·
              refine ⟨69681804330791820043164253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92909072441055760057552337 69681804330791820043164253)
              ·
                refine ⟨26130676624046932516186595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69681804330791820043164253 26130676624046932516186595)
                ·
                  refine ⟨39196014936070398774279893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26130676624046932516186595 39196014936070398774279893)
                  ·
                    refine ⟨918656600064149971272185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39196014936070398774279893 918656600064149971272185)
                    ·
                      rfl

theorem cell23_5367232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_5367232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367232 prefixEnd_5367232 := by exact prefixLift 5367232
  have htrace : WordTrace (prefixWord ++ tailWord_5367232) baseStart_5367232 baseEnd_5367232 := by
    simpa [prefixWord, tailWord_5367232, baseEnd_5367232] using wordTrace_append hprefix tailTrace_5367232
  have hstable : (prefixWord ++ tailWord_5367232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367232).length < 2 ^ (prefixWord ++ tailWord_5367232).sum := by decide
  have hdescent : baseEnd_5367232 < baseStart_5367232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367279 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 5, 4]
def baseStart_5367279 : Nat := 118140960795 + 5367279 * 2 ^ 59
def prefixEnd_5367279 : Nat := 4983230072969 + 3 ^ 40 * 5367279 * 2
def baseEnd_5367279 : Nat := 918664644594403743309613

theorem tailTrace_5367279 : CollatzResearch.WordTrace tailWord_5367279 prefixEnd_5367279 918664644594403743309613 := by
  unfold tailWord_5367279
  simp only [CollatzResearch.WordTrace]
  refine ⟨195760747522272316119416891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130507165014848210746277927 195760747522272316119416891)
  ·
    refine ⟨293641121283408474179125337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195760747522272316119416891 293641121283408474179125337)
    ·
      refine ⟨220230840962556355634344003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293641121283408474179125337 220230840962556355634344003)
      ·
        refine ⟨330346261443834533451516005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220230840962556355634344003 330346261443834533451516005)
        ·
          refine ⟨61939924020718975022159251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 330346261443834533451516005 61939924020718975022159251)
          ·
            refine ⟨92909886031078462533238877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61939924020718975022159251 92909886031078462533238877)
            ·
              refine ⟨34841207261654423449964579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92909886031078462533238877 34841207261654423449964579)
              ·
                refine ⟨52261810892481635174946869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34841207261654423449964579 52261810892481635174946869)
                ·
                  refine ⟨4899544771170153297651269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52261810892481635174946869 4899544771170153297651269)
                  ·
                    refine ⟨918664644594403743309613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4899544771170153297651269 918664644594403743309613)
                    ·
                      rfl

theorem cell23_5367279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 4].length) (baseStart_5367279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367279 prefixEnd_5367279 := by exact prefixLift 5367279
  have htrace : WordTrace (prefixWord ++ tailWord_5367279) baseStart_5367279 baseEnd_5367279 := by
    simpa [prefixWord, tailWord_5367279, baseEnd_5367279] using wordTrace_append hprefix tailTrace_5367279
  have hstable : (prefixWord ++ tailWord_5367279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367279).length < 2 ^ (prefixWord ++ tailWord_5367279).sum := by decide
  have hdescent : baseEnd_5367279 < baseStart_5367279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367286 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_5367286 : Nat := 118140960795 + 5367286 * 2 ^ 59
def prefixEnd_5367286 : Nat := 4983230072969 + 3 ^ 40 * 5367286 * 2
def baseEnd_5367286 : Nat := 2755997528147792702541307

theorem tailTrace_5367286 : CollatzResearch.WordTrace tailWord_5367286 prefixEnd_5367286 2755997528147792702541307 := by
  unfold tailWord_5367286
  simp only [CollatzResearch.WordTrace]
  refine ⟨12235062677077934769682607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130507335222164637543281141 12235062677077934769682607)
  ·
    refine ⟨18352594015616902154523911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12235062677077934769682607 18352594015616902154523911)
    ·
      refine ⟨27528891023425353231785867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18352594015616902154523911 27528891023425353231785867)
      ·
        refine ⟨41293336535138029847678801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27528891023425353231785867 41293336535138029847678801)
        ·
          refine ⟨30970002401353522385759101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41293336535138029847678801 30970002401353522385759101)
          ·
            refine ⟨11613750900507570894659663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30970002401353522385759101 11613750900507570894659663)
            ·
              refine ⟨17420626350761356341989495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11613750900507570894659663 17420626350761356341989495)
              ·
                refine ⟨26130939526142034512984243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17420626350761356341989495 26130939526142034512984243)
                ·
                  refine ⟨39196409289213051769476365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26130939526142034512984243 39196409289213051769476365)
                  ·
                    refine ⟨14698653483454894413553637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39196409289213051769476365 14698653483454894413553637)
                    ·
                      refine ⟨2755997528147792702541307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14698653483454894413553637 2755997528147792702541307)
                      ·
                        rfl

theorem cell23_5367286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_5367286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367286 prefixEnd_5367286 := by exact prefixLift 5367286
  have htrace : WordTrace (prefixWord ++ tailWord_5367286) baseStart_5367286 baseEnd_5367286 := by
    simpa [prefixWord, tailWord_5367286, baseEnd_5367286] using wordTrace_append hprefix tailTrace_5367286
  have hstable : (prefixWord ++ tailWord_5367286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367286).length < 2 ^ (prefixWord ++ tailWord_5367286).sum := by decide
  have hdescent : baseEnd_5367286 < baseStart_5367286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367393 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 5, 2, 2]
def baseStart_5367393 : Nat := 118140960795 + 5367393 * 2 ^ 59
def prefixEnd_5367393 : Nat := 4983230072969 + 3 ^ 40 * 5367393 * 2
def baseEnd_5367393 : Nat := 2756052470577823783903315

theorem tailTrace_5367393 : CollatzResearch.WordTrace tailWord_5367393 prefixEnd_5367393 2756052470577823783903315 := by
  unfold tailWord_5367393
  simp only [CollatzResearch.WordTrace]
  refine ⟨195764905443859313589066833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130509936962572875726044555 195764905443859313589066833)
  ·
    refine ⟨146823679082894485191800125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195764905443859313589066833 146823679082894485191800125)
    ·
      refine ⟨55058879656085431946925047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146823679082894485191800125 55058879656085431946925047)
      ·
        refine ⟨82588319484128147920387571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55058879656085431946925047 82588319484128147920387571)
        ·
          refine ⟨123882479226192221880581357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82588319484128147920387571 123882479226192221880581357)
          ·
            refine ⟨46455929709822083205218009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123882479226192221880581357 46455929709822083205218009)
            ·
              refine ⟨34841947282366562403913507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46455929709822083205218009 34841947282366562403913507)
              ·
                refine ⟨52262920923549843605870261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34841947282366562403913507 52262920923549843605870261)
                ·
                  refine ⟨4899648836582797838050337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52262920923549843605870261 4899648836582797838050337)
                  ·
                    refine ⟨3674736627437098378537753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4899648836582797838050337 3674736627437098378537753)
                    ·
                      refine ⟨2756052470577823783903315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3674736627437098378537753 2756052470577823783903315)
                      ·
                        rfl

theorem cell23_5367393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_5367393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367393 prefixEnd_5367393 := by exact prefixLift 5367393
  have htrace : WordTrace (prefixWord ++ tailWord_5367393) baseStart_5367393 baseEnd_5367393 := by
    simpa [prefixWord, tailWord_5367393, baseEnd_5367393] using wordTrace_append hprefix tailTrace_5367393
  have hstable : (prefixWord ++ tailWord_5367393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367393).length < 2 ^ (prefixWord ++ tailWord_5367393).sum := by decide
  have hdescent : baseEnd_5367393 < baseStart_5367393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367399 : List Nat := [1, 1, 5, 1, 1, 1, 4, 9]
def baseStart_5367399 : Nat := 118140960795 + 5367399 * 2 ^ 59
def prefixEnd_5367399 : Nat := 4983230072969 + 3 ^ 40 * 5367399 * 2
def baseEnd_5367399 : Nat := 102076131535620398534381

theorem tailTrace_5367399 : CollatzResearch.WordTrace tailWord_5367399 prefixEnd_5367399 102076131535620398534381 := by
  unfold tailWord_5367399
  simp only [CollatzResearch.WordTrace]
  refine ⟨195765124281837576613785251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130510082854558384409190167 195765124281837576613785251)
  ·
    refine ⟨293647686422756364920677877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195765124281837576613785251 293647686422756364920677877)
    ·
      refine ⟨27529470602133409211313551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 293647686422756364920677877 27529470602133409211313551)
      ·
        refine ⟨41294205903200113816970327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27529470602133409211313551 41294205903200113816970327)
        ·
          refine ⟨61941308854800170725455491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41294205903200113816970327 61941308854800170725455491)
          ·
            refine ⟨92911963282200256088183237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61941308854800170725455491 92911963282200256088183237)
            ·
              refine ⟨17420993115412548016534357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92911963282200256088183237 17420993115412548016534357)
              ·
                refine ⟨102076131535620398534381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17420993115412548016534357 102076131535620398534381)
                ·
                  rfl

theorem cell23_5367399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 9].length) (baseStart_5367399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367399 prefixEnd_5367399 := by exact prefixLift 5367399
  have htrace : WordTrace (prefixWord ++ tailWord_5367399) baseStart_5367399 baseEnd_5367399 := by
    simpa [prefixWord, tailWord_5367399, baseEnd_5367399] using wordTrace_append hprefix tailTrace_5367399
  have hstable : (prefixWord ++ tailWord_5367399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367399).length < 2 ^ (prefixWord ++ tailWord_5367399).sum := by decide
  have hdescent : baseEnd_5367399 < baseStart_5367399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367410 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 1, 1, 4]
def baseStart_5367410 : Nat := 118140960795 + 5367410 * 2 ^ 59
def prefixEnd_5367410 : Nat := 4983230072969 + 3 ^ 40 * 5367410 * 2
def baseEnd_5367410 : Nat := 2756061199748950217390737

theorem tailTrace_5367410 : CollatzResearch.WordTrace tailWord_5367410 prefixEnd_5367410 2756061199748950217390737 := by
  unfold tailWord_5367410
  simp only [CollatzResearch.WordTrace]
  refine ⟨48941381371199431373108921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130510350323198483661623789 48941381371199431373108921)
  ·
    refine ⟨36706036028399573529831691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48941381371199431373108921 36706036028399573529831691)
    ·
      refine ⟨55059054042599360294747537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36706036028399573529831691 55059054042599360294747537)
      ·
        refine ⟨41294290531949520221060653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55059054042599360294747537 41294290531949520221060653)
        ·
          refine ⟨15485358949481070082897745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41294290531949520221060653 15485358949481070082897745)
          ·
            refine ⟨11614019212110802562173309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15485358949481070082897745 11614019212110802562173309)
            ·
              refine ⟨4355257204541550960814991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11614019212110802562173309 4355257204541550960814991)
              ·
                refine ⟨6532885806812326441222487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4355257204541550960814991 6532885806812326441222487)
                ·
                  refine ⟨9799328710218489661833731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6532885806812326441222487 9799328710218489661833731)
                  ·
                    refine ⟨14698993065327734492750597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9799328710218489661833731 14698993065327734492750597)
                    ·
                      refine ⟨2756061199748950217390737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14698993065327734492750597 2756061199748950217390737)
                      ·
                        rfl

theorem cell23_5367410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_5367410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367410 prefixEnd_5367410 := by exact prefixLift 5367410
  have htrace : WordTrace (prefixWord ++ tailWord_5367410) baseStart_5367410 baseEnd_5367410 := by
    simpa [prefixWord, tailWord_5367410, baseEnd_5367410] using wordTrace_append hprefix tailTrace_5367410
  have hstable : (prefixWord ++ tailWord_5367410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367410).length < 2 ^ (prefixWord ++ tailWord_5367410).sum := by decide
  have hdescent : baseEnd_5367410 < baseStart_5367410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367413 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5367413 : Nat := 118140960795 + 5367413 * 2 ^ 59
def prefixEnd_5367413 : Nat := 4983230072969 + 3 ^ 40 * 5367413 * 2
def baseEnd_5367413 : Nat := 2756062740190913705653223

theorem tailTrace_5367413 : CollatzResearch.WordTrace tailWord_5367413 prefixEnd_5367413 2756062740190913705653223 := by
  unfold tailWord_5367413
  simp only [CollatzResearch.WordTrace]
  refine ⟨195765634903786857004794893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130510423269191238003196595 195765634903786857004794893)
  ·
    refine ⟨73412113088920071376798085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195765634903786857004794893 73412113088920071376798085)
    ·
      refine ⟨13764771204172513383149641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73412113088920071376798085 13764771204172513383149641)
      ·
        refine ⟨10323578403129385037362231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13764771204172513383149641 10323578403129385037362231)
        ·
          refine ⟨15485367604694077556043347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10323578403129385037362231 15485367604694077556043347)
          ·
            refine ⟨23228051407041116334065021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15485367604694077556043347 23228051407041116334065021)
            ·
              refine ⟨8710519277640418625274383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23228051407041116334065021 8710519277640418625274383)
              ·
                refine ⟨13065778916460627937911575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8710519277640418625274383 13065778916460627937911575)
                ·
                  refine ⟨19598668374690941906867363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13065778916460627937911575 19598668374690941906867363)
                  ·
                    refine ⟨29398002562036412860301045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19598668374690941906867363 29398002562036412860301045)
                    ·
                      refine ⟨2756062740190913705653223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29398002562036412860301045 2756062740190913705653223)
                      ·
                        rfl

theorem cell23_5367413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5367413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367413 prefixEnd_5367413 := by exact prefixLift 5367413
  have htrace : WordTrace (prefixWord ++ tailWord_5367413) baseStart_5367413 baseEnd_5367413 := by
    simpa [prefixWord, tailWord_5367413, baseEnd_5367413] using wordTrace_append hprefix tailTrace_5367413
  have hstable : (prefixWord ++ tailWord_5367413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367413).length < 2 ^ (prefixWord ++ tailWord_5367413).sum := by decide
  have hdescent : baseEnd_5367413 < baseStart_5367413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367429 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 1, 9]
def baseStart_5367429 : Nat := 118140960795 + 5367429 * 2 ^ 59
def prefixEnd_5367429 : Nat := 4983230072969 + 3 ^ 40 * 5367429 * 2
def baseEnd_5367429 : Nat := 918690318627128547684383

theorem tailTrace_5367429 : CollatzResearch.WordTrace tailWord_5367429 prefixEnd_5367429 918690318627128547684383 := by
  unfold tailWord_5367429
  simp only [CollatzResearch.WordTrace]
  refine ⟨195766218471728891737377341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130510812314485927824918227 195766218471728891737377341)
  ·
    refine ⟨73412331926898334401516503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195766218471728891737377341 73412331926898334401516503)
    ·
      refine ⟨110118497890347501602274755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73412331926898334401516503 110118497890347501602274755)
      ·
        refine ⟨165177746835521252403412133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110118497890347501602274755 165177746835521252403412133)
        ·
          refine ⟨30970827531660234825639775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 165177746835521252403412133 30970827531660234825639775)
          ·
            refine ⟨46456241297490352238459663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30970827531660234825639775 46456241297490352238459663)
            ·
              refine ⟨69684361946235528357689495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46456241297490352238459663 69684361946235528357689495)
              ·
                refine ⟨104526542919353292536534243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69684361946235528357689495 104526542919353292536534243)
                ·
                  refine ⟨156789814379029938804801365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104526542919353292536534243 156789814379029938804801365)
                  ·
                    refine ⟨918690318627128547684383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 156789814379029938804801365 918690318627128547684383)
                    ·
                      rfl

theorem cell23_5367429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 9].length) (baseStart_5367429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367429 prefixEnd_5367429 := by exact prefixLift 5367429
  have htrace : WordTrace (prefixWord ++ tailWord_5367429) baseStart_5367429 baseEnd_5367429 := by
    simpa [prefixWord, tailWord_5367429, baseEnd_5367429] using wordTrace_append hprefix tailTrace_5367429
  have hstable : (prefixWord ++ tailWord_5367429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367429).length < 2 ^ (prefixWord ++ tailWord_5367429).sum := by decide
  have hdescent : baseEnd_5367429 < baseStart_5367429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367459 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 1, 8]
def baseStart_5367459 : Nat := 118140960795 + 5367459 * 2 ^ 59
def prefixEnd_5367459 : Nat := 4983230072969 + 3 ^ 40 * 5367459 * 2
def baseEnd_5367459 : Nat := 918695453433673508559337

theorem tailTrace_5367459 : CollatzResearch.WordTrace tailWord_5367459 prefixEnd_5367459 918695453433673508559337 := by
  unfold tailWord_5367459
  simp only [CollatzResearch.WordTrace]
  refine ⟨195767312661620206860969431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130511541774413471240646287 195767312661620206860969431)
  ·
    refine ⟨293650968992430310291454147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195767312661620206860969431 293650968992430310291454147)
    ·
      refine ⟨440476453488645465437181221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293650968992430310291454147 440476453488645465437181221)
      ·
        refine ⟨82589335029121024769471479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 440476453488645465437181221 82589335029121024769471479)
        ·
          refine ⟨123884002543681537154207219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82589335029121024769471479 123884002543681537154207219)
          ·
            refine ⟨185826003815522305731310829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123884002543681537154207219 185826003815522305731310829)
            ·
              refine ⟨69684751430820864649241561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185826003815522305731310829 69684751430820864649241561)
              ·
                refine ⟨52263563573115648486931171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69684751430820864649241561 52263563573115648486931171)
                ·
                  refine ⟨78395345359673472730396757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52263563573115648486931171 78395345359673472730396757)
                  ·
                    refine ⟨918695453433673508559337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78395345359673472730396757 918695453433673508559337)
                    ·
                      rfl

theorem cell23_5367459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 8].length) (baseStart_5367459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367459 prefixEnd_5367459 := by exact prefixLift 5367459
  have htrace : WordTrace (prefixWord ++ tailWord_5367459) baseStart_5367459 baseEnd_5367459 := by
    simpa [prefixWord, tailWord_5367459, baseEnd_5367459] using wordTrace_append hprefix tailTrace_5367459
  have hstable : (prefixWord ++ tailWord_5367459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367459).length < 2 ^ (prefixWord ++ tailWord_5367459).sum := by decide
  have hdescent : baseEnd_5367459 < baseStart_5367459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367464 : List Nat := [2, 1, 7, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5367464 : Nat := 118140960795 + 5367464 * 2 ^ 59
def prefixEnd_5367464 : Nat := 4983230072969 + 3 ^ 40 * 5367464 * 2
def baseEnd_5367464 : Nat := 2756088927704293006115489

theorem tailTrace_5367464 : CollatzResearch.WordTrace tailWord_5367464 prefixEnd_5367464 2756088927704293006115489 := by
  unfold tailWord_5367464
  simp only [CollatzResearch.WordTrace]
  refine ⟨97883747513301046357450723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130511663351068061809934297 97883747513301046357450723)
  ·
    refine ⟨146825621269951569536176085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97883747513301046357450723 146825621269951569536176085)
    ·
      refine ⟨3441225498514489911004127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 146825621269951569536176085 3441225498514489911004127)
      ·
        refine ⟨5161838247771734866506191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3441225498514489911004127 5161838247771734866506191)
        ·
          refine ⟨7742757371657602299759287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5161838247771734866506191 7742757371657602299759287)
          ·
            refine ⟨11614136057486403449638931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7742757371657602299759287 11614136057486403449638931)
            ·
              refine ⟨17421204086229605174458397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11614136057486403449638931 17421204086229605174458397)
              ·
                refine ⟨6532951532336101940421899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17421204086229605174458397 6532951532336101940421899)
                ·
                  refine ⟨9799427298504152910632849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6532951532336101940421899 9799427298504152910632849)
                  ·
                    refine ⟨7349570473878114682974637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9799427298504152910632849 7349570473878114682974637)
                    ·
                      refine ⟨2756088927704293006115489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7349570473878114682974637 2756088927704293006115489)
                      ·
                        rfl

theorem cell23_5367464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5367464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367464 prefixEnd_5367464 := by exact prefixLift 5367464
  have htrace : WordTrace (prefixWord ++ tailWord_5367464) baseStart_5367464 baseEnd_5367464 := by
    simpa [prefixWord, tailWord_5367464, baseEnd_5367464] using wordTrace_append hprefix tailTrace_5367464
  have hstable : (prefixWord ++ tailWord_5367464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367464).length < 2 ^ (prefixWord ++ tailWord_5367464).sum := by decide
  have hdescent : baseEnd_5367464 < baseStart_5367464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367494 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_5367494 : Nat := 118140960795 + 5367494 * 2 ^ 59
def prefixEnd_5367494 : Nat := 4983230072969 + 3 ^ 40 * 5367494 * 2
def baseEnd_5367494 : Nat := 2756104332123927888740351

theorem tailTrace_5367494 : CollatzResearch.WordTrace tailWord_5367494 prefixEnd_5367494 2756104332123927888740351 := by
  unfold tailWord_5367494
  simp only [CollatzResearch.WordTrace]
  refine ⟨6117768413015418994952923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130512392810995605225662357 6117768413015418994952923)
  ·
    refine ⟨9176652619523128492429385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6117768413015418994952923 9176652619523128492429385)
    ·
      refine ⟨6882489464642346369322039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9176652619523128492429385 6882489464642346369322039)
      ·
        refine ⟨10323734196963519553983059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882489464642346369322039 10323734196963519553983059)
        ·
          refine ⟨15485601295445279330974589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10323734196963519553983059 15485601295445279330974589)
          ·
            refine ⟨5807100485791979749115471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15485601295445279330974589 5807100485791979749115471)
            ·
              refine ⟨8710650728687969623673207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5807100485791979749115471 8710650728687969623673207)
              ·
                refine ⟨13065976093031954435509811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8710650728687969623673207 13065976093031954435509811)
                ·
                  refine ⟨19598964139547931653264717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13065976093031954435509811 19598964139547931653264717)
                  ·
                    refine ⟨7349611552330474369974269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19598964139547931653264717 7349611552330474369974269)
                    ·
                      refine ⟨2756104332123927888740351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7349611552330474369974269 2756104332123927888740351)
                      ·
                        rfl

theorem cell23_5367494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_5367494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367494 prefixEnd_5367494 := by exact prefixLift 5367494
  have htrace : WordTrace (prefixWord ++ tailWord_5367494) baseStart_5367494 baseEnd_5367494 := by
    simpa [prefixWord, tailWord_5367494, baseEnd_5367494] using wordTrace_append hprefix tailTrace_5367494
  have hstable : (prefixWord ++ tailWord_5367494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367494).length < 2 ^ (prefixWord ++ tailWord_5367494).sum := by decide
  have hdescent : baseEnd_5367494 < baseStart_5367494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367496 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_5367496 : Nat := 118140960795 + 5367496 * 2 ^ 59
def prefixEnd_5367496 : Nat := 4983230072969 + 3 ^ 40 * 5367496 * 2
def baseEnd_5367496 : Nat := 2756105359085236880915341

theorem tailTrace_5367496 : CollatzResearch.WordTrace tailWord_5367496 prefixEnd_5367496 2756105359085236880915341 := by
  unfold tailWord_5367496
  simp only [CollatzResearch.WordTrace]
  refine ⟨97884331081243081090033171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130512441441657441453377561 97884331081243081090033171)
  ·
    refine ⟨146826496621864621635049757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97884331081243081090033171 146826496621864621635049757)
    ·
      refine ⟨55059936233199233113143659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146826496621864621635049757 55059936233199233113143659)
      ·
        refine ⟨82589904349798849669715489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55059936233199233113143659 82589904349798849669715489)
        ·
          refine ⟨61942428262349137252286617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82589904349798849669715489 61942428262349137252286617)
          ·
            refine ⟨46456821196761852939214963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61942428262349137252286617 46456821196761852939214963)
            ·
              refine ⟨69685231795142779408822445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46456821196761852939214963 69685231795142779408822445)
              ·
                refine ⟨26131961923178542278308417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69685231795142779408822445 26131961923178542278308417)
                ·
                  refine ⟨19598971442383906708731313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26131961923178542278308417 19598971442383906708731313)
                  ·
                    refine ⟨14699228581787930031548485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19598971442383906708731313 14699228581787930031548485)
                    ·
                      refine ⟨2756105359085236880915341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14699228581787930031548485 2756105359085236880915341)
                      ·
                        rfl

theorem cell23_5367496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_5367496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367496 prefixEnd_5367496 := by exact prefixLift 5367496
  have htrace : WordTrace (prefixWord ++ tailWord_5367496) baseStart_5367496 baseEnd_5367496 := by
    simpa [prefixWord, tailWord_5367496, baseEnd_5367496] using wordTrace_append hprefix tailTrace_5367496
  have hstable : (prefixWord ++ tailWord_5367496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367496).length < 2 ^ (prefixWord ++ tailWord_5367496).sum := by decide
  have hdescent : baseEnd_5367496 < baseStart_5367496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367499 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 9]
def baseStart_5367499 : Nat := 118140960795 + 5367499 * 2 ^ 59
def prefixEnd_5367499 : Nat := 4983230072969 + 3 ^ 40 * 5367499 * 2
def baseEnd_5367499 : Nat := 2756106899527200369177827

theorem tailTrace_5367499 : CollatzResearch.WordTrace tailWord_5367499 prefixEnd_5367499 2756106899527200369177827 := by
  unfold tailWord_5367499
  simp only [CollatzResearch.WordTrace]
  refine ⟨195768771581475293692425551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130512514387650195794950367 195768771581475293692425551)
  ·
    refine ⟨293653157372212940538638327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195768771581475293692425551 293653157372212940538638327)
    ·
      refine ⟨440479736058319410807957491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293653157372212940538638327 440479736058319410807957491)
      ·
        refine ⟨660719604087479116211936237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440479736058319410807957491 660719604087479116211936237)
        ·
          refine ⟨247769851532804668579476089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 660719604087479116211936237 247769851532804668579476089)
          ·
            refine ⟨185827388649603501434607067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247769851532804668579476089 185827388649603501434607067)
            ·
              refine ⟨278741082974405252151910601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185827388649603501434607067 278741082974405252151910601)
              ·
                refine ⟨209055812230803939113932951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278741082974405252151910601 209055812230803939113932951)
                ·
                  refine ⟨313583718346205908670899427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209055812230803939113932951 313583718346205908670899427)
                  ·
                    refine ⟨470375577519308863006349141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 313583718346205908670899427 470375577519308863006349141)
                    ·
                      refine ⟨2756106899527200369177827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 470375577519308863006349141 2756106899527200369177827)
                      ·
                        rfl

theorem cell23_5367499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_5367499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367499 prefixEnd_5367499 := by exact prefixLift 5367499
  have htrace : WordTrace (prefixWord ++ tailWord_5367499) baseStart_5367499 baseEnd_5367499 := by
    simpa [prefixWord, tailWord_5367499, baseEnd_5367499] using wordTrace_append hprefix tailTrace_5367499
  have hstable : (prefixWord ++ tailWord_5367499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367499).length < 2 ^ (prefixWord ++ tailWord_5367499).sum := by decide
  have hdescent : baseEnd_5367499 < baseStart_5367499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367566 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_5367566 : Nat := 118140960795 + 5367566 * 2 ^ 59
def prefixEnd_5367566 : Nat := 4983230072969 + 3 ^ 40 * 5367566 * 2
def baseEnd_5367566 : Nat := 918713767577017202346673

theorem tailTrace_5367566 : CollatzResearch.WordTrace tailWord_5367566 prefixEnd_5367566 918713767577017202346673 := by
  unfold tailWord_5367566
  simp only [CollatzResearch.WordTrace]
  refine ⟨24471401909029070516889319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130514143514821709423409701 24471401909029070516889319)
  ·
    refine ⟨36707102863543605775333979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24471401909029070516889319 36707102863543605775333979)
    ·
      refine ⟨55060654295315408663000969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36707102863543605775333979 55060654295315408663000969)
      ·
        refine ⟨41295490721486556497250727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55060654295315408663000969 41295490721486556497250727)
        ·
          refine ⟨61943236082229834745876091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41295490721486556497250727 61943236082229834745876091)
          ·
            refine ⟨92914854123344752118814137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61943236082229834745876091 92914854123344752118814137)
            ·
              refine ⟨69686140592508564089110603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92914854123344752118814137 69686140592508564089110603)
              ·
                refine ⟨104529210888762846133665905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69686140592508564089110603 104529210888762846133665905)
                ·
                  refine ⟨78396908166572134600249429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104529210888762846133665905 78396908166572134600249429)
                  ·
                    refine ⟨918713767577017202346673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78396908166572134600249429 918713767577017202346673)
                    ·
                      rfl

theorem cell23_5367566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_5367566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367566 prefixEnd_5367566 := by exact prefixLift 5367566
  have htrace : WordTrace (prefixWord ++ tailWord_5367566) baseStart_5367566 baseEnd_5367566 := by
    simpa [prefixWord, tailWord_5367566, baseEnd_5367566] using wordTrace_append hprefix tailTrace_5367566
  have hstable : (prefixWord ++ tailWord_5367566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367566).length < 2 ^ (prefixWord ++ tailWord_5367566).sum := by decide
  have hdescent : baseEnd_5367566 < baseStart_5367566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367570 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 2, 5]
def baseStart_5367570 : Nat := 118140960795 + 5367570 * 2 ^ 59
def prefixEnd_5367570 : Nat := 4983230072969 + 3 ^ 40 * 5367570 * 2
def baseEnd_5367570 : Nat := 918714452217889863796667

theorem tailTrace_5367570 : CollatzResearch.WordTrace tailWord_5367570 prefixEnd_5367570 918714452217889863796667 := by
  unfold tailWord_5367570
  simp only [CollatzResearch.WordTrace]
  refine ⟨48942840291054518204565041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130514240776145381878840109 48942840291054518204565041)
  ·
    refine ⟨36707130218290888653423781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48942840291054518204565041 36707130218290888653423781)
    ·
      refine ⟨6882586915929541622516959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36707130218290888653423781 6882586915929541622516959)
      ·
        refine ⟨10323880373894312433775439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6882586915929541622516959 10323880373894312433775439)
        ·
          refine ⟨15485820560841468650663159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10323880373894312433775439 15485820560841468650663159)
          ·
            refine ⟨23228730841262202975994739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15485820560841468650663159 23228730841262202975994739)
            ·
              refine ⟨34843096261893304463992109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23228730841262202975994739 34843096261893304463992109)
              ·
                refine ⟨13066161098209989173997041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34843096261893304463992109 13066161098209989173997041)
                ·
                  refine ⟨9799620823657491880497781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13066161098209989173997041 9799620823657491880497781)
                  ·
                    refine ⟨918714452217889863796667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9799620823657491880497781 918714452217889863796667)
                    ·
                      rfl

theorem cell23_5367570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_5367570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367570 prefixEnd_5367570 := by exact prefixLift 5367570
  have htrace : WordTrace (prefixWord ++ tailWord_5367570) baseStart_5367570 baseEnd_5367570 := by
    simpa [prefixWord, tailWord_5367570, baseEnd_5367570] using wordTrace_append hprefix tailTrace_5367570
  have hstable : (prefixWord ++ tailWord_5367570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367570).length < 2 ^ (prefixWord ++ tailWord_5367570).sum := by decide
  have hdescent : baseEnd_5367570 < baseStart_5367570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367573 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_5367573 : Nat := 118140960795 + 5367573 * 2 ^ 59
def prefixEnd_5367573 : Nat := 4983230072969 + 3 ^ 40 * 5367573 * 2
def baseEnd_5367573 : Nat := 2756144897095633079652487

theorem tailTrace_5367573 : CollatzResearch.WordTrace tailWord_5367573 prefixEnd_5367573 2756144897095633079652487 := by
  unfold tailWord_5367573
  simp only [CollatzResearch.WordTrace]
  refine ⟨195771470583207204330619373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130514313722138136220412915 195771470583207204330619373)
  ·
    refine ⟨73414301468702701623982265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195771470583207204330619373 73414301468702701623982265)
    ·
      refine ⟨55060726101527026217986699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73414301468702701623982265 55060726101527026217986699)
      ·
        refine ⟨82591089152290539326980049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55060726101527026217986699 82591089152290539326980049)
        ·
          refine ⟨61943316864217904495235037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82591089152290539326980049 61943316864217904495235037)
          ·
            refine ⟨23228743824081714185713139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61943316864217904495235037 23228743824081714185713139)
            ·
              refine ⟨34843115736122571278569709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23228743824081714185713139 34843115736122571278569709)
              ·
                refine ⟨13066168401045964229463641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34843115736122571278569709 13066168401045964229463641)
                ·
                  refine ⟨9799626300784473172097731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13066168401045964229463641 9799626300784473172097731)
                  ·
                    refine ⟨14699439451176709758146597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9799626300784473172097731 14699439451176709758146597)
                    ·
                      refine ⟨2756144897095633079652487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14699439451176709758146597 2756144897095633079652487)
                      ·
                        rfl

theorem cell23_5367573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_5367573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367573 prefixEnd_5367573 := by exact prefixLift 5367573
  have htrace : WordTrace (prefixWord ++ tailWord_5367573) baseStart_5367573 baseEnd_5367573 := by
    simpa [prefixWord, tailWord_5367573, baseEnd_5367573] using wordTrace_append hprefix tailTrace_5367573
  have hstable : (prefixWord ++ tailWord_5367573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367573).length < 2 ^ (prefixWord ++ tailWord_5367573).sum := by decide
  have hdescent : baseEnd_5367573 < baseStart_5367573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367680 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 4]
def baseStart_5367680 : Nat := 118140960795 + 5367680 * 2 ^ 59
def prefixEnd_5367680 : Nat := 4983230072969 + 3 ^ 40 * 5367680 * 2
def baseEnd_5367680 : Nat := 2756199839525664161014495

theorem tailTrace_5367680 : CollatzResearch.WordTrace tailWord_5367680 prefixEnd_5367680 2756199839525664161014495 := by
  unfold tailWord_5367680
  simp only [CollatzResearch.WordTrace]
  refine ⟨97887686596909780802382247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130516915462546374403176329 97887686596909780802382247)
  ·
    refine ⟨146831529895364671203573371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97887686596909780802382247 146831529895364671203573371)
    ·
      refine ⟨220247294843047006805360057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146831529895364671203573371 220247294843047006805360057)
      ·
        refine ⟨165185471132285255104020043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220247294843047006805360057 165185471132285255104020043)
        ·
          refine ⟨247778206698427882656030065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165185471132285255104020043 247778206698427882656030065)
          ·
            refine ⟨185833655023820911992022549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247778206698427882656030065 185833655023820911992022549)
            ·
              refine ⟨8710952579241605249626057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185833655023820911992022549 8710952579241605249626057)
              ·
                refine ⟨6533214434431203937219543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8710952579241605249626057 6533214434431203937219543)
                ·
                  refine ⟨9799821651646805905829315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6533214434431203937219543 9799821651646805905829315)
                  ·
                    refine ⟨14699732477470208858743973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9799821651646805905829315 14699732477470208858743973)
                    ·
                      refine ⟨2756199839525664161014495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14699732477470208858743973 2756199839525664161014495)
                      ·
                        rfl

theorem cell23_5367680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_5367680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367680 prefixEnd_5367680 := by exact prefixLift 5367680
  have htrace : WordTrace (prefixWord ++ tailWord_5367680) baseStart_5367680 baseEnd_5367680 := by
    simpa [prefixWord, tailWord_5367680, baseEnd_5367680] using wordTrace_append hprefix tailTrace_5367680
  have hstable : (prefixWord ++ tailWord_5367680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367680).length < 2 ^ (prefixWord ++ tailWord_5367680).sum := by decide
  have hdescent : baseEnd_5367680 < baseStart_5367680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367700 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_5367700 : Nat := 118140960795 + 5367700 * 2 ^ 59
def prefixEnd_5367700 : Nat := 4983230072969 + 3 ^ 40 * 5367700 * 2
def baseEnd_5367700 : Nat := 2756210109138754082764403

theorem tailTrace_5367700 : CollatzResearch.WordTrace tailWord_5367700 prefixEnd_5367700 2756210109138754082764403 := by
  unfold tailWord_5367700
  simp only [CollatzResearch.WordTrace]
  refine ⟨97888051326873552510246277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130517401769164736680328369 97888051326873552510246277)
  ·
    refine ⟨18354009623788791095671177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97888051326873552510246277 18354009623788791095671177)
    ·
      refine ⟨13765507217841593321753383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18354009623788791095671177 13765507217841593321753383)
      ·
        refine ⟨20648260826762389982630075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13765507217841593321753383 20648260826762389982630075)
        ·
          refine ⟨30972391240143584973945113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20648260826762389982630075 30972391240143584973945113)
          ·
            refine ⟨23229293430107688730458835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30972391240143584973945113 23229293430107688730458835)
            ·
              refine ⟨34843940145161533095688253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23229293430107688730458835 34843940145161533095688253)
              ·
                refine ⟨13066477554435574910883095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34843940145161533095688253 13066477554435574910883095)
                ·
                  refine ⟨19599716331653362366324643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13066477554435574910883095 19599716331653362366324643)
                  ·
                    refine ⟨29399574497480043549486965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19599716331653362366324643 29399574497480043549486965)
                    ·
                      refine ⟨2756210109138754082764403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29399574497480043549486965 2756210109138754082764403)
                      ·
                        rfl

theorem cell23_5367700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_5367700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367700 prefixEnd_5367700 := by exact prefixLift 5367700
  have htrace : WordTrace (prefixWord ++ tailWord_5367700) baseStart_5367700 baseEnd_5367700 := by
    simpa [prefixWord, tailWord_5367700, baseEnd_5367700] using wordTrace_append hprefix tailTrace_5367700
  have hstable : (prefixWord ++ tailWord_5367700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367700).length < 2 ^ (prefixWord ++ tailWord_5367700).sum := by decide
  have hdescent : baseEnd_5367700 < baseStart_5367700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367703 : List Nat := [1, 1, 3, 3, 1, 5, 9]
def baseStart_5367703 : Nat := 118140960795 + 5367703 * 2 ^ 59
def prefixEnd_5367703 : Nat := 4983230072969 + 3 ^ 40 * 5367703 * 2
def baseEnd_5367703 : Nat := 34027304315811328037369

theorem tailTrace_5367703 : CollatzResearch.WordTrace tailWord_5367703 prefixEnd_5367703 34027304315811328037369 := by
  unfold tailWord_5367703
  simp only [CollatzResearch.WordTrace]
  refine ⟨195776212072736236532851763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130517474715157491021901175 195776212072736236532851763)
  ·
    refine ⟨293664318109104354799277645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195776212072736236532851763 293664318109104354799277645)
    ·
      refine ⟨110124119290914133049729117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 293664318109104354799277645 110124119290914133049729117)
      ·
        refine ⟨41296544734092799893648419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110124119290914133049729117 41296544734092799893648419)
        ·
          refine ⟨61944817101139199840472629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41296544734092799893648419 61944817101139199840472629)
          ·
            refine ⟨5807326603231799985044309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61944817101139199840472629 5807326603231799985044309)
            ·
              refine ⟨34027304315811328037369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5807326603231799985044309 34027304315811328037369)
              ·
                rfl

theorem cell23_5367703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 9].length) (baseStart_5367703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367703 prefixEnd_5367703 := by exact prefixLift 5367703
  have htrace : WordTrace (prefixWord ++ tailWord_5367703) baseStart_5367703 baseEnd_5367703 := by
    simpa [prefixWord, tailWord_5367703, baseEnd_5367703] using wordTrace_append hprefix tailTrace_5367703
  have hstable : (prefixWord ++ tailWord_5367703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367703).length < 2 ^ (prefixWord ++ tailWord_5367703).sum := by decide
  have hdescent : baseEnd_5367703 < baseStart_5367703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367764 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_5367764 : Nat := 118140960795 + 5367764 * 2 ^ 59
def prefixEnd_5367764 : Nat := 4983230072969 + 3 ^ 40 * 5367764 * 2
def baseEnd_5367764 : Nat := 2756242971900641832364109

theorem tailTrace_5367764 : CollatzResearch.WordTrace tailWord_5367764 prefixEnd_5367764 2756242971900641832364109 := by
  unfold tailWord_5367764
  simp only [CollatzResearch.WordTrace]
  refine ⟨97889218462757621975411173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130518957950343495967214897 97889218462757621975411173)
  ·
    refine ⟨18354228461767054120389595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97889218462757621975411173 18354228461767054120389595)
    ·
      refine ⟨27531342692650581180584393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18354228461767054120389595 27531342692650581180584393)
      ·
        refine ⟨20648507019487935885438295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27531342692650581180584393 20648507019487935885438295)
        ·
          refine ⟨30972760529231903828157443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20648507019487935885438295 30972760529231903828157443)
          ·
            refine ⟨46459140793847855742236165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30972760529231903828157443 46459140793847855742236165)
            ·
              refine ⟨8711088898846472951669281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46459140793847855742236165 8711088898846472951669281)
              ·
                refine ⟨6533316674134854713751961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8711088898846472951669281 6533316674134854713751961)
                ·
                  refine ⟨4899987505601141035313971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6533316674134854713751961 4899987505601141035313971)
                  ·
                    refine ⟨7349981258401711552970957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4899987505601141035313971 7349981258401711552970957)
                    ·
                      refine ⟨2756242971900641832364109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7349981258401711552970957 2756242971900641832364109)
                      ·
                        rfl

theorem cell23_5367764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_5367764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367764 prefixEnd_5367764 := by exact prefixLift 5367764
  have htrace : WordTrace (prefixWord ++ tailWord_5367764) baseStart_5367764 baseEnd_5367764 := by
    simpa [prefixWord, tailWord_5367764, baseEnd_5367764] using wordTrace_append hprefix tailTrace_5367764
  have hstable : (prefixWord ++ tailWord_5367764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367764).length < 2 ^ (prefixWord ++ tailWord_5367764).sum := by decide
  have hdescent : baseEnd_5367764 < baseStart_5367764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367820 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 4, 3, 3]
def baseStart_5367820 : Nat := 118140960795 + 5367820 * 2 ^ 59
def prefixEnd_5367820 : Nat := 4983230072969 + 3 ^ 40 * 5367820 * 2
def baseEnd_5367820 : Nat := 2756271726817293613263851

theorem tailTrace_5367820 : CollatzResearch.WordTrace tailWord_5367820 prefixEnd_5367820 2756271726817293613263851 := by
  unfold tailWord_5367820
  simp only [CollatzResearch.WordTrace]
  refine ⟨97890239706656182757430457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130520319608874910343240609 97890239706656182757430457)
  ·
    refine ⟨73417679779992137068072843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97890239706656182757430457 73417679779992137068072843)
    ·
      refine ⟨110126519669988205602109265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73417679779992137068072843 110126519669988205602109265)
      ·
        refine ⟨82594889752491154201581949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110126519669988205602109265 82594889752491154201581949)
        ·
          refine ⟨30973083657184182825593231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82594889752491154201581949 30973083657184182825593231)
          ·
            refine ⟨46459625485776274238389847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30973083657184182825593231 46459625485776274238389847)
            ·
              refine ⟨69689438228664411357584771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46459625485776274238389847 69689438228664411357584771)
              ·
                refine ⟨104534157342996617036377157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69689438228664411357584771 104534157342996617036377157)
                ·
                  refine ⟨19600154501811865694320717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104534157342996617036377157 19600154501811865694320717)
                  ·
                    refine ⟨7350057938179449635370269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19600154501811865694320717 7350057938179449635370269)
                    ·
                      refine ⟨2756271726817293613263851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7350057938179449635370269 2756271726817293613263851)
                      ·
                        rfl

theorem cell23_5367820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_5367820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367820 prefixEnd_5367820 := by exact prefixLift 5367820
  have htrace : WordTrace (prefixWord ++ tailWord_5367820) baseStart_5367820 baseEnd_5367820 := by
    simpa [prefixWord, tailWord_5367820, baseEnd_5367820] using wordTrace_append hprefix tailTrace_5367820
  have hstable : (prefixWord ++ tailWord_5367820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367820).length < 2 ^ (prefixWord ++ tailWord_5367820).sum := by decide
  have hdescent : baseEnd_5367820 < baseStart_5367820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367833 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_5367833 : Nat := 118140960795 + 5367833 * 2 ^ 59
def prefixEnd_5367833 : Nat := 4983230072969 + 3 ^ 40 * 5367833 * 2
def baseEnd_5367833 : Nat := 2756278402065802062401291

theorem tailTrace_5367833 : CollatzResearch.WordTrace tailWord_5367833 prefixEnd_5367833 2756278402065802062401291 := by
  unfold tailWord_5367833
  simp only [CollatzResearch.WordTrace]
  refine ⟨195780953562265268735084153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130520635708176845823389435 195780953562265268735084153)
  ·
    refine ⟨146835715171698951551313115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195780953562265268735084153 146835715171698951551313115)
    ·
      refine ⟨220253572757548427326969673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146835715171698951551313115 220253572757548427326969673)
      ·
        refine ⟨165190179568161320495227255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220253572757548427326969673 165190179568161320495227255)
        ·
          refine ⟨247785269352241980742840883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165190179568161320495227255 247785269352241980742840883)
          ·
            refine ⟨371677904028362971114261325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247785269352241980742840883 371677904028362971114261325)
            ·
              refine ⟨139379214010636114167847997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 371677904028362971114261325 139379214010636114167847997)
              ·
                refine ⟨52267205253988542812942999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139379214010636114167847997 52267205253988542812942999)
                ·
                  refine ⟨78400807880982814219414499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52267205253988542812942999 78400807880982814219414499)
                  ·
                    refine ⟨117601211821474221329121749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78400807880982814219414499 117601211821474221329121749)
                    ·
                      refine ⟨2756278402065802062401291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117601211821474221329121749 2756278402065802062401291)
                      ·
                        rfl

theorem cell23_5367833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_5367833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367833 prefixEnd_5367833 := by exact prefixLift 5367833
  have htrace : WordTrace (prefixWord ++ tailWord_5367833) baseStart_5367833 baseEnd_5367833 := by
    simpa [prefixWord, tailWord_5367833, baseEnd_5367833] using wordTrace_append hprefix tailTrace_5367833
  have hstable : (prefixWord ++ tailWord_5367833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367833).length < 2 ^ (prefixWord ++ tailWord_5367833).sum := by decide
  have hdescent : baseEnd_5367833 < baseStart_5367833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367837 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_5367837 : Nat := 118140960795 + 5367837 * 2 ^ 59
def prefixEnd_5367837 : Nat := 4983230072969 + 3 ^ 40 * 5367837 * 2
def baseEnd_5367837 : Nat := 2756280455988420046751273

theorem tailTrace_5367837 : CollatzResearch.WordTrace tailWord_5367837 prefixEnd_5367837 2756280455988420046751273 := by
  unfold tailWord_5367837
  simp only [CollatzResearch.WordTrace]
  refine ⟨195781099454250777418229765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130520732969500518278819843 195781099454250777418229765)
  ·
    refine ⟨36708956147672020765918081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195781099454250777418229765 36708956147672020765918081)
    ·
      refine ⟨27531717110754015574438561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36708956147672020765918081 27531717110754015574438561)
      ·
        refine ⟨20648787833065511680828921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27531717110754015574438561 20648787833065511680828921)
        ·
          refine ⟨15486590874799133760621691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20648787833065511680828921 15486590874799133760621691)
          ·
            refine ⟨23229886312198700640932537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15486590874799133760621691 23229886312198700640932537)
            ·
              refine ⟨17422414734149025480699403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23229886312198700640932537 17422414734149025480699403)
              ·
                refine ⟨26133622101223538221049105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17422414734149025480699403 26133622101223538221049105)
                ·
                  refine ⟨19600216575917653665786829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26133622101223538221049105 19600216575917653665786829)
                  ·
                    refine ⟨7350081215969120124670061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19600216575917653665786829 7350081215969120124670061)
                    ·
                      refine ⟨2756280455988420046751273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7350081215969120124670061 2756280455988420046751273)
                      ·
                        rfl

theorem cell23_5367837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_5367837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367837 prefixEnd_5367837 := by exact prefixLift 5367837
  have htrace : WordTrace (prefixWord ++ tailWord_5367837) baseStart_5367837 baseEnd_5367837 := by
    simpa [prefixWord, tailWord_5367837, baseEnd_5367837] using wordTrace_append hprefix tailTrace_5367837
  have hstable : (prefixWord ++ tailWord_5367837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367837).length < 2 ^ (prefixWord ++ tailWord_5367837).sum := by decide
  have hdescent : baseEnd_5367837 < baseStart_5367837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367880 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 3, 4, 3]
def baseStart_5367880 : Nat := 118140960795 + 5367880 * 2 ^ 59
def prefixEnd_5367880 : Nat := 4983230072969 + 3 ^ 40 * 5367880 * 2
def baseEnd_5367880 : Nat := 2756302535656563378513575

theorem tailTrace_5367880 : CollatzResearch.WordTrace tailWord_5367880 prefixEnd_5367880 2756302535656563378513575 := by
  unfold tailWord_5367880
  simp only [CollatzResearch.WordTrace]
  refine ⟨97891333896547497881022547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130521778528729997174696729 97891333896547497881022547)
  ·
    refine ⟨146837000844821246821533821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97891333896547497881022547 146837000844821246821533821)
    ·
      refine ⟨55063875316807967558075183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146837000844821246821533821 55063875316807967558075183)
      ·
        refine ⟨82595812975211951337112775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55063875316807967558075183 82595812975211951337112775)
        ·
          refine ⟨123893719462817927005669163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82595812975211951337112775 123893719462817927005669163)
          ·
            refine ⟨185840579194226890508503745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123893719462817927005669163 185840579194226890508503745)
            ·
              refine ⟨139380434395670167881377809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185840579194226890508503745 139380434395670167881377809)
              ·
                refine ⟨104535325796752625911033357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139380434395670167881377809 104535325796752625911033357)
                ·
                  refine ⟨39200747173782234716637509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104535325796752625911033357 39200747173782234716637509)
                  ·
                    refine ⟨7350140095084169009369533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39200747173782234716637509 7350140095084169009369533)
                    ·
                      refine ⟨2756302535656563378513575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7350140095084169009369533 2756302535656563378513575)
                      ·
                        rfl

theorem cell23_5367880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_5367880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367880 prefixEnd_5367880 := by exact prefixLift 5367880
  have htrace : WordTrace (prefixWord ++ tailWord_5367880) baseStart_5367880 baseEnd_5367880 := by
    simpa [prefixWord, tailWord_5367880, baseEnd_5367880] using wordTrace_append hprefix tailTrace_5367880
  have hstable : (prefixWord ++ tailWord_5367880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367880).length < 2 ^ (prefixWord ++ tailWord_5367880).sum := by decide
  have hdescent : baseEnd_5367880 < baseStart_5367880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367954 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_5367954 : Nat := 118140960795 + 5367954 * 2 ^ 59
def prefixEnd_5367954 : Nat := 4983230072969 + 3 ^ 40 * 5367954 * 2
def baseEnd_5367954 : Nat := 2756340533224996088988235

theorem tailTrace_5367954 : CollatzResearch.WordTrace tailWord_5367954 prefixEnd_5367954 2756340533224996088988235 := by
  unfold tailWord_5367954
  simp only [CollatzResearch.WordTrace]
  refine ⟨48946341698706726600059729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130523577863217937600159277 48946341698706726600059729)
  ·
    refine ⟨36709756274030044950044797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48946341698706726600059729 36709756274030044950044797)
    ·
      refine ⟨13766158602761266856266799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36709756274030044950044797 13766158602761266856266799)
      ·
        refine ⟨20649237904141900284400199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13766158602761266856266799 20649237904141900284400199)
        ·
          refine ⟨30973856856212850426600299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20649237904141900284400199 30973856856212850426600299)
          ·
            refine ⟨46460785284319275639900449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30973856856212850426600299 46460785284319275639900449)
            ·
              refine ⟨34845588963239456729925337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46460785284319275639900449 34845588963239456729925337)
              ·
                refine ⟨26134191722429592547444003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34845588963239456729925337 26134191722429592547444003)
                ·
                  refine ⟨39201287583644388821166005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26134191722429592547444003 39201287583644388821166005)
                  ·
                    refine ⟨3675120710966661451984313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39201287583644388821166005 3675120710966661451984313)
                    ·
                      refine ⟨2756340533224996088988235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3675120710966661451984313 2756340533224996088988235)
                      ·
                        rfl

theorem cell23_5367954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_5367954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367954 prefixEnd_5367954 := by exact prefixLift 5367954
  have htrace : WordTrace (prefixWord ++ tailWord_5367954) baseStart_5367954 baseEnd_5367954 := by
    simpa [prefixWord, tailWord_5367954, baseEnd_5367954] using wordTrace_append hprefix tailTrace_5367954
  have hstable : (prefixWord ++ tailWord_5367954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367954).length < 2 ^ (prefixWord ++ tailWord_5367954).sum := by decide
  have hdescent : baseEnd_5367954 < baseStart_5367954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5367980 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 4]
def baseStart_5367980 : Nat := 118140960795 + 5367980 * 2 ^ 59
def prefixEnd_5367980 : Nat := 4983230072969 + 3 ^ 40 * 5367980 * 2
def baseEnd_5367980 : Nat := 2756353883722012987263115

theorem tailTrace_5367980 : CollatzResearch.WordTrace tailWord_5367980 prefixEnd_5367980 2756353883722012987263115 := by
  unfold tailWord_5367980
  simp only [CollatzResearch.WordTrace]
  refine ⟨97893157546366356420342697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130524210061821808560456929 97893157546366356420342697)
  ·
    refine ⟨73419868159774767315257023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97893157546366356420342697 73419868159774767315257023)
    ·
      refine ⟨110129802239662150972885535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73419868159774767315257023 110129802239662150972885535)
      ·
        refine ⟨165194703359493226459328303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110129802239662150972885535 165194703359493226459328303)
        ·
          refine ⟨247792055039239839688992455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165194703359493226459328303 247792055039239839688992455)
          ·
            refine ⟨371688082558859759533488683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247792055039239839688992455 371688082558859759533488683)
            ·
              refine ⟨557532123838289639300233025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371688082558859759533488683 557532123838289639300233025)
              ·
                refine ⟨418149092878717229475174769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557532123838289639300233025 418149092878717229475174769)
                ·
                  refine ⟨313611819659037922106381077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418149092878717229475174769 313611819659037922106381077)
                  ·
                    refine ⟨14700554046517402598736613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 313611819659037922106381077 14700554046517402598736613)
                    ·
                      refine ⟨2756353883722012987263115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14700554046517402598736613 2756353883722012987263115)
                      ·
                        rfl

theorem cell23_5367980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_5367980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5367980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5367980 prefixEnd_5367980 := by exact prefixLift 5367980
  have htrace : WordTrace (prefixWord ++ tailWord_5367980) baseStart_5367980 baseEnd_5367980 := by
    simpa [prefixWord, tailWord_5367980, baseEnd_5367980] using wordTrace_append hprefix tailTrace_5367980
  have hstable : (prefixWord ++ tailWord_5367980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5367980).length < 2 ^ (prefixWord ++ tailWord_5367980).sum := by decide
  have hdescent : baseEnd_5367980 < baseStart_5367980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5367980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
