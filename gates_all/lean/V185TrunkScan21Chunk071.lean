import V185TrunkScan21Chunk070

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_859766 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_859766 : Nat := 118140960795 + 859766 * 2 ^ 59
def prefixEnd_859766 : Nat := 4983230072969 + 3 ^ 40 * 859766 * 2
def baseEnd_859766 : Nat := 196210314841594842342673

theorem tailTrace_859766 : CollatzResearch.WordTrace tailWord_859766 prefixEnd_859766 196210314841594842342673 := by
  unfold tailWord_859766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959890137701380824229447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20905494802148062125114101 1959890137701380824229447)
  ·
    refine ⟨2939835206552071236344171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1959890137701380824229447 2939835206552071236344171)
    ·
      refine ⟨4409752809828106854516257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2939835206552071236344171 4409752809828106854516257)
      ·
        refine ⟨3307314607371080140887193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4409752809828106854516257 3307314607371080140887193)
        ·
          refine ⟨2480485955528310105665395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3307314607371080140887193 2480485955528310105665395)
          ·
            refine ⟨3720728933292465158498093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480485955528310105665395 3720728933292465158498093)
            ·
              refine ⟨1395273349984674434436785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3720728933292465158498093 1395273349984674434436785)
              ·
                refine ⟨1046455012488505825827589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395273349984674434436785 1046455012488505825827589)
                ·
                  refine ⟨196210314841594842342673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046455012488505825827589 196210314841594842342673)
                  ·
                    rfl

theorem cell21_859766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_859766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859766 prefixEnd_859766 := by exact prefixLift 859766
  have htrace : WordTrace (prefixWord ++ tailWord_859766) baseStart_859766 baseEnd_859766 := by
    simpa [prefixWord, tailWord_859766, baseEnd_859766] using wordTrace_append hprefix tailTrace_859766
  have hstable : (prefixWord ++ tailWord_859766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859766).length < 2 ^ (prefixWord ++ tailWord_859766).sum := by decide
  have hdescent : baseEnd_859766 < baseStart_859766 := by decide
  rcases family_descends (prefixWord ++ tailWord_859766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859791 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 10]
def baseStart_859791 : Nat := 118140960795 + 859791 * 2 ^ 59
def prefixEnd_859791 : Nat := 4983230072969 + 3 ^ 40 * 859791 * 2
def baseEnd_859791 : Nat := 196216020182200354425955

theorem tailTrace_859791 : CollatzResearch.WordTrace tailWord_859791 prefixEnd_859791 196216020182200354425955 := by
  unfold tailWord_859791
  simp only [CollatzResearch.WordTrace]
  refine ⟨31359154028131522457331227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20906102685421014971554151 31359154028131522457331227)
  ·
    refine ⟨47038731042197283685996841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31359154028131522457331227 47038731042197283685996841)
    ·
      refine ⟨35279048281647962764497631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47038731042197283685996841 35279048281647962764497631)
      ·
        refine ⟨52918572422471944146746447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35279048281647962764497631 52918572422471944146746447)
        ·
          refine ⟨79377858633707916220119671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52918572422471944146746447 79377858633707916220119671)
          ·
            refine ⟨119066787950561874330179507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79377858633707916220119671 119066787950561874330179507)
            ·
              refine ⟨178600181925842811495269261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119066787950561874330179507 178600181925842811495269261)
              ·
                refine ⟨66975068222191054310725973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178600181925842811495269261 66975068222191054310725973)
                ·
                  refine ⟨196216020182200354425955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 66975068222191054310725973 196216020182200354425955)
                  ·
                    rfl

theorem cell21_859791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_859791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859791 prefixEnd_859791 := by exact prefixLift 859791
  have htrace : WordTrace (prefixWord ++ tailWord_859791) baseStart_859791 baseEnd_859791 := by
    simpa [prefixWord, tailWord_859791, baseEnd_859791] using wordTrace_append hprefix tailTrace_859791
  have hstable : (prefixWord ++ tailWord_859791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859791).length < 2 ^ (prefixWord ++ tailWord_859791).sum := by decide
  have hdescent : baseEnd_859791 < baseStart_859791 := by decide
  rcases family_descends (prefixWord ++ tailWord_859791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859808 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 6]
def baseStart_859808 : Nat := 118140960795 + 859808 * 2 ^ 59
def prefixEnd_859808 : Nat := 4983230072969 + 3 ^ 40 * 859808 * 2
def baseEnd_859808 : Nat := 196219899813812102642587

theorem tailTrace_859808 : CollatzResearch.WordTrace tailWord_859808 prefixEnd_859808 196219899813812102642587 := by
  unfold tailWord_859808
  simp only [CollatzResearch.WordTrace]
  refine ⟨15679887034534967180350039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20906516046046622907133385 15679887034534967180350039)
  ·
    refine ⟨23519830551802450770525059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15679887034534967180350039 23519830551802450770525059)
    ·
      refine ⟨35279745827703676155787589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23519830551802450770525059 35279745827703676155787589)
      ·
        refine ⟨6614952342694439279210173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35279745827703676155787589 6614952342694439279210173)
        ·
          refine ⟨2480607128510414729703815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6614952342694439279210173 2480607128510414729703815)
          ·
            refine ⟨3720910692765622094555723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480607128510414729703815 3720910692765622094555723)
            ·
              refine ⟨5581366039148433141833585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720910692765622094555723 5581366039148433141833585)
              ·
                refine ⟨4186024529361324856375189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5581366039148433141833585 4186024529361324856375189)
                ·
                  refine ⟨196219899813812102642587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4186024529361324856375189 196219899813812102642587)
                  ·
                    rfl

theorem cell21_859808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_859808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859808 prefixEnd_859808 := by exact prefixLift 859808
  have htrace : WordTrace (prefixWord ++ tailWord_859808) baseStart_859808 baseEnd_859808 := by
    simpa [prefixWord, tailWord_859808, baseEnd_859808] using wordTrace_append hprefix tailTrace_859808
  have hstable : (prefixWord ++ tailWord_859808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859808).length < 2 ^ (prefixWord ++ tailWord_859808).sum := by decide
  have hdescent : baseEnd_859808 < baseStart_859808 := by decide
  rcases family_descends (prefixWord ++ tailWord_859808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859884 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_859884 : Nat := 118140960795 + 859884 * 2 ^ 59
def prefixEnd_859884 : Nat := 4983230072969 + 3 ^ 40 * 859884 * 2
def baseEnd_859884 : Nat := 196237244049252859375765

theorem tailTrace_859884 : CollatzResearch.WordTrace tailWord_859884 prefixEnd_859884 196237244049252859375765 := by
  unfold tailWord_859884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15681273008397299670233353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20908364011196399560311137 15681273008397299670233353)
  ·
    refine ⟨11760954756297974752675015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15681273008397299670233353 11760954756297974752675015)
    ·
      refine ⟨17641432134446962129012523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11760954756297974752675015 17641432134446962129012523)
      ·
        refine ⟨26462148201670443193518785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17641432134446962129012523 26462148201670443193518785)
        ·
          refine ⟨19846611151252832395139089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26462148201670443193518785 19846611151252832395139089)
          ·
            refine ⟨14884958363439624296354317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19846611151252832395139089 14884958363439624296354317)
            ·
              refine ⟨5581859386289859111132869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14884958363439624296354317 5581859386289859111132869)
              ·
                refine ⟨1046598634929348583337413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5581859386289859111132869 1046598634929348583337413)
                ·
                  refine ⟨196237244049252859375765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046598634929348583337413 196237244049252859375765)
                  ·
                    rfl

theorem cell21_859884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_859884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859884 prefixEnd_859884 := by exact prefixLift 859884
  have htrace : WordTrace (prefixWord ++ tailWord_859884) baseStart_859884 baseEnd_859884 := by
    simpa [prefixWord, tailWord_859884, baseEnd_859884] using wordTrace_append hprefix tailTrace_859884
  have hstable : (prefixWord ++ tailWord_859884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859884).length < 2 ^ (prefixWord ++ tailWord_859884).sum := by decide
  have hdescent : baseEnd_859884 < baseStart_859884 := by decide
  rcases family_descends (prefixWord ++ tailWord_859884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859980 : List Nat := [2, 2, 1, 3, 4, 2, 1, 3, 3]
def baseStart_859980 : Nat := 118140960795 + 859980 * 2 ^ 59
def prefixEnd_859980 : Nat := 4983230072969 + 3 ^ 40 * 859980 * 2
def baseEnd_859980 : Nat := 196259152557178025775569

theorem tailTrace_859980 : CollatzResearch.WordTrace tailWord_859980 prefixEnd_859980 196259152557178025775569 := by
  unfold tailWord_859980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15683023712223403867980697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20910698282964538490640929 15683023712223403867980697)
  ·
    refine ⟨11762267784167552900985523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15683023712223403867980697 11762267784167552900985523)
    ·
      refine ⟨17643401676251329351478285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11762267784167552900985523 17643401676251329351478285)
      ·
        refine ⟨6616275628594248506804357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17643401676251329351478285 6616275628594248506804357)
        ·
          refine ⟨1240551680361421595025817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6616275628594248506804357 1240551680361421595025817)
          ·
            refine ⟨930413760271066196269363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240551680361421595025817 930413760271066196269363)
            ·
              refine ⟨1395620640406599294404045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930413760271066196269363 1395620640406599294404045)
              ·
                refine ⟨523357740152474735401517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1395620640406599294404045 523357740152474735401517)
                ·
                  refine ⟨196259152557178025775569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523357740152474735401517 196259152557178025775569)
                  ·
                    rfl

theorem cell21_859980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_859980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859980 prefixEnd_859980 := by exact prefixLift 859980
  have htrace : WordTrace (prefixWord ++ tailWord_859980) baseStart_859980 baseEnd_859980 := by
    simpa [prefixWord, tailWord_859980, baseEnd_859980] using wordTrace_append hprefix tailTrace_859980
  have hstable : (prefixWord ++ tailWord_859980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859980).length < 2 ^ (prefixWord ++ tailWord_859980).sum := by decide
  have hdescent : baseEnd_859980 < baseStart_859980 := by decide
  rcases family_descends (prefixWord ++ tailWord_859980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_859991 : List Nat := [1, 1, 3, 2, 5, 2, 7]
def baseStart_859991 : Nat := 118140960795 + 859991 * 2 ^ 59
def prefixEnd_859991 : Nat := 4983230072969 + 3 ^ 40 * 859991 * 2
def baseEnd_859991 : Nat := 21806851434116050121357

theorem tailTrace_859991 : CollatzResearch.WordTrace tailWord_859991 prefixEnd_859991 21806851434116050121357 := by
  unfold tailWord_859991
  simp only [CollatzResearch.WordTrace]
  refine ⟨31366448627406956614611827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20910965751604637743074551 31366448627406956614611827)
  ·
    refine ⟨47049672941110434921917741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31366448627406956614611827 47049672941110434921917741)
    ·
      refine ⟨17643627352916413095719153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47049672941110434921917741 17643627352916413095719153)
      ·
        refine ⟨13232720514687309821789365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17643627352916413095719153 13232720514687309821789365)
        ·
          refine ⟨1240567548251935295792753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13232720514687309821789365 1240567548251935295792753)
          ·
            refine ⟨930425661188951471844565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240567548251935295792753 930425661188951471844565)
            ·
              refine ⟨21806851434116050121357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 930425661188951471844565 21806851434116050121357)
              ·
                rfl

theorem cell21_859991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 7].length) (baseStart_859991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_859991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_859991 prefixEnd_859991 := by exact prefixLift 859991
  have htrace : WordTrace (prefixWord ++ tailWord_859991) baseStart_859991 baseEnd_859991 := by
    simpa [prefixWord, tailWord_859991, baseEnd_859991] using wordTrace_append hprefix tailTrace_859991
  have hstable : (prefixWord ++ tailWord_859991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_859991).length < 2 ^ (prefixWord ++ tailWord_859991).sum := by decide
  have hdescent : baseEnd_859991 < baseStart_859991 := by decide
  rcases family_descends (prefixWord ++ tailWord_859991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860056 : List Nat := [2, 1, 2, 6, 1, 1, 1, 4, 3]
def baseStart_860056 : Nat := 118140960795 + 860056 * 2 ^ 59
def prefixEnd_860056 : Nat := 4983230072969 + 3 ^ 40 * 860056 * 2
def baseEnd_860056 : Nat := 196276496792618782508747

theorem tailTrace_860056 : CollatzResearch.WordTrace tailWord_860056 prefixEnd_860056 196276496792618782508747 := by
  unfold tailWord_860056
  simp only [CollatzResearch.WordTrace]
  refine ⟨15684409686085736357864011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20912546248114315143818681 15684409686085736357864011)
  ·
    refine ⟨23526614529128604536796017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15684409686085736357864011 23526614529128604536796017)
    ·
      refine ⟨17644960896846453402597013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23526614529128604536796017 17644960896846453402597013)
      ·
        refine ⟨827107542039677503246735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17644960896846453402597013 827107542039677503246735)
        ·
          refine ⟨1240661313059516254870103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827107542039677503246735 1240661313059516254870103)
          ·
            refine ⟨1860991969589274382305155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240661313059516254870103 1860991969589274382305155)
            ·
              refine ⟨2791487954383911573457733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1860991969589274382305155 2791487954383911573457733)
              ·
                refine ⟨523403991446983420023325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2791487954383911573457733 523403991446983420023325)
                ·
                  refine ⟨196276496792618782508747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523403991446983420023325 196276496792618782508747)
                  ·
                    rfl

theorem cell21_860056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 3].length) (baseStart_860056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860056 prefixEnd_860056 := by exact prefixLift 860056
  have htrace : WordTrace (prefixWord ++ tailWord_860056) baseStart_860056 baseEnd_860056 := by
    simpa [prefixWord, tailWord_860056, baseEnd_860056] using wordTrace_append hprefix tailTrace_860056
  have hstable : (prefixWord ++ tailWord_860056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860056).length < 2 ^ (prefixWord ++ tailWord_860056).sum := by decide
  have hdescent : baseEnd_860056 < baseStart_860056 := by decide
  rcases family_descends (prefixWord ++ tailWord_860056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860081 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 7]
def baseStart_860081 : Nat := 118140960795 + 860081 * 2 ^ 59
def prefixEnd_860081 : Nat := 4983230072969 + 3 ^ 40 * 860081 * 2
def baseEnd_860081 : Nat := 196282202133224294592029

theorem tailTrace_860081 : CollatzResearch.WordTrace tailWord_860081 prefixEnd_860081 196282202133224294592029 := by
  unfold tailWord_860081
  simp only [CollatzResearch.WordTrace]
  refine ⟨31369731197080901985388097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20913154131387267990258731 31369731197080901985388097)
  ·
    refine ⟨23527298397810676489041073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31369731197080901985388097 23527298397810676489041073)
    ·
      refine ⟨17645473798358007366780805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23527298397810676489041073 17645473798358007366780805)
      ·
        refine ⟨3308526337192126381271401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17645473798358007366780805 3308526337192126381271401)
        ·
          refine ⟨2481394752894094785953551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3308526337192126381271401 2481394752894094785953551)
          ·
            refine ⟨3722092129341142178930327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2481394752894094785953551 3722092129341142178930327)
            ·
              refine ⟨5583138194011713268395491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3722092129341142178930327 5583138194011713268395491)
              ·
                refine ⟨8374707291017569902593237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5583138194011713268395491 8374707291017569902593237)
                ·
                  refine ⟨196282202133224294592029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8374707291017569902593237 196282202133224294592029)
                  ·
                    rfl

theorem cell21_860081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_860081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860081 prefixEnd_860081 := by exact prefixLift 860081
  have htrace : WordTrace (prefixWord ++ tailWord_860081) baseStart_860081 baseEnd_860081 := by
    simpa [prefixWord, tailWord_860081, baseEnd_860081] using wordTrace_append hprefix tailTrace_860081
  have hstable : (prefixWord ++ tailWord_860081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860081).length < 2 ^ (prefixWord ++ tailWord_860081).sum := by decide
  have hdescent : baseEnd_860081 < baseStart_860081 := by decide
  rcases family_descends (prefixWord ++ tailWord_860081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860095 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 6]
def baseStart_860095 : Nat := 118140960795 + 860095 * 2 ^ 59
def prefixEnd_860095 : Nat := 4983230072969 + 3 ^ 40 * 860095 * 2
def baseEnd_860095 : Nat := 196285397123963381358667

theorem tailTrace_860095 : CollatzResearch.WordTrace tailWord_860095 prefixEnd_860095 196285397123963381358667 := by
  unfold tailWord_860095
  simp only [CollatzResearch.WordTrace]
  refine ⟨31370241819030182376397739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20913494546020121584265159 31370241819030182376397739)
  ·
    refine ⟨47055362728545273564596609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31370241819030182376397739 47055362728545273564596609)
    ·
      refine ⟨35291522046408955173447457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47055362728545273564596609 35291522046408955173447457)
      ·
        refine ⟨26468641534806716380085593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35291522046408955173447457 26468641534806716380085593)
        ·
          refine ⟨19851481151105037285064195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26468641534806716380085593 19851481151105037285064195)
          ·
            refine ⟨29777221726657555927596293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19851481151105037285064195 29777221726657555927596293)
            ·
              refine ⟨5583229073748291736424305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29777221726657555927596293 5583229073748291736424305)
              ·
                refine ⟨4187421805311218802318229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5583229073748291736424305 4187421805311218802318229)
                ·
                  refine ⟨196285397123963381358667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4187421805311218802318229 196285397123963381358667)
                  ·
                    rfl

theorem cell21_860095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_860095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860095 prefixEnd_860095 := by exact prefixLift 860095
  have htrace : WordTrace (prefixWord ++ tailWord_860095) baseStart_860095 baseEnd_860095 := by
    simpa [prefixWord, tailWord_860095, baseEnd_860095] using wordTrace_append hprefix tailTrace_860095
  have hstable : (prefixWord ++ tailWord_860095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860095).length < 2 ^ (prefixWord ++ tailWord_860095).sum := by decide
  have hdescent : baseEnd_860095 < baseStart_860095 := by decide
  rcases family_descends (prefixWord ++ tailWord_860095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860112 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_860112 : Nat := 118140960795 + 860112 * 2 ^ 59
def prefixEnd_860112 : Nat := 4983230072969 + 3 ^ 40 * 860112 * 2
def baseEnd_860112 : Nat := 196289276755575129575299

theorem tailTrace_860112 : CollatzResearch.WordTrace tailWord_860112 prefixEnd_860112 196289276755575129575299 := by
  unfold tailWord_860112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15685430929984297139883295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20913907906645729519844393 15685430929984297139883295)
  ·
    refine ⟨23528146394976445709824943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15685430929984297139883295 23528146394976445709824943)
    ·
      refine ⟨35292219592464668564737415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23528146394976445709824943 35292219592464668564737415)
      ·
        refine ⟨52938329388697002847106123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35292219592464668564737415 52938329388697002847106123)
        ·
          refine ⟨79407494083045504270659185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52938329388697002847106123 79407494083045504270659185)
          ·
            refine ⟨59555620562284128202994389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79407494083045504270659185 59555620562284128202994389)
            ·
              refine ⟨1395834856928534254757681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59555620562284128202994389 1395834856928534254757681)
              ·
                refine ⟨1046876142696400691068261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395834856928534254757681 1046876142696400691068261)
                ·
                  refine ⟨196289276755575129575299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046876142696400691068261 196289276755575129575299)
                  ·
                    rfl

theorem cell21_860112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_860112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860112 prefixEnd_860112 := by exact prefixLift 860112
  have htrace : WordTrace (prefixWord ++ tailWord_860112) baseStart_860112 baseEnd_860112 := by
    simpa [prefixWord, tailWord_860112, baseEnd_860112] using wordTrace_append hprefix tailTrace_860112
  have hstable : (prefixWord ++ tailWord_860112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860112).length < 2 ^ (prefixWord ++ tailWord_860112).sum := by decide
  have hdescent : baseEnd_860112 < baseStart_860112 := by decide
  rcases family_descends (prefixWord ++ tailWord_860112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860166 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_860166 : Nat := 118140960795 + 860166 * 2 ^ 59
def prefixEnd_860166 : Nat := 4983230072969 + 3 ^ 40 * 860166 * 2
def baseEnd_860166 : Nat := 196301600291283035675189

theorem tailTrace_860166 : CollatzResearch.WordTrace tailWord_860166 prefixEnd_860166 196301600291283035675189 := by
  unfold tailWord_860166
  simp only [CollatzResearch.WordTrace]
  refine ⟨980400981305405046944761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20915220934515307668154901 980400981305405046944761)
  ·
    refine ⟨735300735979053785208571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 980400981305405046944761 735300735979053785208571)
    ·
      refine ⟨1102951103968580677812857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 735300735979053785208571 1102951103968580677812857)
      ·
        refine ⟨827213327976435508359643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1102951103968580677812857 827213327976435508359643)
        ·
          refine ⟨1240819991964653262539465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827213327976435508359643 1240819991964653262539465)
          ·
            refine ⟨930614993973489946904599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240819991964653262539465 930614993973489946904599)
            ·
              refine ⟨1395922490960234920356899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930614993973489946904599 1395922490960234920356899)
              ·
                refine ⟨2093883736440352380535349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395922490960234920356899 2093883736440352380535349)
                ·
                  refine ⟨196301600291283035675189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2093883736440352380535349 196301600291283035675189)
                  ·
                    rfl

theorem cell21_860166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_860166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860166 prefixEnd_860166 := by exact prefixLift 860166
  have htrace : WordTrace (prefixWord ++ tailWord_860166) baseStart_860166 baseEnd_860166 := by
    simpa [prefixWord, tailWord_860166, baseEnd_860166] using wordTrace_append hprefix tailTrace_860166
  have hstable : (prefixWord ++ tailWord_860166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860166).length < 2 ^ (prefixWord ++ tailWord_860166).sum := by decide
  have hdescent : baseEnd_860166 < baseStart_860166 := by decide
  rcases family_descends (prefixWord ++ tailWord_860166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860171 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 6]
def baseStart_860171 : Nat := 118140960795 + 860171 * 2 ^ 59
def prefixEnd_860171 : Nat := 4983230072969 + 3 ^ 40 * 860171 * 2
def baseEnd_860171 : Nat := 196302741359404138091845

theorem tailTrace_860171 : CollatzResearch.WordTrace tailWord_860171 prefixEnd_860171 196302741359404138091845 := by
  unfold tailWord_860171
  simp only [CollatzResearch.WordTrace]
  refine ⟨31373013766754847356164367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20915342511169898237442911 31373013766754847356164367)
  ·
    refine ⟨47059520650132271034246551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31373013766754847356164367 47059520650132271034246551)
    ·
      refine ⟨70589280975198406551369827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47059520650132271034246551 70589280975198406551369827)
      ·
        refine ⟨105883921462797609827054741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70589280975198406551369827 105883921462797609827054741)
        ·
          refine ⟨4963308818568637960643191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105883921462797609827054741 4963308818568637960643191)
          ·
            refine ⟨7444963227852956940964787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963308818568637960643191 7444963227852956940964787)
            ·
              refine ⟨11167444841779435411447181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7444963227852956940964787 11167444841779435411447181)
              ·
                refine ⟨4187791815667288279292693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11167444841779435411447181 4187791815667288279292693)
                ·
                  refine ⟨196302741359404138091845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4187791815667288279292693 196302741359404138091845)
                  ·
                    rfl

theorem cell21_860171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_860171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860171 prefixEnd_860171 := by exact prefixLift 860171
  have htrace : WordTrace (prefixWord ++ tailWord_860171) baseStart_860171 baseEnd_860171 := by
    simpa [prefixWord, tailWord_860171, baseEnd_860171] using wordTrace_append hprefix tailTrace_860171
  have hstable : (prefixWord ++ tailWord_860171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860171).length < 2 ^ (prefixWord ++ tailWord_860171).sum := by decide
  have hdescent : baseEnd_860171 < baseStart_860171 := by decide
  rcases family_descends (prefixWord ++ tailWord_860171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860180 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 4]
def baseStart_860180 : Nat := 118140960795 + 860180 * 2 ^ 59
def prefixEnd_860180 : Nat := 4983230072969 + 3 ^ 40 * 860180 * 2
def baseEnd_860180 : Nat := 196304795282022122441827

theorem tailTrace_860180 : CollatzResearch.WordTrace tailWord_860180 prefixEnd_860180 196304795282022122441827 := by
  unfold tailWord_860180
  simp only [CollatzResearch.WordTrace]
  refine ⟨15686671011861120946620997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20915561349148161262161329 15686671011861120946620997)
  ·
    refine ⟨2941250814723960177491437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15686671011861120946620997 2941250814723960177491437)
    ·
      refine ⟨1102969055521485066559289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2941250814723960177491437 1102969055521485066559289)
      ·
        refine ⟨827226791641113799919467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1102969055521485066559289 827226791641113799919467)
        ·
          refine ⟨1240840187461670699879201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 827226791641113799919467 1240840187461670699879201)
          ·
            refine ⟨930630140596253024909401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1240840187461670699879201 930630140596253024909401)
            ·
              refine ⟨697972605447189768682051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930630140596253024909401 697972605447189768682051)
              ·
                refine ⟨1046958908170784653023077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 697972605447189768682051 1046958908170784653023077)
                ·
                  refine ⟨196304795282022122441827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046958908170784653023077 196304795282022122441827)
                  ·
                    rfl

theorem cell21_860180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_860180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860180 prefixEnd_860180 := by exact prefixLift 860180
  have htrace : WordTrace (prefixWord ++ tailWord_860180) baseStart_860180 baseEnd_860180 := by
    simpa [prefixWord, tailWord_860180, baseEnd_860180] using wordTrace_append hprefix tailTrace_860180
  have hstable : (prefixWord ++ tailWord_860180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860180).length < 2 ^ (prefixWord ++ tailWord_860180).sum := by decide
  have hdescent : baseEnd_860180 < baseStart_860180 := by decide
  rcases family_descends (prefixWord ++ tailWord_860180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860222 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 4]
def baseStart_860222 : Nat := 118140960795 + 860222 * 2 ^ 59
def prefixEnd_860222 : Nat := 4983230072969 + 3 ^ 40 * 860222 * 2
def baseEnd_860222 : Nat := 196314380254239382741741

theorem tailTrace_860222 : CollatzResearch.WordTrace tailWord_860222 prefixEnd_860222 196314380254239382741741 := by
  unfold tailWord_860222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3921859236196260383283865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20916582593046722044180613 3921859236196260383283865)
  ·
    refine ⟨2941394427147195287462899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3921859236196260383283865 2941394427147195287462899)
    ·
      refine ⟨4412091640720792931194349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2941394427147195287462899 4412091640720792931194349)
      ·
        refine ⟨1654534365270297349197881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4412091640720792931194349 1654534365270297349197881)
        ·
          refine ⟨1240900773952723011898411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1654534365270297349197881 1240900773952723011898411)
          ·
            refine ⟨1861351160929084517847617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1240900773952723011898411 1861351160929084517847617)
            ·
              refine ⟨1396013370696813388385713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1861351160929084517847617 1396013370696813388385713)
              ·
                refine ⟨1047010028022610041289285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396013370696813388385713 1047010028022610041289285)
                ·
                  refine ⟨196314380254239382741741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1047010028022610041289285 196314380254239382741741)
                  ·
                    rfl

theorem cell21_860222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_860222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860222 prefixEnd_860222 := by exact prefixLift 860222
  have htrace : WordTrace (prefixWord ++ tailWord_860222) baseStart_860222 baseEnd_860222 := by
    simpa [prefixWord, tailWord_860222, baseEnd_860222] using wordTrace_append hprefix tailTrace_860222
  have hstable : (prefixWord ++ tailWord_860222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860222).length < 2 ^ (prefixWord ++ tailWord_860222).sum := by decide
  have hdescent : baseEnd_860222 < baseStart_860222 := by decide
  rcases family_descends (prefixWord ++ tailWord_860222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860281 : List Nat := [1, 2, 1, 3, 4, 3, 1, 2, 4]
def baseStart_860281 : Nat := 118140960795 + 860281 * 2 ^ 59
def prefixEnd_860281 : Nat := 4983230072969 + 3 ^ 40 * 860281 * 2
def baseEnd_860281 : Nat := 196327844858068391258287

theorem tailTrace_860281 : CollatzResearch.WordTrace tailWord_860281 prefixEnd_860281 196327844858068391258287 := by
  unfold tailWord_860281
  simp only [CollatzResearch.WordTrace]
  refine ⟨31377025796356336142668697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20918017197570890761779131 31377025796356336142668697)
  ·
    refine ⟨23532769347267252107001523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31377025796356336142668697 23532769347267252107001523)
    ·
      refine ⟨35299154020900878160502285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23532769347267252107001523 35299154020900878160502285)
      ·
        refine ⟨13237182757837829310188357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35299154020900878160502285 13237182757837829310188357)
        ·
          refine ⟨2481971767094592995660317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13237182757837829310188357 2481971767094592995660317)
          ·
            refine ⟨930739412660472373372619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2481971767094592995660317 930739412660472373372619)
            ·
              refine ⟨1396109118990708560058929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 930739412660472373372619 1396109118990708560058929)
              ·
                refine ⟨1047081839243031420044197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1396109118990708560058929 1047081839243031420044197)
                ·
                  refine ⟨196327844858068391258287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1047081839243031420044197 196327844858068391258287)
                  ·
                    rfl

theorem cell21_860281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_860281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860281 prefixEnd_860281 := by exact prefixLift 860281
  have htrace : WordTrace (prefixWord ++ tailWord_860281) baseStart_860281 baseEnd_860281 := by
    simpa [prefixWord, tailWord_860281, baseEnd_860281] using wordTrace_append hprefix tailTrace_860281
  have hstable : (prefixWord ++ tailWord_860281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860281).length < 2 ^ (prefixWord ++ tailWord_860281).sum := by decide
  have hdescent : baseEnd_860281 < baseStart_860281 := by decide
  rcases family_descends (prefixWord ++ tailWord_860281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860312 : List Nat := [2, 1, 2, 4, 3, 2, 2, 5]
def baseStart_860312 : Nat := 118140960795 + 860312 * 2 ^ 59
def prefixEnd_860312 : Nat := 4983230072969 + 3 ^ 40 * 860312 * 2
def baseEnd_860312 : Nat := 65444973160139742080519

theorem tailTrace_860312 : CollatzResearch.WordTrace tailWord_860312 prefixEnd_860312 65444973160139742080519 := by
  unfold tailWord_860312
  simp only [CollatzResearch.WordTrace]
  refine ⟨15689078229622014218523595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20918770972829352291364793 15689078229622014218523595)
  ·
    refine ⟨23533617344433021327785393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15689078229622014218523595 23533617344433021327785393)
    ·
      refine ⟨17650213008324765995839045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23533617344433021327785393 17650213008324765995839045)
      ·
        refine ⟨3309414939060893624219821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17650213008324765995839045 3309414939060893624219821)
        ·
          refine ⟨1241030602147835109082433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3309414939060893624219821 1241030602147835109082433)
          ·
            refine ⟨930772951610876331811825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1241030602147835109082433 930772951610876331811825)
            ·
              refine ⟨698079713708157248858869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930772951610876331811825 698079713708157248858869)
              ·
                refine ⟨65444973160139742080519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 698079713708157248858869 65444973160139742080519)
                ·
                  rfl

theorem cell21_860312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 5].length) (baseStart_860312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860312 prefixEnd_860312 := by exact prefixLift 860312
  have htrace : WordTrace (prefixWord ++ tailWord_860312) baseStart_860312 baseEnd_860312 := by
    simpa [prefixWord, tailWord_860312, baseEnd_860312] using wordTrace_append hprefix tailTrace_860312
  have hstable : (prefixWord ++ tailWord_860312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860312).length < 2 ^ (prefixWord ++ tailWord_860312).sum := by decide
  have hdescent : baseEnd_860312 < baseStart_860312 := by decide
  rcases family_descends (prefixWord ++ tailWord_860312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860343 : List Nat := [1, 1, 3, 1, 4, 3, 3, 2, 3]
def baseStart_860343 : Nat := 118140960795 + 860343 * 2 ^ 59
def prefixEnd_860343 : Nat := 4983230072969 + 3 ^ 40 * 860343 * 2
def baseEnd_860343 : Nat := 196341994102770061224827

theorem tailTrace_860343 : CollatzResearch.WordTrace tailWord_860343 prefixEnd_860343 196341994102770061224827 := by
  unfold tailWord_860343
  simp only [CollatzResearch.WordTrace]
  refine ⟨31379287122131720731425683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20919524748087813820950455 31379287122131720731425683)
  ·
    refine ⟨47068930683197581097138525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31379287122131720731425683 47068930683197581097138525)
    ·
      refine ⟨17650849006199092911426947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47068930683197581097138525 17650849006199092911426947)
      ·
        refine ⟨26476273509298639367140421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17650849006199092911426947 26476273509298639367140421)
        ·
          refine ⟨4964301282993494881338829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26476273509298639367140421 4964301282993494881338829)
          ·
            refine ⟨1861612981122560580502061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4964301282993494881338829 1861612981122560580502061)
            ·
              refine ⟨698104867920960217688273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1861612981122560580502061 698104867920960217688273)
              ·
                refine ⟨523578650940720163266205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698104867920960217688273 523578650940720163266205)
                ·
                  refine ⟨196341994102770061224827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523578650940720163266205 196341994102770061224827)
                  ·
                    rfl

theorem cell21_860343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 3].length) (baseStart_860343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860343 prefixEnd_860343 := by exact prefixLift 860343
  have htrace : WordTrace (prefixWord ++ tailWord_860343) baseStart_860343 baseEnd_860343 := by
    simpa [prefixWord, tailWord_860343, baseEnd_860343] using wordTrace_append hprefix tailTrace_860343
  have hstable : (prefixWord ++ tailWord_860343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860343).length < 2 ^ (prefixWord ++ tailWord_860343).sum := by decide
  have hdescent : baseEnd_860343 < baseStart_860343 := by decide
  rcases family_descends (prefixWord ++ tailWord_860343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860444 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 9]
def baseStart_860444 : Nat := 118140960795 + 860444 * 2 ^ 59
def prefixEnd_860444 : Nat := 4983230072969 + 3 ^ 40 * 860444 * 2
def baseEnd_860444 : Nat := 196365043678816330041287

theorem tailTrace_860444 : CollatzResearch.WordTrace tailWord_860444 prefixEnd_860444 196365043678816330041287 := by
  unfold tailWord_860444
  simp only [CollatzResearch.WordTrace]
  refine ⟨15691485447382907490426193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20921980596510543320568257 15691485447382907490426193)
  ·
    refine ⟨11768614085537180617819645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15691485447382907490426193 11768614085537180617819645)
    ·
      refine ⟨4413230282076442731682367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11768614085537180617819645 4413230282076442731682367)
      ·
        refine ⟨6619845423114664097523551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4413230282076442731682367 6619845423114664097523551)
        ·
          refine ⟨9929768134671996146285327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619845423114664097523551 9929768134671996146285327)
          ·
            refine ⟨14894652202007994219427991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9929768134671996146285327 14894652202007994219427991)
            ·
              refine ⟨22341978303011991329141987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14894652202007994219427991 22341978303011991329141987)
              ·
                refine ⟨33512967454517986993712981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22341978303011991329141987 33512967454517986993712981)
                ·
                  refine ⟨196365043678816330041287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33512967454517986993712981 196365043678816330041287)
                  ·
                    rfl

theorem cell21_860444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_860444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860444 prefixEnd_860444 := by exact prefixLift 860444
  have htrace : WordTrace (prefixWord ++ tailWord_860444) baseStart_860444 baseEnd_860444 := by
    simpa [prefixWord, tailWord_860444, baseEnd_860444] using wordTrace_append hprefix tailTrace_860444
  have hstable : (prefixWord ++ tailWord_860444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860444).length < 2 ^ (prefixWord ++ tailWord_860444).sum := by decide
  have hdescent : baseEnd_860444 < baseStart_860444 := by decide
  rcases family_descends (prefixWord ++ tailWord_860444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860481 : List Nat := [1, 2, 5, 2, 3, 1, 2, 5]
def baseStart_860481 : Nat := 118140960795 + 860481 * 2 ^ 59
def prefixEnd_860481 : Nat := 4983230072969 + 3 ^ 40 * 860481 * 2
def baseEnd_860481 : Nat := 65457829194304162641515

theorem tailTrace_860481 : CollatzResearch.WordTrace tailWord_860481 prefixEnd_860481 65457829194304162641515 := by
  unfold tailWord_860481
  simp only [CollatzResearch.WordTrace]
  refine ⟨31384320395631770299949297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20922880263754513533299531 31384320395631770299949297)
  ·
    refine ⟨23538240296723827724961973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31384320395631770299949297 23538240296723827724961973)
    ·
      refine ⟨2206710027817858849215185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23538240296723827724961973 2206710027817858849215185)
      ·
        refine ⟨1655032520863394136911389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2206710027817858849215185 1655032520863394136911389)
        ·
          refine ⟨620637195323772801341771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1655032520863394136911389 620637195323772801341771)
          ·
            refine ⟨930955792985659202012657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620637195323772801341771 930955792985659202012657)
            ·
              refine ⟨698216844739244401509493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 930955792985659202012657 698216844739244401509493)
              ·
                refine ⟨65457829194304162641515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 698216844739244401509493 65457829194304162641515)
                ·
                  rfl

theorem cell21_860481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 5].length) (baseStart_860481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860481 prefixEnd_860481 := by exact prefixLift 860481
  have htrace : WordTrace (prefixWord ++ tailWord_860481) baseStart_860481 baseEnd_860481 := by
    simpa [prefixWord, tailWord_860481, baseEnd_860481] using wordTrace_append hprefix tailTrace_860481
  have hstable : (prefixWord ++ tailWord_860481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860481).length < 2 ^ (prefixWord ++ tailWord_860481).sum := by decide
  have hdescent : baseEnd_860481 < baseStart_860481 := by decide
  rcases family_descends (prefixWord ++ tailWord_860481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860568 : List Nat := [2, 1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_860568 : Nat := 118140960795 + 860568 * 2 ^ 59
def prefixEnd_860568 : Nat := 4983230072969 + 3 ^ 40 * 860568 * 2
def baseEnd_860568 : Nat := 196393342168219669974367

theorem tailTrace_860568 : CollatzResearch.WordTrace tailWord_860568 prefixEnd_860568 196393342168219669974367 := by
  unfold tailWord_860568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15693746773158292079183179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20924995697544389438910905 15693746773158292079183179)
  ·
    refine ⟨23540620159737438118774769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15693746773158292079183179 23540620159737438118774769)
    ·
      refine ⟨17655465119803078589081077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23540620159737438118774769 17655465119803078589081077)
      ·
        refine ⟨1655199854981538617726351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17655465119803078589081077 1655199854981538617726351)
        ·
          refine ⟨2482799782472307926589527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1655199854981538617726351 2482799782472307926589527)
          ·
            refine ⟨3724199673708461889884291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2482799782472307926589527 3724199673708461889884291)
            ·
              refine ⟨5586299510562692834826437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3724199673708461889884291 5586299510562692834826437)
              ·
                refine ⟨1047431158230504906529957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5586299510562692834826437 1047431158230504906529957)
                ·
                  refine ⟨196393342168219669974367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1047431158230504906529957 196393342168219669974367)
                  ·
                    rfl

theorem cell21_860568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_860568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860568 prefixEnd_860568 := by exact prefixLift 860568
  have htrace : WordTrace (prefixWord ++ tailWord_860568) baseStart_860568 baseEnd_860568 := by
    simpa [prefixWord, tailWord_860568, baseEnd_860568] using wordTrace_append hprefix tailTrace_860568
  have hstable : (prefixWord ++ tailWord_860568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860568).length < 2 ^ (prefixWord ++ tailWord_860568).sum := by decide
  have hdescent : baseEnd_860568 < baseStart_860568 := by decide
  rcases family_descends (prefixWord ++ tailWord_860568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860630 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_860630 : Nat := 118140960795 + 860630 * 2 ^ 59
def prefixEnd_860630 : Nat := 4983230072969 + 3 ^ 40 * 860630 * 2
def baseEnd_860630 : Nat := 196407491412921339940907

theorem tailTrace_860630 : CollatzResearch.WordTrace tailWord_860630 prefixEnd_860630 196407491412921339940907 := by
  unfold tailWord_860630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961859679505748046695209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20926503248061312498082229 1961859679505748046695209)
  ·
    refine ⟨1471394759629311035021407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1961859679505748046695209 1471394759629311035021407)
    ·
      refine ⟨2207092139443966552532111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1471394759629311035021407 2207092139443966552532111)
      ·
        refine ⟨3310638209165949828798167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2207092139443966552532111 3310638209165949828798167)
        ·
          refine ⟨4965957313748924743197251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3310638209165949828798167 4965957313748924743197251)
          ·
            refine ⟨7448935970623387114795877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4965957313748924743197251 7448935970623387114795877)
            ·
              refine ⟨1396675494491885084024227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7448935970623387114795877 1396675494491885084024227)
              ·
                refine ⟨2095013241737827626036341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1396675494491885084024227 2095013241737827626036341)
                ·
                  refine ⟨196407491412921339940907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2095013241737827626036341 196407491412921339940907)
                  ·
                    rfl

theorem cell21_860630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_860630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860630 prefixEnd_860630 := by exact prefixLift 860630
  have htrace : WordTrace (prefixWord ++ tailWord_860630) baseStart_860630 baseEnd_860630 := by
    simpa [prefixWord, tailWord_860630, baseEnd_860630] using wordTrace_append hprefix tailTrace_860630
  have hstable : (prefixWord ++ tailWord_860630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860630).length < 2 ^ (prefixWord ++ tailWord_860630).sum := by decide
  have hdescent : baseEnd_860630 < baseStart_860630 := by decide
  rcases family_descends (prefixWord ++ tailWord_860630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860641 : List Nat := [1, 2, 3, 1, 2, 2, 2, 8]
def baseStart_860641 : Nat := 118140960795 + 860641 * 2 ^ 59
def prefixEnd_860641 : Nat := 4983230072969 + 3 ^ 40 * 860641 * 2
def baseEnd_860641 : Nat := 65470000587595921752517

theorem tailTrace_860641 : CollatzResearch.WordTrace tailWord_860641 prefixEnd_860641 65470000587595921752517 := by
  unfold tailWord_860641
  simp only [CollatzResearch.WordTrace]
  refine ⟨31390156075052117625773777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20926770716701411750515851 31390156075052117625773777)
  ·
    refine ⟨23542617056289088219330333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31390156075052117625773777 23542617056289088219330333)
    ·
      refine ⟨8828481396108408082248875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23542617056289088219330333 8828481396108408082248875)
      ·
        refine ⟨13242722094162612123373313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8828481396108408082248875 13242722094162612123373313)
        ·
          refine ⟨9932041570621959092529985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13242722094162612123373313 9932041570621959092529985)
          ·
            refine ⟨7449031177966469319397489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9932041570621959092529985 7449031177966469319397489)
            ·
              refine ⟨5586773383474851989548117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7449031177966469319397489 5586773383474851989548117)
              ·
                refine ⟨65470000587595921752517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5586773383474851989548117 65470000587595921752517)
                ·
                  rfl

theorem cell21_860641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 8].length) (baseStart_860641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860641 prefixEnd_860641 := by exact prefixLift 860641
  have htrace : WordTrace (prefixWord ++ tailWord_860641) baseStart_860641 baseEnd_860641 := by
    simpa [prefixWord, tailWord_860641, baseEnd_860641] using wordTrace_append hprefix tailTrace_860641
  have hstable : (prefixWord ++ tailWord_860641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860641).length < 2 ^ (prefixWord ++ tailWord_860641).sum := by decide
  have hdescent : baseEnd_860641 < baseStart_860641 := by decide
  rcases family_descends (prefixWord ++ tailWord_860641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860678 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_860678 : Nat := 118140960795 + 860678 * 2 ^ 59
def prefixEnd_860678 : Nat := 4983230072969 + 3 ^ 40 * 860678 * 2
def baseEnd_860678 : Nat := 196418445666883923140809

theorem tailTrace_860678 : CollatzResearch.WordTrace tailWord_860678 prefixEnd_860678 196418445666883923140809 := by
  unfold tailWord_860678
  simp only [CollatzResearch.WordTrace]
  refine ⟨980984549247439779527209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20927670383945381963247125 980984549247439779527209)
  ·
    refine ⟨735738411935579834645407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 980984549247439779527209 735738411935579834645407)
    ·
      refine ⟨1103607617903369751968111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 735738411935579834645407 1103607617903369751968111)
      ·
        refine ⟨1655411426855054627952167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1103607617903369751968111 1655411426855054627952167)
        ·
          refine ⟨2483117140282581941928251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1655411426855054627952167 2483117140282581941928251)
          ·
            refine ⟨3724675710423872912892377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483117140282581941928251 3724675710423872912892377)
            ·
              refine ⟨2793506782817904684669283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3724675710423872912892377 2793506782817904684669283)
              ·
                refine ⟨4190260174226857027003925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2793506782817904684669283 4190260174226857027003925)
                ·
                  refine ⟨196418445666883923140809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4190260174226857027003925 196418445666883923140809)
                  ·
                    rfl

theorem cell21_860678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_860678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860678 prefixEnd_860678 := by exact prefixLift 860678
  have htrace : WordTrace (prefixWord ++ tailWord_860678) baseStart_860678 baseEnd_860678 := by
    simpa [prefixWord, tailWord_860678, baseEnd_860678] using wordTrace_append hprefix tailTrace_860678
  have hstable : (prefixWord ++ tailWord_860678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860678).length < 2 ^ (prefixWord ++ tailWord_860678).sum := by decide
  have hdescent : baseEnd_860678 < baseStart_860678 := by decide
  rcases family_descends (prefixWord ++ tailWord_860678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860695 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 4]
def baseStart_860695 : Nat := 118140960795 + 860695 * 2 ^ 59
def prefixEnd_860695 : Nat := 4983230072969 + 3 ^ 40 * 860695 * 2
def baseEnd_860695 : Nat := 196422325298495671357441

theorem tailTrace_860695 : CollatzResearch.WordTrace tailWord_860695 prefixEnd_860695 196422325298495671357441 := by
  unfold tailWord_860695
  simp only [CollatzResearch.WordTrace]
  refine ⟨31392125616856484848239539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20928083744570989898826359 31392125616856484848239539)
  ·
    refine ⟨47088188425284727272359309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31392125616856484848239539 47088188425284727272359309)
    ·
      refine ⟨17658070659481772727134741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47088188425284727272359309 17658070659481772727134741)
      ·
        refine ⟨827722062163208096584441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17658070659481772727134741 827722062163208096584441)
        ·
          refine ⟨620791546622406072438331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827722062163208096584441 620791546622406072438331)
          ·
            refine ⟨931187319933609108657497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620791546622406072438331 931187319933609108657497)
            ·
              refine ⟨698390489950206831493123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931187319933609108657497 698390489950206831493123)
              ·
                refine ⟨1047585734925310247239685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698390489950206831493123 1047585734925310247239685)
                ·
                  refine ⟨196422325298495671357441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1047585734925310247239685 196422325298495671357441)
                  ·
                    rfl

theorem cell21_860695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 4].length) (baseStart_860695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860695 prefixEnd_860695 := by exact prefixLift 860695
  have htrace : WordTrace (prefixWord ++ tailWord_860695) baseStart_860695 baseEnd_860695 := by
    simpa [prefixWord, tailWord_860695, baseEnd_860695] using wordTrace_append hprefix tailTrace_860695
  have hstable : (prefixWord ++ tailWord_860695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860695).length < 2 ^ (prefixWord ++ tailWord_860695).sum := by decide
  have hdescent : baseEnd_860695 < baseStart_860695 := by decide
  rcases family_descends (prefixWord ++ tailWord_860695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860734 : List Nat := [4, 2, 1, 4, 10]
def baseStart_860734 : Nat := 118140960795 + 860734 * 2 ^ 59
def prefixEnd_860734 : Nat := 4983230072969 + 3 ^ 40 * 860734 * 2
def baseEnd_860734 : Nat := 2425076859627657656881

theorem tailTrace_860734 : CollatzResearch.WordTrace tailWord_860734 prefixEnd_860734 2425076859627657656881 := by
  unfold tailWord_860734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924193507964399313613657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20929032042476796339272837 3924193507964399313613657)
  ·
    refine ⟨2943145130973299485210243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3924193507964399313613657 2943145130973299485210243)
    ·
      refine ⟨4414717696459949227815365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2943145130973299485210243 4414717696459949227815365)
      ·
        refine ⟨827759568086240480215381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4414717696459949227815365 827759568086240480215381)
        ·
          refine ⟨2425076859627657656881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 827759568086240480215381 2425076859627657656881)
          ·
            rfl

theorem cell21_860734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 10].length) (baseStart_860734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860734 prefixEnd_860734 := by exact prefixLift 860734
  have htrace : WordTrace (prefixWord ++ tailWord_860734) baseStart_860734 baseEnd_860734 := by
    simpa [prefixWord, tailWord_860734, baseEnd_860734] using wordTrace_append hprefix tailTrace_860734
  have hstable : (prefixWord ++ tailWord_860734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860734).length < 2 ^ (prefixWord ++ tailWord_860734).sum := by decide
  have hdescent : baseEnd_860734 < baseStart_860734 := by decide
  rcases family_descends (prefixWord ++ tailWord_860734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860748 : List Nat := [2, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_860748 : Nat := 118140960795 + 860748 * 2 ^ 59
def prefixEnd_860748 : Nat := 4983230072969 + 3 ^ 40 * 860748 * 2
def baseEnd_860748 : Nat := 196434420620579356973999

theorem tailTrace_860748 : CollatzResearch.WordTrace tailWord_860748 prefixEnd_860748 196434420620579356973999 := by
  unfold tailWord_860748
  simp only [CollatzResearch.WordTrace]
  refine ⟨15697029342832237449959449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20929372457109649933279265 15697029342832237449959449)
  ·
    refine ⟨11772772007124178087469587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15697029342832237449959449 11772772007124178087469587)
    ·
      refine ⟨17659158010686267131204381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11772772007124178087469587 17659158010686267131204381)
      ·
        refine ⟨6622184254007350174201643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17659158010686267131204381 6622184254007350174201643)
        ·
          refine ⟨9933276381011025261302465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6622184254007350174201643 9933276381011025261302465)
          ·
            refine ⟨7449957285758268945976849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9933276381011025261302465 7449957285758268945976849)
            ·
              refine ⟨5587467964318701709482637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7449957285758268945976849 5587467964318701709482637)
              ·
                refine ⟨2095300486619513141055989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5587467964318701709482637 2095300486619513141055989)
                ·
                  refine ⟨196434420620579356973999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2095300486619513141055989 196434420620579356973999)
                  ·
                    rfl

theorem cell21_860748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_860748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860748 prefixEnd_860748 := by exact prefixLift 860748
  have htrace : WordTrace (prefixWord ++ tailWord_860748) baseStart_860748 baseEnd_860748 := by
    simpa [prefixWord, tailWord_860748, baseEnd_860748] using wordTrace_append hprefix tailTrace_860748
  have hstable : (prefixWord ++ tailWord_860748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860748).length < 2 ^ (prefixWord ++ tailWord_860748).sum := by decide
  have hdescent : baseEnd_860748 < baseStart_860748 := by decide
  rcases family_descends (prefixWord ++ tailWord_860748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860762 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_860762 : Nat := 118140960795 + 860762 * 2 ^ 59
def prefixEnd_860762 : Nat := 4983230072969 + 3 ^ 40 * 860762 * 2
def baseEnd_860762 : Nat := 196437615611318443740637

theorem tailTrace_860762 : CollatzResearch.WordTrace tailWord_860762 prefixEnd_860762 196437615611318443740637 := by
  unfold tailWord_860762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7848642326903438822732135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20929712871742503527285693 7848642326903438822732135)
  ·
    refine ⟨11772963490355158234098203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7848642326903438822732135 11772963490355158234098203)
    ·
      refine ⟨17659445235532737351147305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11772963490355158234098203 17659445235532737351147305)
      ·
        refine ⟨13244583926649553013360479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17659445235532737351147305 13244583926649553013360479)
        ·
          refine ⟨19866875889974329520040719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13244583926649553013360479 19866875889974329520040719)
          ·
            refine ⟨29800313834961494280061079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19866875889974329520040719 29800313834961494280061079)
            ·
              refine ⟨44700470752442241420091619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29800313834961494280061079 44700470752442241420091619)
              ·
                refine ⟨67050706128663362130137429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44700470752442241420091619 67050706128663362130137429)
                ·
                  refine ⟨196437615611318443740637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 67050706128663362130137429 196437615611318443740637)
                  ·
                    rfl

theorem cell21_860762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_860762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860762 prefixEnd_860762 := by exact prefixLift 860762
  have htrace : WordTrace (prefixWord ++ tailWord_860762) baseStart_860762 baseEnd_860762 := by
    simpa [prefixWord, tailWord_860762, baseEnd_860762] using wordTrace_append hprefix tailTrace_860762
  have hstable : (prefixWord ++ tailWord_860762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860762).length < 2 ^ (prefixWord ++ tailWord_860762).sum := by decide
  have hdescent : baseEnd_860762 < baseStart_860762 := by decide
  rcases family_descends (prefixWord ++ tailWord_860762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860782 : List Nat := [4, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_860782 : Nat := 118140960795 + 860782 * 2 ^ 59
def prefixEnd_860782 : Nat := 4983230072969 + 3 ^ 40 * 860782 * 2
def baseEnd_860782 : Nat := 196442179883802853407263

theorem tailTrace_860782 : CollatzResearch.WordTrace tailWord_860782 prefixEnd_860782 196442179883802853407263 := by
  unfold tailWord_860782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3924412345942662338332075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20930199178360865804437733 3924412345942662338332075)
  ·
    refine ⟨5886618518913993507498113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3924412345942662338332075 5886618518913993507498113)
    ·
      refine ⟨4414963889185495130623585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5886618518913993507498113 4414963889185495130623585)
      ·
        refine ⟨3311222916889121347967689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4414963889185495130623585 3311222916889121347967689)
        ·
          refine ⟨2483417187666841010975767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3311222916889121347967689 2483417187666841010975767)
          ·
            refine ⟨3725125781500261516463651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2483417187666841010975767 3725125781500261516463651)
            ·
              refine ⟨5587688672250392274695477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3725125781500261516463651 5587688672250392274695477)
              ·
                refine ⟨523845813023474275752701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5587688672250392274695477 523845813023474275752701)
                ·
                  refine ⟨196442179883802853407263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523845813023474275752701 196442179883802853407263)
                  ·
                    rfl

theorem cell21_860782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_860782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860782 prefixEnd_860782 := by exact prefixLift 860782
  have htrace : WordTrace (prefixWord ++ tailWord_860782) baseStart_860782 baseEnd_860782 := by
    simpa [prefixWord, tailWord_860782, baseEnd_860782] using wordTrace_append hprefix tailTrace_860782
  have hstable : (prefixWord ++ tailWord_860782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860782).length < 2 ^ (prefixWord ++ tailWord_860782).sum := by decide
  have hdescent : baseEnd_860782 < baseStart_860782 := by decide
  rcases family_descends (prefixWord ++ tailWord_860782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860793 : List Nat := [1, 2, 1, 3, 3, 3, 8]
def baseStart_860793 : Nat := 118140960795 + 860793 * 2 ^ 59
def prefixEnd_860793 : Nat := 4983230072969 + 3 ^ 40 * 860793 * 2
def baseEnd_860793 : Nat := 21827187803741030969323

theorem tailTrace_860793 : CollatzResearch.WordTrace tailWord_860793 prefixEnd_860793 21827187803741030969323 := by
  unfold tailWord_860793
  simp only [CollatzResearch.WordTrace]
  refine ⟨31395699970501447585307033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20930466647000965056871355 31395699970501447585307033)
  ·
    refine ⟨23546774977876085688980275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31395699970501447585307033 23546774977876085688980275)
    ·
      refine ⟨35320162466814128533470413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23546774977876085688980275 35320162466814128533470413)
      ·
        refine ⟨13245060925055298200051405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35320162466814128533470413 13245060925055298200051405)
        ·
          refine ⟨4966897846895736825019277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13245060925055298200051405 4966897846895736825019277)
          ·
            refine ⟨1862586692585901309382229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4966897846895736825019277 1862586692585901309382229)
            ·
              refine ⟨21827187803741030969323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1862586692585901309382229 21827187803741030969323)
              ·
                rfl

theorem cell21_860793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 8].length) (baseStart_860793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860793 prefixEnd_860793 := by exact prefixLift 860793
  have htrace : WordTrace (prefixWord ++ tailWord_860793) baseStart_860793 baseEnd_860793 := by
    simpa [prefixWord, tailWord_860793, baseEnd_860793] using wordTrace_append hprefix tailTrace_860793
  have hstable : (prefixWord ++ tailWord_860793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860793).length < 2 ^ (prefixWord ++ tailWord_860793).sum := by decide
  have hdescent : baseEnd_860793 < baseStart_860793 := by decide
  rcases family_descends (prefixWord ++ tailWord_860793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860824 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 5]
def baseStart_860824 : Nat := 118140960795 + 860824 * 2 ^ 59
def prefixEnd_860824 : Nat := 4983230072969 + 3 ^ 40 * 860824 * 2
def baseEnd_860824 : Nat := 196451764856020113707177

theorem tailTrace_860824 : CollatzResearch.WordTrace tailWord_860824 prefixEnd_860824 196451764856020113707177 := by
  unfold tailWord_860824
  simp only [CollatzResearch.WordTrace]
  refine ⟨15698415316694569939842763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20931220422259426586457017 15698415316694569939842763)
  ·
    refine ⟨23547622975041854909764145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15698415316694569939842763 23547622975041854909764145)
    ·
      refine ⟨17660717231281391182323109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23547622975041854909764145 17660717231281391182323109)
      ·
        refine ⟨3311384480865260846685583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17660717231281391182323109 3311384480865260846685583)
        ·
          refine ⟨4967076721297891270028375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3311384480865260846685583 4967076721297891270028375)
          ·
            refine ⟨7450615081946836905042563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4967076721297891270028375 7450615081946836905042563)
            ·
              refine ⟨11175922622920255357563845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7450615081946836905042563 11175922622920255357563845)
              ·
                refine ⟨2095485491797547879543221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11175922622920255357563845 2095485491797547879543221)
                ·
                  refine ⟨196451764856020113707177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2095485491797547879543221 196451764856020113707177)
                  ·
                    rfl

theorem cell21_860824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 5].length) (baseStart_860824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860824 prefixEnd_860824 := by exact prefixLift 860824
  have htrace : WordTrace (prefixWord ++ tailWord_860824) baseStart_860824 baseEnd_860824 := by
    simpa [prefixWord, tailWord_860824, baseEnd_860824] using wordTrace_append hprefix tailTrace_860824
  have hstable : (prefixWord ++ tailWord_860824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860824).length < 2 ^ (prefixWord ++ tailWord_860824).sum := by decide
  have hdescent : baseEnd_860824 < baseStart_860824 := by decide
  rcases family_descends (prefixWord ++ tailWord_860824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860858 : List Nat := [3, 1, 1, 1, 2, 3, 5, 2, 3]
def baseStart_860858 : Nat := 118140960795 + 860858 * 2 ^ 59
def prefixEnd_860858 : Nat := 4983230072969 + 3 ^ 40 * 860858 * 2
def baseEnd_860858 : Nat := 196459524119243610140441

theorem tailTrace_860858 : CollatzResearch.WordTrace tailWord_860858 prefixEnd_860858 196459524119243610140441 := by
  unfold tailWord_860858
  simp only [CollatzResearch.WordTrace]
  refine ⟨7849517678816490921605807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20932047143510642457615485 7849517678816490921605807)
  ·
    refine ⟨11774276518224736382408711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7849517678816490921605807 11774276518224736382408711)
    ·
      refine ⟨17661414777337104573613067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11774276518224736382408711 17661414777337104573613067)
      ·
        refine ⟨26492122166005656860419601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17661414777337104573613067 26492122166005656860419601)
        ·
          refine ⟨19869091624504242645314701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26492122166005656860419601 19869091624504242645314701)
          ·
            refine ⟨7450909359189090991993013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19869091624504242645314701 7450909359189090991993013)
            ·
              refine ⟨698522752423977280499345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7450909359189090991993013 698522752423977280499345)
              ·
                refine ⟨523892064317982960374509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 698522752423977280499345 523892064317982960374509)
                ·
                  refine ⟨196459524119243610140441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 523892064317982960374509 196459524119243610140441)
                  ·
                    rfl

theorem cell21_860858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 3].length) (baseStart_860858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860858 prefixEnd_860858 := by exact prefixLift 860858
  have htrace : WordTrace (prefixWord ++ tailWord_860858) baseStart_860858 baseEnd_860858 := by
    simpa [prefixWord, tailWord_860858, baseEnd_860858] using wordTrace_append hprefix tailTrace_860858
  have hstable : (prefixWord ++ tailWord_860858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860858).length < 2 ^ (prefixWord ++ tailWord_860858).sum := by decide
  have hdescent : baseEnd_860858 < baseStart_860858 := by decide
  rcases family_descends (prefixWord ++ tailWord_860858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860872 : List Nat := [2, 1, 3, 1, 2, 3, 4, 1, 4]
def baseStart_860872 : Nat := 118140960795 + 860872 * 2 ^ 59
def prefixEnd_860872 : Nat := 4983230072969 + 3 ^ 40 * 860872 * 2
def baseEnd_860872 : Nat := 196462719109982696907079

theorem tailTrace_860872 : CollatzResearch.WordTrace tailWord_860872 prefixEnd_860872 196462719109982696907079 := by
  unfold tailWord_860872
  simp only [CollatzResearch.WordTrace]
  refine ⟨15699290668607622038716435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20932387558143496051621913 15699290668607622038716435)
  ·
    refine ⟨23548936002911433058074653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15699290668607622038716435 23548936002911433058074653)
    ·
      refine ⟨8830851001091787396777995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23548936002911433058074653 8830851001091787396777995)
      ·
        refine ⟨13246276501637681095166993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8830851001091787396777995 13246276501637681095166993)
        ·
          refine ⟨9934707376228260821375245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13246276501637681095166993 9934707376228260821375245)
          ·
            refine ⟨3725515266085597808015717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9934707376228260821375245 3725515266085597808015717)
            ·
              refine ⟨698534112391049589002947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3725515266085597808015717 698534112391049589002947)
              ·
                refine ⟨1047801168586574383504421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698534112391049589002947 1047801168586574383504421)
                ·
                  refine ⟨196462719109982696907079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1047801168586574383504421 196462719109982696907079)
                  ·
                    rfl

theorem cell21_860872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_860872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860872 prefixEnd_860872 := by exact prefixLift 860872
  have htrace : WordTrace (prefixWord ++ tailWord_860872) baseStart_860872 baseEnd_860872 := by
    simpa [prefixWord, tailWord_860872, baseEnd_860872] using wordTrace_append hprefix tailTrace_860872
  have hstable : (prefixWord ++ tailWord_860872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860872).length < 2 ^ (prefixWord ++ tailWord_860872).sum := by decide
  have hdescent : baseEnd_860872 < baseStart_860872 := by decide
  rcases family_descends (prefixWord ++ tailWord_860872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_860982 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_860982 : Nat := 118140960795 + 860982 * 2 ^ 59
def prefixEnd_860982 : Nat := 4983230072969 + 3 ^ 40 * 860982 * 2
def baseEnd_860982 : Nat := 196487822608646950073521

theorem tailTrace_860982 : CollatzResearch.WordTrace tailWord_860982 prefixEnd_860982 196487822608646950073521 := by
  unfold tailWord_860982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1962662085426045803996075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20935062244544488575958133 1962662085426045803996075)
  ·
    refine ⟨2943993128139068705994113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1962662085426045803996075 2943993128139068705994113)
    ·
      refine ⟨2207994846104301529495585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2943993128139068705994113 2207994846104301529495585)
      ·
        refine ⟨1655996134578226147121689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2207994846104301529495585 1655996134578226147121689)
        ·
          refine ⟨1241997100933669610341267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1655996134578226147121689 1241997100933669610341267)
          ·
            refine ⟨1862995651400504415511901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1241997100933669610341267 1862995651400504415511901)
            ·
              refine ⟨698623369275189155816963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1862995651400504415511901 698623369275189155816963)
              ·
                refine ⟨1047935053912783733725445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 698623369275189155816963 1047935053912783733725445)
                ·
                  refine ⟨196487822608646950073521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1047935053912783733725445 196487822608646950073521)
                  ·
                    rfl

theorem cell21_860982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_860982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_860982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_860982 prefixEnd_860982 := by exact prefixLift 860982
  have htrace : WordTrace (prefixWord ++ tailWord_860982) baseStart_860982 baseEnd_860982 := by
    simpa [prefixWord, tailWord_860982, baseEnd_860982] using wordTrace_append hprefix tailTrace_860982
  have hstable : (prefixWord ++ tailWord_860982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_860982).length < 2 ^ (prefixWord ++ tailWord_860982).sum := by decide
  have hdescent : baseEnd_860982 < baseStart_860982 := by decide
  rcases family_descends (prefixWord ++ tailWord_860982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861080 : List Nat := [2, 1, 2, 16]
def baseStart_861080 : Nat := 118140960795 + 861080 * 2 ^ 59
def prefixEnd_861080 : Nat := 4983230072969 + 3 ^ 40 * 861080 * 2
def baseEnd_861080 : Nat := 808683899357286244609

theorem tailTrace_861080 : CollatzResearch.WordTrace tailWord_861080 prefixEnd_861080 808683899357286244609 := by
  unfold tailWord_861080
  simp only [CollatzResearch.WordTrace]
  refine ⟨15703083860230847800502347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20937445146974463734003129 15703083860230847800502347)
  ·
    refine ⟨23554625790346271700753521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15703083860230847800502347 23554625790346271700753521)
    ·
      refine ⟨17665969342759703775565141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23554625790346271700753521 17665969342759703775565141)
      ·
        refine ⟨808683899357286244609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 17665969342759703775565141 808683899357286244609)
        ·
          rfl

theorem cell21_861080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 16].length) (baseStart_861080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861080 prefixEnd_861080 := by exact prefixLift 861080
  have htrace : WordTrace (prefixWord ++ tailWord_861080) baseStart_861080 baseEnd_861080 := by
    simpa [prefixWord, tailWord_861080, baseEnd_861080] using wordTrace_append hprefix tailTrace_861080
  have hstable : (prefixWord ++ tailWord_861080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861080).length < 2 ^ (prefixWord ++ tailWord_861080).sum := by decide
  have hdescent : baseEnd_861080 < baseStart_861080 := by decide
  rcases family_descends (prefixWord ++ tailWord_861080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861111 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 7]
def baseStart_861111 : Nat := 118140960795 + 861111 * 2 ^ 59
def prefixEnd_861111 : Nat := 4983230072969 + 3 ^ 40 * 861111 * 2
def baseEnd_861111 : Nat := 196517262166171392423257

theorem tailTrace_861111 : CollatzResearch.WordTrace tailWord_861111 prefixEnd_861111 196517262166171392423257 := by
  unfold tailWord_861111
  simp only [CollatzResearch.WordTrace]
  refine ⟨31407298383349387895383187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20938198922232925263588791 31407298383349387895383187)
  ·
    refine ⟨47110947575024081843074781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31407298383349387895383187 47110947575024081843074781)
    ·
      refine ⟨17666605340634030691153043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47110947575024081843074781 17666605340634030691153043)
      ·
        refine ⟨26499908010951046036729565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17666605340634030691153043 26499908010951046036729565)
        ·
          refine ⟨9937465504106642263773587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26499908010951046036729565 9937465504106642263773587)
          ·
            refine ⟨14906198256159963395660381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9937465504106642263773587 14906198256159963395660381)
            ·
              refine ⟨5589824346059986273372643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14906198256159963395660381 5589824346059986273372643)
              ·
                refine ⟨8384736519089979410058965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5589824346059986273372643 8384736519089979410058965)
                ·
                  refine ⟨196517262166171392423257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8384736519089979410058965 196517262166171392423257)
                  ·
                    rfl

theorem cell21_861111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 7].length) (baseStart_861111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861111 prefixEnd_861111 := by exact prefixLift 861111
  have htrace : WordTrace (prefixWord ++ tailWord_861111) baseStart_861111 baseEnd_861111 := by
    simpa [prefixWord, tailWord_861111, baseEnd_861111] using wordTrace_append hprefix tailTrace_861111
  have hstable : (prefixWord ++ tailWord_861111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861111).length < 2 ^ (prefixWord ++ tailWord_861111).sum := by decide
  have hdescent : baseEnd_861111 < baseStart_861111 := by decide
  rcases family_descends (prefixWord ++ tailWord_861111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861145 : List Nat := [1, 2, 1, 2, 5, 1, 2, 4, 3]
def baseStart_861145 : Nat := 118140960795 + 861145 * 2 ^ 59
def prefixEnd_861145 : Nat := 4983230072969 + 3 ^ 40 * 861145 * 2
def baseEnd_861145 : Nat := 196525021429394888856521

theorem tailTrace_861145 : CollatzResearch.WordTrace tailWord_861145 prefixEnd_861145 196525021429394888856521 := by
  unfold tailWord_861145
  simp only [CollatzResearch.WordTrace]
  refine ⟨31408538465226211702120889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20939025643484141134747259 31408538465226211702120889)
  ·
    refine ⟨23556403848919658776590667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31408538465226211702120889 23556403848919658776590667)
    ·
      refine ⟨35334605773379488164886001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23556403848919658776590667 35334605773379488164886001)
      ·
        refine ⟨26500954330034616123664501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35334605773379488164886001 26500954330034616123664501)
        ·
          refine ⟨2484464468440745261593547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26500954330034616123664501 2484464468440745261593547)
          ·
            refine ⟨3726696702661117892390321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2484464468440745261593547 3726696702661117892390321)
            ·
              refine ⟨2795022526995838419292741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3726696702661117892390321 2795022526995838419292741)
              ·
                refine ⟨524066723811719703617389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2795022526995838419292741 524066723811719703617389)
                ·
                  refine ⟨196525021429394888856521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524066723811719703617389 196525021429394888856521)
                  ·
                    rfl

theorem cell21_861145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 3].length) (baseStart_861145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861145 prefixEnd_861145 := by exact prefixLift 861145
  have htrace : WordTrace (prefixWord ++ tailWord_861145) baseStart_861145 baseEnd_861145 := by
    simpa [prefixWord, tailWord_861145, baseEnd_861145] using wordTrace_append hprefix tailTrace_861145
  have hstable : (prefixWord ++ tailWord_861145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861145).length < 2 ^ (prefixWord ++ tailWord_861145).sum := by decide
  have hdescent : baseEnd_861145 < baseStart_861145 := by decide
  rcases family_descends (prefixWord ++ tailWord_861145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861232 : List Nat := [2, 1, 1, 1, 2, 4, 1, 9]
def baseStart_861232 : Nat := 118140960795 + 861232 * 2 ^ 59
def prefixEnd_861232 : Nat := 4983230072969 + 3 ^ 40 * 861232 * 2
def baseEnd_861232 : Nat := 65514958671567356968781

theorem tailTrace_861232 : CollatzResearch.WordTrace tailWord_861232 prefixEnd_861232 65514958671567356968781 := by
  unfold tailWord_861232
  simp only [CollatzResearch.WordTrace]
  refine ⟨15705855807955512780268975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20941141077274017040358633 15705855807955512780268975)
  ·
    refine ⟨23558783711933269170403463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15705855807955512780268975 23558783711933269170403463)
    ·
      refine ⟨35338175567899903755605195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23558783711933269170403463 35338175567899903755605195)
      ·
        refine ⟨53007263351849855633407793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35338175567899903755605195 53007263351849855633407793)
        ·
          refine ⟨39755447513887391725055845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53007263351849855633407793 39755447513887391725055845)
          ·
            refine ⟨7454146408853885948447971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39755447513887391725055845 7454146408853885948447971)
            ·
              refine ⟨11181219613280828922671957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7454146408853885948447971 11181219613280828922671957)
              ·
                refine ⟨65514958671567356968781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11181219613280828922671957 65514958671567356968781)
                ·
                  rfl

theorem cell21_861232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_861232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861232 prefixEnd_861232 := by exact prefixLift 861232
  have htrace : WordTrace (prefixWord ++ tailWord_861232) baseStart_861232 baseEnd_861232 := by
    simpa [prefixWord, tailWord_861232, baseEnd_861232] using wordTrace_append hprefix tailTrace_861232
  have hstable : (prefixWord ++ tailWord_861232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861232).length < 2 ^ (prefixWord ++ tailWord_861232).sum := by decide
  have hdescent : baseEnd_861232 < baseStart_861232 := by decide
  rcases family_descends (prefixWord ++ tailWord_861232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861249 : List Nat := [1, 2, 5, 1, 3, 9]
def baseStart_861249 : Nat := 118140960795 + 861249 * 2 ^ 59
def prefixEnd_861249 : Nat := 4983230072969 + 3 ^ 40 * 861249 * 2
def baseEnd_861249 : Nat := 7279583542456067374925

theorem tailTrace_861249 : CollatzResearch.WordTrace tailWord_861249 prefixEnd_861249 7279583542456067374925 := by
  unfold tailWord_861249
  simp only [CollatzResearch.WordTrace]
  refine ⟨31412331656849437463906801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20941554437899624975937867 31412331656849437463906801)
  ·
    refine ⟨23559248742637078097930101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31412331656849437463906801 23559248742637078097930101)
    ·
      refine ⟨2208679569622226071680947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23559248742637078097930101 2208679569622226071680947)
      ·
        refine ⟨3313019354433339107521421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2208679569622226071680947 3313019354433339107521421)
        ·
          refine ⟨1242382257912502165320533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3313019354433339107521421 1242382257912502165320533)
          ·
            refine ⟨7279583542456067374925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1242382257912502165320533 7279583542456067374925)
            ·
              rfl

theorem cell21_861249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 9].length) (baseStart_861249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861249 prefixEnd_861249 := by exact prefixLift 861249
  have htrace : WordTrace (prefixWord ++ tailWord_861249) baseStart_861249 baseEnd_861249 := by
    simpa [prefixWord, tailWord_861249, baseEnd_861249] using wordTrace_append hprefix tailTrace_861249
  have hstable : (prefixWord ++ tailWord_861249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861249).length < 2 ^ (prefixWord ++ tailWord_861249).sum := by decide
  have hdescent : baseEnd_861249 < baseStart_861249 := by decide
  rcases family_descends (prefixWord ++ tailWord_861249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861266 : List Nat := [3, 2, 2, 1, 3, 3, 1, 6]
def baseStart_861266 : Nat := 118140960795 + 861266 * 2 ^ 59
def prefixEnd_861266 : Nat := 4983230072969 + 3 ^ 40 * 861266 * 2
def baseEnd_861266 : Nat := 65517545092641855779869

theorem tailTrace_861266 : CollatzResearch.WordTrace tailWord_861266 prefixEnd_861266 65517545092641855779869 := by
  unfold tailWord_861266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853237924446962341818913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20941967798525232911517101 7853237924446962341818913)
  ·
    refine ⟨5889928443335221756364185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7853237924446962341818913 5889928443335221756364185)
    ·
      refine ⟨4417446332501416317273139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5889928443335221756364185 4417446332501416317273139)
      ·
        refine ⟨6626169498752124475909709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4417446332501416317273139 6626169498752124475909709)
        ·
          refine ⟨2484813562032046678466141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6626169498752124475909709 2484813562032046678466141)
          ·
            refine ⟨931805085762017504424803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2484813562032046678466141 931805085762017504424803)
            ·
              refine ⟨1397707628643026256637205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 931805085762017504424803 1397707628643026256637205)
              ·
                refine ⟨65517545092641855779869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1397707628643026256637205 65517545092641855779869)
                ·
                  rfl

theorem cell21_861266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_861266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861266 prefixEnd_861266 := by exact prefixLift 861266
  have htrace : WordTrace (prefixWord ++ tailWord_861266) baseStart_861266 baseEnd_861266 := by
    simpa [prefixWord, tailWord_861266, baseEnd_861266] using wordTrace_append hprefix tailTrace_861266
  have hstable : (prefixWord ++ tailWord_861266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861266).length < 2 ^ (prefixWord ++ tailWord_861266).sum := by decide
  have hdescent : baseEnd_861266 < baseStart_861266 := by decide
  rcases family_descends (prefixWord ++ tailWord_861266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861308 : List Nat := [2, 2, 2, 1, 1, 3, 10]
def baseStart_861308 : Nat := 118140960795 + 861308 * 2 ^ 59
def prefixEnd_861308 : Nat := 4983230072969 + 3 ^ 40 * 861308 * 2
def baseEnd_861308 : Nat := 21840246694460314182169

theorem tailTrace_861308 : CollatzResearch.WordTrace tailWord_861308 prefixEnd_861308 21840246694460314182169 := by
  unfold tailWord_861308
  simp only [CollatzResearch.WordTrace]
  refine ⟨15707241781817845270152289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20942989042423793693536385 15707241781817845270152289)
  ·
    refine ⟨11780431336363383952614217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15707241781817845270152289 11780431336363383952614217)
    ·
      refine ⟨8835323502272537964460663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11780431336363383952614217 8835323502272537964460663)
      ·
        refine ⟨13252985253408806946690995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8835323502272537964460663 13252985253408806946690995)
        ·
          refine ⟨19879477880113210420036493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13252985253408806946690995 19879477880113210420036493)
          ·
            refine ⟨7454804205042453907513685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19879477880113210420036493 7454804205042453907513685)
            ·
              refine ⟨21840246694460314182169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7454804205042453907513685 21840246694460314182169)
              ·
                rfl

theorem cell21_861308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 10].length) (baseStart_861308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861308 prefixEnd_861308 := by exact prefixLift 861308
  have htrace : WordTrace (prefixWord ++ tailWord_861308) baseStart_861308 baseEnd_861308 := by
    simpa [prefixWord, tailWord_861308, baseEnd_861308] using wordTrace_append hprefix tailTrace_861308
  have hstable : (prefixWord ++ tailWord_861308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861308).length < 2 ^ (prefixWord ++ tailWord_861308).sum := by decide
  have hdescent : baseEnd_861308 < baseStart_861308 := by decide
  rcases family_descends (prefixWord ++ tailWord_861308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861342 : List Nat := [4, 3, 1, 1, 2, 2, 1, 7]
def baseStart_861342 : Nat := 118140960795 + 861342 * 2 ^ 59
def prefixEnd_861342 : Nat := 4983230072969 + 3 ^ 40 * 861342 * 2
def baseEnd_861342 : Nat := 65523326504455441357595

theorem tailTrace_861342 : CollatzResearch.WordTrace tailWord_861342 prefixEnd_861342 65523326504455441357595 := by
  unfold tailWord_861342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3926965455689064293380285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20943815763675009564694853 3926965455689064293380285)
  ·
    refine ⟨1472612045883399110017607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3926965455689064293380285 1472612045883399110017607)
    ·
      refine ⟨2208918068825098665026411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472612045883399110017607 2208918068825098665026411)
      ·
        refine ⟨3313377103237647997539617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2208918068825098665026411 3313377103237647997539617)
        ·
          refine ⟨2485032827428235998154713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3313377103237647997539617 2485032827428235998154713)
          ·
            refine ⟨1863774620571176998616035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2485032827428235998154713 1863774620571176998616035)
            ·
              refine ⟨2795661930856765497924053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1863774620571176998616035 2795661930856765497924053)
              ·
                refine ⟨65523326504455441357595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2795661930856765497924053 65523326504455441357595)
                ·
                  rfl

theorem cell21_861342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_861342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861342 prefixEnd_861342 := by exact prefixLift 861342
  have htrace : WordTrace (prefixWord ++ tailWord_861342) baseStart_861342 baseEnd_861342 := by
    simpa [prefixWord, tailWord_861342, baseEnd_861342] using wordTrace_append hprefix tailTrace_861342
  have hstable : (prefixWord ++ tailWord_861342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861342).length < 2 ^ (prefixWord ++ tailWord_861342).sum := by decide
  have hdescent : baseEnd_861342 < baseStart_861342 := by decide
  rcases family_descends (prefixWord ++ tailWord_861342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861356 : List Nat := [2, 2, 1, 1, 1, 1, 1, 9, 3]
def baseStart_861356 : Nat := 118140960795 + 861356 * 2 ^ 59
def prefixEnd_861356 : Nat := 4983230072969 + 3 ^ 40 * 861356 * 2
def baseEnd_861356 : Nat := 196573174504105410839423

theorem tailTrace_861356 : CollatzResearch.WordTrace tailWord_861356 prefixEnd_861356 196573174504105410839423 := by
  unfold tailWord_861356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15708117133730897369025961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20944156178307863158701281 15708117133730897369025961)
  ·
    refine ⟨11781087850298173026769471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15708117133730897369025961 11781087850298173026769471)
    ·
      refine ⟨17671631775447259540154207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11781087850298173026769471 17671631775447259540154207)
      ·
        refine ⟨26507447663170889310231311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17671631775447259540154207 26507447663170889310231311)
        ·
          refine ⟨39761171494756333965346967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26507447663170889310231311 39761171494756333965346967)
          ·
            refine ⟨59641757242134500948020451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39761171494756333965346967 59641757242134500948020451)
            ·
              refine ⟨89462635863201751422030677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59641757242134500948020451 89462635863201751422030677)
              ·
                refine ⟨524195132010947762238461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 89462635863201751422030677 524195132010947762238461)
                ·
                  refine ⟨196573174504105410839423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524195132010947762238461 196573174504105410839423)
                  ·
                    rfl

theorem cell21_861356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_861356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861356 prefixEnd_861356 := by exact prefixLift 861356
  have htrace : WordTrace (prefixWord ++ tailWord_861356) baseStart_861356 baseEnd_861356 := by
    simpa [prefixWord, tailWord_861356, baseEnd_861356] using wordTrace_append hprefix tailTrace_861356
  have hstable : (prefixWord ++ tailWord_861356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861356).length < 2 ^ (prefixWord ++ tailWord_861356).sum := by decide
  have hdescent : baseEnd_861356 < baseStart_861356 := by decide
  rcases family_descends (prefixWord ++ tailWord_861356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861370 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 4]
def baseStart_861370 : Nat := 118140960795 + 861370 * 2 ^ 59
def prefixEnd_861370 : Nat := 4983230072969 + 3 ^ 40 * 861370 * 2
def baseEnd_861370 : Nat := 196576369494844497606061

theorem tailTrace_861370 : CollatzResearch.WordTrace tailWord_861370 prefixEnd_861370 196576369494844497606061 := by
  unfold tailWord_861370
  simp only [CollatzResearch.WordTrace]
  refine ⟨7854186222352768782265391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20944496592940716752707709 7854186222352768782265391)
  ·
    refine ⟨11781279333529153173398087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7854186222352768782265391 11781279333529153173398087)
    ·
      refine ⟨17671919000293729760097131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11781279333529153173398087 17671919000293729760097131)
      ·
        refine ⟨26507878500440594640145697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17671919000293729760097131 26507878500440594640145697)
        ·
          refine ⟨19880908875330445980109273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26507878500440594640145697 19880908875330445980109273)
          ·
            refine ⟨14910681656497834485081955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19880908875330445980109273 14910681656497834485081955)
            ·
              refine ⟨22366022484746751727622933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14910681656497834485081955 22366022484746751727622933)
              ·
                refine ⟨1048407303972503987232325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22366022484746751727622933 1048407303972503987232325)
                ·
                  refine ⟨196576369494844497606061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1048407303972503987232325 196576369494844497606061)
                  ·
                    rfl

theorem cell21_861370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_861370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861370 prefixEnd_861370 := by exact prefixLift 861370
  have htrace : WordTrace (prefixWord ++ tailWord_861370) baseStart_861370 baseEnd_861370 := by
    simpa [prefixWord, tailWord_861370, baseEnd_861370] using wordTrace_append hprefix tailTrace_861370
  have hstable : (prefixWord ++ tailWord_861370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861370).length < 2 ^ (prefixWord ++ tailWord_861370).sum := by decide
  have hdescent : baseEnd_861370 < baseStart_861370 := by decide
  rcases family_descends (prefixWord ++ tailWord_861370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861384 : List Nat := [2, 1, 3, 1, 2, 1, 3, 8]
def baseStart_861384 : Nat := 118140960795 + 861384 * 2 ^ 59
def prefixEnd_861384 : Nat := 4983230072969 + 3 ^ 40 * 861384 * 2
def baseEnd_861384 : Nat := 65526521495194528124233

theorem tailTrace_861384 : CollatzResearch.WordTrace tailWord_861384 prefixEnd_861384 65526521495194528124233 := by
  unfold tailWord_861384
  simp only [CollatzResearch.WordTrace]
  refine ⟨15708627755680177760035603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20944837007573570346714137 15708627755680177760035603)
  ·
    refine ⟨23562941633520266640053405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15708627755680177760035603 23562941633520266640053405)
    ·
      refine ⟨8836103112570099990020027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23562941633520266640053405 8836103112570099990020027)
      ·
        refine ⟨13254154668855149985030041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8836103112570099990020027 13254154668855149985030041)
        ·
          refine ⟨9940616001641362488772531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13254154668855149985030041 9940616001641362488772531)
          ·
            refine ⟨14910924002462043733158797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9940616001641362488772531 14910924002462043733158797)
            ·
              refine ⟨5591596500923266399934549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14910924002462043733158797 5591596500923266399934549)
              ·
                refine ⟨65526521495194528124233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5591596500923266399934549 65526521495194528124233)
                ·
                  rfl

theorem cell21_861384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_861384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861384 prefixEnd_861384 := by exact prefixLift 861384
  have htrace : WordTrace (prefixWord ++ tailWord_861384) baseStart_861384 baseEnd_861384 := by
    simpa [prefixWord, tailWord_861384, baseEnd_861384] using wordTrace_append hprefix tailTrace_861384
  have hstable : (prefixWord ++ tailWord_861384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861384).length < 2 ^ (prefixWord ++ tailWord_861384).sum := by decide
  have hdescent : baseEnd_861384 < baseStart_861384 := by decide
  rcases family_descends (prefixWord ++ tailWord_861384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861480 : List Nat := [2, 1, 5, 1, 2, 3, 1, 2, 4]
def baseStart_861480 : Nat := 118140960795 + 861480 * 2 ^ 59
def prefixEnd_861480 : Nat := 4983230072969 + 3 ^ 40 * 861480 * 2
def baseEnd_861480 : Nat := 196601472993508750772503

theorem tailTrace_861480 : CollatzResearch.WordTrace tailWord_861480 prefixEnd_861480 196601472993508750772503 := by
  unfold tailWord_861480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15710378459506281957782947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20947171279341709277043929 15710378459506281957782947)
  ·
    refine ⟨23565567689259422936674421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15710378459506281957782947 23565567689259422936674421)
    ·
      refine ⟨2209271970868070900313227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23565567689259422936674421 2209271970868070900313227)
      ·
        refine ⟨3313907956302106350469841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209271970868070900313227 3313907956302106350469841)
        ·
          refine ⟨2485430967226579762852381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3313907956302106350469841 2485430967226579762852381)
          ·
            refine ⟨932036612709967411069643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2485430967226579762852381 932036612709967411069643)
            ·
              refine ⟨1398054919064951116604465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932036612709967411069643 1398054919064951116604465)
              ·
                refine ⟨1048541189298713337453349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398054919064951116604465 1048541189298713337453349)
                ·
                  refine ⟨196601472993508750772503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1048541189298713337453349 196601472993508750772503)
                  ·
                    rfl

theorem cell21_861480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_861480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861480 prefixEnd_861480 := by exact prefixLift 861480
  have htrace : WordTrace (prefixWord ++ tailWord_861480) baseStart_861480 baseEnd_861480 := by
    simpa [prefixWord, tailWord_861480, baseEnd_861480] using wordTrace_append hprefix tailTrace_861480
  have hstable : (prefixWord ++ tailWord_861480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861480).length < 2 ^ (prefixWord ++ tailWord_861480).sum := by decide
  have hdescent : baseEnd_861480 < baseStart_861480 := by decide
  rcases family_descends (prefixWord ++ tailWord_861480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861491 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 5]
def baseStart_861491 : Nat := 118140960795 + 861491 * 2 ^ 59
def prefixEnd_861491 : Nat := 4983230072969 + 3 ^ 40 * 861491 * 2
def baseEnd_861491 : Nat := 196603983343375176089147

theorem tailTrace_861491 : CollatzResearch.WordTrace tailWord_861491 prefixEnd_861491 196603983343375176089147 := by
  unfold tailWord_861491
  simp only [CollatzResearch.WordTrace]
  refine ⟨31421158121972712794216327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20947438747981808529477551 31421158121972712794216327)
  ·
    refine ⟨47131737182959069191324491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31421158121972712794216327 47131737182959069191324491)
    ·
      refine ⟨70697605774438603786986737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47131737182959069191324491 70697605774438603786986737)
      ·
        refine ⟨53023204330828952840240053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70697605774438603786986737 53023204330828952840240053)
        ·
          refine ⟨4970925406015214328772505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53023204330828952840240053 4970925406015214328772505)
          ·
            refine ⟨3728194054511410746579379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4970925406015214328772505 3728194054511410746579379)
            ·
              refine ⟨5592291081767116119869069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3728194054511410746579379 5592291081767116119869069)
              ·
                refine ⟨2097109155662668544950901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5592291081767116119869069 2097109155662668544950901)
                ·
                  refine ⟨196603983343375176089147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2097109155662668544950901 196603983343375176089147)
                  ·
                    rfl

theorem cell21_861491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 5].length) (baseStart_861491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861491 prefixEnd_861491 := by exact prefixLift 861491
  have htrace : WordTrace (prefixWord ++ tailWord_861491) baseStart_861491 baseEnd_861491 := by
    simpa [prefixWord, tailWord_861491, baseEnd_861491] using wordTrace_append hprefix tailTrace_861491
  have hstable : (prefixWord ++ tailWord_861491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861491).length < 2 ^ (prefixWord ++ tailWord_861491).sum := by decide
  have hdescent : baseEnd_861491 < baseStart_861491 := by decide
  rcases family_descends (prefixWord ++ tailWord_861491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861525 : List Nat := [1, 3, 2, 2, 3, 1, 3, 3, 3]
def baseStart_861525 : Nat := 118140960795 + 861525 * 2 ^ 59
def prefixEnd_861525 : Nat := 4983230072969 + 3 ^ 40 * 861525 * 2
def baseEnd_861525 : Nat := 196611742606598672522411

theorem tailTrace_861525 : CollatzResearch.WordTrace tailWord_861525 prefixEnd_861525 196611742606598672522411 := by
  unfold tailWord_861525
  simp only [CollatzResearch.WordTrace]
  refine ⟨31422398203849536600954029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20948265469233024400636019 31422398203849536600954029)
  ·
    refine ⟨11783399326443576225357761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31422398203849536600954029 11783399326443576225357761)
    ·
      refine ⟨8837549494832682169018321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11783399326443576225357761 8837549494832682169018321)
      ·
        refine ⟨6628162121124511626763741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8837549494832682169018321 6628162121124511626763741)
        ·
          refine ⟨2485560795421691860036403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6628162121124511626763741 2485560795421691860036403)
          ·
            refine ⟨3728341193132537790054605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485560795421691860036403 3728341193132537790054605)
            ·
              refine ⟨1398127947424701671270477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3728341193132537790054605 1398127947424701671270477)
              ·
                refine ⟨524297980284263126726429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1398127947424701671270477 524297980284263126726429)
                ·
                  refine ⟨196611742606598672522411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524297980284263126726429 196611742606598672522411)
                  ·
                    rfl

theorem cell21_861525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_861525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861525 prefixEnd_861525 := by exact prefixLift 861525
  have htrace : WordTrace (prefixWord ++ tailWord_861525) baseStart_861525 baseEnd_861525 := by
    simpa [prefixWord, tailWord_861525, baseEnd_861525] using wordTrace_append hprefix tailTrace_861525
  have hstable : (prefixWord ++ tailWord_861525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861525).length < 2 ^ (prefixWord ++ tailWord_861525).sum := by decide
  have hdescent : baseEnd_861525 < baseStart_861525 := by decide
  rcases family_descends (prefixWord ++ tailWord_861525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861536 : List Nat := [2, 1, 1, 3, 4, 1, 9]
def baseStart_861536 : Nat := 118140960795 + 861536 * 2 ^ 59
def prefixEnd_861536 : Nat := 4983230072969 + 3 ^ 40 * 861536 * 2
def baseEnd_861536 : Nat := 21846028106273899759895

theorem tailTrace_861536 : CollatzResearch.WordTrace tailWord_861536 prefixEnd_861536 21846028106273899759895 := by
  unfold tailWord_861536
  simp only [CollatzResearch.WordTrace]
  refine ⟨15711399703404842739802231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20948532937873123653069641 15711399703404842739802231)
  ·
    refine ⟨23567099555107264109703347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15711399703404842739802231 23567099555107264109703347)
    ·
      refine ⟨35350649332660896164555021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23567099555107264109703347 35350649332660896164555021)
      ·
        refine ⟨13256493499747836061708133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35350649332660896164555021 13256493499747836061708133)
        ·
          refine ⟨2485592531202719261570275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13256493499747836061708133 2485592531202719261570275)
          ·
            refine ⟨3728388796804078892355413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485592531202719261570275 3728388796804078892355413)
            ·
              refine ⟨21846028106273899759895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3728388796804078892355413 21846028106273899759895)
              ·
                rfl

theorem cell21_861536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 9].length) (baseStart_861536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861536 prefixEnd_861536 := by exact prefixLift 861536
  have htrace : WordTrace (prefixWord ++ tailWord_861536) baseStart_861536 baseEnd_861536 := by
    simpa [prefixWord, tailWord_861536, baseEnd_861536] using wordTrace_append hprefix tailTrace_861536
  have hstable : (prefixWord ++ tailWord_861536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861536).length < 2 ^ (prefixWord ++ tailWord_861536).sum := by decide
  have hdescent : baseEnd_861536 < baseStart_861536 := by decide
  rcases family_descends (prefixWord ++ tailWord_861536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861570 : List Nat := [3, 4, 2, 1, 1, 1, 2, 7]
def baseStart_861570 : Nat := 118140960795 + 861570 * 2 ^ 59
def prefixEnd_861570 : Nat := 4983230072969 + 3 ^ 40 * 861570 * 2
def baseEnd_861570 : Nat := 65540670739896198090773

theorem tailTrace_861570 : CollatzResearch.WordTrace tailWord_861570 prefixEnd_861570 65540670739896198090773 := by
  unfold tailWord_861570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7856009872171627321585541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20949359659124339524228109 7856009872171627321585541)
  ·
    refine ⟨1473001851032180122797289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7856009872171627321585541 1473001851032180122797289)
    ·
      refine ⟨1104751388274135092097967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1473001851032180122797289 1104751388274135092097967)
      ·
        refine ⟨1657127082411202638146951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1104751388274135092097967 1657127082411202638146951)
        ·
          refine ⟨2485690623616803957220427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657127082411202638146951 2485690623616803957220427)
          ·
            refine ⟨3728535935425205935830641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2485690623616803957220427 3728535935425205935830641)
            ·
              refine ⟨2796401951568904451872981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3728535935425205935830641 2796401951568904451872981)
              ·
                refine ⟨65540670739896198090773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2796401951568904451872981 65540670739896198090773)
                ·
                  rfl

theorem cell21_861570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_861570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861570 prefixEnd_861570 := by exact prefixLift 861570
  have htrace : WordTrace (prefixWord ++ tailWord_861570) baseStart_861570 baseEnd_861570 := by
    simpa [prefixWord, tailWord_861570, baseEnd_861570] using wordTrace_append hprefix tailTrace_861570
  have hstable : (prefixWord ++ tailWord_861570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861570).length < 2 ^ (prefixWord ++ tailWord_861570).sum := by decide
  have hdescent : baseEnd_861570 < baseStart_861570 := by decide
  rcases family_descends (prefixWord ++ tailWord_861570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861612 : List Nat := [2, 2, 1, 1, 1, 1, 7, 6]
def baseStart_861612 : Nat := 118140960795 + 861612 * 2 ^ 59
def prefixEnd_861612 : Nat := 4983230072969 + 3 ^ 40 * 861612 * 2
def baseEnd_861612 : Nat := 65543865730635284857411

theorem tailTrace_861612 : CollatzResearch.WordTrace tailWord_861612 prefixEnd_861612 65543865730635284857411 := by
  unfold tailWord_861612
  simp only [CollatzResearch.WordTrace]
  refine ⟨15712785677267175229685545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20950380903022900306247393 15712785677267175229685545)
  ·
    refine ⟨11784589257950381422264159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15712785677267175229685545 11784589257950381422264159)
    ·
      refine ⟨17676883886925572133396239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11784589257950381422264159 17676883886925572133396239)
      ·
        refine ⟨26515325830388358200094359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17676883886925572133396239 26515325830388358200094359)
        ·
          refine ⟨39772988745582537300141539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26515325830388358200094359 39772988745582537300141539)
          ·
            refine ⟨59659483118373805950212309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39772988745582537300141539 59659483118373805950212309)
            ·
              refine ⟨1398269135586886076958101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59659483118373805950212309 1398269135586886076958101)
              ·
                refine ⟨65543865730635284857411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1398269135586886076958101 65543865730635284857411)
                ·
                  rfl

theorem cell21_861612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_861612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861612 prefixEnd_861612 := by exact prefixLift 861612
  have htrace : WordTrace (prefixWord ++ tailWord_861612) baseStart_861612 baseEnd_861612 := by
    simpa [prefixWord, tailWord_861612, baseEnd_861612] using wordTrace_append hprefix tailTrace_861612
  have hstable : (prefixWord ++ tailWord_861612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861612).length < 2 ^ (prefixWord ++ tailWord_861612).sum := by decide
  have hdescent : baseEnd_861612 < baseStart_861612 := by decide
  rcases family_descends (prefixWord ++ tailWord_861612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861629 : List Nat := [1, 4, 1, 2, 2, 1, 5, 5]
def baseStart_861629 : Nat := 118140960795 + 861629 * 2 ^ 59
def prefixEnd_861629 : Nat := 4983230072969 + 3 ^ 40 * 861629 * 2
def baseEnd_861629 : Nat := 65545158941172534262955

theorem tailTrace_861629 : CollatzResearch.WordTrace tailWord_861629 prefixEnd_861629 65545158941172534262955 := by
  unfold tailWord_861629
  simp only [CollatzResearch.WordTrace]
  refine ⟨31426191395472762362739941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20950794263648508241826627 31426191395472762362739941)
  ·
    refine ⟨5892410886651142943013739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31426191395472762362739941 5892410886651142943013739)
    ·
      refine ⟨8838616329976714414520609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5892410886651142943013739 8838616329976714414520609)
      ·
        refine ⟨6628962247482535810890457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8838616329976714414520609 6628962247482535810890457)
        ·
          refine ⟨4971721685611901858167843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6628962247482535810890457 4971721685611901858167843)
          ·
            refine ⟨7457582528417852787251765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4971721685611901858167843 7457582528417852787251765)
            ·
              refine ⟨699148362039173698804853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7457582528417852787251765 699148362039173698804853)
              ·
                refine ⟨65545158941172534262955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 699148362039173698804853 65545158941172534262955)
                ·
                  rfl

theorem cell21_861629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 5].length) (baseStart_861629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861629 prefixEnd_861629 := by exact prefixLift 861629
  have htrace : WordTrace (prefixWord ++ tailWord_861629) baseStart_861629 baseEnd_861629 := by
    simpa [prefixWord, tailWord_861629, baseEnd_861629] using wordTrace_append hprefix tailTrace_861629
  have hstable : (prefixWord ++ tailWord_861629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861629).length < 2 ^ (prefixWord ++ tailWord_861629).sum := by decide
  have hdescent : baseEnd_861629 < baseStart_861629 := by decide
  rcases family_descends (prefixWord ++ tailWord_861629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861688 : List Nat := [2, 1, 2, 1, 1, 6, 1, 7]
def baseStart_861688 : Nat := 118140960795 + 861688 * 2 ^ 59
def prefixEnd_861688 : Nat := 4983230072969 + 3 ^ 40 * 861688 * 2
def baseEnd_861688 : Nat := 65549647142448870435137

theorem tailTrace_861688 : CollatzResearch.WordTrace tailWord_861688 prefixEnd_861688 65549647142448870435137 := by
  unfold tailWord_861688
  simp only [CollatzResearch.WordTrace]
  refine ⟨15714171651129507719568859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20952228868172676959425145 15714171651129507719568859)
  ·
    refine ⟨23571257476694261579353289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15714171651129507719568859 23571257476694261579353289)
    ·
      refine ⟨17678443107520696184514967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23571257476694261579353289 17678443107520696184514967)
      ·
        refine ⟨26517664661281044276772451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17678443107520696184514967 26517664661281044276772451)
        ·
          refine ⟨39776496991921566415158677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26517664661281044276772451 39776496991921566415158677)
          ·
            refine ⟨1864523296496323425710563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39776496991921566415158677 1864523296496323425710563)
            ·
              refine ⟨2796784944744485138565845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864523296496323425710563 2796784944744485138565845)
              ·
                refine ⟨65549647142448870435137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2796784944744485138565845 65549647142448870435137)
                ·
                  rfl

theorem cell21_861688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 7].length) (baseStart_861688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861688 prefixEnd_861688 := by exact prefixLift 861688
  have htrace : WordTrace (prefixWord ++ tailWord_861688) baseStart_861688 baseEnd_861688 := by
    simpa [prefixWord, tailWord_861688, baseEnd_861688] using wordTrace_append hprefix tailTrace_861688
  have hstable : (prefixWord ++ tailWord_861688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861688).length < 2 ^ (prefixWord ++ tailWord_861688).sum := by decide
  have hdescent : baseEnd_861688 < baseStart_861688 := by decide
  rcases family_descends (prefixWord ++ tailWord_861688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861767 : List Nat := [1, 1, 4, 1, 5, 1, 2, 2, 4]
def baseStart_861767 : Nat := 118140960795 + 861767 * 2 ^ 59
def prefixEnd_861767 : Nat := 4983230072969 + 3 ^ 40 * 861767 * 2
def baseEnd_861767 : Nat := 196666970303660029488583

theorem tailTrace_861767 : CollatzResearch.WordTrace tailWord_861767 prefixEnd_861767 196666970303660029488583 := by
  unfold tailWord_861767
  simp only [CollatzResearch.WordTrace]
  refine ⟨31431224668972811931263555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20954149779315207954175703 31431224668972811931263555)
  ·
    refine ⟨47146837003459217896895333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31431224668972811931263555 47146837003459217896895333)
    ·
      refine ⟨8840031938148603355667875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47146837003459217896895333 8840031938148603355667875)
      ·
        refine ⟨13260047907222905033501813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8840031938148603355667875 13260047907222905033501813)
        ·
          refine ⟨1243129491302147346890795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13260047907222905033501813 1243129491302147346890795)
          ·
            refine ⟨1864694236953221020336193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1243129491302147346890795 1864694236953221020336193)
            ·
              refine ⟨1398520677714915765252145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1864694236953221020336193 1398520677714915765252145)
              ·
                refine ⟨1048890508286186823939109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1398520677714915765252145 1048890508286186823939109)
                ·
                  refine ⟨196666970303660029488583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1048890508286186823939109 196666970303660029488583)
                  ·
                    rfl

theorem cell21_861767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 2, 4].length) (baseStart_861767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861767 prefixEnd_861767 := by exact prefixLift 861767
  have htrace : WordTrace (prefixWord ++ tailWord_861767) baseStart_861767 baseEnd_861767 := by
    simpa [prefixWord, tailWord_861767, baseEnd_861767] using wordTrace_append hprefix tailTrace_861767
  have hstable : (prefixWord ++ tailWord_861767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861767).length < 2 ^ (prefixWord ++ tailWord_861767).sum := by decide
  have hdescent : baseEnd_861767 < baseStart_861767 := by decide
  rcases family_descends (prefixWord ++ tailWord_861767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861795 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 5]
def baseStart_861795 : Nat := 118140960795 + 861795 * 2 ^ 59
def prefixEnd_861795 : Nat := 4983230072969 + 3 ^ 40 * 861795 * 2
def baseEnd_861795 : Nat := 196673360285138203021859

theorem tailTrace_861795 : CollatzResearch.WordTrace tailWord_861795 prefixEnd_861795 196673360285138203021859 := by
  unfold tailWord_861795
  simp only [CollatzResearch.WordTrace]
  refine ⟨31432245912871372713282839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20954830608580915142188559 31432245912871372713282839)
  ·
    refine ⟨47148368869307059069924259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31432245912871372713282839 47148368869307059069924259)
    ·
      refine ⟨70722553303960588604886389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47148368869307059069924259 70722553303960588604886389)
      ·
        refine ⟨6630239372246305181708099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70722553303960588604886389 6630239372246305181708099)
        ·
          refine ⟨9945359058369457772562149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6630239372246305181708099 9945359058369457772562149)
          ·
            refine ⟨1864754823444273332355403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9945359058369457772562149 1864754823444273332355403)
            ·
              refine ⟨2797132235166409998533105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1864754823444273332355403 2797132235166409998533105)
              ·
                refine ⟨2097849176374807498899829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2797132235166409998533105 2097849176374807498899829)
                ·
                  refine ⟨196673360285138203021859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2097849176374807498899829 196673360285138203021859)
                  ·
                    rfl

theorem cell21_861795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 5].length) (baseStart_861795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861795 prefixEnd_861795 := by exact prefixLift 861795
  have htrace : WordTrace (prefixWord ++ tailWord_861795) baseStart_861795 baseEnd_861795 := by
    simpa [prefixWord, tailWord_861795, baseEnd_861795] using wordTrace_append hprefix tailTrace_861795
  have hstable : (prefixWord ++ tailWord_861795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861795).length < 2 ^ (prefixWord ++ tailWord_861795).sum := by decide
  have hdescent : baseEnd_861795 < baseStart_861795 := by decide
  rcases family_descends (prefixWord ++ tailWord_861795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861857 : List Nat := [1, 2, 3, 3, 2, 1, 4, 5]
def baseStart_861857 : Nat := 118140960795 + 861857 * 2 ^ 59
def prefixEnd_861857 : Nat := 4983230072969 + 3 ^ 40 * 861857 * 2
def baseEnd_861857 : Nat := 65562503176613290996133

theorem tailTrace_861857 : CollatzResearch.WordTrace tailWord_861857 prefixEnd_861857 65562503176613290996133 := by
  unfold tailWord_861857
  simp only [CollatzResearch.WordTrace]
  refine ⟨31434507238646757302039825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20956338159097838201359883 31434507238646757302039825)
  ·
    refine ⟨23575880428985067976529869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31434507238646757302039825 23575880428985067976529869)
    ·
      refine ⟨8840955160869400491198701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23575880428985067976529869 8840955160869400491198701)
      ·
        refine ⟨3315358185326025184199513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8840955160869400491198701 3315358185326025184199513)
        ·
          refine ⟨2486518638994518888149635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3315358185326025184199513 2486518638994518888149635)
          ·
            refine ⟨3729777958491778332224453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2486518638994518888149635 3729777958491778332224453)
            ·
              refine ⟨699333367217208437292085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3729777958491778332224453 699333367217208437292085)
              ·
                refine ⟨65562503176613290996133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 699333367217208437292085 65562503176613290996133)
                ·
                  rfl

theorem cell21_861857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 5].length) (baseStart_861857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861857 prefixEnd_861857 := by exact prefixLift 861857
  have htrace : WordTrace (prefixWord ++ tailWord_861857) baseStart_861857 baseEnd_861857 := by
    simpa [prefixWord, tailWord_861857, baseEnd_861857] using wordTrace_append hprefix tailTrace_861857
  have hstable : (prefixWord ++ tailWord_861857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861857).length < 2 ^ (prefixWord ++ tailWord_861857).sum := by decide
  have hdescent : baseEnd_861857 < baseStart_861857 := by decide
  rcases family_descends (prefixWord ++ tailWord_861857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861885 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 6]
def baseStart_861885 : Nat := 118140960795 + 861885 * 2 ^ 59
def prefixEnd_861885 : Nat := 4983230072969 + 3 ^ 40 * 861885 * 2
def baseEnd_861885 : Nat := 196693899511318046521675

theorem tailTrace_861885 : CollatzResearch.WordTrace tailWord_861885 prefixEnd_861885 196693899511318046521675 := by
  unfold tailWord_861885
  simp only [CollatzResearch.WordTrace]
  refine ⟨31435528482545318084059109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20957018988363545389372739 31435528482545318084059109)
  ·
    refine ⟨5894161590477247140761083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31435528482545318084059109 5894161590477247140761083)
    ·
      refine ⟨8841242385715870711141625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5894161590477247140761083 8841242385715870711141625)
      ·
        refine ⟨6630931789286903033356219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8841242385715870711141625 6630931789286903033356219)
        ·
          refine ⟨9946397683930354550034329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6630931789286903033356219 9946397683930354550034329)
          ·
            refine ⟨7459798262947765912525747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9946397683930354550034329 7459798262947765912525747)
            ·
              refine ⟨11189697394421648868788621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7459798262947765912525747 11189697394421648868788621)
              ·
                refine ⟨4196136522908118325795733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11189697394421648868788621 4196136522908118325795733)
                ·
                  refine ⟨196693899511318046521675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4196136522908118325795733 196693899511318046521675)
                  ·
                    rfl

theorem cell21_861885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_861885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861885 prefixEnd_861885 := by exact prefixLift 861885
  have htrace : WordTrace (prefixWord ++ tailWord_861885) baseStart_861885 baseEnd_861885 := by
    simpa [prefixWord, tailWord_861885, baseEnd_861885] using wordTrace_append hprefix tailTrace_861885
  have hstable : (prefixWord ++ tailWord_861885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861885).length < 2 ^ (prefixWord ++ tailWord_861885).sum := by decide
  have hdescent : baseEnd_861885 < baseStart_861885 := by decide
  rcases family_descends (prefixWord ++ tailWord_861885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861894 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_861894 : Nat := 118140960795 + 861894 * 2 ^ 59
def prefixEnd_861894 : Nat := 4983230072969 + 3 ^ 40 * 861894 * 2
def baseEnd_861894 : Nat := 196695953433936030871657

theorem tailTrace_861894 : CollatzResearch.WordTrace tailWord_861894 prefixEnd_861894 196695953433936030871657 := by
  unfold tailWord_861894
  simp only [CollatzResearch.WordTrace]
  refine ⟨982370523109772269410523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20957237826341808414091157 982370523109772269410523)
  ·
    refine ⟨1473555784664658404115785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 982370523109772269410523 1473555784664658404115785)
    ·
      refine ⟨1105166838498493803086839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1473555784664658404115785 1105166838498493803086839)
      ·
        refine ⟨1657750257747740704630259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105166838498493803086839 1657750257747740704630259)
        ·
          refine ⟨2486625386621611056945389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1657750257747740704630259 2486625386621611056945389)
          ·
            refine ⟨932484519983104146354521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2486625386621611056945389 932484519983104146354521)
            ·
              refine ⟨699363389987328109765891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 932484519983104146354521 699363389987328109765891)
              ·
                refine ⟨1049045084980992164648837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699363389987328109765891 1049045084980992164648837)
                ·
                  refine ⟨196695953433936030871657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1049045084980992164648837 196695953433936030871657)
                  ·
                    rfl

theorem cell21_861894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_861894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861894 prefixEnd_861894 := by exact prefixLift 861894
  have htrace : WordTrace (prefixWord ++ tailWord_861894) baseStart_861894 baseEnd_861894 := by
    simpa [prefixWord, tailWord_861894, baseEnd_861894] using wordTrace_append hprefix tailTrace_861894
  have hstable : (prefixWord ++ tailWord_861894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861894).length < 2 ^ (prefixWord ++ tailWord_861894).sum := by decide
  have hdescent : baseEnd_861894 < baseStart_861894 := by decide
  rcases family_descends (prefixWord ++ tailWord_861894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861902 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_861902 : Nat := 118140960795 + 861902 * 2 ^ 59
def prefixEnd_861902 : Nat := 4983230072969 + 3 ^ 40 * 861902 * 2
def baseEnd_861902 : Nat := 196697779142929794738307

theorem tailTrace_861902 : CollatzResearch.WordTrace tailWord_861902 prefixEnd_861902 196697779142929794738307 := by
  unfold tailWord_861902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3929518565435466248428495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20957432348989153324951973 3929518565435466248428495)
  ·
    refine ⟨5894277848153199372642743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3929518565435466248428495 5894277848153199372642743)
    ·
      refine ⟨8841416772229799058964115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5894277848153199372642743 8841416772229799058964115)
      ·
        refine ⟨13262125158344698588446173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8841416772229799058964115 13262125158344698588446173)
        ·
          refine ⟨4973296934379261970667315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13262125158344698588446173 4973296934379261970667315)
          ·
            refine ⟨7459945401568892956000973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4973296934379261970667315 7459945401568892956000973)
            ·
              refine ⟨2797479525588334858500365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7459945401568892956000973 2797479525588334858500365)
              ·
                refine ⟨1049054822095625571937637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2797479525588334858500365 1049054822095625571937637)
                ·
                  refine ⟨196697779142929794738307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1049054822095625571937637 196697779142929794738307)
                  ·
                    rfl

theorem cell21_861902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_861902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861902 prefixEnd_861902 := by exact prefixLift 861902
  have htrace : WordTrace (prefixWord ++ tailWord_861902) baseStart_861902 baseEnd_861902 := by
    simpa [prefixWord, tailWord_861902, baseEnd_861902] using wordTrace_append hprefix tailTrace_861902
  have hstable : (prefixWord ++ tailWord_861902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861902).length < 2 ^ (prefixWord ++ tailWord_861902).sum := by decide
  have hdescent : baseEnd_861902 < baseStart_861902 := by decide
  rcases family_descends (prefixWord ++ tailWord_861902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861950 : List Nat := [4, 2, 2, 1, 3, 2, 1, 6]
def baseStart_861950 : Nat := 118140960795 + 861950 * 2 ^ 59
def prefixEnd_861950 : Nat := 4983230072969 + 3 ^ 40 * 861950 * 2
def baseEnd_861950 : Nat := 65569577798964125979403

theorem tailTrace_861950 : CollatzResearch.WordTrace tailWord_861950 prefixEnd_861950 65569577798964125979403 := by
  unfold tailWord_861950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3929737403413729273146913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20958599484873222790116869 3929737403413729273146913)
  ·
    refine ⟨2947303052560296954860185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3929737403413729273146913 2947303052560296954860185)
    ·
      refine ⟨2210477289420222716145139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2947303052560296954860185 2210477289420222716145139)
      ·
        refine ⟨3315715934130334074217709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210477289420222716145139 3315715934130334074217709)
        ·
          refine ⟨1243393475298875277831641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3315715934130334074217709 1243393475298875277831641)
          ·
            refine ⟨932545106474156458373731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1243393475298875277831641 932545106474156458373731)
            ·
              refine ⟨1398817659711234687560597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932545106474156458373731 1398817659711234687560597)
              ·
                refine ⟨65569577798964125979403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1398817659711234687560597 65569577798964125979403)
                ·
                  rfl

theorem cell21_861950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_861950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861950 prefixEnd_861950 := by exact prefixLift 861950
  have htrace : WordTrace (prefixWord ++ tailWord_861950) baseStart_861950 baseEnd_861950 := by
    simpa [prefixWord, tailWord_861950, baseEnd_861950] using wordTrace_append hprefix tailTrace_861950
  have hstable : (prefixWord ++ tailWord_861950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861950).length < 2 ^ (prefixWord ++ tailWord_861950).sum := by decide
  have hdescent : baseEnd_861950 < baseStart_861950 := by decide
  rcases family_descends (prefixWord ++ tailWord_861950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_861992 : List Nat := [2, 1, 5, 1, 1, 3, 8]
def baseStart_861992 : Nat := 118140960795 + 861992 * 2 ^ 59
def prefixEnd_861992 : Nat := 4983230072969 + 3 ^ 40 * 861992 * 2
def baseEnd_861992 : Nat := 21857590929901070915347

theorem tailTrace_861992 : CollatzResearch.WordTrace tailWord_861992 prefixEnd_861992 21857590929901070915347 := by
  unfold tailWord_861992
  simp only [CollatzResearch.WordTrace]
  refine ⟨15719715546578837679102115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20959620728771783572136153 15719715546578837679102115)
  ·
    refine ⟨23579573319868256518653173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15719715546578837679102115 23579573319868256518653173)
    ·
      refine ⟨2210584998737649048623735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23579573319868256518653173 2210584998737649048623735)
      ·
        refine ⟨3315877498106473572935603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2210584998737649048623735 3315877498106473572935603)
        ·
          refine ⟨4973816247159710359403405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3315877498106473572935603 4973816247159710359403405)
          ·
            refine ⟨1865181092684891384776277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4973816247159710359403405 1865181092684891384776277)
            ·
              refine ⟨21857590929901070915347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1865181092684891384776277 21857590929901070915347)
              ·
                rfl

theorem cell21_861992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 8].length) (baseStart_861992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_861992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_861992 prefixEnd_861992 := by exact prefixLift 861992
  have htrace : WordTrace (prefixWord ++ tailWord_861992) baseStart_861992 baseEnd_861992 := by
    simpa [prefixWord, tailWord_861992, baseEnd_861992] using wordTrace_append hprefix tailTrace_861992
  have hstable : (prefixWord ++ tailWord_861992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_861992).length < 2 ^ (prefixWord ++ tailWord_861992).sum := by decide
  have hdescent : baseEnd_861992 < baseStart_861992 := by decide
  rcases family_descends (prefixWord ++ tailWord_861992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862037 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 6]
def baseStart_862037 : Nat := 118140960795 + 862037 * 2 ^ 59
def prefixEnd_862037 : Nat := 4983230072969 + 3 ^ 40 * 862037 * 2
def baseEnd_862037 : Nat := 196728587982199559988031

theorem tailTrace_862037 : CollatzResearch.WordTrace tailWord_862037 prefixEnd_862037 196728587982199559988031 := by
  unfold tailWord_862037
  simp only [CollatzResearch.WordTrace]
  refine ⟨31441072377994648043592365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20960714918663098695728243 31441072377994648043592365)
  ·
    refine ⟨11790402141747993016347137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31441072377994648043592365 11790402141747993016347137)
    ·
      refine ⟨8842801606310994762260353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11790402141747993016347137 8842801606310994762260353)
      ·
        refine ⟨6632101204733246071695265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8842801606310994762260353 6632101204733246071695265)
        ·
          refine ⟨4974075903549934553771449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6632101204733246071695265 4974075903549934553771449)
          ·
            refine ⟨3730556927662450915328587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4974075903549934553771449 3730556927662450915328587)
            ·
              refine ⟨5595835391493676372992881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3730556927662450915328587 5595835391493676372992881)
              ·
                refine ⟨4196876543620257279744661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5595835391493676372992881 4196876543620257279744661)
                ·
                  refine ⟨196728587982199559988031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4196876543620257279744661 196728587982199559988031)
                  ·
                    rfl

theorem cell21_862037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_862037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862037 prefixEnd_862037 := by exact prefixLift 862037
  have htrace : WordTrace (prefixWord ++ tailWord_862037) baseStart_862037 baseEnd_862037 := by
    simpa [prefixWord, tailWord_862037, baseEnd_862037] using wordTrace_append hprefix tailTrace_862037
  have hstable : (prefixWord ++ tailWord_862037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862037).length < 2 ^ (prefixWord ++ tailWord_862037).sum := by decide
  have hdescent : baseEnd_862037 < baseStart_862037 := by decide
  rcases family_descends (prefixWord ++ tailWord_862037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862102 : List Nat := [5, 3, 1, 1, 2, 9]
def baseStart_862102 : Nat := 118140960795 + 862102 * 2 ^ 59
def prefixEnd_862102 : Nat := 4983230072969 + 3 ^ 40 * 862102 * 2
def baseEnd_862102 : Nat := 7286793402510144126095

theorem tailTrace_862102 : CollatzResearch.WordTrace tailWord_862102 prefixEnd_862102 7286793402510144126095 := by
  unfold tailWord_862102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1965215195172447759044285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20962295415172776096472373 1965215195172447759044285)
  ·
    refine ⟨736955698189667909641607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1965215195172447759044285 736955698189667909641607)
    ·
      refine ⟨1105433547284501864462411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 736955698189667909641607 1105433547284501864462411)
      ·
        refine ⟨1658150320926752796693617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105433547284501864462411 1658150320926752796693617)
        ·
          refine ⟨1243612740695064597520213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1658150320926752796693617 1243612740695064597520213)
          ·
            refine ⟨7286793402510144126095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1243612740695064597520213 7286793402510144126095)
            ·
              rfl

theorem cell21_862102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 9].length) (baseStart_862102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862102 prefixEnd_862102 := by exact prefixLift 862102
  have htrace : WordTrace (prefixWord ++ tailWord_862102) baseStart_862102 baseEnd_862102 := by
    simpa [prefixWord, tailWord_862102, baseEnd_862102] using wordTrace_append hprefix tailTrace_862102
  have hstable : (prefixWord ++ tailWord_862102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862102).length < 2 ^ (prefixWord ++ tailWord_862102).sum := by decide
  have hdescent : baseEnd_862102 < baseStart_862102 := by decide
  rcases family_descends (prefixWord ++ tailWord_862102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862116 : List Nat := [2, 3, 1, 2, 1, 4, 1, 4, 3]
def baseStart_862116 : Nat := 118140960795 + 862116 * 2 ^ 59
def prefixEnd_862116 : Nat := 4983230072969 + 3 ^ 40 * 862116 * 2
def baseEnd_862116 : Nat := 196746616858512978171203

theorem tailTrace_862116 : CollatzResearch.WordTrace tailWord_862116 prefixEnd_862116 196746616858512978171203 := by
  unfold tailWord_862116
  simp only [CollatzResearch.WordTrace]
  refine ⟨15721976872354222267859101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20962635829805629690478801 15721976872354222267859101)
  ·
    refine ⟨5895741327132833350447163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15721976872354222267859101 5895741327132833350447163)
    ·
      refine ⟨8843611990699250025670745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5895741327132833350447163 8843611990699250025670745)
      ·
        refine ⟨6632708993024437519253059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8843611990699250025670745 6632708993024437519253059)
        ·
          refine ⟨9949063489536656278879589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6632708993024437519253059 9949063489536656278879589)
          ·
            refine ⟨1865449404288123052289923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9949063489536656278879589 1865449404288123052289923)
            ·
              refine ⟨2798174106432184578434885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865449404288123052289923 2798174106432184578434885)
              ·
                refine ⟨524657644956034608456541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2798174106432184578434885 524657644956034608456541)
                ·
                  refine ⟨196746616858512978171203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524657644956034608456541 196746616858512978171203)
                  ·
                    rfl

theorem cell21_862116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_862116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862116 prefixEnd_862116 := by exact prefixLift 862116
  have htrace : WordTrace (prefixWord ++ tailWord_862116) baseStart_862116 baseEnd_862116 := by
    simpa [prefixWord, tailWord_862116, baseEnd_862116] using wordTrace_append hprefix tailTrace_862116
  have hstable : (prefixWord ++ tailWord_862116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862116).length < 2 ^ (prefixWord ++ tailWord_862116).sum := by decide
  have hdescent : baseEnd_862116 < baseStart_862116 := by decide
  rcases family_descends (prefixWord ++ tailWord_862116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862144 : List Nat := [2, 1, 1, 2, 3, 2, 5, 5]
def baseStart_862144 : Nat := 118140960795 + 862144 * 2 ^ 59
def prefixEnd_862144 : Nat := 4983230072969 + 3 ^ 40 * 862144 * 2
def baseEnd_862144 : Nat := 65584335613330383901493

theorem tailTrace_862144 : CollatzResearch.WordTrace tailWord_862144 prefixEnd_862144 65584335613330383901493 := by
  unfold tailWord_862144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15722487494303502658868743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20963316659071336878491657 15722487494303502658868743)
  ·
    refine ⟨23583731241455253988303115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15722487494303502658868743 23583731241455253988303115)
    ·
      refine ⟨35375596862182880982454673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23583731241455253988303115 35375596862182880982454673)
      ·
        refine ⟨26531697646637160736841005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35375596862182880982454673 26531697646637160736841005)
        ·
          refine ⟨9949386617488935276315377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26531697646637160736841005 9949386617488935276315377)
          ·
            refine ⟨7462039963116701457236533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9949386617488935276315377 7462039963116701457236533)
            ·
              refine ⟨699566246542190761615925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7462039963116701457236533 699566246542190761615925)
              ·
                refine ⟨65584335613330383901493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 699566246542190761615925 65584335613330383901493)
                ·
                  rfl

theorem cell21_862144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 5].length) (baseStart_862144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862144 prefixEnd_862144 := by exact prefixLift 862144
  have htrace : WordTrace (prefixWord ++ tailWord_862144) baseStart_862144 baseEnd_862144 := by
    simpa [prefixWord, tailWord_862144, baseEnd_862144] using wordTrace_append hprefix tailTrace_862144
  have hstable : (prefixWord ++ tailWord_862144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862144).length < 2 ^ (prefixWord ++ tailWord_862144).sum := by decide
  have hdescent : baseEnd_862144 < baseStart_862144 := by decide
  rcases family_descends (prefixWord ++ tailWord_862144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862158 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_862158 : Nat := 118140960795 + 862158 * 2 ^ 59
def prefixEnd_862158 : Nat := 4983230072969 + 3 ^ 40 * 862158 * 2
def baseEnd_862158 : Nat := 196756201830730238471117

theorem tailTrace_862158 : CollatzResearch.WordTrace tailWord_862158 prefixEnd_862158 196756201830730238471117 := by
  unfold tailWord_862158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930685701319535713593391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20963657073704190472498085 3930685701319535713593391)
  ·
    refine ⟨5896028551979303570390087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3930685701319535713593391 5896028551979303570390087)
    ·
      refine ⟨8844042827968955355585131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5896028551979303570390087 8844042827968955355585131)
      ·
        refine ⟨13266064241953433033377697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8844042827968955355585131 13266064241953433033377697)
        ·
          refine ⟨9949548181465074775033273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13266064241953433033377697 9949548181465074775033273)
          ·
            refine ⟨7462161136098806081274955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9949548181465074775033273 7462161136098806081274955)
            ·
              refine ⟨11193241704148209121912433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7462161136098806081274955 11193241704148209121912433)
              ·
                refine ⟨8394931278111156841434325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11193241704148209121912433 8394931278111156841434325)
                ·
                  refine ⟨196756201830730238471117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8394931278111156841434325 196756201830730238471117)
                  ·
                    rfl

theorem cell21_862158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_862158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862158 prefixEnd_862158 := by exact prefixLift 862158
  have htrace : WordTrace (prefixWord ++ tailWord_862158) baseStart_862158 baseEnd_862158 := by
    simpa [prefixWord, tailWord_862158, baseEnd_862158] using wordTrace_append hprefix tailTrace_862158
  have hstable : (prefixWord ++ tailWord_862158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862158).length < 2 ^ (prefixWord ++ tailWord_862158).sum := by decide
  have hdescent : baseEnd_862158 < baseStart_862158 := by decide
  rcases family_descends (prefixWord ++ tailWord_862158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862175 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 5]
def baseStart_862175 : Nat := 118140960795 + 862175 * 2 ^ 59
def prefixEnd_862175 : Nat := 4983230072969 + 3 ^ 40 * 862175 * 2
def baseEnd_862175 : Nat := 196760081462341986687749

theorem tailTrace_862175 : CollatzResearch.WordTrace tailWord_862175 prefixEnd_862175 196760081462341986687749 := by
  unfold tailWord_862175
  simp only [CollatzResearch.WordTrace]
  refine ⟨31446105651494697612115979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20964070434329798408077319 31446105651494697612115979)
  ·
    refine ⟨47169158477242046418173969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31446105651494697612115979 47169158477242046418173969)
    ·
      refine ⟨35376868857931534813630477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47169158477242046418173969 35376868857931534813630477)
      ·
        refine ⟨13266325821724325555111429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35376868857931534813630477 13266325821724325555111429)
        ·
          refine ⟨2487436091573311041583393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13266325821724325555111429 2487436091573311041583393)
          ·
            refine ⟨1865577068679983281187545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2487436091573311041583393 1865577068679983281187545)
            ·
              refine ⟨1399182801509987460890659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1865577068679983281187545 1399182801509987460890659)
              ·
                refine ⟨2098774202264981191335989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399182801509987460890659 2098774202264981191335989)
                ·
                  refine ⟨196760081462341986687749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2098774202264981191335989 196760081462341986687749)
                  ·
                    rfl

theorem cell21_862175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 5].length) (baseStart_862175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862175 prefixEnd_862175 := by exact prefixLift 862175
  have htrace : WordTrace (prefixWord ++ tailWord_862175) baseStart_862175 baseEnd_862175 := by
    simpa [prefixWord, tailWord_862175, baseEnd_862175] using wordTrace_append hprefix tailTrace_862175
  have hstable : (prefixWord ++ tailWord_862175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862175).length < 2 ^ (prefixWord ++ tailWord_862175).sum := by decide
  have hdescent : baseEnd_862175 < baseStart_862175 := by decide
  rcases family_descends (prefixWord ++ tailWord_862175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862206 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_862206 : Nat := 118140960795 + 862206 * 2 ^ 59
def prefixEnd_862206 : Nat := 4983230072969 + 3 ^ 40 * 862206 * 2
def baseEnd_862206 : Nat := 196767156084692821671019

theorem tailTrace_862206 : CollatzResearch.WordTrace tailWord_862206 prefixEnd_862206 196767156084692821671019 := by
  unfold tailWord_862206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3930904539297798738311809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20964824209588259937662981 3930904539297798738311809)
  ·
    refine ⟨2948178404473349053733857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3930904539297798738311809 2948178404473349053733857)
    ·
      refine ⟨2211133803355011790300393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2948178404473349053733857 2211133803355011790300393)
      ·
        refine ⟨1658350352516258842725295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2211133803355011790300393 1658350352516258842725295)
        ·
          refine ⟨2487525528774388264087943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658350352516258842725295 2487525528774388264087943)
          ·
            refine ⟨3731288293161582396131915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487525528774388264087943 3731288293161582396131915)
            ·
              refine ⟨5596932439742373594197873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731288293161582396131915 5596932439742373594197873)
              ·
                refine ⟨4197699329806780195648405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5596932439742373594197873 4197699329806780195648405)
                ·
                  refine ⟨196767156084692821671019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4197699329806780195648405 196767156084692821671019)
                  ·
                    rfl

theorem cell21_862206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_862206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862206 prefixEnd_862206 := by exact prefixLift 862206
  have htrace : WordTrace (prefixWord ++ tailWord_862206) baseStart_862206 baseEnd_862206 := by
    simpa [prefixWord, tailWord_862206, baseEnd_862206] using wordTrace_append hprefix tailTrace_862206
  have hstable : (prefixWord ++ tailWord_862206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862206).length < 2 ^ (prefixWord ++ tailWord_862206).sum := by decide
  have hdescent : baseEnd_862206 < baseStart_862206 := by decide
  rcases family_descends (prefixWord ++ tailWord_862206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862296 : List Nat := [2, 1, 2, 2, 1, 6, 1, 6]
def baseStart_862296 : Nat := 118140960795 + 862296 * 2 ^ 59
def prefixEnd_862296 : Nat := 4983230072969 + 3 ^ 40 * 862296 * 2
def baseEnd_862296 : Nat := 65595898436957555056945

theorem tailTrace_862296 : CollatzResearch.WordTrace tailWord_862296 prefixEnd_862296 65595898436957555056945 := by
  unfold tailWord_862296
  simp only [CollatzResearch.WordTrace]
  refine ⟨15725259442028167638635371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20967012589370890184847161 15725259442028167638635371)
  ·
    refine ⟨23587889163042251457953057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15725259442028167638635371 23587889163042251457953057)
    ·
      refine ⟨17690916872281688593464793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23587889163042251457953057 17690916872281688593464793)
      ·
        refine ⟨13268187654211266445098595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17690916872281688593464793 13268187654211266445098595)
        ·
          refine ⟨19902281481316899667647893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13268187654211266445098595 19902281481316899667647893)
          ·
            refine ⟨932919444436729671920995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19902281481316899667647893 932919444436729671920995)
            ·
              refine ⟨1399379166655094507881493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932919444436729671920995 1399379166655094507881493)
              ·
                refine ⟨65595898436957555056945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1399379166655094507881493 65595898436957555056945)
                ·
                  rfl

theorem cell21_862296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_862296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862296 prefixEnd_862296 := by exact prefixLift 862296
  have htrace : WordTrace (prefixWord ++ tailWord_862296) baseStart_862296 baseEnd_862296 := by
    simpa [prefixWord, tailWord_862296, baseEnd_862296] using wordTrace_append hprefix tailTrace_862296
  have hstable : (prefixWord ++ tailWord_862296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862296).length < 2 ^ (prefixWord ++ tailWord_862296).sum := by decide
  have hdescent : baseEnd_862296 < baseStart_862296 := by decide
  rcases family_descends (prefixWord ++ tailWord_862296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862327 : List Nat := [1, 1, 3, 1, 1, 5, 1, 5, 3]
def baseStart_862327 : Nat := 118140960795 + 862327 * 2 ^ 59
def prefixEnd_862327 : Nat := 4983230072969 + 3 ^ 40 * 862327 * 2
def baseEnd_862327 : Nat := 196794769933223500154105

theorem tailTrace_862327 : CollatzResearch.WordTrace tailWord_862327 prefixEnd_862327 196794769933223500154105 := by
  unfold tailWord_862327
  simp only [CollatzResearch.WordTrace]
  refine ⟨31451649546944027571649235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20967766364629351714432823 31451649546944027571649235)
  ·
    refine ⟨47177474320416041357473853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31451649546944027571649235 47177474320416041357473853)
    ·
      refine ⟨17691552870156015509052695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47177474320416041357473853 17691552870156015509052695)
      ·
        refine ⟨26537329305234023263579043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17691552870156015509052695 26537329305234023263579043)
        ·
          refine ⟨39805993957851034895368565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26537329305234023263579043 39805993957851034895368565)
          ·
            refine ⟨3731811933548534521440803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39805993957851034895368565 3731811933548534521440803)
            ·
              refine ⟨5597717900322801782161205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3731811933548534521440803 5597717900322801782161205)
              ·
                refine ⟨524786053155262667077613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5597717900322801782161205 524786053155262667077613)
                ·
                  refine ⟨196794769933223500154105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524786053155262667077613 196794769933223500154105)
                  ·
                    rfl

theorem cell21_862327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 3].length) (baseStart_862327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862327 prefixEnd_862327 := by exact prefixLift 862327
  have htrace : WordTrace (prefixWord ++ tailWord_862327) baseStart_862327 baseEnd_862327 := by
    simpa [prefixWord, tailWord_862327, baseEnd_862327] using wordTrace_append hprefix tailTrace_862327
  have hstable : (prefixWord ++ tailWord_862327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862327).length < 2 ^ (prefixWord ++ tailWord_862327).sum := by decide
  have hdescent : baseEnd_862327 < baseStart_862327 := by decide
  rcases family_descends (prefixWord ++ tailWord_862327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862341 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 6]
def baseStart_862341 : Nat := 118140960795 + 862341 * 2 ^ 59
def prefixEnd_862341 : Nat := 4983230072969 + 3 ^ 40 * 862341 * 2
def baseEnd_862341 : Nat := 196797964923962586920743

theorem tailTrace_862341 : CollatzResearch.WordTrace tailWord_862341 prefixEnd_862341 196797964923962586920743 := by
  unfold tailWord_862341
  simp only [CollatzResearch.WordTrace]
  refine ⟨31452160168893307962658877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20968106779262205308439251 31452160168893307962658877)
  ·
    refine ⟨11794560063334990485997079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31452160168893307962658877 11794560063334990485997079)
    ·
      refine ⟨17691840095002485728995619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11794560063334990485997079 17691840095002485728995619)
      ·
        refine ⟨26537760142503728593493429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17691840095002485728995619 26537760142503728593493429)
        ·
          refine ⟨2487915013359724555640009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26537760142503728593493429 2487915013359724555640009)
          ·
            refine ⟨1865936260019793416730007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2487915013359724555640009 1865936260019793416730007)
            ·
              refine ⟨2798904390029690125095011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1865936260019793416730007 2798904390029690125095011)
              ·
                refine ⟨4198356585044535187642517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2798904390029690125095011 4198356585044535187642517)
                ·
                  refine ⟨196797964923962586920743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4198356585044535187642517 196797964923962586920743)
                  ·
                    rfl

theorem cell21_862341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_862341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862341 prefixEnd_862341 := by exact prefixLift 862341
  have htrace : WordTrace (prefixWord ++ tailWord_862341) baseStart_862341 baseEnd_862341 := by
    simpa [prefixWord, tailWord_862341, baseEnd_862341] using wordTrace_append hprefix tailTrace_862341
  have hstable : (prefixWord ++ tailWord_862341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862341).length < 2 ^ (prefixWord ++ tailWord_862341).sum := by decide
  have hdescent : baseEnd_862341 < baseStart_862341 := by decide
  rcases family_descends (prefixWord ++ tailWord_862341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862344 : List Nat := [2, 1, 3, 4, 1, 1, 2, 4, 3]
def baseStart_862344 : Nat := 118140960795 + 862344 * 2 ^ 59
def prefixEnd_862344 : Nat := 4983230072969 + 3 ^ 40 * 862344 * 2
def baseEnd_862344 : Nat := 196798649564835248370737

theorem tailTrace_862344 : CollatzResearch.WordTrace tailWord_862344 prefixEnd_862344 196798649564835248370737 := by
  unfold tailWord_862344
  simp only [CollatzResearch.WordTrace]
  refine ⟨15726134793941219737509043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20968179725254959650012057 15726134793941219737509043)
  ·
    refine ⟨23589202190911829606263565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15726134793941219737509043 23589202190911829606263565)
    ·
      refine ⟨8845950821591936102348837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23589202190911829606263565 8845950821591936102348837)
      ·
        refine ⟨1658615779048488019190407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8845950821591936102348837 1658615779048488019190407)
        ·
          refine ⟨2487923668572732028785611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1658615779048488019190407 2487923668572732028785611)
          ·
            refine ⟨3731885502859098043178417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2487923668572732028785611 3731885502859098043178417)
            ·
              refine ⟨2798914127144323532383813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3731885502859098043178417 2798914127144323532383813)
              ·
                refine ⟨524796398839560662321965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2798914127144323532383813 524796398839560662321965)
                ·
                  refine ⟨196798649564835248370737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524796398839560662321965 196798649564835248370737)
                  ·
                    rfl

theorem cell21_862344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 3].length) (baseStart_862344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862344 prefixEnd_862344 := by exact prefixLift 862344
  have htrace : WordTrace (prefixWord ++ tailWord_862344) baseStart_862344 baseEnd_862344 := by
    simpa [prefixWord, tailWord_862344, baseEnd_862344] using wordTrace_append hprefix tailTrace_862344
  have hstable : (prefixWord ++ tailWord_862344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862344).length < 2 ^ (prefixWord ++ tailWord_862344).sum := by decide
  have hdescent : baseEnd_862344 < baseStart_862344 := by decide
  rcases family_descends (prefixWord ++ tailWord_862344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862372 : List Nat := [2, 3, 1, 2, 4, 1, 1, 7]
def baseStart_862372 : Nat := 118140960795 + 862372 * 2 ^ 59
def prefixEnd_862372 : Nat := 4983230072969 + 3 ^ 40 * 862372 * 2
def baseEnd_862372 : Nat := 65601679848771140634671

theorem tailTrace_862372 : CollatzResearch.WordTrace tailWord_862372 prefixEnd_862372 65601679848771140634671 := by
  unfold tailWord_862372
  simp only [CollatzResearch.WordTrace]
  refine ⟨15726645415890500128518685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20968860554520666838024913 15726645415890500128518685)
  ·
    refine ⟨5897492030958937548194507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15726645415890500128518685 5897492030958937548194507)
    ·
      refine ⟨8846238046438406322291761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5897492030958937548194507 8846238046438406322291761)
      ·
        refine ⟨6634678534828804741718821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8846238046438406322291761 6634678534828804741718821)
        ·
          refine ⟨1244002225280400889072279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6634678534828804741718821 1244002225280400889072279)
          ·
            refine ⟨1866003337920601333608419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244002225280400889072279 1866003337920601333608419)
            ·
              refine ⟨2799005006880902000412629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1866003337920601333608419 2799005006880902000412629)
              ·
                refine ⟨65601679848771140634671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2799005006880902000412629 65601679848771140634671)
                ·
                  rfl

theorem cell21_862372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 7].length) (baseStart_862372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862372 prefixEnd_862372 := by exact prefixLift 862372
  have htrace : WordTrace (prefixWord ++ tailWord_862372) baseStart_862372 baseEnd_862372 := by
    simpa [prefixWord, tailWord_862372, baseEnd_862372] using wordTrace_append hprefix tailTrace_862372
  have hstable : (prefixWord ++ tailWord_862372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862372).length < 2 ^ (prefixWord ++ tailWord_862372).sum := by decide
  have hdescent : baseEnd_862372 < baseStart_862372 := by decide
  rcases family_descends (prefixWord ++ tailWord_862372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862378 : List Nat := [3, 1, 5, 1, 2, 2, 1, 3, 3]
def baseStart_862378 : Nat := 118140960795 + 862378 * 2 ^ 59
def prefixEnd_862378 : Nat := 4983230072969 + 3 ^ 40 * 862378 * 2
def baseEnd_862378 : Nat := 196806408828058744804001

theorem tailTrace_862378 : CollatzResearch.WordTrace tailWord_862378 prefixEnd_862378 196806408828058744804001 := by
  unfold tailWord_862378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7863377417439815820438947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20969006446506175521170525 7863377417439815820438947)
  ·
    refine ⟨11795066126159723730658421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7863377417439815820438947 11795066126159723730658421)
    ·
      refine ⟨1105787449327474099749227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11795066126159723730658421 1105787449327474099749227)
      ·
        refine ⟨1658681173991211149623841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1105787449327474099749227 1658681173991211149623841)
        ·
          refine ⟨1244010880493408362217881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1658681173991211149623841 1244010880493408362217881)
          ·
            refine ⟨933008160370056271663411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244010880493408362217881 933008160370056271663411)
            ·
              refine ⟨1399512240555084407495117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933008160370056271663411 1399512240555084407495117)
              ·
                refine ⟨524817090208156652810669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1399512240555084407495117 524817090208156652810669)
                ·
                  refine ⟨196806408828058744804001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524817090208156652810669 196806408828058744804001)
                  ·
                    rfl

theorem cell21_862378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 3].length) (baseStart_862378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862378 prefixEnd_862378 := by exact prefixLift 862378
  have htrace : WordTrace (prefixWord ++ tailWord_862378) baseStart_862378 baseEnd_862378 := by
    simpa [prefixWord, tailWord_862378, baseEnd_862378] using wordTrace_append hprefix tailTrace_862378
  have hstable : (prefixWord ++ tailWord_862378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862378).length < 2 ^ (prefixWord ++ tailWord_862378).sum := by decide
  have hdescent : baseEnd_862378 < baseStart_862378 := by decide
  rcases family_descends (prefixWord ++ tailWord_862378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862389 : List Nat := [1, 3, 3, 4, 1, 2, 7]
def baseStart_862389 : Nat := 118140960795 + 862389 * 2 ^ 59
def prefixEnd_862389 : Nat := 4983230072969 + 3 ^ 40 * 862389 * 2
def baseEnd_862389 : Nat := 21867657686436130013405

theorem tailTrace_862389 : CollatzResearch.WordTrace tailWord_862389 prefixEnd_862389 21867657686436130013405 := by
  unfold tailWord_862389
  simp only [CollatzResearch.WordTrace]
  refine ⟨31453910872719412160406221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20969273915146274773604147 31453910872719412160406221)
  ·
    refine ⟨11795216577269779560152333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31453910872719412160406221 11795216577269779560152333)
    ·
      refine ⟨4423206216476167335057125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11795216577269779560152333 4423206216476167335057125)
      ·
        refine ⟨829351165589281375323211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4423206216476167335057125 829351165589281375323211)
        ·
          refine ⟨1244026748383922062984817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 829351165589281375323211 1244026748383922062984817)
          ·
            refine ⟨933020061287941547238613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1244026748383922062984817 933020061287941547238613)
            ·
              refine ⟨21867657686436130013405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 933020061287941547238613 21867657686436130013405)
              ·
                rfl

theorem cell21_862389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 7].length) (baseStart_862389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862389 prefixEnd_862389 := by exact prefixLift 862389
  have htrace : WordTrace (prefixWord ++ tailWord_862389) baseStart_862389 baseEnd_862389 := by
    simpa [prefixWord, tailWord_862389, baseEnd_862389] using wordTrace_append hprefix tailTrace_862389
  have hstable : (prefixWord ++ tailWord_862389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862389).length < 2 ^ (prefixWord ++ tailWord_862389).sum := by decide
  have hdescent : baseEnd_862389 < baseStart_862389 := by decide
  rcases family_descends (prefixWord ++ tailWord_862389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862496 : List Nat := [2, 1, 1, 5, 2, 2, 2, 3, 3]
def baseStart_862496 : Nat := 118140960795 + 862496 * 2 ^ 59
def prefixEnd_862496 : Nat := 4983230072969 + 3 ^ 40 * 862496 * 2
def baseEnd_862496 : Nat := 196833338035716761837093

theorem tailTrace_862496 : CollatzResearch.WordTrace tailWord_862496 prefixEnd_862496 196833338035716761837093 := by
  unfold tailWord_862496
  simp only [CollatzResearch.WordTrace]
  refine ⟨15728906741665884717275671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20971875655554512956367561 15728906741665884717275671)
  ·
    refine ⟨23593360112498827075913507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15728906741665884717275671 23593360112498827075913507)
    ·
      refine ⟨35390040168748240613870261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23593360112498827075913507 35390040168748240613870261)
      ·
        refine ⟨3317816265820147557550337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35390040168748240613870261 3317816265820147557550337)
        ·
          refine ⟨2488362199365110668162753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3317816265820147557550337 2488362199365110668162753)
          ·
            refine ⟨1866271649523833001122065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2488362199365110668162753 1866271649523833001122065)
            ·
              refine ⟨1399703737142874750841549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866271649523833001122065 1399703737142874750841549)
              ·
                refine ⟨524888901428578031565581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1399703737142874750841549 524888901428578031565581)
                ·
                  refine ⟨196833338035716761837093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524888901428578031565581 196833338035716761837093)
                  ·
                    rfl

theorem cell21_862496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 3].length) (baseStart_862496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862496 prefixEnd_862496 := by exact prefixLift 862496
  have htrace : WordTrace (prefixWord ++ tailWord_862496) baseStart_862496 baseEnd_862496 := by
    simpa [prefixWord, tailWord_862496, baseEnd_862496] using wordTrace_append hprefix tailTrace_862496
  have hstable : (prefixWord ++ tailWord_862496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862496).length < 2 ^ (prefixWord ++ tailWord_862496).sum := by decide
  have hdescent : baseEnd_862496 < baseStart_862496 := by decide
  rcases family_descends (prefixWord ++ tailWord_862496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862572 : List Nat := [2, 2, 1, 1, 7, 1, 1, 1, 5]
def baseStart_862572 : Nat := 118140960795 + 862572 * 2 ^ 59
def prefixEnd_862572 : Nat := 4983230072969 + 3 ^ 40 * 862572 * 2
def baseEnd_862572 : Nat := 196850682271157518570271

theorem tailTrace_862572 : CollatzResearch.WordTrace tailWord_862572 prefixEnd_862572 196850682271157518570271 := by
  unfold tailWord_862572
  simp only [CollatzResearch.WordTrace]
  refine ⟨15730292715528217207158985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20973723620704289609545313 15730292715528217207158985)
  ·
    refine ⟨11797719536646162905369239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15730292715528217207158985 11797719536646162905369239)
    ·
      refine ⟨17696579304969244358053859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11797719536646162905369239 17696579304969244358053859)
      ·
        refine ⟨26544868957453866537080789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17696579304969244358053859 26544868957453866537080789)
        ·
          refine ⟨622145366190324996962831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26544868957453866537080789 622145366190324996962831)
          ·
            refine ⟨933218049285487495444247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622145366190324996962831 933218049285487495444247)
            ·
              refine ⟨1399827073928231243166371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933218049285487495444247 1399827073928231243166371)
              ·
                refine ⟨2099740610892346864749557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1399827073928231243166371 2099740610892346864749557)
                ·
                  refine ⟨196850682271157518570271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2099740610892346864749557 196850682271157518570271)
                  ·
                    rfl

theorem cell21_862572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_862572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862572 prefixEnd_862572 := by exact prefixLift 862572
  have htrace : WordTrace (prefixWord ++ tailWord_862572) baseStart_862572 baseEnd_862572 := by
    simpa [prefixWord, tailWord_862572, baseEnd_862572] using wordTrace_append hprefix tailTrace_862572
  have hstable : (prefixWord ++ tailWord_862572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862572).length < 2 ^ (prefixWord ++ tailWord_862572).sum := by decide
  have hdescent : baseEnd_862572 < baseStart_862572 := by decide
  rcases family_descends (prefixWord ++ tailWord_862572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862597 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 7]
def baseStart_862597 : Nat := 118140960795 + 862597 * 2 ^ 59
def prefixEnd_862597 : Nat := 4983230072969 + 3 ^ 40 * 862597 * 2
def baseEnd_862597 : Nat := 196856387611763030653553

theorem tailTrace_862597 : CollatzResearch.WordTrace tailWord_862597 prefixEnd_862597 196856387611763030653553 := by
  unfold tailWord_862597
  simp only [CollatzResearch.WordTrace]
  refine ⟨31461497255965863683978045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20974331503977242455985363 31461497255965863683978045)
  ·
    refine ⟨11798061470987198881491767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31461497255965863683978045 11798061470987198881491767)
    ·
      refine ⟨17697092206480798322237651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11798061470987198881491767 17697092206480798322237651)
      ·
        refine ⟨26545638309721197483356477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17697092206480798322237651 26545638309721197483356477)
        ·
          refine ⟨9954614366145449056258679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26545638309721197483356477 9954614366145449056258679)
          ·
            refine ⟨14931921549218173584388019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9954614366145449056258679 14931921549218173584388019)
            ·
              refine ⟨22397882323827260376582029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14931921549218173584388019 22397882323827260376582029)
              ·
                refine ⟨8399205871435222641218261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22397882323827260376582029 8399205871435222641218261)
                ·
                  refine ⟨196856387611763030653553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8399205871435222641218261 196856387611763030653553)
                  ·
                    rfl

theorem cell21_862597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_862597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862597 prefixEnd_862597 := by exact prefixLift 862597
  have htrace : WordTrace (prefixWord ++ tailWord_862597) baseStart_862597 baseEnd_862597 := by
    simpa [prefixWord, tailWord_862597, baseEnd_862597] using wordTrace_append hprefix tailTrace_862597
  have hstable : (prefixWord ++ tailWord_862597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862597).length < 2 ^ (prefixWord ++ tailWord_862597).sum := by decide
  have hdescent : baseEnd_862597 < baseStart_862597 := by decide
  rcases family_descends (prefixWord ++ tailWord_862597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862628 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_862628 : Nat := 118140960795 + 862628 * 2 ^ 59
def prefixEnd_862628 : Nat := 4983230072969 + 3 ^ 40 * 862628 * 2
def baseEnd_862628 : Nat := 196863462234113865636823

theorem tailTrace_862628 : CollatzResearch.WordTrace tailWord_862628 prefixEnd_862628 196863462234113865636823 := by
  unfold tailWord_862628
  simp only [CollatzResearch.WordTrace]
  refine ⟨15731313959426777989178269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20975085279235703985571025 15731313959426777989178269)
  ·
    refine ⟨5899242734785041745941851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15731313959426777989178269 5899242734785041745941851)
    ·
      refine ⟨8848864102177562618912777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5899242734785041745941851 8848864102177562618912777)
      ·
        refine ⟨6636648076633171964184583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8848864102177562618912777 6636648076633171964184583)
        ·
          refine ⟨9954972114949757946276875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6636648076633171964184583 9954972114949757946276875)
          ·
            refine ⟨14932458172424636919415313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9954972114949757946276875 14932458172424636919415313)
            ·
              refine ⟨11199343629318477689561485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14932458172424636919415313 11199343629318477689561485)
              ·
                refine ⟨4199753860994429133585557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11199343629318477689561485 4199753860994429133585557)
                ·
                  refine ⟨196863462234113865636823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4199753860994429133585557 196863462234113865636823)
                  ·
                    rfl

theorem cell21_862628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_862628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862628 prefixEnd_862628 := by exact prefixLift 862628
  have htrace : WordTrace (prefixWord ++ tailWord_862628) baseStart_862628 baseEnd_862628 := by
    simpa [prefixWord, tailWord_862628, baseEnd_862628] using wordTrace_append hprefix tailTrace_862628
  have hstable : (prefixWord ++ tailWord_862628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862628).length < 2 ^ (prefixWord ++ tailWord_862628).sum := by decide
  have hdescent : baseEnd_862628 < baseStart_862628 := by decide
  rcases family_descends (prefixWord ++ tailWord_862628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862724 : List Nat := [2, 3, 2, 3, 1, 1, 3, 3, 3]
def baseStart_862724 : Nat := 118140960795 + 862724 * 2 ^ 59
def prefixEnd_862724 : Nat := 4983230072969 + 3 ^ 40 * 862724 * 2
def baseEnd_862724 : Nat := 196885370742039032036627

theorem tailTrace_862724 : CollatzResearch.WordTrace tailWord_862724 prefixEnd_862724 196885370742039032036627 := by
  unfold tailWord_862724
  simp only [CollatzResearch.WordTrace]
  refine ⟨15733064663252882186925613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20977419551003842915900817 15733064663252882186925613)
  ·
    refine ⟨5899899248719830820097105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15733064663252882186925613 5899899248719830820097105)
    ·
      refine ⟨4424924436539873115072829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5899899248719830820097105 4424924436539873115072829)
      ·
        refine ⟨1659346663702452418152311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4424924436539873115072829 1659346663702452418152311)
        ·
          refine ⟨2489019995553678627228467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1659346663702452418152311 2489019995553678627228467)
          ·
            refine ⟨3733529993330517940842701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2489019995553678627228467 3733529993330517940842701)
            ·
              refine ⟨1400073747498944227816013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3733529993330517940842701 1400073747498944227816013)
              ·
                refine ⟨525027655312104085431005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1400073747498944227816013 525027655312104085431005)
                ·
                  refine ⟨196885370742039032036627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525027655312104085431005 196885370742039032036627)
                  ·
                    rfl

theorem cell21_862724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_862724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862724 prefixEnd_862724 := by exact prefixLift 862724
  have htrace : WordTrace (prefixWord ++ tailWord_862724) baseStart_862724 baseEnd_862724 := by
    simpa [prefixWord, tailWord_862724, baseEnd_862724] using wordTrace_append hprefix tailTrace_862724
  have hstable : (prefixWord ++ tailWord_862724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862724).length < 2 ^ (prefixWord ++ tailWord_862724).sum := by decide
  have hdescent : baseEnd_862724 < baseStart_862724 := by decide
  rcases family_descends (prefixWord ++ tailWord_862724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862752 : List Nat := [2, 1, 1, 6, 2, 1, 2, 6]
def baseStart_862752 : Nat := 118140960795 + 862752 * 2 ^ 59
def prefixEnd_862752 : Nat := 4983230072969 + 3 ^ 40 * 862752 * 2
def baseEnd_862752 : Nat := 65630586907839068523301

theorem tailTrace_862752 : CollatzResearch.WordTrace tailWord_862752 prefixEnd_862752 65630586907839068523301 := by
  unfold tailWord_862752
  simp only [CollatzResearch.WordTrace]
  refine ⟨15733575285202162577935255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20978100380269550103913673 15733575285202162577935255)
  ·
    refine ⟨23600362927803243866902883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15733575285202162577935255 23600362927803243866902883)
    ·
      refine ⟨35400544391704865800354325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23600362927803243866902883 35400544391704865800354325)
      ·
        refine ⟨1659400518361165584391609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35400544391704865800354325 1659400518361165584391609)
        ·
          refine ⟨1244550388770874188293707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1659400518361165584391609 1244550388770874188293707)
          ·
            refine ⟨1866825583156311282440561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1244550388770874188293707 1866825583156311282440561)
            ·
              refine ⟨1400119187367233461830421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1866825583156311282440561 1400119187367233461830421)
              ·
                refine ⟨65630586907839068523301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1400119187367233461830421 65630586907839068523301)
                ·
                  rfl

theorem cell21_862752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_862752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862752 prefixEnd_862752 := by exact prefixLift 862752
  have htrace : WordTrace (prefixWord ++ tailWord_862752) baseStart_862752 baseEnd_862752 := by
    simpa [prefixWord, tailWord_862752, baseEnd_862752] using wordTrace_append hprefix tailTrace_862752
  have hstable : (prefixWord ++ tailWord_862752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862752).length < 2 ^ (prefixWord ++ tailWord_862752).sum := by decide
  have hdescent : baseEnd_862752 < baseStart_862752 := by decide
  rcases family_descends (prefixWord ++ tailWord_862752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862794 : List Nat := [3, 1, 2, 1, 1, 13]
def baseStart_862794 : Nat := 118140960795 + 862794 * 2 ^ 59
def prefixEnd_862794 : Nat := 4983230072969 + 3 ^ 40 * 862794 * 2
def baseEnd_862794 : Nat := 7292642433175350587771

theorem tailTrace_862794 : CollatzResearch.WordTrace tailWord_862794 prefixEnd_862794 7292642433175350587771 := by
  unfold tailWord_862794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7867170609063041582224859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20979121624168110885932957 7867170609063041582224859)
  ·
    refine ⟨11800755913594562373337289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7867170609063041582224859 11800755913594562373337289)
    ·
      refine ⟨8850566935195921780002967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11800755913594562373337289 8850566935195921780002967)
      ·
        refine ⟨13275850402793882670004451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8850566935195921780002967 13275850402793882670004451)
        ·
          refine ⟨19913775604190824005006677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13275850402793882670004451 19913775604190824005006677)
          ·
            refine ⟨7292642433175350587771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 19913775604190824005006677 7292642433175350587771)
            ·
              rfl

theorem cell21_862794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 13].length) (baseStart_862794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862794 prefixEnd_862794 := by exact prefixLift 862794
  have htrace : WordTrace (prefixWord ++ tailWord_862794) baseStart_862794 baseEnd_862794 := by
    simpa [prefixWord, tailWord_862794, baseEnd_862794] using wordTrace_append hprefix tailTrace_862794
  have hstable : (prefixWord ++ tailWord_862794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862794).length < 2 ^ (prefixWord ++ tailWord_862794).sum := by decide
  have hdescent : baseEnd_862794 < baseStart_862794 := by decide
  rcases family_descends (prefixWord ++ tailWord_862794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862873 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 4]
def baseStart_862873 : Nat := 118140960795 + 862873 * 2 ^ 59
def prefixEnd_862873 : Nat := 4983230072969 + 3 ^ 40 * 862873 * 2
def baseEnd_862873 : Nat := 196919374572047884052989

theorem tailTrace_862873 : CollatzResearch.WordTrace tailWord_862873 prefixEnd_862873 196919374572047884052989 := by
  unfold tailWord_862873
  simp only [CollatzResearch.WordTrace]
  refine ⟨31471563802965962821025273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20981042535310641880683515 31471563802965962821025273)
  ·
    refine ⟨23603672852224472115768955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31471563802965962821025273 23603672852224472115768955)
    ·
      refine ⟨35405509278336708173653433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23603672852224472115768955 35405509278336708173653433)
      ·
        refine ⟨26554131958752531130240075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35405509278336708173653433 26554131958752531130240075)
        ·
          refine ⟨39831197938128796695360113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26554131958752531130240075 39831197938128796695360113)
          ·
            refine ⟨29873398453596597521520085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39831197938128796695360113 29873398453596597521520085)
            ·
              refine ⟨700157776256170254410627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29873398453596597521520085 700157776256170254410627)
              ·
                refine ⟨1050236664384255381615941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700157776256170254410627 1050236664384255381615941)
                ·
                  refine ⟨196919374572047884052989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1050236664384255381615941 196919374572047884052989)
                  ·
                    rfl

theorem cell21_862873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_862873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862873 prefixEnd_862873 := by exact prefixLift 862873
  have htrace : WordTrace (prefixWord ++ tailWord_862873) baseStart_862873 baseEnd_862873 := by
    simpa [prefixWord, tailWord_862873, baseEnd_862873] using wordTrace_append hprefix tailTrace_862873
  have hstable : (prefixWord ++ tailWord_862873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862873).length < 2 ^ (prefixWord ++ tailWord_862873).sum := by decide
  have hdescent : baseEnd_862873 < baseStart_862873 := by decide
  rcases family_descends (prefixWord ++ tailWord_862873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_862977 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 5]
def baseStart_862977 : Nat := 118140960795 + 862977 * 2 ^ 59
def prefixEnd_862977 : Nat := 4983230072969 + 3 ^ 40 * 862977 * 2
def baseEnd_862977 : Nat := 196943108788966814319443

theorem tailTrace_862977 : CollatzResearch.WordTrace tailWord_862977 prefixEnd_862977 196943108788966814319443 := by
  unfold tailWord_862977
  simp only [CollatzResearch.WordTrace]
  refine ⟨31475356994589188582811185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20983571329726125721874123 31475356994589188582811185)
  ·
    refine ⟨23606517745941891437108389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31475356994589188582811185 23606517745941891437108389)
    ·
      refine ⟨4426222077364104644457823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23606517745941891437108389 4426222077364104644457823)
      ·
        refine ⟨6639333116046156966686735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4426222077364104644457823 6639333116046156966686735)
        ·
          refine ⟨9958999674069235450030103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6639333116046156966686735 9958999674069235450030103)
          ·
            refine ⟨14938499511103853175045155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9958999674069235450030103 14938499511103853175045155)
            ·
              refine ⟨22407749266655779762567733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14938499511103853175045155 22407749266655779762567733)
              ·
                refine ⟨2100726493748979352740725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22407749266655779762567733 2100726493748979352740725)
                ·
                  refine ⟨196943108788966814319443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2100726493748979352740725 196943108788966814319443)
                  ·
                    rfl

theorem cell21_862977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_862977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_862977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_862977 prefixEnd_862977 := by exact prefixLift 862977
  have htrace : WordTrace (prefixWord ++ tailWord_862977) baseStart_862977 baseEnd_862977 := by
    simpa [prefixWord, tailWord_862977, baseEnd_862977] using wordTrace_append hprefix tailTrace_862977
  have hstable : (prefixWord ++ tailWord_862977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_862977).length < 2 ^ (prefixWord ++ tailWord_862977).sum := by decide
  have hdescent : baseEnd_862977 < baseStart_862977 := by decide
  rcases family_descends (prefixWord ++ tailWord_862977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863084 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_863084 : Nat := 118140960795 + 863084 * 2 ^ 59
def prefixEnd_863084 : Nat := 4983230072969 + 3 ^ 40 * 863084 * 2
def baseEnd_863084 : Nat := 196967527646758406035891

theorem tailTrace_863084 : CollatzResearch.WordTrace tailWord_863084 prefixEnd_863084 196967527646758406035891 := by
  unfold tailWord_863084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15739629802600772928478153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20986173070134363904637537 15739629802600772928478153)
  ·
    refine ⟨11804722351950579696358615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15739629802600772928478153 11804722351950579696358615)
    ·
      refine ⟨17707083527925869544537923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11804722351950579696358615 17707083527925869544537923)
      ·
        refine ⟨26560625291888804316806885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17707083527925869544537923 26560625291888804316806885)
        ·
          refine ⟨4980117242229150809401291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26560625291888804316806885 4980117242229150809401291)
          ·
            refine ⟨7470175863343726214101937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4980117242229150809401291 7470175863343726214101937)
            ·
              refine ⟨5602631897507794660576453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7470175863343726214101937 5602631897507794660576453)
              ·
                refine ⟨1050493480782711498858085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5602631897507794660576453 1050493480782711498858085)
                ·
                  refine ⟨196967527646758406035891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1050493480782711498858085 196967527646758406035891)
                  ·
                    rfl

theorem cell21_863084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_863084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863084 prefixEnd_863084 := by exact prefixLift 863084
  have htrace : WordTrace (prefixWord ++ tailWord_863084) baseStart_863084 baseEnd_863084 := by
    simpa [prefixWord, tailWord_863084, baseEnd_863084] using wordTrace_append hprefix tailTrace_863084
  have hstable : (prefixWord ++ tailWord_863084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863084).length < 2 ^ (prefixWord ++ tailWord_863084).sum := by decide
  have hdescent : baseEnd_863084 < baseStart_863084 := by decide
  rcases family_descends (prefixWord ++ tailWord_863084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863101 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 4]
def baseStart_863101 : Nat := 118140960795 + 863101 * 2 ^ 59
def prefixEnd_863101 : Nat := 4983230072969 + 3 ^ 40 * 863101 * 2
def baseEnd_863101 : Nat := 196971407278370154252523

theorem tailTrace_863101 : CollatzResearch.WordTrace tailWord_863101 prefixEnd_863101 196971407278370154252523 := by
  unfold tailWord_863101
  simp only [CollatzResearch.WordTrace]
  refine ⟨31479879646139957760325157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20986586430759971840216771 31479879646139957760325157)
  ·
    refine ⟨5902477433651242080060967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31479879646139957760325157 5902477433651242080060967)
    ·
      refine ⟨8853716150476863120091451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5902477433651242080060967 8853716150476863120091451)
      ·
        refine ⟨13280574225715294680137177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8853716150476863120091451 13280574225715294680137177)
        ·
          refine ⟨9960430669286471010102883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13280574225715294680137177 9960430669286471010102883)
          ·
            refine ⟨14940646003929706515154325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9960430669286471010102883 14940646003929706515154325)
            ·
              refine ⟨700342781434204992897859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14940646003929706515154325 700342781434204992897859)
              ·
                refine ⟨1050514172151307489346789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 700342781434204992897859 1050514172151307489346789)
                ·
                  refine ⟨196971407278370154252523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1050514172151307489346789 196971407278370154252523)
                  ·
                    rfl

theorem cell21_863101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_863101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863101 prefixEnd_863101 := by exact prefixLift 863101
  have htrace : WordTrace (prefixWord ++ tailWord_863101) baseStart_863101 baseEnd_863101 := by
    simpa [prefixWord, tailWord_863101, baseEnd_863101] using wordTrace_append hprefix tailTrace_863101
  have hstable : (prefixWord ++ tailWord_863101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863101).length < 2 ^ (prefixWord ++ tailWord_863101).sum := by decide
  have hdescent : baseEnd_863101 < baseStart_863101 := by decide
  rcases family_descends (prefixWord ++ tailWord_863101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863149 : List Nat := [1, 5, 2, 3, 1, 2, 1, 6]
def baseStart_863149 : Nat := 118140960795 + 863149 * 2 ^ 59
def prefixEnd_863149 : Nat := 4983230072969 + 3 ^ 40 * 863149 * 2
def baseEnd_863149 : Nat := 65660787177444245817475

theorem tailTrace_863149 : CollatzResearch.WordTrace tailWord_863149 prefixEnd_863149 65660787177444245817475 := by
  unfold tailWord_863149
  simp only [CollatzResearch.WordTrace]
  refine ⟨31481630349966061958072501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20987753566644041305381667 31481630349966061958072501)
  ·
    refine ⟨2951402845309318308569297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31481630349966061958072501 2951402845309318308569297)
    ·
      refine ⟨2213552133981988731426973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2951402845309318308569297 2213552133981988731426973)
      ·
        refine ⟨830082050243245774285115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2213552133981988731426973 830082050243245774285115)
        ·
          refine ⟨1245123075364868661427673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830082050243245774285115 1245123075364868661427673)
          ·
            refine ⟨933842306523651496070755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1245123075364868661427673 933842306523651496070755)
            ·
              refine ⟨1400763459785477244106133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 933842306523651496070755 1400763459785477244106133)
              ·
                refine ⟨65660787177444245817475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1400763459785477244106133 65660787177444245817475)
                ·
                  rfl

theorem cell21_863149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 6].length) (baseStart_863149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863149 prefixEnd_863149 := by exact prefixLift 863149
  have htrace : WordTrace (prefixWord ++ tailWord_863149) baseStart_863149 baseEnd_863149 := by
    simpa [prefixWord, tailWord_863149, baseEnd_863149] using wordTrace_append hprefix tailTrace_863149
  have hstable : (prefixWord ++ tailWord_863149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863149).length < 2 ^ (prefixWord ++ tailWord_863149).sum := by decide
  have hdescent : baseEnd_863149 < baseStart_863149 := by decide
  rcases family_descends (prefixWord ++ tailWord_863149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863160 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_863160 : Nat := 118140960795 + 863160 * 2 ^ 59
def prefixEnd_863160 : Nat := 4983230072969 + 3 ^ 40 * 863160 * 2
def baseEnd_863160 : Nat := 196984871882199162769069

theorem tailTrace_863160 : CollatzResearch.WordTrace tailWord_863160 prefixEnd_863160 196984871882199162769069 := by
  unfold tailWord_863160
  simp only [CollatzResearch.WordTrace]
  refine ⟨15741015776463105418361467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20988021035284140557815289 15741015776463105418361467)
  ·
    refine ⟨23611523664694658127542201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15741015776463105418361467 23611523664694658127542201)
    ·
      refine ⟨17708642748520993595656651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23611523664694658127542201 17708642748520993595656651)
      ·
        refine ⟨26562964122781490393484977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17708642748520993595656651 26562964122781490393484977)
        ·
          refine ⟨19922223092086117795113733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26562964122781490393484977 19922223092086117795113733)
          ·
            refine ⟨3735416829766147086583825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19922223092086117795113733 3735416829766147086583825)
            ·
              refine ⟨2801562622324610314937869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735416829766147086583825 2801562622324610314937869)
              ·
                refine ⟨1050585983371728868101701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2801562622324610314937869 1050585983371728868101701)
                ·
                  refine ⟨196984871882199162769069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1050585983371728868101701 196984871882199162769069)
                  ·
                    rfl

theorem cell21_863160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_863160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863160 prefixEnd_863160 := by exact prefixLift 863160
  have htrace : WordTrace (prefixWord ++ tailWord_863160) baseStart_863160 baseEnd_863160 := by
    simpa [prefixWord, tailWord_863160, baseEnd_863160] using wordTrace_append hprefix tailTrace_863160
  have hstable : (prefixWord ++ tailWord_863160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863160).length < 2 ^ (prefixWord ++ tailWord_863160).sum := by decide
  have hdescent : baseEnd_863160 < baseStart_863160 := by decide
  rcases family_descends (prefixWord ++ tailWord_863160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863222 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_863222 : Nat := 118140960795 + 863222 * 2 ^ 59
def prefixEnd_863222 : Nat := 4983230072969 + 3 ^ 40 * 863222 * 2
def baseEnd_863222 : Nat := 196999021126900832735609

theorem tailTrace_863222 : CollatzResearch.WordTrace tailWord_863222 prefixEnd_863222 196999021126900832735609 := by
  unfold tailWord_863222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967768304918849714092495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20989528585801063616986613 1967768304918849714092495)
  ·
    refine ⟨2951652457378274571138743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1967768304918849714092495 2951652457378274571138743)
    ·
      refine ⟨4427478686067411856708115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2951652457378274571138743 4427478686067411856708115)
      ·
        refine ⟨6641218029101117785062173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4427478686067411856708115 6641218029101117785062173)
        ·
          refine ⟨2490456760912919169398315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6641218029101117785062173 2490456760912919169398315)
          ·
            refine ⟨3735685141369378754097473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2490456760912919169398315 3735685141369378754097473)
            ·
              refine ⟨2801763856027034065573105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3735685141369378754097473 2801763856027034065573105)
              ·
                refine ⟨2101322892020275549179829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2801763856027034065573105 2101322892020275549179829)
                ·
                  refine ⟨196999021126900832735609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2101322892020275549179829 196999021126900832735609)
                  ·
                    rfl

theorem cell21_863222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_863222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863222 prefixEnd_863222 := by exact prefixLift 863222
  have htrace : WordTrace (prefixWord ++ tailWord_863222) baseStart_863222 baseEnd_863222 := by
    simpa [prefixWord, tailWord_863222, baseEnd_863222] using wordTrace_append hprefix tailTrace_863222
  have hstable : (prefixWord ++ tailWord_863222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863222).length < 2 ^ (prefixWord ++ tailWord_863222).sum := by decide
  have hdescent : baseEnd_863222 < baseStart_863222 := by decide
  rcases family_descends (prefixWord ++ tailWord_863222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863318 : List Nat := [5, 2, 2, 1, 3, 1, 1, 6]
def baseStart_863318 : Nat := 118140960795 + 863318 * 2 ^ 59
def prefixEnd_863318 : Nat := 4983230072969 + 3 ^ 40 * 863318 * 2
def baseEnd_863318 : Nat := 65673643211608666378471

theorem tailTrace_863318 : CollatzResearch.WordTrace tailWord_863318 prefixEnd_863318 65673643211608666378471 := by
  unfold tailWord_863318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967987142897112738810913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20991862857569202547316405 1967987142897112738810913)
  ·
    refine ⟨1475990357172834554108185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1967987142897112738810913 1475990357172834554108185)
    ·
      refine ⟨1106992767879625915581139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1475990357172834554108185 1106992767879625915581139)
      ·
        refine ⟨1660489151819438873371709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1106992767879625915581139 1660489151819438873371709)
        ·
          refine ⟨622683431932289577514391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1660489151819438873371709 622683431932289577514391)
          ·
            refine ⟨934025147898434366271587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622683431932289577514391 934025147898434366271587)
            ·
              refine ⟨1401037721847651549407381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934025147898434366271587 1401037721847651549407381)
              ·
                refine ⟨65673643211608666378471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1401037721847651549407381 65673643211608666378471)
                ·
                  rfl

theorem cell21_863318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_863318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863318 prefixEnd_863318 := by exact prefixLift 863318
  have htrace : WordTrace (prefixWord ++ tailWord_863318) baseStart_863318 baseEnd_863318 := by
    simpa [prefixWord, tailWord_863318, baseEnd_863318] using wordTrace_append hprefix tailTrace_863318
  have hstable : (prefixWord ++ tailWord_863318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863318).length < 2 ^ (prefixWord ++ tailWord_863318).sum := by decide
  have hdescent : baseEnd_863318 < baseStart_863318 := by decide
  rcases family_descends (prefixWord ++ tailWord_863318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863374 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_863374 : Nat := 118140960795 + 863374 * 2 ^ 59
def prefixEnd_863374 : Nat := 4983230072969 + 3 ^ 40 * 863374 * 2
def baseEnd_863374 : Nat := 197033709597782346201965

theorem tailTrace_863374 : CollatzResearch.WordTrace tailWord_863374 prefixEnd_863374 197033709597782346201965 := by
  unfold tailWord_863374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936229596768865673126647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20993224516100616923342117 3936229596768865673126647)
  ·
    refine ⟨5904344395153298509689971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3936229596768865673126647 5904344395153298509689971)
    ·
      refine ⟨8856516592729947764534957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5904344395153298509689971 8856516592729947764534957)
      ·
        refine ⟨3321193722273730411700609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8856516592729947764534957 3321193722273730411700609)
        ·
          refine ⟨2490895291705297808775457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3321193722273730411700609 2490895291705297808775457)
          ·
            refine ⟨1868171468778973356581593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2490895291705297808775457 1868171468778973356581593)
            ·
              refine ⟨1401128601584230017436195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1868171468778973356581593 1401128601584230017436195)
              ·
                refine ⟨2101692902376345026154293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1401128601584230017436195 2101692902376345026154293)
                ·
                  refine ⟨197033709597782346201965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2101692902376345026154293 197033709597782346201965)
                  ·
                    rfl

theorem cell21_863374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_863374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863374 prefixEnd_863374 := by exact prefixLift 863374
  have htrace : WordTrace (prefixWord ++ tailWord_863374) baseStart_863374 baseEnd_863374 := by
    simpa [prefixWord, tailWord_863374, baseEnd_863374] using wordTrace_append hprefix tailTrace_863374
  have hstable : (prefixWord ++ tailWord_863374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863374).length < 2 ^ (prefixWord ++ tailWord_863374).sum := by decide
  have hdescent : baseEnd_863374 < baseStart_863374 := by decide
  rcases family_descends (prefixWord ++ tailWord_863374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863484 : List Nat := [2, 2, 2, 1, 5, 2, 2, 2, 3]
def baseStart_863484 : Nat := 118140960795 + 863484 * 2 ^ 59
def prefixEnd_863484 : Nat := 4983230072969 + 3 ^ 40 * 863484 * 2
def baseEnd_863484 : Nat := 197058813096446599368407

theorem tailTrace_863484 : CollatzResearch.WordTrace tailWord_863484 prefixEnd_863484 197058813096446599368407 := by
  unfold tailWord_863484
  simp only [CollatzResearch.WordTrace]
  refine ⟨15746924401876207085758753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20995899202501609447678337 15746924401876207085758753)
  ·
    refine ⟨11810193301407155314319065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15746924401876207085758753 11810193301407155314319065)
    ·
      refine ⟨8857644976055366485739299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11810193301407155314319065 8857644976055366485739299)
      ·
        refine ⟨13286467464083049728608949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8857644976055366485739299 13286467464083049728608949)
        ·
          refine ⟨1245606324757785912057089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13286467464083049728608949 1245606324757785912057089)
          ·
            refine ⟨934204743568339434042817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1245606324757785912057089 934204743568339434042817)
            ·
              refine ⟨700653557676254575532113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934204743568339434042817 700653557676254575532113)
              ·
                refine ⟨525490168257190931649085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 700653557676254575532113 525490168257190931649085)
                ·
                  refine ⟨197058813096446599368407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525490168257190931649085 197058813096446599368407)
                  ·
                    rfl

theorem cell21_863484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_863484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863484 prefixEnd_863484 := by exact prefixLift 863484
  have htrace : WordTrace (prefixWord ++ tailWord_863484) baseStart_863484 baseEnd_863484 := by
    simpa [prefixWord, tailWord_863484, baseEnd_863484] using wordTrace_append hprefix tailTrace_863484
  have hstable : (prefixWord ++ tailWord_863484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863484).length < 2 ^ (prefixWord ++ tailWord_863484).sum := by decide
  have hdescent : baseEnd_863484 < baseStart_863484 := by decide
  rcases family_descends (prefixWord ++ tailWord_863484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863540 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_863540 : Nat := 118140960795 + 863540 * 2 ^ 59
def prefixEnd_863540 : Nat := 4983230072969 + 3 ^ 40 * 863540 * 2
def baseEnd_863540 : Nat := 197071593059402946434959

theorem tailTrace_863540 : CollatzResearch.WordTrace tailWord_863540 prefixEnd_863540 197071593059402946434959 := by
  unfold tailWord_863540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15747945645774767867778037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20997260861033023823704049 15747945645774767867778037)
  ·
    refine ⟨1476369904291384487604191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15747945645774767867778037 1476369904291384487604191)
    ·
      refine ⟨2214554856437076731406287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476369904291384487604191 2214554856437076731406287)
      ·
        refine ⟨3321832284655615097109431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2214554856437076731406287 3321832284655615097109431)
        ·
          refine ⟨4982748426983422645664147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3321832284655615097109431 4982748426983422645664147)
          ·
            refine ⟨7474122640475133968496221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4982748426983422645664147 7474122640475133968496221)
            ·
              refine ⟨2802795990178175238186083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7474122640475133968496221 2802795990178175238186083)
              ·
                refine ⟨4204193985267262857279125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2802795990178175238186083 4204193985267262857279125)
                ·
                  refine ⟨197071593059402946434959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4204193985267262857279125 197071593059402946434959)
                  ·
                    rfl

theorem cell21_863540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_863540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863540 prefixEnd_863540 := by exact prefixLift 863540
  have htrace : WordTrace (prefixWord ++ tailWord_863540) baseStart_863540 baseEnd_863540 := by
    simpa [prefixWord, tailWord_863540, baseEnd_863540] using wordTrace_append hprefix tailTrace_863540
  have hstable : (prefixWord ++ tailWord_863540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863540).length < 2 ^ (prefixWord ++ tailWord_863540).sum := by decide
  have hdescent : baseEnd_863540 < baseStart_863540 := by decide
  rcases family_descends (prefixWord ++ tailWord_863540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863568 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_863568 : Nat := 118140960795 + 863568 * 2 ^ 59
def prefixEnd_863568 : Nat := 4983230072969 + 3 ^ 40 * 863568 * 2
def baseEnd_863568 : Nat := 197077983040881119968235

theorem tailTrace_863568 : CollatzResearch.WordTrace tailWord_863568 prefixEnd_863568 197077983040881119968235 := by
  unfold tailWord_863568
  simp only [CollatzResearch.WordTrace]
  refine ⟨15748456267724048258787679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20997941690298731011716905 15748456267724048258787679)
  ·
    refine ⟨23622684401586072388181519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15748456267724048258787679 23622684401586072388181519)
    ·
      refine ⟨35434026602379108582272279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23622684401586072388181519 35434026602379108582272279)
      ·
        refine ⟨53151039903568662873408419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35434026602379108582272279 53151039903568662873408419)
        ·
          refine ⟨79726559855352994310112629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53151039903568662873408419 79726559855352994310112629)
          ·
            refine ⟨7474364986439343216573059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79726559855352994310112629 7474364986439343216573059)
            ·
              refine ⟨11211547479659014824859589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7474364986439343216573059 11211547479659014824859589)
              ·
                refine ⟨2102165152436065279661173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11211547479659014824859589 2102165152436065279661173)
                ·
                  refine ⟨197077983040881119968235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2102165152436065279661173 197077983040881119968235)
                  ·
                    rfl

theorem cell21_863568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_863568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863568 prefixEnd_863568 := by exact prefixLift 863568
  have htrace : WordTrace (prefixWord ++ tailWord_863568) baseStart_863568 baseEnd_863568 := by
    simpa [prefixWord, tailWord_863568, baseEnd_863568] using wordTrace_append hprefix tailTrace_863568
  have hstable : (prefixWord ++ tailWord_863568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863568).length < 2 ^ (prefixWord ++ tailWord_863568).sum := by decide
  have hdescent : baseEnd_863568 < baseStart_863568 := by decide
  rcases family_descends (prefixWord ++ tailWord_863568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863599 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 4]
def baseStart_863599 : Nat := 118140960795 + 863599 * 2 ^ 59
def prefixEnd_863599 : Nat := 4983230072969 + 3 ^ 40 * 863599 * 2
def baseEnd_863599 : Nat := 197085057663231954951505

theorem tailTrace_863599 : CollatzResearch.WordTrace tailWord_863599 prefixEnd_863599 197085057663231954951505 := by
  unfold tailWord_863599
  simp only [CollatzResearch.WordTrace]
  refine ⟨31498043198335788811953851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20998695465557192541302567 31498043198335788811953851)
  ·
    refine ⟨47247064797503683217930777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31498043198335788811953851 47247064797503683217930777)
    ·
      refine ⟨35435298598127762413448083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47247064797503683217930777 35435298598127762413448083)
      ·
        refine ⟨53152947897191643620172125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35435298598127762413448083 53152947897191643620172125)
        ·
          refine ⟨19932355461446866357564547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53152947897191643620172125 19932355461446866357564547)
          ·
            refine ⟨29898533192170299536346821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19932355461446866357564547 29898533192170299536346821)
            ·
              refine ⟨5605974973531931163065029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29898533192170299536346821 5605974973531931163065029)
              ·
                refine ⟨1051120307537237093074693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5605974973531931163065029 1051120307537237093074693)
                ·
                  refine ⟨197085057663231954951505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051120307537237093074693 197085057663231954951505)
                  ·
                    rfl

theorem cell21_863599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 4].length) (baseStart_863599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863599 prefixEnd_863599 := by exact prefixLift 863599
  have htrace : WordTrace (prefixWord ++ tailWord_863599) baseStart_863599 baseEnd_863599 := by
    simpa [prefixWord, tailWord_863599, baseEnd_863599] using wordTrace_append hprefix tailTrace_863599
  have hstable : (prefixWord ++ tailWord_863599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863599).length < 2 ^ (prefixWord ++ tailWord_863599).sum := by decide
  have hdescent : baseEnd_863599 < baseStart_863599 := by decide
  rcases family_descends (prefixWord ++ tailWord_863599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863709 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 4]
def baseStart_863709 : Nat := 118140960795 + 863709 * 2 ^ 59
def prefixEnd_863709 : Nat := 4983230072969 + 3 ^ 40 * 863709 * 2
def baseEnd_863709 : Nat := 197110161161896208117947

theorem tailTrace_863709 : CollatzResearch.WordTrace tailWord_863709 prefixEnd_863709 197110161161896208117947 := by
  unfold tailWord_863709
  simp only [CollatzResearch.WordTrace]
  refine ⟨31502055227937277598458181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21001370151958185065638787 31502055227937277598458181)
  ·
    refine ⟨5906635355238239549710909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31502055227937277598458181 5906635355238239549710909)
    ·
      refine ⟨2214988258214339831141591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5906635355238239549710909 2214988258214339831141591)
      ·
        refine ⟨3322482387321509746712387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2214988258214339831141591 3322482387321509746712387)
        ·
          refine ⟨4983723580982264620068581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322482387321509746712387 4983723580982264620068581)
          ·
            refine ⟨934448171434174616262859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4983723580982264620068581 934448171434174616262859)
            ·
              refine ⟨1401672257151261924394289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934448171434174616262859 1401672257151261924394289)
              ·
                refine ⟨1051254192863446443295717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1401672257151261924394289 1051254192863446443295717)
                ·
                  refine ⟨197110161161896208117947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051254192863446443295717 197110161161896208117947)
                  ·
                    rfl

theorem cell21_863709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_863709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863709 prefixEnd_863709 := by exact prefixLift 863709
  have htrace : WordTrace (prefixWord ++ tailWord_863709) baseStart_863709 baseEnd_863709 := by
    simpa [prefixWord, tailWord_863709, baseEnd_863709] using wordTrace_append hprefix tailTrace_863709
  have hstable : (prefixWord ++ tailWord_863709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863709).length < 2 ^ (prefixWord ++ tailWord_863709).sum := by decide
  have hdescent : baseEnd_863709 < baseStart_863709 := by decide
  rcases family_descends (prefixWord ++ tailWord_863709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863751 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 6]
def baseStart_863751 : Nat := 118140960795 + 863751 * 2 ^ 59
def prefixEnd_863751 : Nat := 4983230072969 + 3 ^ 40 * 863751 * 2
def baseEnd_863751 : Nat := 197119746134113468417861

theorem tailTrace_863751 : CollatzResearch.WordTrace tailWord_863751 prefixEnd_863751 197119746134113468417861 := by
  unfold tailWord_863751
  simp only [CollatzResearch.WordTrace]
  refine ⟨31503587093785118771487107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21002391395856745847658071 31503587093785118771487107)
  ·
    refine ⟨47255380640677678157230661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31503587093785118771487107 47255380640677678157230661)
    ·
      refine ⟨8860383870127064654480749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47255380640677678157230661 8860383870127064654480749)
      ·
        refine ⟨3322643951297649245430281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8860383870127064654480749 3322643951297649245430281)
        ·
          refine ⟨2491982963473236934072711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3322643951297649245430281 2491982963473236934072711)
          ·
            refine ⟨3737974445209855401109067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491982963473236934072711 3737974445209855401109067)
            ·
              refine ⟨5606961667814783101663601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3737974445209855401109067 5606961667814783101663601)
              ·
                refine ⟨4205221250861087326247701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5606961667814783101663601 4205221250861087326247701)
                ·
                  refine ⟨197119746134113468417861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4205221250861087326247701 197119746134113468417861)
                  ·
                    rfl

theorem cell21_863751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 6].length) (baseStart_863751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863751 prefixEnd_863751 := by exact prefixLift 863751
  have htrace : WordTrace (prefixWord ++ tailWord_863751) baseStart_863751 baseEnd_863751 := by
    simpa [prefixWord, tailWord_863751, baseEnd_863751] using wordTrace_append hprefix tailTrace_863751
  have hstable : (prefixWord ++ tailWord_863751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863751).length < 2 ^ (prefixWord ++ tailWord_863751).sum := by decide
  have hdescent : baseEnd_863751 < baseStart_863751 := by decide
  rcases family_descends (prefixWord ++ tailWord_863751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863754 : List Nat := [3, 1, 2, 2, 2, 2, 3, 3, 3]
def baseStart_863754 : Nat := 118140960795 + 863754 * 2 ^ 59
def prefixEnd_863754 : Nat := 4983230072969 + 3 ^ 40 * 863754 * 2
def baseEnd_863754 : Nat := 197120430774986129867855

theorem tailTrace_863754 : CollatzResearch.WordTrace tailWord_863754 prefixEnd_863754 197120430774986129867855 := by
  unfold tailWord_863754
  simp only [CollatzResearch.WordTrace]
  refine ⟨7875924128193562570961579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21002464341849500189230877 7875924128193562570961579)
  ·
    refine ⟨11813886192290343856442369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7875924128193562570961579 11813886192290343856442369)
    ·
      refine ⟨8860414644217757892331777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11813886192290343856442369 8860414644217757892331777)
      ·
        refine ⟨6645310983163318419248833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8860414644217757892331777 6645310983163318419248833)
        ·
          refine ⟨4983983237372488814436625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6645310983163318419248833 4983983237372488814436625)
          ·
            refine ⟨3737987428029366610827469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4983983237372488814436625 3737987428029366610827469)
            ·
              refine ⟨1401745285511012479060301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3737987428029366610827469 1401745285511012479060301)
              ·
                refine ⟨525654482066629679647613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1401745285511012479060301 525654482066629679647613)
                ·
                  refine ⟨197120430774986129867855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525654482066629679647613 197120430774986129867855)
                  ·
                    rfl

theorem cell21_863754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_863754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863754 prefixEnd_863754 := by exact prefixLift 863754
  have htrace : WordTrace (prefixWord ++ tailWord_863754) baseStart_863754 baseEnd_863754 := by
    simpa [prefixWord, tailWord_863754, baseEnd_863754] using wordTrace_append hprefix tailTrace_863754
  have hstable : (prefixWord ++ tailWord_863754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863754).length < 2 ^ (prefixWord ++ tailWord_863754).sum := by decide
  have hdescent : baseEnd_863754 < baseStart_863754 := by decide
  rcases family_descends (prefixWord ++ tailWord_863754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863757 : List Nat := [1, 7, 1, 1, 3, 1, 7]
def baseStart_863757 : Nat := 118140960795 + 863757 * 2 ^ 59
def prefixEnd_863757 : Nat := 4983230072969 + 3 ^ 40 * 863757 * 2
def baseEnd_863757 : Nat := 21902346157317643479761

theorem tailTrace_863757 : CollatzResearch.WordTrace tailWord_863757 prefixEnd_863757 21902346157317643479761 := by
  unfold tailWord_863757
  simp only [CollatzResearch.WordTrace]
  refine ⟨31503805931763381796205525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21002537287842254530803683 31503805931763381796205525)
  ·
    refine ⟨738370451525704260848567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31503805931763381796205525 738370451525704260848567)
    ·
      refine ⟨1107555677288556391272851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738370451525704260848567 1107555677288556391272851)
      ·
        refine ⟨1661333515932834586909277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107555677288556391272851 1661333515932834586909277)
        ·
          refine ⟨623000068474812970090979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1661333515932834586909277 623000068474812970090979)
          ·
            refine ⟨934500102712219455136469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623000068474812970090979 934500102712219455136469)
            ·
              refine ⟨21902346157317643479761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 934500102712219455136469 21902346157317643479761)
              ·
                rfl

theorem cell21_863757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 7].length) (baseStart_863757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863757 prefixEnd_863757 := by exact prefixLift 863757
  have htrace : WordTrace (prefixWord ++ tailWord_863757) baseStart_863757 baseEnd_863757 := by
    simpa [prefixWord, tailWord_863757, baseEnd_863757] using wordTrace_append hprefix tailTrace_863757
  have hstable : (prefixWord ++ tailWord_863757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863757).length < 2 ^ (prefixWord ++ tailWord_863757).sum := by decide
  have hdescent : baseEnd_863757 < baseStart_863757 := by decide
  rcases family_descends (prefixWord ++ tailWord_863757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863765 : List Nat := [1, 3, 2, 1, 3, 2, 9]
def baseStart_863765 : Nat := 118140960795 + 863765 * 2 ^ 59
def prefixEnd_863765 : Nat := 4983230072969 + 3 ^ 40 * 863765 * 2
def baseEnd_863765 : Nat := 21902549013872506131611

theorem tailTrace_863765 : CollatzResearch.WordTrace tailWord_863765 prefixEnd_863765 21902549013872506131611 := by
  unfold tailWord_863765
  simp only [CollatzResearch.WordTrace]
  refine ⟨31504097715734399162496749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21002731810489599441664499 31504097715734399162496749)
  ·
    refine ⟨11814036643400399685936281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31504097715734399162496749 11814036643400399685936281)
    ·
      refine ⟨8860527482550299764452211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11814036643400399685936281 8860527482550299764452211)
      ·
        refine ⟨13290791223825449646678317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8860527482550299764452211 13290791223825449646678317)
        ·
          refine ⟨4984046708934543617504369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13290791223825449646678317 4984046708934543617504369)
          ·
            refine ⟨3738035031700907713128277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4984046708934543617504369 3738035031700907713128277)
            ·
              refine ⟨21902549013872506131611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3738035031700907713128277 21902549013872506131611)
              ·
                rfl

theorem cell21_863765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 9].length) (baseStart_863765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863765 prefixEnd_863765 := by exact prefixLift 863765
  have htrace : WordTrace (prefixWord ++ tailWord_863765) baseStart_863765 baseEnd_863765 := by
    simpa [prefixWord, tailWord_863765, baseEnd_863765] using wordTrace_append hprefix tailTrace_863765
  have hstable : (prefixWord ++ tailWord_863765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863765).length < 2 ^ (prefixWord ++ tailWord_863765).sum := by decide
  have hdescent : baseEnd_863765 < baseStart_863765 := by decide
  rcases family_descends (prefixWord ++ tailWord_863765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863813 : List Nat := [1, 3, 1, 1, 1, 4, 2, 5, 3]
def baseStart_863813 : Nat := 118140960795 + 863813 * 2 ^ 59
def prefixEnd_863813 : Nat := 4983230072969 + 3 ^ 40 * 863813 * 2
def baseEnd_863813 : Nat := 197133895378815138384401

theorem tailTrace_863813 : CollatzResearch.WordTrace tailWord_863813 prefixEnd_863813 197133895378815138384401 := by
  unfold tailWord_863813
  simp only [CollatzResearch.WordTrace]
  refine ⟨31505848419560503360244093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21003898946373668906829395 31505848419560503360244093)
  ·
    refine ⟨11814693157335188760091535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31505848419560503360244093 11814693157335188760091535)
    ·
      refine ⟨17722039736002783140137303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11814693157335188760091535 17722039736002783140137303)
      ·
        refine ⟨26583059604004174710205955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17722039736002783140137303 26583059604004174710205955)
        ·
          refine ⟨39874589406006262065308933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26583059604004174710205955 39874589406006262065308933)
          ·
            refine ⟨7476485513626174137245425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39874589406006262065308933 7476485513626174137245425)
            ·
              refine ⟨5607364135219630602934069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7476485513626174137245425 5607364135219630602934069)
              ·
                refine ⟨525690387676840369025069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5607364135219630602934069 525690387676840369025069)
                ·
                  refine ⟨197133895378815138384401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525690387676840369025069 197133895378815138384401)
                  ·
                    rfl

theorem cell21_863813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_863813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863813 prefixEnd_863813 := by exact prefixLift 863813
  have htrace : WordTrace (prefixWord ++ tailWord_863813) baseStart_863813 baseEnd_863813 := by
    simpa [prefixWord, tailWord_863813, baseEnd_863813] using wordTrace_append hprefix tailTrace_863813
  have hstable : (prefixWord ++ tailWord_863813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863813).length < 2 ^ (prefixWord ++ tailWord_863813).sum := by decide
  have hdescent : baseEnd_863813 < baseStart_863813 := by decide
  rcases family_descends (prefixWord ++ tailWord_863813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863931 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 7]
def baseStart_863931 : Nat := 118140960795 + 863931 * 2 ^ 59
def prefixEnd_863931 : Nat := 4983230072969 + 3 ^ 40 * 863931 * 2
def baseEnd_863931 : Nat := 197160824586473155417493

theorem tailTrace_863931 : CollatzResearch.WordTrace tailWord_863931 prefixEnd_863931 197160824586473155417493 := by
  unfold tailWord_863931
  simp only [CollatzResearch.WordTrace]
  refine ⟨31510152233133009513039647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21006768155422006342026431 31510152233133009513039647)
  ·
    refine ⟨47265228349699514269559471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31510152233133009513039647 47265228349699514269559471)
    ·
      refine ⟨70897842524549271404339207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47265228349699514269559471 70897842524549271404339207)
      ·
        refine ⟨106346763786823907106508811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70897842524549271404339207 106346763786823907106508811)
        ·
          refine ⟨159520145680235860659763217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106346763786823907106508811 159520145680235860659763217)
          ·
            refine ⟨119640109260176895494822413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159520145680235860659763217 119640109260176895494822413)
            ·
              refine ⟨44865040972566335810558405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119640109260176895494822413 44865040972566335810558405)
              ·
                refine ⟨8412195182356187964479701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44865040972566335810558405 8412195182356187964479701)
                ·
                  refine ⟨197160824586473155417493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8412195182356187964479701 197160824586473155417493)
                  ·
                    rfl

theorem cell21_863931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 7].length) (baseStart_863931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863931 prefixEnd_863931 := by exact prefixLift 863931
  have htrace : WordTrace (prefixWord ++ tailWord_863931) baseStart_863931 baseEnd_863931 := by
    simpa [prefixWord, tailWord_863931, baseEnd_863931] using wordTrace_append hprefix tailTrace_863931
  have hstable : (prefixWord ++ tailWord_863931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863931).length < 2 ^ (prefixWord ++ tailWord_863931).sum := by decide
  have hdescent : baseEnd_863931 < baseStart_863931 := by decide
  rcases family_descends (prefixWord ++ tailWord_863931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863934 : List Nat := [4, 2, 1, 1, 2, 4, 7]
def baseStart_863934 : Nat := 118140960795 + 863934 * 2 ^ 59
def prefixEnd_863934 : Nat := 4983230072969 + 3 ^ 40 * 863934 * 2
def baseEnd_863934 : Nat := 21906834358593979651943

theorem tailTrace_863934 : CollatzResearch.WordTrace tailWord_863934 prefixEnd_863934 21906834358593979651943 := by
  unfold tailWord_863934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3938782706515267628174857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21006841101414760683599237 3938782706515267628174857)
  ·
    refine ⟨2954087029886450721131143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3938782706515267628174857 2954087029886450721131143)
    ·
      refine ⟨4431130544829676081696715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2954087029886450721131143 4431130544829676081696715)
      ·
        refine ⟨6646695817244514122545073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4431130544829676081696715 6646695817244514122545073)
        ·
          refine ⟨4985021862933385591908805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6646695817244514122545073 4985021862933385591908805)
          ·
            refine ⟨934691599300009798482901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4985021862933385591908805 934691599300009798482901)
            ·
              refine ⟨21906834358593979651943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 934691599300009798482901 21906834358593979651943)
              ·
                rfl

theorem cell21_863934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 7].length) (baseStart_863934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_863934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_863934 prefixEnd_863934 := by exact prefixLift 863934
  have htrace : WordTrace (prefixWord ++ tailWord_863934) baseStart_863934 baseEnd_863934 := by
    simpa [prefixWord, tailWord_863934, baseEnd_863934] using wordTrace_append hprefix tailTrace_863934
  have hstable : (prefixWord ++ tailWord_863934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863934).length < 2 ^ (prefixWord ++ tailWord_863934).sum := by decide
  have hdescent : baseEnd_863934 < baseStart_863934 := by decide
  rcases family_descends (prefixWord ++ tailWord_863934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864010 : List Nat := [3, 1, 2, 2, 1, 5, 1, 6]
def baseStart_864010 : Nat := 118140960795 + 864010 * 2 ^ 59
def prefixEnd_864010 : Nat := 4983230072969 + 3 ^ 40 * 864010 * 2
def baseEnd_864010 : Nat := 65726284487595524533555

theorem tailTrace_864010 : CollatzResearch.WordTrace tailWord_864010 prefixEnd_864010 65726284487595524533555 := by
  unfold tailWord_864010
  simp only [CollatzResearch.WordTrace]
  refine ⟨7878258399961701501291371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21008689066564537336776989 7878258399961701501291371)
  ·
    refine ⟨11817387599942552251937057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7878258399961701501291371 11817387599942552251937057)
    ·
      refine ⟨8863040699956914188952793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11817387599942552251937057 8863040699956914188952793)
      ·
        refine ⟨6647280524967685641714595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8863040699956914188952793 6647280524967685641714595)
        ·
          refine ⟨9970920787451528462571893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6647280524967685641714595 9970920787451528462571893)
          ·
            refine ⟨934773823823580793366115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9970920787451528462571893 934773823823580793366115)
            ·
              refine ⟨1402160735735371190049173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934773823823580793366115 1402160735735371190049173)
              ·
                refine ⟨65726284487595524533555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1402160735735371190049173 65726284487595524533555)
                ·
                  rfl

theorem cell21_864010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_864010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864010 prefixEnd_864010 := by exact prefixLift 864010
  have htrace : WordTrace (prefixWord ++ tailWord_864010) baseStart_864010 baseEnd_864010 := by
    simpa [prefixWord, tailWord_864010, baseEnd_864010] using wordTrace_append hprefix tailTrace_864010
  have hstable : (prefixWord ++ tailWord_864010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864010).length < 2 ^ (prefixWord ++ tailWord_864010).sum := by decide
  have hdescent : baseEnd_864010 < baseStart_864010 := by decide
  rcases family_descends (prefixWord ++ tailWord_864010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864072 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 4]
def baseStart_864072 : Nat := 118140960795 + 864072 * 2 ^ 59
def prefixEnd_864072 : Nat := 4983230072969 + 3 ^ 40 * 864072 * 2
def baseEnd_864072 : Nat := 197193002707488243567205

theorem tailTrace_864072 : CollatzResearch.WordTrace tailWord_864072 prefixEnd_864072 197193002707488243567205 := by
  unfold tailWord_864072
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757647462811095296961235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21010196617081460395948313 15757647462811095296961235)
  ·
    refine ⟨23636471194216642945441853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15757647462811095296961235 23636471194216642945441853)
    ·
      refine ⟨8863676697831241104540695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23636471194216642945441853 8863676697831241104540695)
      ·
        refine ⟨13295515046746861656811043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8863676697831241104540695 13295515046746861656811043)
        ·
          refine ⟨19943272570120292485216565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13295515046746861656811043 19943272570120292485216565)
          ·
            refine ⟨1869681803448777420489053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19943272570120292485216565 1869681803448777420489053)
            ·
              refine ⟨701130676293291532683395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1869681803448777420489053 701130676293291532683395)
              ·
                refine ⟨1051696014439937299025093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701130676293291532683395 1051696014439937299025093)
                ·
                  refine ⟨197193002707488243567205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051696014439937299025093 197193002707488243567205)
                  ·
                    rfl

theorem cell21_864072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_864072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864072 prefixEnd_864072 := by exact prefixLift 864072
  have htrace : WordTrace (prefixWord ++ tailWord_864072) baseStart_864072 baseEnd_864072 := by
    simpa [prefixWord, tailWord_864072, baseEnd_864072] using wordTrace_append hprefix tailTrace_864072
  have hstable : (prefixWord ++ tailWord_864072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864072).length < 2 ^ (prefixWord ++ tailWord_864072).sum := by decide
  have hdescent : baseEnd_864072 < baseStart_864072 := by decide
  rcases family_descends (prefixWord ++ tailWord_864072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864092 : List Nat := [2, 2, 4, 2, 3, 1, 1, 3, 3]
def baseStart_864092 : Nat := 118140960795 + 864092 * 2 ^ 59
def prefixEnd_864092 : Nat := 4983230072969 + 3 ^ 40 * 864092 * 2
def baseEnd_864092 : Nat := 197197566979972653233831

theorem tailTrace_864092 : CollatzResearch.WordTrace tailWord_864092 prefixEnd_864092 197197566979972653233831 := by
  unfold tailWord_864092
  simp only [CollatzResearch.WordTrace]
  refine ⟨15758012192774867004825265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21010682923699822673100353 15758012192774867004825265)
  ·
    refine ⟨11818509144581150253618949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15758012192774867004825265 11818509144581150253618949)
    ·
      refine ⟨2215970464608965672553553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11818509144581150253618949 2215970464608965672553553)
      ·
        refine ⟨1661977848456724254415165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2215970464608965672553553 1661977848456724254415165)
        ·
          refine ⟨623241693171271595405687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1661977848456724254415165 623241693171271595405687)
          ·
            refine ⟨934862539756907393108531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623241693171271595405687 934862539756907393108531)
            ·
              refine ⟨1402293809635361089662797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934862539756907393108531 1402293809635361089662797)
              ·
                refine ⟨525860178613260408623549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1402293809635361089662797 525860178613260408623549)
                ·
                  refine ⟨197197566979972653233831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 525860178613260408623549 197197566979972653233831)
                  ·
                    rfl

theorem cell21_864092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_864092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864092 prefixEnd_864092 := by exact prefixLift 864092
  have htrace : WordTrace (prefixWord ++ tailWord_864092) baseStart_864092 baseEnd_864092 := by
    simpa [prefixWord, tailWord_864092, baseEnd_864092] using wordTrace_append hprefix tailTrace_864092
  have hstable : (prefixWord ++ tailWord_864092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864092).length < 2 ^ (prefixWord ++ tailWord_864092).sum := by decide
  have hdescent : baseEnd_864092 < baseStart_864092 := by decide
  rcases family_descends (prefixWord ++ tailWord_864092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864131 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 4]
def baseStart_864131 : Nat := 118140960795 + 864131 * 2 ^ 59
def prefixEnd_864131 : Nat := 4983230072969 + 3 ^ 40 * 864131 * 2
def baseEnd_864131 : Nat := 197206467311317252083751

theorem tailTrace_864131 : CollatzResearch.WordTrace tailWord_864131 prefixEnd_864131 197206467311317252083751 := by
  unfold tailWord_864131
  simp only [CollatzResearch.WordTrace]
  refine ⟨31517446832408443670320247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21011631221605629113546831 31517446832408443670320247)
  ·
    refine ⟨47276170248612665505480371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31517446832408443670320247 47276170248612665505480371)
    ·
      refine ⟨70914255372918998258220557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47276170248612665505480371 70914255372918998258220557)
      ·
        refine ⟨26592845764844624346832709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70914255372918998258220557 26592845764844624346832709)
        ·
          refine ⟨4986158580908367065031133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26592845764844624346832709 4986158580908367065031133)
          ·
            refine ⟨1869809467840637649386675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4986158580908367065031133 1869809467840637649386675)
            ·
              refine ⟨2804714201760956474080013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1869809467840637649386675 2804714201760956474080013)
              ·
                refine ⟨1051767825660358677780005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2804714201760956474080013 1051767825660358677780005)
                ·
                  refine ⟨197206467311317252083751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1051767825660358677780005 197206467311317252083751)
                  ·
                    rfl

theorem cell21_864131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 4].length) (baseStart_864131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864131 prefixEnd_864131 := by exact prefixLift 864131
  have htrace : WordTrace (prefixWord ++ tailWord_864131) baseStart_864131 baseEnd_864131 := by
    simpa [prefixWord, tailWord_864131, baseEnd_864131] using wordTrace_append hprefix tailTrace_864131
  have hstable : (prefixWord ++ tailWord_864131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864131).length < 2 ^ (prefixWord ++ tailWord_864131).sum := by decide
  have hdescent : baseEnd_864131 < baseStart_864131 := by decide
  rcases family_descends (prefixWord ++ tailWord_864131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864162 : List Nat := [3, 3, 1, 2, 4, 8]
def baseStart_864162 : Nat := 118140960795 + 864162 * 2 ^ 59
def prefixEnd_864162 : Nat := 4983230072969 + 3 ^ 40 * 864162 * 2
def baseEnd_864162 : Nat := 7304205256802521743223

theorem tailTrace_864162 : CollatzResearch.WordTrace tailWord_864162 prefixEnd_864162 7304205256802521743223 := by
  unfold tailWord_864162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7879644373824033991174685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21012384996864090643132493 7879644373824033991174685)
  ·
    refine ⟨2954866640184012746690507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7879644373824033991174685 2954866640184012746690507)
    ·
      refine ⟨4432299960276019120035761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2954866640184012746690507 4432299960276019120035761)
      ·
        refine ⟨3324224970207014340026821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4432299960276019120035761 3324224970207014340026821)
        ·
          refine ⟨623292181913815188755029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3324224970207014340026821 623292181913815188755029)
          ·
            refine ⟨7304205256802521743223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 623292181913815188755029 7304205256802521743223)
            ·
              rfl

theorem cell21_864162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 8].length) (baseStart_864162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864162 prefixEnd_864162 := by exact prefixLift 864162
  have htrace : WordTrace (prefixWord ++ tailWord_864162) baseStart_864162 baseEnd_864162 := by
    simpa [prefixWord, tailWord_864162, baseEnd_864162] using wordTrace_append hprefix tailTrace_864162
  have hstable : (prefixWord ++ tailWord_864162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864162).length < 2 ^ (prefixWord ++ tailWord_864162).sum := by decide
  have hdescent : baseEnd_864162 < baseStart_864162 := by decide
  rcases family_descends (prefixWord ++ tailWord_864162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864311 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 5]
def baseStart_864311 : Nat := 118140960795 + 864311 * 2 ^ 59
def prefixEnd_864311 : Nat := 4983230072969 + 3 ^ 40 * 864311 * 2
def baseEnd_864311 : Nat := 197247545763676939083383

theorem tailTrace_864311 : CollatzResearch.WordTrace tailWord_864311 prefixEnd_864311 197247545763676939083383 := by
  unfold tailWord_864311
  simp only [CollatzResearch.WordTrace]
  refine ⟨31524011971756334411872787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21016007981170889607915191 31524011971756334411872787)
  ·
    refine ⟨47286017957634501617809181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31524011971756334411872787 47286017957634501617809181)
    ·
      refine ⟨17732256734112938106678443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47286017957634501617809181 17732256734112938106678443)
      ·
        refine ⟨26598385101169407160017665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17732256734112938106678443 26598385101169407160017665)
        ·
          refine ⟨19948788825877055370013249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26598385101169407160017665 19948788825877055370013249)
          ·
            refine ⟨14961591619407791527509937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19948788825877055370013249 14961591619407791527509937)
            ·
              refine ⟨11221193714555843645632453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14961591619407791527509937 11221193714555843645632453)
              ·
                refine ⟨2103973821479220683556085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11221193714555843645632453 2103973821479220683556085)
                ·
                  refine ⟨197247545763676939083383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2103973821479220683556085 197247545763676939083383)
                  ·
                    rfl

theorem cell21_864311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_864311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864311 prefixEnd_864311 := by exact prefixLift 864311
  have htrace : WordTrace (prefixWord ++ tailWord_864311) baseStart_864311 baseEnd_864311 := by
    simpa [prefixWord, tailWord_864311, baseEnd_864311] using wordTrace_append hprefix tailTrace_864311
  have hstable : (prefixWord ++ tailWord_864311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864311).length < 2 ^ (prefixWord ++ tailWord_864311).sum := by decide
  have hdescent : baseEnd_864311 < baseStart_864311 := by decide
  rcases family_descends (prefixWord ++ tailWord_864311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864469 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 4]
def baseStart_864469 : Nat := 118140960795 + 864469 * 2 ^ 59
def prefixEnd_864469 : Nat := 4983230072969 + 3 ^ 40 * 864469 * 2
def baseEnd_864469 : Nat := 197283603516303775449727

theorem tailTrace_864469 : CollatzResearch.WordTrace tailWord_864469 prefixEnd_864469 197283603516303775449727 := by
  unfold tailWord_864469
  simp only [CollatzResearch.WordTrace]
  refine ⟨31529774705183927396124461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21019849803455951597416307 31529774705183927396124461)
  ·
    refine ⟨11823665514443972773546673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31529774705183927396124461 11823665514443972773546673)
    ·
      refine ⟨8867749135832979580160005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11823665514443972773546673 8867749135832979580160005)
      ·
        refine ⟨1662702962968683671280001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8867749135832979580160005 1662702962968683671280001)
        ·
          refine ⟨1247027222226512753460001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1662702962968683671280001 1247027222226512753460001)
          ·
            refine ⟨935270416669884565095001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1247027222226512753460001 935270416669884565095001)
            ·
              refine ⟨701452812502413423821251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935270416669884565095001 701452812502413423821251)
              ·
                refine ⟨1052179218753620135731877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701452812502413423821251 1052179218753620135731877)
                ·
                  refine ⟨197283603516303775449727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1052179218753620135731877 197283603516303775449727)
                  ·
                    rfl

theorem cell21_864469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_864469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864469 prefixEnd_864469 := by exact prefixLift 864469
  have htrace : WordTrace (prefixWord ++ tailWord_864469) baseStart_864469 baseEnd_864469 := by
    simpa [prefixWord, tailWord_864469, baseEnd_864469] using wordTrace_append hprefix tailTrace_864469
  have hstable : (prefixWord ++ tailWord_864469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864469).length < 2 ^ (prefixWord ++ tailWord_864469).sum := by decide
  have hdescent : baseEnd_864469 < baseStart_864469 := by decide
  rcases family_descends (prefixWord ++ tailWord_864469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864508 : List Nat := [2, 2, 2, 1, 4, 10]
def baseStart_864508 : Nat := 118140960795 + 864508 * 2 ^ 59
def prefixEnd_864508 : Nat := 4983230072969 + 3 ^ 40 * 864508 * 2
def baseEnd_864508 : Nat := 7307129772135124974061

theorem tailTrace_864508 : CollatzResearch.WordTrace tailWord_864508 prefixEnd_864508 7307129772135124974061 := by
  unfold tailWord_864508
  simp only [CollatzResearch.WordTrace]
  refine ⟨15765598576021318528397089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21020798101361758037862785 15765598576021318528397089)
  ·
    refine ⟨11824198932015988896297817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15765598576021318528397089 11824198932015988896297817)
    ·
      refine ⟨8868149199011991672223363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11824198932015988896297817 8868149199011991672223363)
      ·
        refine ⟨13302223798517987508335045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8868149199011991672223363 13302223798517987508335045)
        ·
          refine ⟨2494166962222122657812821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13302223798517987508335045 2494166962222122657812821)
          ·
            refine ⟨7307129772135124974061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2494166962222122657812821 7307129772135124974061)
            ·
              rfl

theorem cell21_864508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 10].length) (baseStart_864508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864508 prefixEnd_864508 := by exact prefixLift 864508
  have htrace : WordTrace (prefixWord ++ tailWord_864508) baseStart_864508 baseEnd_864508 := by
    simpa [prefixWord, tailWord_864508, baseEnd_864508] using wordTrace_append hprefix tailTrace_864508
  have hstable : (prefixWord ++ tailWord_864508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864508).length < 2 ^ (prefixWord ++ tailWord_864508).sum := by decide
  have hdescent : baseEnd_864508 < baseStart_864508 := by decide
  rcases family_descends (prefixWord ++ tailWord_864508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864514 : List Nat := [3, 4, 1, 1, 2, 2, 1, 4, 3]
def baseStart_864514 : Nat := 118140960795 + 864514 * 2 ^ 59
def prefixEnd_864514 : Nat := 4983230072969 + 3 ^ 40 * 864514 * 2
def baseEnd_864514 : Nat := 197293873129393697199635

theorem tailTrace_864514 : CollatzResearch.WordTrace tailWord_864514 prefixEnd_864514 197293873129393697199635 := by
  unfold tailWord_864514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7882853997505225020378149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21020943993347266721008397 7882853997505225020378149)
  ·
    refine ⟨1478035124532229691320903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7882853997505225020378149 1478035124532229691320903)
    ·
      refine ⟨2217052686798344536981355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478035124532229691320903 2217052686798344536981355)
      ·
        refine ⟨3325579030197516805472033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217052686798344536981355 3325579030197516805472033)
        ·
          refine ⟨2494184272648137604104025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3325579030197516805472033 2494184272648137604104025)
          ·
            refine ⟨1870638204486103203078019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494184272648137604104025 1870638204486103203078019)
            ·
              refine ⟨2805957306729154804617029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870638204486103203078019 2805957306729154804617029)
              ·
                refine ⟨526116995011716525865693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2805957306729154804617029 526116995011716525865693)
                ·
                  refine ⟨197293873129393697199635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526116995011716525865693 197293873129393697199635)
                  ·
                    rfl

theorem cell21_864514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_864514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864514 prefixEnd_864514 := by exact prefixLift 864514
  have htrace : WordTrace (prefixWord ++ tailWord_864514) baseStart_864514 baseEnd_864514 := by
    simpa [prefixWord, tailWord_864514, baseEnd_864514] using wordTrace_append hprefix tailTrace_864514
  have hstable : (prefixWord ++ tailWord_864514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864514).length < 2 ^ (prefixWord ++ tailWord_864514).sum := by decide
  have hdescent : baseEnd_864514 < baseStart_864514 := by decide
  rcases family_descends (prefixWord ++ tailWord_864514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864556 : List Nat := [2, 2, 1, 1, 1, 3, 3, 5, 3]
def baseStart_864556 : Nat := 118140960795 + 864556 * 2 ^ 59
def prefixEnd_864556 : Nat := 4983230072969 + 3 ^ 40 * 864556 * 2
def baseEnd_864556 : Nat := 197303458101610957499549

theorem tailTrace_864556 : CollatzResearch.WordTrace tailWord_864556 prefixEnd_864556 197303458101610957499549 := by
  unfold tailWord_864556
  simp only [CollatzResearch.WordTrace]
  refine ⟨15766473927934370627270761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21021965237245827503027681 15766473927934370627270761)
  ·
    refine ⟨11824855445950777970453071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15766473927934370627270761 11824855445950777970453071)
    ·
      refine ⟨17737283168926166955679607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11824855445950777970453071 17737283168926166955679607)
      ·
        refine ⟨26605924753389250433519411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17737283168926166955679607 26605924753389250433519411)
        ·
          refine ⟨39908887130083875650279117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26605924753389250433519411 39908887130083875650279117)
          ·
            refine ⟨14965832673781453368854669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39908887130083875650279117 14965832673781453368854669)
            ·
              refine ⟨5612187252668045013320501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14965832673781453368854669 5612187252668045013320501)
              ·
                refine ⟨526142554937629219998797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5612187252668045013320501 526142554937629219998797)
                ·
                  refine ⟨197303458101610957499549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526142554937629219998797 197303458101610957499549)
                  ·
                    rfl

theorem cell21_864556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_864556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864556 prefixEnd_864556 := by exact prefixLift 864556
  have htrace : WordTrace (prefixWord ++ tailWord_864556) baseStart_864556 baseEnd_864556 := by
    simpa [prefixWord, tailWord_864556, baseEnd_864556] using wordTrace_append hprefix tailTrace_864556
  have hstable : (prefixWord ++ tailWord_864556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864556).length < 2 ^ (prefixWord ++ tailWord_864556).sum := by decide
  have hdescent : baseEnd_864556 < baseStart_864556 := by decide
  rcases family_descends (prefixWord ++ tailWord_864556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864570 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_864570 : Nat := 118140960795 + 864570 * 2 ^ 59
def prefixEnd_864570 : Nat := 4983230072969 + 3 ^ 40 * 864570 * 2
def baseEnd_864570 : Nat := 197306653092350044266187

theorem tailTrace_864570 : CollatzResearch.WordTrace tailWord_864570 prefixEnd_864570 197306653092350044266187 := by
  unfold tailWord_864570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7883364619454505411387791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21022305651878681097034109 7883364619454505411387791)
  ·
    refine ⟨11825046929181758117081687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7883364619454505411387791 11825046929181758117081687)
    ·
      refine ⟨17737570393772637175622531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11825046929181758117081687 17737570393772637175622531)
      ·
        refine ⟨26606355590658955763433797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17737570393772637175622531 26606355590658955763433797)
        ·
          refine ⟨4988691673248554205643837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26606355590658955763433797 4988691673248554205643837)
          ·
            refine ⟨1870759377468207827116439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4988691673248554205643837 1870759377468207827116439)
            ·
              refine ⟨2806139066202311740674659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1870759377468207827116439 2806139066202311740674659)
              ·
                refine ⟨4209208599303467611011989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2806139066202311740674659 4209208599303467611011989)
                ·
                  refine ⟨197306653092350044266187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4209208599303467611011989 197306653092350044266187)
                  ·
                    rfl

theorem cell21_864570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_864570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864570 prefixEnd_864570 := by exact prefixLift 864570
  have htrace : WordTrace (prefixWord ++ tailWord_864570) baseStart_864570 baseEnd_864570 := by
    simpa [prefixWord, tailWord_864570, baseEnd_864570] using wordTrace_append hprefix tailTrace_864570
  have hstable : (prefixWord ++ tailWord_864570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864570).length < 2 ^ (prefixWord ++ tailWord_864570).sum := by decide
  have hdescent : baseEnd_864570 < baseStart_864570 := by decide
  rcases family_descends (prefixWord ++ tailWord_864570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864680 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_864680 : Nat := 118140960795 + 864680 * 2 ^ 59
def prefixEnd_864680 : Nat := 4983230072969 + 3 ^ 40 * 864680 * 2
def baseEnd_864680 : Nat := 197331756591014297432629

theorem tailTrace_864680 : CollatzResearch.WordTrace tailWord_864680 prefixEnd_864680 197331756591014297432629 := by
  unfold tailWord_864680
  simp only [CollatzResearch.WordTrace]
  refine ⟨15768735253709755216027747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21024980338279673621370329 15768735253709755216027747)
  ·
    refine ⟨23653102880564632824041621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15768735253709755216027747 23653102880564632824041621)
    ·
      refine ⟨1108739197526467163626951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23653102880564632824041621 1108739197526467163626951)
      ·
        refine ⟨1663108796289700745440427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1108739197526467163626951 1663108796289700745440427)
        ·
          refine ⟨2494663194434551118160641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1663108796289700745440427 2494663194434551118160641)
          ·
            refine ⟨1870997395825913338620481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494663194434551118160641 1870997395825913338620481)
            ·
              refine ⟨1403248046869435003965361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1870997395825913338620481 1403248046869435003965361)
              ·
                refine ⟨1052436035152076252974021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403248046869435003965361 1052436035152076252974021)
                ·
                  refine ⟨197331756591014297432629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1052436035152076252974021 197331756591014297432629)
                  ·
                    rfl

theorem cell21_864680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_864680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864680 prefixEnd_864680 := by exact prefixLift 864680
  have htrace : WordTrace (prefixWord ++ tailWord_864680) baseStart_864680 baseEnd_864680 := by
    simpa [prefixWord, tailWord_864680, baseEnd_864680] using wordTrace_append hprefix tailTrace_864680
  have hstable : (prefixWord ++ tailWord_864680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864680).length < 2 ^ (prefixWord ++ tailWord_864680).sum := by decide
  have hdescent : baseEnd_864680 < baseStart_864680 := by decide
  rcases family_descends (prefixWord ++ tailWord_864680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864725 : List Nat := [1, 3, 2, 3, 1, 3, 2, 3, 3]
def baseStart_864725 : Nat := 118140960795 + 864725 * 2 ^ 59
def prefixEnd_864725 : Nat := 4983230072969 + 3 ^ 40 * 864725 * 2
def baseEnd_864725 : Nat := 197342026204104219182537

theorem tailTrace_864725 : CollatzResearch.WordTrace tailWord_864725 prefixEnd_864725 197342026204104219182537 := by
  unfold tailWord_864725
  simp only [CollatzResearch.WordTrace]
  refine ⟨31539111792256483117443629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21026074528170988744962419 31539111792256483117443629)
  ·
    refine ⟨11827166922096181169041361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31539111792256483117443629 11827166922096181169041361)
    ·
      refine ⟨8870375191572135876781021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11827166922096181169041361 8870375191572135876781021)
      ·
        refine ⟨3326390696839550953792883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8870375191572135876781021 3326390696839550953792883)
        ·
          refine ⟨4989586045259326430689325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326390696839550953792883 4989586045259326430689325)
          ·
            refine ⟨1871094766972247411508497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4989586045259326430689325 1871094766972247411508497)
            ·
              refine ⟨1403321075229185558631373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871094766972247411508497 1403321075229185558631373)
              ·
                refine ⟨526245403210944584486765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1403321075229185558631373 526245403210944584486765)
                ·
                  refine ⟨197342026204104219182537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526245403210944584486765 197342026204104219182537)
                  ·
                    rfl

theorem cell21_864725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_864725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864725 prefixEnd_864725 := by exact prefixLift 864725
  have htrace : WordTrace (prefixWord ++ tailWord_864725) baseStart_864725 baseEnd_864725 := by
    simpa [prefixWord, tailWord_864725, baseEnd_864725] using wordTrace_append hprefix tailTrace_864725
  have hstable : (prefixWord ++ tailWord_864725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864725).length < 2 ^ (prefixWord ++ tailWord_864725).sum := by decide
  have hdescent : baseEnd_864725 < baseStart_864725 := by decide
  rcases family_descends (prefixWord ++ tailWord_864725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864770 : List Nat := [3, 4, 1, 2, 2, 1, 1, 7]
def baseStart_864770 : Nat := 118140960795 + 864770 * 2 ^ 59
def prefixEnd_864770 : Nat := 4983230072969 + 3 ^ 40 * 864770 * 2
def baseEnd_864770 : Nat := 65784098605731380310815

theorem tailTrace_864770 : CollatzResearch.WordTrace tailWord_864770 prefixEnd_864770 65784098605731380310815 := by
  unfold tailWord_864770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885188269273363950707941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21027168718062303868554509 7885188269273363950707941)
  ·
    refine ⟨1478472800488755740757739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7885188269273363950707941 1478472800488755740757739)
    ·
      refine ⟨2217709200733133611136609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478472800488755740757739 2217709200733133611136609)
      ·
        refine ⟨1663281900549850208352457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2217709200733133611136609 1663281900549850208352457)
        ·
          refine ⟨1247461425412387656264343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1663281900549850208352457 1247461425412387656264343)
          ·
            refine ⟨1871192138118581484396515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247461425412387656264343 1871192138118581484396515)
            ·
              refine ⟨2806788207177872226594773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871192138118581484396515 2806788207177872226594773)
              ·
                refine ⟨65784098605731380310815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2806788207177872226594773 65784098605731380310815)
                ·
                  rfl

theorem cell21_864770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_864770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864770 prefixEnd_864770 := by exact prefixLift 864770
  have htrace : WordTrace (prefixWord ++ tailWord_864770) baseStart_864770 baseEnd_864770 := by
    simpa [prefixWord, tailWord_864770, baseEnd_864770] using wordTrace_append hprefix tailTrace_864770
  have hstable : (prefixWord ++ tailWord_864770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864770).length < 2 ^ (prefixWord ++ tailWord_864770).sum := by decide
  have hdescent : baseEnd_864770 < baseStart_864770 := by decide
  rcases family_descends (prefixWord ++ tailWord_864770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864801 : List Nat := [1, 2, 3, 2, 2, 1, 5, 2, 3]
def baseStart_864801 : Nat := 118140960795 + 864801 * 2 ^ 59
def prefixEnd_864801 : Nat := 4983230072969 + 3 ^ 40 * 864801 * 2
def baseEnd_864801 : Nat := 197359370439544975915715

theorem tailTrace_864801 : CollatzResearch.WordTrace tailWord_864801 prefixEnd_864801 197359370439544975915715 := by
  unfold tailWord_864801
  simp only [CollatzResearch.WordTrace]
  refine ⟨31541883739981148097210257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21027922493320765398140171 31541883739981148097210257)
  ·
    refine ⟨23656412804985861072907693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31541883739981148097210257 23656412804985861072907693)
    ·
      refine ⟨8871154801869697902340385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23656412804985861072907693 8871154801869697902340385)
      ·
        refine ⟨6653366101402273426755289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8871154801869697902340385 6653366101402273426755289)
        ·
          refine ⟨4990024576051705070066467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6653366101402273426755289 4990024576051705070066467)
          ·
            refine ⟨7485036864077557605099701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990024576051705070066467 7485036864077557605099701)
            ·
              refine ⟨701722206007271025478097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7485036864077557605099701 701722206007271025478097)
              ·
                refine ⟨526291654505453269108573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701722206007271025478097 526291654505453269108573)
                ·
                  refine ⟨197359370439544975915715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526291654505453269108573 197359370439544975915715)
                  ·
                    rfl

theorem cell21_864801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 2, 3].length) (baseStart_864801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864801 prefixEnd_864801 := by exact prefixLift 864801
  have htrace : WordTrace (prefixWord ++ tailWord_864801) baseStart_864801 baseEnd_864801 := by
    simpa [prefixWord, tailWord_864801, baseEnd_864801] using wordTrace_append hprefix tailTrace_864801
  have hstable : (prefixWord ++ tailWord_864801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864801).length < 2 ^ (prefixWord ++ tailWord_864801).sum := by decide
  have hdescent : baseEnd_864801 < baseStart_864801 := by decide
  rcases family_descends (prefixWord ++ tailWord_864801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864874 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_864874 : Nat := 118140960795 + 864874 * 2 ^ 59
def prefixEnd_864874 : Nat := 4983230072969 + 3 ^ 40 * 864874 * 2
def baseEnd_864874 : Nat := 197376030034113071198899

theorem tailTrace_864874 : CollatzResearch.WordTrace tailWord_864874 prefixEnd_864874 197376030034113071198899 := by
  unfold tailWord_864874
  simp only [CollatzResearch.WordTrace]
  refine ⟨7886136567179170391154419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21029697512477787709745117 7886136567179170391154419)
  ·
    refine ⟨11829204850768755586731629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7886136567179170391154419 11829204850768755586731629)
    ·
      refine ⟨4435951819038283345024361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11829204850768755586731629 4435951819038283345024361)
      ·
        refine ⟨3326963864278712508768271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4435951819038283345024361 3326963864278712508768271)
        ·
          refine ⟨4990445796418068763152407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326963864278712508768271 4990445796418068763152407)
          ·
            refine ⟨7485668694627103144728611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990445796418068763152407 7485668694627103144728611)
            ·
              refine ⟨11228503041940654717092917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7485668694627103144728611 11228503041940654717092917)
              ·
                refine ⟨1052672160181936379727461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11228503041940654717092917 1052672160181936379727461)
                ·
                  refine ⟨197376030034113071198899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1052672160181936379727461 197376030034113071198899)
                  ·
                    rfl

theorem cell21_864874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_864874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864874 prefixEnd_864874 := by exact prefixLift 864874
  have htrace : WordTrace (prefixWord ++ tailWord_864874) baseStart_864874 baseEnd_864874 := by
    simpa [prefixWord, tailWord_864874, baseEnd_864874] using wordTrace_append hprefix tailTrace_864874
  have hstable : (prefixWord ++ tailWord_864874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864874).length < 2 ^ (prefixWord ++ tailWord_864874).sum := by decide
  have hdescent : baseEnd_864874 < baseStart_864874 := by decide
  rcases family_descends (prefixWord ++ tailWord_864874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864919 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 5]
def baseStart_864919 : Nat := 118140960795 + 864919 * 2 ^ 59
def prefixEnd_864919 : Nat := 4983230072969 + 3 ^ 40 * 864919 * 2
def baseEnd_864919 : Nat := 197386299647202992948807

theorem tailTrace_864919 : CollatzResearch.WordTrace tailWord_864919 prefixEnd_864919 197386299647202992948807 := by
  unfold tailWord_864919
  simp only [CollatzResearch.WordTrace]
  refine ⟨31546187553553654250005811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21030791702369102833337207 31546187553553654250005811)
  ·
    refine ⟨47319281330330481375008717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31546187553553654250005811 47319281330330481375008717)
    ·
      refine ⟨17744730498873930515628269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47319281330330481375008717 17744730498873930515628269)
      ·
        refine ⟨6654273937077723943360601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17744730498873930515628269 6654273937077723943360601)
        ·
          refine ⟨4990705452808292957520451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6654273937077723943360601 4990705452808292957520451)
          ·
            refine ⟨7486058179212439436280677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990705452808292957520451 7486058179212439436280677)
            ·
              refine ⟨1403635908602332394302627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7486058179212439436280677 1403635908602332394302627)
              ·
                refine ⟨2105453862903498591453941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403635908602332394302627 2105453862903498591453941)
                ·
                  refine ⟨197386299647202992948807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2105453862903498591453941 197386299647202992948807)
                  ·
                    rfl

theorem cell21_864919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 5].length) (baseStart_864919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864919 prefixEnd_864919 := by exact prefixLift 864919
  have htrace : WordTrace (prefixWord ++ tailWord_864919) baseStart_864919 baseEnd_864919 := by
    simpa [prefixWord, tailWord_864919, baseEnd_864919] using wordTrace_append hprefix tailTrace_864919
  have hstable : (prefixWord ++ tailWord_864919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864919).length < 2 ^ (prefixWord ++ tailWord_864919).sum := by decide
  have hdescent : baseEnd_864919 < baseStart_864919 := by decide
  rcases family_descends (prefixWord ++ tailWord_864919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864964 : List Nat := [2, 3, 3, 1, 1, 2, 9]
def baseStart_864964 : Nat := 118140960795 + 864964 * 2 ^ 59
def prefixEnd_864964 : Nat := 4983230072969 + 3 ^ 40 * 864964 * 2
def baseEnd_864964 : Nat := 21932952140032546077635

theorem tailTrace_864964 : CollatzResearch.WordTrace tailWord_864964 prefixEnd_864964 21932952140032546077635 := by
  unfold tailWord_864964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15773914419195313467696973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21031885892260417956929297 15773914419195313467696973)
  ·
    refine ⟨5915217907198242550386365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15773914419195313467696973 5915217907198242550386365)
    ·
      refine ⟨2218206715199340956394887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5915217907198242550386365 2218206715199340956394887)
      ·
        refine ⟨3327310072799011434592331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218206715199340956394887 3327310072799011434592331)
        ·
          refine ⟨4990965109198517151888497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327310072799011434592331 4990965109198517151888497)
          ·
            refine ⟨3743223831898887863916373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4990965109198517151888497 3743223831898887863916373)
            ·
              refine ⟨21932952140032546077635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3743223831898887863916373 21932952140032546077635)
              ·
                rfl

theorem cell21_864964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 9].length) (baseStart_864964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_864964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_864964 prefixEnd_864964 := by exact prefixLift 864964
  have htrace : WordTrace (prefixWord ++ tailWord_864964) baseStart_864964 baseEnd_864964 := by
    simpa [prefixWord, tailWord_864964, baseEnd_864964] using wordTrace_append hprefix tailTrace_864964
  have hstable : (prefixWord ++ tailWord_864964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864964).length < 2 ^ (prefixWord ++ tailWord_864964).sum := by decide
  have hdescent : baseEnd_864964 < baseStart_864964 := by decide
  rcases family_descends (prefixWord ++ tailWord_864964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865122 : List Nat := [3, 3, 2, 1, 3, 2, 1, 3, 3]
def baseStart_865122 : Nat := 118140960795 + 865122 * 2 ^ 59
def prefixEnd_865122 : Nat := 4983230072969 + 3 ^ 40 * 865122 * 2
def baseEnd_865122 : Nat := 197432627012919751065059

theorem tailTrace_865122 : CollatzResearch.WordTrace tailWord_865122 prefixEnd_865122 197432627012919751065059 := by
  unfold tailWord_865122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7888397892954554979911405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21035727714545479946430413 7888397892954554979911405)
  ·
    refine ⟨2958149209857958117466777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7888397892954554979911405 2958149209857958117466777)
    ·
      refine ⟨2218611907393468588100083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2958149209857958117466777 2218611907393468588100083)
      ·
        refine ⟨3327917861090202882150125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218611907393468588100083 3327917861090202882150125)
        ·
          refine ⟨1247969197908826080806297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3327917861090202882150125 1247969197908826080806297)
          ·
            refine ⟨935976898431619560604723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1247969197908826080806297 935976898431619560604723)
            ·
              refine ⟨1403965347647429340907085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935976898431619560604723 1403965347647429340907085)
              ·
                refine ⟨526487005367786002840157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1403965347647429340907085 526487005367786002840157)
                ·
                  refine ⟨197432627012919751065059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526487005367786002840157 197432627012919751065059)
                  ·
                    rfl

theorem cell21_865122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_865122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865122 prefixEnd_865122 := by exact prefixLift 865122
  have htrace : WordTrace (prefixWord ++ tailWord_865122) baseStart_865122 baseEnd_865122 := by
    simpa [prefixWord, tailWord_865122, baseEnd_865122] using wordTrace_append hprefix tailTrace_865122
  have hstable : (prefixWord ++ tailWord_865122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865122).length < 2 ^ (prefixWord ++ tailWord_865122).sum := by decide
  have hdescent : baseEnd_865122 < baseStart_865122 := by decide
  rcases family_descends (prefixWord ++ tailWord_865122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865147 : List Nat := [1, 1, 1, 1, 1, 5, 2, 6, 3]
def baseStart_865147 : Nat := 118140960795 + 865147 * 2 ^ 59
def prefixEnd_865147 : Nat := 4983230072969 + 3 ^ 40 * 865147 * 2
def baseEnd_865147 : Nat := 197438332353525263148341

theorem tailTrace_865147 : CollatzResearch.WordTrace tailWord_865147 prefixEnd_865147 197438332353525263148341 := by
  unfold tailWord_865147
  simp only [CollatzResearch.WordTrace]
  refine ⟨31554503396727649189305695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21036335597818432792870463 31554503396727649189305695)
  ·
    refine ⟨47331755095091473783958543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31554503396727649189305695 47331755095091473783958543)
    ·
      refine ⟨70997632642637210675937815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47331755095091473783958543 70997632642637210675937815)
      ·
        refine ⟨106496448963955816013906723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70997632642637210675937815 106496448963955816013906723)
        ·
          refine ⟨159744673445933724020860085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106496448963955816013906723 159744673445933724020860085)
          ·
            refine ⟨14976063135556286626955633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 159744673445933724020860085 14976063135556286626955633)
            ·
              refine ⟨11232047351667214970216725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14976063135556286626955633 11232047351667214970216725)
              ·
                refine ⟨526502219609400701728909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11232047351667214970216725 526502219609400701728909)
                ·
                  refine ⟨197438332353525263148341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526502219609400701728909 197438332353525263148341)
                  ·
                    rfl

theorem cell21_865147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 3].length) (baseStart_865147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865147 prefixEnd_865147 := by exact prefixLift 865147
  have htrace : WordTrace (prefixWord ++ tailWord_865147) baseStart_865147 baseEnd_865147 := by
    simpa [prefixWord, tailWord_865147, baseEnd_865147] using wordTrace_append hprefix tailTrace_865147
  have hstable : (prefixWord ++ tailWord_865147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865147).length < 2 ^ (prefixWord ++ tailWord_865147).sum := by decide
  have hdescent : baseEnd_865147 < baseStart_865147 := by decide
  rcases family_descends (prefixWord ++ tailWord_865147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865150 : List Nat := [4, 2, 3, 1, 2, 1, 2, 6]
def baseStart_865150 : Nat := 118140960795 + 865150 * 2 ^ 59
def prefixEnd_865150 : Nat := 4983230072969 + 3 ^ 40 * 865150 * 2
def baseEnd_865150 : Nat := 65813005664799308199445

theorem tailTrace_865150 : CollatzResearch.WordTrace tailWord_865150 prefixEnd_865150 65813005664799308199445 := by
  unfold tailWord_865150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944326601964597587708113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21036408543811187134443269 3944326601964597587708113)
  ·
    refine ⟨2958244951473448190781085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3944326601964597587708113 2958244951473448190781085)
    ·
      refine ⟨1109341856802543071542907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2958244951473448190781085 1109341856802543071542907)
      ·
        refine ⟨1664012785203814607314361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1109341856802543071542907 1664012785203814607314361)
        ·
          refine ⟨1248009588902860955485771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1664012785203814607314361 1248009588902860955485771)
          ·
            refine ⟨1872014383354291433228657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248009588902860955485771 1872014383354291433228657)
            ·
              refine ⟨1404010787515718574921493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872014383354291433228657 1404010787515718574921493)
              ·
                refine ⟨65813005664799308199445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1404010787515718574921493 65813005664799308199445)
                ·
                  rfl

theorem cell21_865150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_865150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865150 prefixEnd_865150 := by exact prefixLift 865150
  have htrace : WordTrace (prefixWord ++ tailWord_865150) baseStart_865150 baseEnd_865150 := by
    simpa [prefixWord, tailWord_865150, baseEnd_865150] using wordTrace_append hprefix tailTrace_865150
  have hstable : (prefixWord ++ tailWord_865150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865150).length < 2 ^ (prefixWord ++ tailWord_865150).sum := by decide
  have hdescent : baseEnd_865150 < baseStart_865150 := by decide
  rcases family_descends (prefixWord ++ tailWord_865150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865175 : List Nat := [1, 1, 3, 3, 1, 2, 1, 9]
def baseStart_865175 : Nat := 118140960795 + 865175 * 2 ^ 59
def prefixEnd_865175 : Nat := 4983230072969 + 3 ^ 40 * 865175 * 2
def baseEnd_865175 : Nat := 65814907445001145560539

theorem tailTrace_865175 : CollatzResearch.WordTrace tailWord_865175 prefixEnd_865175 65814907445001145560539 := by
  unfold tailWord_865175
  simp only [CollatzResearch.WordTrace]
  refine ⟨31555524640626209971324979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21037016427084139980883319 31555524640626209971324979)
  ·
    refine ⟨47333286960939314956987469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31555524640626209971324979 47333286960939314956987469)
    ·
      refine ⟨17749982610352243108870301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47333286960939314956987469 17749982610352243108870301)
      ·
        refine ⟨6656243478882091165826363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17749982610352243108870301 6656243478882091165826363)
        ·
          refine ⟨9984365218323136748739545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6656243478882091165826363 9984365218323136748739545)
          ·
            refine ⟨7488273913742352561554659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9984365218323136748739545 7488273913742352561554659)
            ·
              refine ⟨11232410870613528842331989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7488273913742352561554659 11232410870613528842331989)
              ·
                refine ⟨65814907445001145560539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11232410870613528842331989 65814907445001145560539)
                ·
                  rfl

theorem cell21_865175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 9].length) (baseStart_865175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865175 prefixEnd_865175 := by exact prefixLift 865175
  have htrace : WordTrace (prefixWord ++ tailWord_865175) baseStart_865175 baseEnd_865175 := by
    simpa [prefixWord, tailWord_865175, baseEnd_865175] using wordTrace_append hprefix tailTrace_865175
  have hstable : (prefixWord ++ tailWord_865175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865175).length < 2 ^ (prefixWord ++ tailWord_865175).sum := by decide
  have hdescent : baseEnd_865175 < baseStart_865175 := by decide
  rcases family_descends (prefixWord ++ tailWord_865175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865240 : List Nat := [2, 1, 2, 2, 2, 4, 2, 3, 3]
def baseStart_865240 : Nat := 118140960795 + 865240 * 2 ^ 59
def prefixEnd_865240 : Nat := 4983230072969 + 3 ^ 40 * 865240 * 2
def baseEnd_865240 : Nat := 197459556220577768098151

theorem tailTrace_865240 : CollatzResearch.WordTrace tailWord_865240 prefixEnd_865240 197459556220577768098151 := by
  unfold tailWord_865240
  simp only [CollatzResearch.WordTrace]
  refine ⟨15778947692695363036220587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21038596923593817381627449 15778947692695363036220587)
  ·
    refine ⟨23668421539043044554330881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15778947692695363036220587 23668421539043044554330881)
    ·
      refine ⟨17751316154282283415748161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23668421539043044554330881 17751316154282283415748161)
      ·
        refine ⟨13313487115711712561811121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17751316154282283415748161 13313487115711712561811121)
        ·
          refine ⟨9985115336783784421358341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13313487115711712561811121 9985115336783784421358341)
          ·
            refine ⟨1872209125646959579004689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9985115336783784421358341 1872209125646959579004689)
            ·
              refine ⟨1404156844235219684253517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872209125646959579004689 1404156844235219684253517)
              ·
                refine ⟨526558816588207381595069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1404156844235219684253517 526558816588207381595069)
                ·
                  refine ⟨197459556220577768098151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526558816588207381595069 197459556220577768098151)
                  ·
                    rfl

theorem cell21_865240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 3].length) (baseStart_865240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865240 prefixEnd_865240 := by exact prefixLift 865240
  have htrace : WordTrace (prefixWord ++ tailWord_865240) baseStart_865240 baseEnd_865240 := by
    simpa [prefixWord, tailWord_865240, baseEnd_865240] using wordTrace_append hprefix tailTrace_865240
  have hstable : (prefixWord ++ tailWord_865240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865240).length < 2 ^ (prefixWord ++ tailWord_865240).sum := by decide
  have hdescent : baseEnd_865240 < baseStart_865240 := by decide
  rcases family_descends (prefixWord ++ tailWord_865240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865251 : List Nat := [1, 1, 1, 6, 1, 1, 10]
def baseStart_865251 : Nat := 118140960795 + 865251 * 2 ^ 59
def prefixEnd_865251 : Nat := 4983230072969 + 3 ^ 40 * 865251 * 2
def baseEnd_865251 : Nat := 21940229618938243712755

theorem tailTrace_865251 : CollatzResearch.WordTrace tailWord_865251 prefixEnd_865251 21940229618938243712755 := by
  unfold tailWord_865251
  simp only [CollatzResearch.WordTrace]
  refine ⟨31558296588350874951091607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21038864392233916634061071 31558296588350874951091607)
  ·
    refine ⟨47337444882526312426637411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31558296588350874951091607 47337444882526312426637411)
    ·
      refine ⟨71006167323789468639956117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47337444882526312426637411 71006167323789468639956117)
      ·
        refine ⟨3328414093302631342497943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 71006167323789468639956117 3328414093302631342497943)
        ·
          refine ⟨4992621139953947013746915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3328414093302631342497943 4992621139953947013746915)
          ·
            refine ⟨7488931709930920520620373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4992621139953947013746915 7488931709930920520620373)
            ·
              refine ⟨21940229618938243712755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7488931709930920520620373 21940229618938243712755)
              ·
                rfl

theorem cell21_865251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 10].length) (baseStart_865251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865251 prefixEnd_865251 := by exact prefixLift 865251
  have htrace : WordTrace (prefixWord ++ tailWord_865251) baseStart_865251 baseEnd_865251 := by
    simpa [prefixWord, tailWord_865251, baseEnd_865251] using wordTrace_append hprefix tailTrace_865251
  have hstable : (prefixWord ++ tailWord_865251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865251).length < 2 ^ (prefixWord ++ tailWord_865251).sum := by decide
  have hdescent : baseEnd_865251 < baseStart_865251 := by decide
  rcases family_descends (prefixWord ++ tailWord_865251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865313 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 6]
def baseStart_865313 : Nat := 118140960795 + 865313 * 2 ^ 59
def prefixEnd_865313 : Nat := 4983230072969 + 3 ^ 40 * 865313 * 2
def baseEnd_865313 : Nat := 197476215815145863381335

theorem tailTrace_865313 : CollatzResearch.WordTrace tailWord_865313 prefixEnd_865313 197476215815145863381335 := by
  unfold tailWord_865313
  simp only [CollatzResearch.WordTrace]
  refine ⟨31560557914126259539848593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21040371942750839693232395 31560557914126259539848593)
  ·
    refine ⟨23670418435594694654886445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31560557914126259539848593 23670418435594694654886445)
    ·
      refine ⟨8876406913348010495582417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23670418435594694654886445 8876406913348010495582417)
      ·
        refine ⟨6657305185011007871686813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8876406913348010495582417 6657305185011007871686813)
        ·
          refine ⟨2496489444379127951882555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6657305185011007871686813 2496489444379127951882555)
          ·
            refine ⟨3744734166568691927823833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496489444379127951882555 3744734166568691927823833)
            ·
              refine ⟨2808550624926518945867875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3744734166568691927823833 2808550624926518945867875)
              ·
                refine ⟨4212825937389778418801813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2808550624926518945867875 4212825937389778418801813)
                ·
                  refine ⟨197476215815145863381335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4212825937389778418801813 197476215815145863381335)
                  ·
                    rfl

theorem cell21_865313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_865313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865313 prefixEnd_865313 := by exact prefixLift 865313
  have htrace : WordTrace (prefixWord ++ tailWord_865313) baseStart_865313 baseEnd_865313 := by
    simpa [prefixWord, tailWord_865313, baseEnd_865313] using wordTrace_append hprefix tailTrace_865313
  have hstable : (prefixWord ++ tailWord_865313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865313).length < 2 ^ (prefixWord ++ tailWord_865313).sum := by decide
  have hdescent : baseEnd_865313 < baseStart_865313 := by decide
  rcases family_descends (prefixWord ++ tailWord_865313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865316 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 5]
def baseStart_865316 : Nat := 118140960795 + 865316 * 2 ^ 59
def prefixEnd_865316 : Nat := 4983230072969 + 3 ^ 40 * 865316 * 2
def baseEnd_865316 : Nat := 197476900456018524831329

theorem tailTrace_865316 : CollatzResearch.WordTrace tailWord_865316 prefixEnd_865316 197476900456018524831329 := by
  unfold tailWord_865316
  simp only [CollatzResearch.WordTrace]
  refine ⟨15780333666557695526103901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21040444888743594034805201 15780333666557695526103901)
  ·
    refine ⟨5917625124959135822288963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15780333666557695526103901 5917625124959135822288963)
    ·
      refine ⟨8876437687438703733433445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5917625124959135822288963 8876437687438703733433445)
      ·
        refine ⟨1664332066394756950018771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8876437687438703733433445 1664332066394756950018771)
        ·
          refine ⟨2496498099592135425028157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664332066394756950018771 2496498099592135425028157)
          ·
            refine ⟨936186787347050784385559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2496498099592135425028157 936186787347050784385559)
            ·
              refine ⟨1404280181020576176578339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936186787347050784385559 1404280181020576176578339)
              ·
                refine ⟨2106420271530864264867509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404280181020576176578339 2106420271530864264867509)
                ·
                  refine ⟨197476900456018524831329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2106420271530864264867509 197476900456018524831329)
                  ·
                    rfl

theorem cell21_865316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_865316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865316 prefixEnd_865316 := by exact prefixLift 865316
  have htrace : WordTrace (prefixWord ++ tailWord_865316) baseStart_865316 baseEnd_865316 := by
    simpa [prefixWord, tailWord_865316, baseEnd_865316] using wordTrace_append hprefix tailTrace_865316
  have hstable : (prefixWord ++ tailWord_865316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865316).length < 2 ^ (prefixWord ++ tailWord_865316).sum := by decide
  have hdescent : baseEnd_865316 < baseStart_865316 := by decide
  rcases family_descends (prefixWord ++ tailWord_865316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865375 : List Nat := [1, 1, 2, 3, 1, 1, 5, 4, 3]
def baseStart_865375 : Nat := 118140960795 + 865375 * 2 ^ 59
def prefixEnd_865375 : Nat := 4983230072969 + 3 ^ 40 * 865375 * 2
def baseEnd_865375 : Nat := 197490365059847533347875

theorem tailTrace_865375 : CollatzResearch.WordTrace tailWord_865375 prefixEnd_865375 197490365059847533347875 := by
  unfold tailWord_865375
  simp only [CollatzResearch.WordTrace]
  refine ⟨31562819239901644128605579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21041879493267762752403719 31562819239901644128605579)
  ·
    refine ⟨47344228859852466192908369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31562819239901644128605579 47344228859852466192908369)
    ·
      refine ⟨35508171644889349644681277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47344228859852466192908369 35508171644889349644681277)
      ·
        refine ⟨13315564366833506116755479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35508171644889349644681277 13315564366833506116755479)
        ·
          refine ⟨19973346550250259175133219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13315564366833506116755479 19973346550250259175133219)
          ·
            refine ⟨29960019825375388762699829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19973346550250259175133219 29960019825375388762699829)
            ·
              refine ⟨2808751858628942696503109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29960019825375388762699829 2808751858628942696503109)
              ·
                refine ⟨526640973492926755594333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2808751858628942696503109 526640973492926755594333)
                ·
                  refine ⟨197490365059847533347875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526640973492926755594333 197490365059847533347875)
                  ·
                    rfl

theorem cell21_865375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 3].length) (baseStart_865375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865375 prefixEnd_865375 := by exact prefixLift 865375
  have htrace : WordTrace (prefixWord ++ tailWord_865375) baseStart_865375 baseEnd_865375 := by
    simpa [prefixWord, tailWord_865375, baseEnd_865375] using wordTrace_append hprefix tailTrace_865375
  have hstable : (prefixWord ++ tailWord_865375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865375).length < 2 ^ (prefixWord ++ tailWord_865375).sum := by decide
  have hdescent : baseEnd_865375 < baseStart_865375 := by decide
  rcases family_descends (prefixWord ++ tailWord_865375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865468 : List Nat := [2, 2, 2, 3, 2, 1, 3, 3, 3]
def baseStart_865468 : Nat := 118140960795 + 865468 * 2 ^ 59
def prefixEnd_865468 : Nat := 4983230072969 + 3 ^ 40 * 865468 * 2
def baseEnd_865468 : Nat := 197511588926900038297685

theorem tailTrace_865468 : CollatzResearch.WordTrace tailWord_865468 prefixEnd_865468 197511588926900038297685 := by
  unfold tailWord_865468
  simp only [CollatzResearch.WordTrace]
  refine ⟨15783105614282360505870529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21044140819043147341160705 15783105614282360505870529)
  ·
    refine ⟨11837329210711770379402897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15783105614282360505870529 11837329210711770379402897)
    ·
      refine ⟨8877996908033827784552173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11837329210711770379402897 8877996908033827784552173)
      ·
        refine ⟨3329248840512685419207065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8877996908033827784552173 3329248840512685419207065)
        ·
          refine ⟨2496936630384514064405299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3329248840512685419207065 2496936630384514064405299)
          ·
            refine ⟨3745404945576771096607949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496936630384514064405299 3745404945576771096607949)
            ·
              refine ⟨1404526854591289161227981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3745404945576771096607949 1404526854591289161227981)
              ·
                refine ⟨526697570471733435460493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1404526854591289161227981 526697570471733435460493)
                ·
                  refine ⟨197511588926900038297685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526697570471733435460493 197511588926900038297685)
                  ·
                    rfl

theorem cell21_865468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_865468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865468 prefixEnd_865468 := by exact prefixLift 865468
  have htrace : WordTrace (prefixWord ++ tailWord_865468) baseStart_865468 baseEnd_865468 := by
    simpa [prefixWord, tailWord_865468, baseEnd_865468] using wordTrace_append hprefix tailTrace_865468
  have hstable : (prefixWord ++ tailWord_865468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865468).length < 2 ^ (prefixWord ++ tailWord_865468).sum := by decide
  have hdescent : baseEnd_865468 < baseStart_865468 := by decide
  rcases family_descends (prefixWord ++ tailWord_865468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865496 : List Nat := [2, 1, 2, 2, 5, 1, 2, 6]
def baseStart_865496 : Nat := 118140960795 + 865496 * 2 ^ 59
def prefixEnd_865496 : Nat := 4983230072969 + 3 ^ 40 * 865496 * 2
def baseEnd_865496 : Nat := 65839326302792737276987

theorem tailTrace_865496 : CollatzResearch.WordTrace tailWord_865496 prefixEnd_865496 65839326302792737276987 := by
  unfold tailWord_865496
  simp only [CollatzResearch.WordTrace]
  refine ⟨15783616236231640896880171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21044821648308854529173561 15783616236231640896880171)
  ·
    refine ⟨23675424354347461345320257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15783616236231640896880171 23675424354347461345320257)
    ·
      refine ⟨17756568265760596008990193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23675424354347461345320257 17756568265760596008990193)
      ·
        refine ⟨13317426199320447006742645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17756568265760596008990193 13317426199320447006742645)
        ·
          refine ⟨1248508706186291906882123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13317426199320447006742645 1248508706186291906882123)
          ·
            refine ⟨1872763059279437860323185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248508706186291906882123 1872763059279437860323185)
            ·
              refine ⟨1404572294459578395242389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872763059279437860323185 1404572294459578395242389)
              ·
                refine ⟨65839326302792737276987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1404572294459578395242389 65839326302792737276987)
                ·
                  rfl

theorem cell21_865496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 6].length) (baseStart_865496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865496 prefixEnd_865496 := by exact prefixLift 865496
  have htrace : WordTrace (prefixWord ++ tailWord_865496) baseStart_865496 baseEnd_865496 := by
    simpa [prefixWord, tailWord_865496, baseEnd_865496] using wordTrace_append hprefix tailTrace_865496
  have hstable : (prefixWord ++ tailWord_865496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865496).length < 2 ^ (prefixWord ++ tailWord_865496).sum := by decide
  have hdescent : baseEnd_865496 < baseStart_865496 := by decide
  rcases family_descends (prefixWord ++ tailWord_865496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865541 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 4]
def baseStart_865541 : Nat := 118140960795 + 865541 * 2 ^ 59
def prefixEnd_865541 : Nat := 4983230072969 + 3 ^ 40 * 865541 * 2
def baseEnd_865541 : Nat := 197528248521468133580869

theorem tailTrace_865541 : CollatzResearch.WordTrace tailWord_865541 prefixEnd_865541 197528248521468133580869 := by
  unfold tailWord_865541
  simp only [CollatzResearch.WordTrace]
  refine ⟨31568873757300254479148477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21045915838200169652765651 31568873757300254479148477)
  ·
    refine ⟨11838327658987595429680679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31568873757300254479148477 11838327658987595429680679)
    ·
      refine ⟨17757491488481393144521019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11838327658987595429680679 17757491488481393144521019)
      ·
        refine ⟨26636237232722089716781529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17757491488481393144521019 26636237232722089716781529)
        ·
          refine ⟨19977177924541567287586147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26636237232722089716781529 19977177924541567287586147)
          ·
            refine ⟨29965766886812350931379221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19977177924541567287586147 29965766886812350931379221)
            ·
              refine ⟨1404645322819328949908401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29965766886812350931379221 1404645322819328949908401)
              ·
                refine ⟨1053483992114496712431301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404645322819328949908401 1053483992114496712431301)
                ·
                  refine ⟨197528248521468133580869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1053483992114496712431301 197528248521468133580869)
                  ·
                    rfl

theorem cell21_865541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_865541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865541 prefixEnd_865541 := by exact prefixLift 865541
  have htrace : WordTrace (prefixWord ++ tailWord_865541) baseStart_865541 baseEnd_865541 := by
    simpa [prefixWord, tailWord_865541, baseEnd_865541] using wordTrace_append hprefix tailTrace_865541
  have hstable : (prefixWord ++ tailWord_865541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865541).length < 2 ^ (prefixWord ++ tailWord_865541).sum := by decide
  have hdescent : baseEnd_865541 < baseStart_865541 := by decide
  rcases family_descends (prefixWord ++ tailWord_865541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865544 : List Nat := [2, 1, 3, 2, 4, 1, 1, 4, 3]
def baseStart_865544 : Nat := 118140960795 + 865544 * 2 ^ 59
def prefixEnd_865544 : Nat := 4983230072969 + 3 ^ 40 * 865544 * 2
def baseEnd_865544 : Nat := 197528933162340795030863

theorem tailTrace_865544 : CollatzResearch.WordTrace tailWord_865544 prefixEnd_865544 197528933162340795030863 := by
  unfold tailWord_865544
  simp only [CollatzResearch.WordTrace]
  refine ⟨15784491588144692995753843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21045988784192923994338457 15784491588144692995753843)
  ·
    refine ⟨23676737382217039493630765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15784491588144692995753843 23676737382217039493630765)
    ·
      refine ⟨8878776518331389810111537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23676737382217039493630765 8878776518331389810111537)
      ·
        refine ⟨6659082388748542357583653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8878776518331389810111537 6659082388748542357583653)
        ·
          refine ⟨1248577947890351692046935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6659082388748542357583653 1248577947890351692046935)
          ·
            refine ⟨1872866921835527538070403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248577947890351692046935 1872866921835527538070403)
            ·
              refine ⟨2809300382753291307105605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872866921835527538070403 2809300382753291307105605)
              ·
                refine ⟨526743821766242120082301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2809300382753291307105605 526743821766242120082301)
                ·
                  refine ⟨197528933162340795030863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526743821766242120082301 197528933162340795030863)
                  ·
                    rfl

theorem cell21_865544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 3].length) (baseStart_865544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865544 prefixEnd_865544 := by exact prefixLift 865544
  have htrace : WordTrace (prefixWord ++ tailWord_865544) baseStart_865544 baseEnd_865544 := by
    simpa [prefixWord, tailWord_865544, baseEnd_865544] using wordTrace_append hprefix tailTrace_865544
  have hstable : (prefixWord ++ tailWord_865544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865544).length < 2 ^ (prefixWord ++ tailWord_865544).sum := by decide
  have hdescent : baseEnd_865544 < baseStart_865544 := by decide
  rcases family_descends (prefixWord ++ tailWord_865544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865572 : List Nat := [2, 3, 1, 3, 1, 1, 5, 5]
def baseStart_865572 : Nat := 118140960795 + 865572 * 2 ^ 59
def prefixEnd_865572 : Nat := 4983230072969 + 3 ^ 40 * 865572 * 2
def baseEnd_865572 : Nat := 65845107714606322854713

theorem tailTrace_865572 : CollatzResearch.WordTrace tailWord_865572 prefixEnd_865572 65845107714606322854713 := by
  unfold tailWord_865572
  simp only [CollatzResearch.WordTrace]
  refine ⟨15785002210093973386763485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21046669613458631182351313 15785002210093973386763485)
  ·
    refine ⟨5919375828785240020036307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15785002210093973386763485 5919375828785240020036307)
    ·
      refine ⟨8879063743177860030054461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5919375828785240020036307 8879063743177860030054461)
      ·
        refine ⟨3329648903691697511270423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8879063743177860030054461 3329648903691697511270423)
        ·
          refine ⟨4994473355537546266905635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329648903691697511270423 4994473355537546266905635)
          ·
            refine ⟨7491710033306319400358453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4994473355537546266905635 7491710033306319400358453)
            ·
              refine ⟨702347815622467443783605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7491710033306319400358453 702347815622467443783605)
              ·
                refine ⟨65845107714606322854713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 702347815622467443783605 65845107714606322854713)
                ·
                  rfl

theorem cell21_865572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_865572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865572 prefixEnd_865572 := by exact prefixLift 865572
  have htrace : WordTrace (prefixWord ++ tailWord_865572) baseStart_865572 baseEnd_865572 := by
    simpa [prefixWord, tailWord_865572, baseEnd_865572] using wordTrace_append hprefix tailTrace_865572
  have hstable : (prefixWord ++ tailWord_865572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865572).length < 2 ^ (prefixWord ++ tailWord_865572).sum := by decide
  have hdescent : baseEnd_865572 < baseStart_865572 := by decide
  rcases family_descends (prefixWord ++ tailWord_865572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865600 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_865600 : Nat := 118140960795 + 865600 * 2 ^ 59
def prefixEnd_865600 : Nat := 4983230072969 + 3 ^ 40 * 865600 * 2
def baseEnd_865600 : Nat := 197541713125297142097415

theorem tailTrace_865600 : CollatzResearch.WordTrace tailWord_865600 prefixEnd_865600 197541713125297142097415 := by
  unfold tailWord_865600
  simp only [CollatzResearch.WordTrace]
  refine ⟨15785512832043253777773127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21047350442724338370364169 15785512832043253777773127)
  ·
    refine ⟨23678269248064880666659691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15785512832043253777773127 23678269248064880666659691)
    ·
      refine ⟨35517403872097320999989537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23678269248064880666659691 35517403872097320999989537)
      ·
        refine ⟨26638052904072990749992153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35517403872097320999989537 26638052904072990749992153)
        ·
          refine ⟨19978539678054743062494115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26638052904072990749992153 19978539678054743062494115)
          ·
            refine ⟨29967809517082114593741173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19978539678054743062494115 29967809517082114593741173)
            ·
              refine ⟨2809482142226448243163235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29967809517082114593741173 2809482142226448243163235)
              ·
                refine ⟨4214223213339672364744853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809482142226448243163235 4214223213339672364744853)
                ·
                  refine ⟨197541713125297142097415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4214223213339672364744853 197541713125297142097415)
                  ·
                    rfl

theorem cell21_865600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_865600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865600 prefixEnd_865600 := by exact prefixLift 865600
  have htrace : WordTrace (prefixWord ++ tailWord_865600) baseStart_865600 baseEnd_865600 := by
    simpa [prefixWord, tailWord_865600, baseEnd_865600] using wordTrace_append hprefix tailTrace_865600
  have hstable : (prefixWord ++ tailWord_865600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865600).length < 2 ^ (prefixWord ++ tailWord_865600).sum := by decide
  have hdescent : baseEnd_865600 < baseStart_865600 := by decide
  rcases family_descends (prefixWord ++ tailWord_865600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865730 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 5]
def baseStart_865730 : Nat := 118140960795 + 865730 * 2 ^ 59
def prefixEnd_865730 : Nat := 4983230072969 + 3 ^ 40 * 865730 * 2
def baseEnd_865730 : Nat := 197571380896445804930483

theorem tailTrace_865730 : CollatzResearch.WordTrace tailWord_865730 prefixEnd_865730 197571380896445804930483 := by
  unfold tailWord_865730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7893941788403884939444661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21050511435743693171852429 7893941788403884939444661)
  ·
    refine ⟨740057042662864213072937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7893941788403884939444661 740057042662864213072937)
    ·
      refine ⟨555042781997148159804703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 740057042662864213072937 555042781997148159804703)
      ·
        refine ⟨832564172995722239707055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555042781997148159804703 832564172995722239707055)
        ·
          refine ⟨1248846259493583359560583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832564172995722239707055 1248846259493583359560583)
          ·
            refine ⟨1873269389240375039340875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248846259493583359560583 1873269389240375039340875)
            ·
              refine ⟨2809904083860562559011313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873269389240375039340875 2809904083860562559011313)
              ·
                refine ⟨2107428062895421919258485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2809904083860562559011313 2107428062895421919258485)
                ·
                  refine ⟨197571380896445804930483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2107428062895421919258485 197571380896445804930483)
                  ·
                    rfl

theorem cell21_865730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_865730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865730 prefixEnd_865730 := by exact prefixLift 865730
  have htrace : WordTrace (prefixWord ++ tailWord_865730) baseStart_865730 baseEnd_865730 := by
    simpa [prefixWord, tailWord_865730, baseEnd_865730] using wordTrace_append hprefix tailTrace_865730
  have hstable : (prefixWord ++ tailWord_865730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865730).length < 2 ^ (prefixWord ++ tailWord_865730).sum := by decide
  have hdescent : baseEnd_865730 < baseStart_865730 := by decide
  rcases family_descends (prefixWord ++ tailWord_865730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865738 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_865738 : Nat := 118140960795 + 865738 * 2 ^ 59
def prefixEnd_865738 : Nat := 4983230072969 + 3 ^ 40 * 865738 * 2
def baseEnd_865738 : Nat := 197573206605439568797133

theorem tailTrace_865738 : CollatzResearch.WordTrace tailWord_865738 prefixEnd_865738 197573206605439568797133 := by
  unfold tailWord_865738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7894014734396639281017467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21050705958391038082713245 7894014734396639281017467)
  ·
    refine ⟨11841022101594958921526201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7894014734396639281017467 11841022101594958921526201)
    ·
      refine ⟨8880766576196219191144651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11841022101594958921526201 8880766576196219191144651)
      ·
        refine ⟨13321149864294328786716977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8880766576196219191144651 13321149864294328786716977)
        ·
          refine ⟨9990862398220746590037733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13321149864294328786716977 9990862398220746590037733)
          ·
            refine ⟨1873286699666389985632075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9990862398220746590037733 1873286699666389985632075)
            ·
              refine ⟨2809930049499584978448113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873286699666389985632075 2809930049499584978448113)
              ·
                refine ⟨2107447537124688733836085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2809930049499584978448113 2107447537124688733836085)
                ·
                  refine ⟨197573206605439568797133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2107447537124688733836085 197573206605439568797133)
                  ·
                    rfl

theorem cell21_865738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_865738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865738 prefixEnd_865738 := by exact prefixLift 865738
  have htrace : WordTrace (prefixWord ++ tailWord_865738) baseStart_865738 baseEnd_865738 := by
    simpa [prefixWord, tailWord_865738, baseEnd_865738] using wordTrace_append hprefix tailTrace_865738
  have hstable : (prefixWord ++ tailWord_865738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865738).length < 2 ^ (prefixWord ++ tailWord_865738).sum := by decide
  have hdescent : baseEnd_865738 < baseStart_865738 := by decide
  rcases family_descends (prefixWord ++ tailWord_865738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865845 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 4]
def baseStart_865845 : Nat := 118140960795 + 865845 * 2 ^ 59
def prefixEnd_865845 : Nat := 4983230072969 + 3 ^ 40 * 865845 * 2
def baseEnd_865845 : Nat := 197597625463231160513581

theorem tailTrace_865845 : CollatzResearch.WordTrace tailWord_865845 prefixEnd_865845 197597625463231160513581 := by
  unfold tailWord_865845
  simp only [CollatzResearch.WordTrace]
  refine ⟨31579961548198914398214989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21053307698799276265476659 31579961548198914398214989)
  ·
    refine ⟨11842485580574592899330621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31579961548198914398214989 11842485580574592899330621)
    ·
      refine ⟨4440932092715472337248983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11842485580574592899330621 4440932092715472337248983)
      ·
        refine ⟨6661398139073208505873475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440932092715472337248983 6661398139073208505873475)
        ·
          refine ⟨9992097208609812758810213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6661398139073208505873475 9992097208609812758810213)
          ·
            refine ⟨1873518226614339892276915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9992097208609812758810213 1873518226614339892276915)
            ·
              refine ⟨2810277339921509838415373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873518226614339892276915 2810277339921509838415373)
              ·
                refine ⟨1053854002470566189405765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2810277339921509838415373 1053854002470566189405765)
                ·
                  refine ⟨197597625463231160513581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1053854002470566189405765 197597625463231160513581)
                  ·
                    rfl

theorem cell21_865845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_865845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865845 prefixEnd_865845 := by exact prefixLift 865845
  have htrace : WordTrace (prefixWord ++ tailWord_865845) baseStart_865845 baseEnd_865845 := by
    simpa [prefixWord, tailWord_865845, baseEnd_865845] using wordTrace_append hprefix tailTrace_865845
  have hstable : (prefixWord ++ tailWord_865845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865845).length < 2 ^ (prefixWord ++ tailWord_865845).sum := by decide
  have hdescent : baseEnd_865845 < baseStart_865845 := by decide
  rcases family_descends (prefixWord ++ tailWord_865845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865924 : List Nat := [2, 3, 2, 1, 4, 1, 2, 3, 3]
def baseStart_865924 : Nat := 118140960795 + 865924 * 2 ^ 59
def prefixEnd_865924 : Nat := 4983230072969 + 3 ^ 40 * 865924 * 2
def baseEnd_865924 : Nat := 197615654339544578696753

theorem tailTrace_865924 : CollatzResearch.WordTrace tailWord_865924 prefixEnd_865924 197615654339544578696753 := by
  unfold tailWord_865924
  simp only [CollatzResearch.WordTrace]
  refine ⟨15791421457456355445170413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21055228609941807260227217 15791421457456355445170413)
  ·
    refine ⟨5921783046546133291938905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15791421457456355445170413 5921783046546133291938905)
    ·
      refine ⟨4441337284909599968954179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5921783046546133291938905 4441337284909599968954179)
      ·
        refine ⟨6662005927364399953431269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4441337284909599968954179 6662005927364399953431269)
        ·
          refine ⟨1249126111380824991268363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6662005927364399953431269 1249126111380824991268363)
          ·
            refine ⟨1873689167071237486902545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249126111380824991268363 1873689167071237486902545)
            ·
              refine ⟨1405266875303428115176909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1873689167071237486902545 1405266875303428115176909)
              ·
                refine ⟨526975078238785543191341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1405266875303428115176909 526975078238785543191341)
                ·
                  refine ⟨197615654339544578696753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 526975078238785543191341 197615654339544578696753)
                  ·
                    rfl

theorem cell21_865924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_865924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865924 prefixEnd_865924 := by exact prefixLift 865924
  have htrace : WordTrace (prefixWord ++ tailWord_865924) baseStart_865924 baseEnd_865924 := by
    simpa [prefixWord, tailWord_865924, baseEnd_865924] using wordTrace_append hprefix tailTrace_865924
  have hstable : (prefixWord ++ tailWord_865924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865924).length < 2 ^ (prefixWord ++ tailWord_865924).sum := by decide
  have hdescent : baseEnd_865924 < baseStart_865924 := by decide
  rcases family_descends (prefixWord ++ tailWord_865924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865980 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_865980 : Nat := 118140960795 + 865980 * 2 ^ 59
def prefixEnd_865980 : Nat := 4983230072969 + 3 ^ 40 * 865980 * 2
def baseEnd_865980 : Nat := 197628434302500925763305

theorem tailTrace_865980 : CollatzResearch.WordTrace tailWord_865980 prefixEnd_865980 197628434302500925763305 := by
  unfold tailWord_865980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15792442701354916227189697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21056590268473221636252929 15792442701354916227189697)
  ·
    refine ⟨11844332026016187170392273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15792442701354916227189697 11844332026016187170392273)
    ·
      refine ⟨8883249019512140377794205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11844332026016187170392273 8883249019512140377794205)
      ·
        refine ⟨3331218382317052641672827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8883249019512140377794205 3331218382317052641672827)
        ·
          refine ⟨4996827573475578962509241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3331218382317052641672827 4996827573475578962509241)
          ·
            refine ⟨3747620680106684221881931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4996827573475578962509241 3747620680106684221881931)
            ·
              refine ⟨5621431020160026332822897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747620680106684221881931 5621431020160026332822897)
              ·
                refine ⟨4216073265120019749617173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5621431020160026332822897 4216073265120019749617173)
                ·
                  refine ⟨197628434302500925763305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4216073265120019749617173 197628434302500925763305)
                  ·
                    rfl

theorem cell21_865980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_865980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865980 prefixEnd_865980 := by exact prefixLift 865980
  have htrace : WordTrace (prefixWord ++ tailWord_865980) baseStart_865980 baseEnd_865980 := by
    simpa [prefixWord, tailWord_865980, baseEnd_865980] using wordTrace_append hprefix tailTrace_865980
  have hstable : (prefixWord ++ tailWord_865980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865980).length < 2 ^ (prefixWord ++ tailWord_865980).sum := by decide
  have hdescent : baseEnd_865980 < baseStart_865980 := by decide
  rcases family_descends (prefixWord ++ tailWord_865980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865986 : List Nat := [3, 5, 1, 2, 1, 2, 7]
def baseStart_865986 : Nat := 118140960795 + 865986 * 2 ^ 59
def prefixEnd_865986 : Nat := 4983230072969 + 3 ^ 40 * 865986 * 2
def baseEnd_865986 : Nat := 21958867064916249851477

theorem tailTrace_865986 : CollatzResearch.WordTrace tailWord_865986 prefixEnd_865986 21958867064916249851477 := by
  unfold tailWord_865986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7896276060172023869774453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21056736160458730319398541 7896276060172023869774453)
  ·
    refine ⟨740275880641127237791355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7896276060172023869774453 740275880641127237791355)
    ·
      refine ⟨1110413820961690856687033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 740275880641127237791355 1110413820961690856687033)
      ·
        refine ⟨832810365721268142515275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1110413820961690856687033 832810365721268142515275)
        ·
          refine ⟨1249215548581902213772913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832810365721268142515275 1249215548581902213772913)
          ·
            refine ⟨936911661436426660329685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249215548581902213772913 936911661436426660329685)
            ·
              refine ⟨21958867064916249851477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 936911661436426660329685 21958867064916249851477)
              ·
                rfl

theorem cell21_865986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 7].length) (baseStart_865986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_865986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_865986 prefixEnd_865986 := by exact prefixLift 865986
  have htrace : WordTrace (prefixWord ++ tailWord_865986) baseStart_865986 baseEnd_865986 := by
    simpa [prefixWord, tailWord_865986, baseEnd_865986] using wordTrace_append hprefix tailTrace_865986
  have hstable : (prefixWord ++ tailWord_865986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865986).length < 2 ^ (prefixWord ++ tailWord_865986).sum := by decide
  have hdescent : baseEnd_865986 < baseStart_865986 := by decide
  rcases family_descends (prefixWord ++ tailWord_865986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866039 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 8]
def baseStart_866039 : Nat := 118140960795 + 866039 * 2 ^ 59
def prefixEnd_866039 : Nat := 4983230072969 + 3 ^ 40 * 866039 * 2
def baseEnd_866039 : Nat := 197641898906329934279851

theorem tailTrace_866039 : CollatzResearch.WordTrace tailWord_866039 prefixEnd_866039 197641898906329934279851 := by
  unfold tailWord_866039
  simp only [CollatzResearch.WordTrace]
  refine ⟨31587037309496085530777171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21058024872997390353851447 31587037309496085530777171)
  ·
    refine ⟨47380555964244128296165757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31587037309496085530777171 47380555964244128296165757)
    ·
      refine ⟨17767708486591548111062159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47380555964244128296165757 17767708486591548111062159)
      ·
        refine ⟨26651562729887322166593239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17767708486591548111062159 26651562729887322166593239)
        ·
          refine ⟨39977344094830983249889859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26651562729887322166593239 39977344094830983249889859)
          ·
            refine ⟨59966016142246474874834789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39977344094830983249889859 59966016142246474874834789)
            ·
              refine ⟨11243628026671214039031523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59966016142246474874834789 11243628026671214039031523)
              ·
                refine ⟨16865442040006821058547285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11243628026671214039031523 16865442040006821058547285)
                ·
                  refine ⟨197641898906329934279851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16865442040006821058547285 197641898906329934279851)
                  ·
                    rfl

theorem cell21_866039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_866039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866039 prefixEnd_866039 := by exact prefixLift 866039
  have htrace : WordTrace (prefixWord ++ tailWord_866039) baseStart_866039 baseEnd_866039 := by
    simpa [prefixWord, tailWord_866039, baseEnd_866039] using wordTrace_append hprefix tailTrace_866039
  have hstable : (prefixWord ++ tailWord_866039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866039).length < 2 ^ (prefixWord ++ tailWord_866039).sum := by decide
  have hdescent : baseEnd_866039 < baseStart_866039 := by decide
  rcases family_descends (prefixWord ++ tailWord_866039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866042 : List Nat := [3, 1, 1, 1, 1, 3, 1, 7, 3]
def baseStart_866042 : Nat := 118140960795 + 866042 * 2 ^ 59
def prefixEnd_866042 : Nat := 4983230072969 + 3 ^ 40 * 866042 * 2
def baseEnd_866042 : Nat := 197642583547202595729845

theorem tailTrace_866042 : CollatzResearch.WordTrace tailWord_866042 prefixEnd_866042 197642583547202595729845 := by
  unfold tailWord_866042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7896786682121304260784095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21058097818990144695424253 7896786682121304260784095)
  ·
    refine ⟨11845180023181956391176143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7896786682121304260784095 11845180023181956391176143)
    ·
      refine ⟨17767770034772934586764215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11845180023181956391176143 17767770034772934586764215)
      ·
        refine ⟨26651655052159401880146323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17767770034772934586764215 26651655052159401880146323)
        ·
          refine ⟨39977482578239102820219485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26651655052159401880146323 39977482578239102820219485)
          ·
            refine ⟨14991555966839663557582307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39977482578239102820219485 14991555966839663557582307)
            ·
              refine ⟨22487333950259495336373461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14991555966839663557582307 22487333950259495336373461)
              ·
                refine ⟨527046889459206921946253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22487333950259495336373461 527046889459206921946253)
                ·
                  refine ⟨197642583547202595729845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527046889459206921946253 197642583547202595729845)
                  ·
                    rfl

theorem cell21_866042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 3].length) (baseStart_866042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866042 prefixEnd_866042 := by exact prefixLift 866042
  have htrace : WordTrace (prefixWord ++ tailWord_866042) baseStart_866042 baseEnd_866042 := by
    simpa [prefixWord, tailWord_866042, baseEnd_866042] using wordTrace_append hprefix tailTrace_866042
  have hstable : (prefixWord ++ tailWord_866042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866042).length < 2 ^ (prefixWord ++ tailWord_866042).sum := by decide
  have hdescent : baseEnd_866042 < baseStart_866042 := by decide
  rcases family_descends (prefixWord ++ tailWord_866042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866059 : List Nat := [1, 1, 1, 1, 5, 1, 6, 2, 3]
def baseStart_866059 : Nat := 118140960795 + 866059 * 2 ^ 59
def prefixEnd_866059 : Nat := 4983230072969 + 3 ^ 40 * 866059 * 2
def baseEnd_866059 : Nat := 197646463178814343946477

theorem tailTrace_866059 : CollatzResearch.WordTrace tailWord_866059 prefixEnd_866059 197646463178814343946477 := by
  unfold tailWord_866059
  simp only [CollatzResearch.WordTrace]
  refine ⟨31587766769423628946505231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21058511179615752631003487 31587766769423628946505231)
  ·
    refine ⟨47381650154135443419757847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31587766769423628946505231 47381650154135443419757847)
    ·
      refine ⟨71072475231203165129636771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47381650154135443419757847 71072475231203165129636771)
      ·
        refine ⟨106608712846804747694455157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71072475231203165129636771 106608712846804747694455157)
        ·
          refine ⟨9994566829387945096355171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106608712846804747694455157 9994566829387945096355171)
          ·
            refine ⟨14991850244081917644532757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994566829387945096355171 14991850244081917644532757)
            ·
              refine ⟨702742980191339889587473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14991850244081917644532757 702742980191339889587473)
              ·
                refine ⟨527057235143504917190605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702742980191339889587473 527057235143504917190605)
                ·
                  refine ⟨197646463178814343946477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527057235143504917190605 197646463178814343946477)
                  ·
                    rfl

theorem cell21_866059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 3].length) (baseStart_866059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866059 prefixEnd_866059 := by exact prefixLift 866059
  have htrace : WordTrace (prefixWord ++ tailWord_866059) baseStart_866059 baseEnd_866059 := by
    simpa [prefixWord, tailWord_866059, baseEnd_866059] using wordTrace_append hprefix tailTrace_866059
  have hstable : (prefixWord ++ tailWord_866059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866059).length < 2 ^ (prefixWord ++ tailWord_866059).sum := by decide
  have hdescent : baseEnd_866059 < baseStart_866059 := by decide
  rcases family_descends (prefixWord ++ tailWord_866059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866183 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 4]
def baseStart_866183 : Nat := 118140960795 + 866183 * 2 ^ 59
def prefixEnd_866183 : Nat := 4983230072969 + 3 ^ 40 * 866183 * 2
def baseEnd_866183 : Nat := 197674761668217683879557

theorem tailTrace_866183 : CollatzResearch.WordTrace tailWord_866183 prefixEnd_866183 197674761668217683879557 := by
  unfold tailWord_866183
  simp only [CollatzResearch.WordTrace]
  refine ⟨31592289420974398124019203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21061526280649598749346135 31592289420974398124019203)
  ·
    refine ⟨47388434131461597186028805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31592289420974398124019203 47388434131461597186028805)
    ·
      refine ⟨8885331399649049472380401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47388434131461597186028805 8885331399649049472380401)
      ·
        refine ⟨6663998549736787104285301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8885331399649049472380401 6663998549736787104285301)
        ·
          refine ⟨624749864037823791026747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6663998549736787104285301 624749864037823791026747)
          ·
            refine ⟨937124796056735686540121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624749864037823791026747 937124796056735686540121)
            ·
              refine ⟨702843597042551764905091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937124796056735686540121 702843597042551764905091)
              ·
                refine ⟨1054265395563827647357637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702843597042551764905091 1054265395563827647357637)
                ·
                  refine ⟨197674761668217683879557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1054265395563827647357637 197674761668217683879557)
                  ·
                    rfl

theorem cell21_866183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 4].length) (baseStart_866183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866183 prefixEnd_866183 := by exact prefixLift 866183
  have htrace : WordTrace (prefixWord ++ tailWord_866183) baseStart_866183 baseEnd_866183 := by
    simpa [prefixWord, tailWord_866183, baseEnd_866183] using wordTrace_append hprefix tailTrace_866183
  have hstable : (prefixWord ++ tailWord_866183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866183).length < 2 ^ (prefixWord ++ tailWord_866183).sum := by decide
  have hdescent : baseEnd_866183 < baseStart_866183 := by decide
  rcases family_descends (prefixWord ++ tailWord_866183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866225 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 4]
def baseStart_866225 : Nat := 118140960795 + 866225 * 2 ^ 59
def prefixEnd_866225 : Nat := 4983230072969 + 3 ^ 40 * 866225 * 2
def baseEnd_866225 : Nat := 197684346640434944179471

theorem tailTrace_866225 : CollatzResearch.WordTrace tailWord_866225 prefixEnd_866225 197684346640434944179471 := by
  unfold tailWord_866225
  simp only [CollatzResearch.WordTrace]
  refine ⟨31593821286822239297048129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21062547524548159531365419 31593821286822239297048129)
  ·
    refine ⟨23695365965116679472786097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31593821286822239297048129 23695365965116679472786097)
    ·
      refine ⟨17771524473837509604589573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23695365965116679472786097 17771524473837509604589573)
      ·
        refine ⟨3332160838844533050860545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17771524473837509604589573 3332160838844533050860545)
        ·
          refine ⟨2499120629133399788145409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3332160838844533050860545 2499120629133399788145409)
          ·
            refine ⟨1874340471850049841109057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2499120629133399788145409 1874340471850049841109057)
            ·
              refine ⟨1405755353887537380831793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1874340471850049841109057 1405755353887537380831793)
              ·
                refine ⟨1054316515415653035623845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405755353887537380831793 1054316515415653035623845)
                ·
                  refine ⟨197684346640434944179471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1054316515415653035623845 197684346640434944179471)
                  ·
                    rfl

theorem cell21_866225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_866225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866225 prefixEnd_866225 := by exact prefixLift 866225
  have htrace : WordTrace (prefixWord ++ tailWord_866225) baseStart_866225 baseEnd_866225 := by
    simpa [prefixWord, tailWord_866225, baseEnd_866225] using wordTrace_append hprefix tailTrace_866225
  have hstable : (prefixWord ++ tailWord_866225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866225).length < 2 ^ (prefixWord ++ tailWord_866225).sum := by decide
  have hdescent : baseEnd_866225 < baseStart_866225 := by decide
  rcases family_descends (prefixWord ++ tailWord_866225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866346 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_866346 : Nat := 118140960795 + 866346 * 2 ^ 59
def prefixEnd_866346 : Nat := 4983230072969 + 3 ^ 40 * 866346 * 2
def baseEnd_866346 : Nat := 197711960488965622662557

theorem tailTrace_866346 : CollatzResearch.WordTrace tailWord_866346 prefixEnd_866346 197711960488965622662557 := by
  unfold tailWord_866346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7899558629845969240550723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21065489679589251308135261 7899558629845969240550723)
  ·
    refine ⟨11849337944768953860826085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7899558629845969240550723 11849337944768953860826085)
    ·
      refine ⟨2221750864644178848904891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11849337944768953860826085 2221750864644178848904891)
      ·
        refine ⟨3332626296966268273357337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221750864644178848904891 3332626296966268273357337)
        ·
          refine ⟨2499469722724701205018003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3332626296966268273357337 2499469722724701205018003)
          ·
            refine ⟨3749204584087051807527005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2499469722724701205018003 3749204584087051807527005)
            ·
              refine ⟨1405951719032644427822627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3749204584087051807527005 1405951719032644427822627)
              ·
                refine ⟨2108927578548966641733941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405951719032644427822627 2108927578548966641733941)
                ·
                  refine ⟨197711960488965622662557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2108927578548966641733941 197711960488965622662557)
                  ·
                    rfl

theorem cell21_866346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_866346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866346 prefixEnd_866346 := by exact prefixLift 866346
  have htrace : WordTrace (prefixWord ++ tailWord_866346) baseStart_866346 baseEnd_866346 := by
    simpa [prefixWord, tailWord_866346, baseEnd_866346] using wordTrace_append hprefix tailTrace_866346
  have hstable : (prefixWord ++ tailWord_866346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866346).length < 2 ^ (prefixWord ++ tailWord_866346).sum := by decide
  have hdescent : baseEnd_866346 < baseStart_866346 := by decide
  rcases family_descends (prefixWord ++ tailWord_866346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866397 : List Nat := [1, 4, 4, 1, 1, 3, 2, 2, 3]
def baseStart_866397 : Nat := 118140960795 + 866397 * 2 ^ 59
def prefixEnd_866397 : Nat := 4983230072969 + 3 ^ 40 * 866397 * 2
def baseEnd_866397 : Nat := 197723599383800867312453

theorem tailTrace_866397 : CollatzResearch.WordTrace tailWord_866397 prefixEnd_866397 197723599383800867312453 := by
  unfold tailWord_866397
  simp only [CollatzResearch.WordTrace]
  refine ⟨31600094642199112672309445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21066729761466075114872963 31600094642199112672309445)
  ·
    refine ⟨5925017745412333626058021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31600094642199112672309445 5925017745412333626058021)
    ·
      refine ⟨1110940827264812554885879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5925017745412333626058021 1110940827264812554885879)
      ·
        refine ⟨1666411240897218832328819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110940827264812554885879 1666411240897218832328819)
        ·
          refine ⟨2499616861345828248493229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1666411240897218832328819 2499616861345828248493229)
          ·
            refine ⟨937356323004685593184961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2499616861345828248493229 937356323004685593184961)
            ·
              refine ⟨703017242253514194888721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937356323004685593184961 703017242253514194888721)
              ·
                refine ⟨527262931690135646166541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703017242253514194888721 527262931690135646166541)
                ·
                  refine ⟨197723599383800867312453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527262931690135646166541 197723599383800867312453)
                  ·
                    rfl

theorem cell21_866397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_866397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866397 prefixEnd_866397 := by exact prefixLift 866397
  have htrace : WordTrace (prefixWord ++ tailWord_866397) baseStart_866397 baseEnd_866397 := by
    simpa [prefixWord, tailWord_866397, baseEnd_866397] using wordTrace_append hprefix tailTrace_866397
  have hstable : (prefixWord ++ tailWord_866397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866397).length < 2 ^ (prefixWord ++ tailWord_866397).sum := by decide
  have hdescent : baseEnd_866397 < baseStart_866397 := by decide
  rcases family_descends (prefixWord ++ tailWord_866397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866422 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_866422 : Nat := 118140960795 + 866422 * 2 ^ 59
def prefixEnd_866422 : Nat := 4983230072969 + 3 ^ 40 * 866422 * 2
def baseEnd_866422 : Nat := 197729304724406379395735

theorem tailTrace_866422 : CollatzResearch.WordTrace tailWord_866422 prefixEnd_866422 197729304724406379395735 := by
  unfold tailWord_866422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975062904194283871373095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21067337644739027961313013 1975062904194283871373095)
  ·
    refine ⟨2962594356291425807059643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1975062904194283871373095 2962594356291425807059643)
    ·
      refine ⟨4443891534437138710589465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2962594356291425807059643 4443891534437138710589465)
      ·
        refine ⟨3332918650827854032942099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4443891534437138710589465 3332918650827854032942099)
        ·
          refine ⟨4999377976241781049413149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3332918650827854032942099 4999377976241781049413149)
          ·
            refine ⟨1874766741090667893529931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4999377976241781049413149 1874766741090667893529931)
            ·
              refine ⟨2812150111636001840294897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874766741090667893529931 2812150111636001840294897)
              ·
                refine ⟨2109112583727001380221173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2812150111636001840294897 2109112583727001380221173)
                ·
                  refine ⟨197729304724406379395735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2109112583727001380221173 197729304724406379395735)
                  ·
                    rfl

theorem cell21_866422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_866422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866422 prefixEnd_866422 := by exact prefixLift 866422
  have htrace : WordTrace (prefixWord ++ tailWord_866422) baseStart_866422 baseEnd_866422 := by
    simpa [prefixWord, tailWord_866422, baseEnd_866422] using wordTrace_append hprefix tailTrace_866422
  have hstable : (prefixWord ++ tailWord_866422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866422).length < 2 ^ (prefixWord ++ tailWord_866422).sum := by decide
  have hdescent : baseEnd_866422 < baseStart_866422 := by decide
  rcases family_descends (prefixWord ++ tailWord_866422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866450 : List Nat := [3, 2, 3, 1, 1, 1, 10]
def baseStart_866450 : Nat := 118140960795 + 866450 * 2 ^ 59
def prefixEnd_866450 : Nat := 4983230072969 + 3 ^ 40 * 866450 * 2
def baseEnd_866450 : Nat := 21970632745098283658779

theorem tailTrace_866450 : CollatzResearch.WordTrace tailWord_866450 prefixEnd_866450 21970632745098283658779 := by
  unfold tailWord_866450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7900506927751775680997201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21068018474004735149325869 7900506927751775680997201)
  ·
    refine ⟨5925380195813831760747901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7900506927751775680997201 5925380195813831760747901)
    ·
      refine ⟨2222017573430186910280463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5925380195813831760747901 2222017573430186910280463)
      ·
        refine ⟨3333026360145280365420695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2222017573430186910280463 3333026360145280365420695)
        ·
          refine ⟨4999539540217920548131043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333026360145280365420695 4999539540217920548131043)
          ·
            refine ⟨7499309310326880822196565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4999539540217920548131043 7499309310326880822196565)
            ·
              refine ⟨21970632745098283658779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7499309310326880822196565 21970632745098283658779)
              ·
                rfl

theorem cell21_866450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 10].length) (baseStart_866450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866450 prefixEnd_866450 := by exact prefixLift 866450
  have htrace : WordTrace (prefixWord ++ tailWord_866450) baseStart_866450 baseEnd_866450 := by
    simpa [prefixWord, tailWord_866450, baseEnd_866450] using wordTrace_append hprefix tailTrace_866450
  have hstable : (prefixWord ++ tailWord_866450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866450).length < 2 ^ (prefixWord ++ tailWord_866450).sum := by decide
  have hdescent : baseEnd_866450 < baseStart_866450 := by decide
  rcases family_descends (prefixWord ++ tailWord_866450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866540 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_866540 : Nat := 118140960795 + 866540 * 2 ^ 59
def prefixEnd_866540 : Nat := 4983230072969 + 3 ^ 40 * 866540 * 2
def baseEnd_866540 : Nat := 197756233932064396428827

theorem tailTrace_866540 : CollatzResearch.WordTrace tailWord_866540 prefixEnd_866540 197756233932064396428827 := by
  unfold tailWord_866540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15802655140340524047382537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21070206853787365396510049 15802655140340524047382537)
  ·
    refine ⟨11851991355255393035536903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15802655140340524047382537 11851991355255393035536903)
    ·
      refine ⟨17777987032883089553305355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11851991355255393035536903 17777987032883089553305355)
      ·
        refine ⟨26666980549324634329958033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17777987032883089553305355 26666980549324634329958033)
        ·
          refine ⟨20000235411993475747468525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26666980549324634329958033 20000235411993475747468525)
          ·
            refine ⟨7500088279497553405300697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20000235411993475747468525 7500088279497553405300697)
            ·
              refine ⟨5625066209623165053975523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7500088279497553405300697 5625066209623165053975523)
              ·
                refine ⟨8437599314434747580963285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5625066209623165053975523 8437599314434747580963285)
                ·
                  refine ⟨197756233932064396428827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8437599314434747580963285 197756233932064396428827)
                  ·
                    rfl

theorem cell21_866540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_866540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866540 prefixEnd_866540 := by exact prefixLift 866540
  have htrace : WordTrace (prefixWord ++ tailWord_866540) baseStart_866540 baseEnd_866540 := by
    simpa [prefixWord, tailWord_866540, baseEnd_866540] using wordTrace_append hprefix tailTrace_866540
  have hstable : (prefixWord ++ tailWord_866540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866540).length < 2 ^ (prefixWord ++ tailWord_866540).sum := by decide
  have hdescent : baseEnd_866540 < baseStart_866540 := by decide
  rcases family_descends (prefixWord ++ tailWord_866540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866574 : List Nat := [4, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_866574 : Nat := 118140960795 + 866574 * 2 ^ 59
def prefixEnd_866574 : Nat := 4983230072969 + 3 ^ 40 * 866574 * 2
def baseEnd_866574 : Nat := 197763993195287892862091

theorem tailTrace_866574 : CollatzResearch.WordTrace tailWord_866574 prefixEnd_866574 197763993195287892862091 := by
  unfold tailWord_866574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3950818795319733987687847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21071033575038581267668517 3950818795319733987687847)
  ·
    refine ⟨5926228192979600981531771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3950818795319733987687847 5926228192979600981531771)
    ·
      refine ⟨8889342289469401472297657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5926228192979600981531771 8889342289469401472297657)
      ·
        refine ⟨6667006717102051104223243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8889342289469401472297657 6667006717102051104223243)
        ·
          refine ⟨10000510075653076656334865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6667006717102051104223243 10000510075653076656334865)
          ·
            refine ⟨7500382556739807492251149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10000510075653076656334865 7500382556739807492251149)
            ·
              refine ⟨2812643458777427809594181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7500382556739807492251149 2812643458777427809594181)
              ·
                refine ⟨527370648520767714298909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2812643458777427809594181 527370648520767714298909)
                ·
                  refine ⟨197763993195287892862091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527370648520767714298909 197763993195287892862091)
                  ·
                    rfl

theorem cell21_866574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_866574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866574 prefixEnd_866574 := by exact prefixLift 866574
  have htrace : WordTrace (prefixWord ++ tailWord_866574) baseStart_866574 baseEnd_866574 := by
    simpa [prefixWord, tailWord_866574, baseEnd_866574] using wordTrace_append hprefix tailTrace_866574
  have hstable : (prefixWord ++ tailWord_866574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866574).length < 2 ^ (prefixWord ++ tailWord_866574).sum := by decide
  have hdescent : baseEnd_866574 < baseStart_866574 := by decide
  rcases family_descends (prefixWord ++ tailWord_866574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866737 : List Nat := [1, 2, 2, 4, 1, 11]
def baseStart_866737 : Nat := 118140960795 + 866737 * 2 ^ 59
def prefixEnd_866737 : Nat := 4983230072969 + 3 ^ 40 * 866737 * 2
def baseEnd_866737 : Nat := 7325970074667993764633

theorem tailTrace_866737 : CollatzResearch.WordTrace tailWord_866737 prefixEnd_866737 7325970074667993764633 := by
  unfold tailWord_866737
  simp only [CollatzResearch.WordTrace]
  refine ⟨31612495460967350739686465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21074996973978233826457643 31612495460967350739686465)
  ·
    refine ⟨23709371595725513054764849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31612495460967350739686465 23709371595725513054764849)
    ·
      refine ⟨17782028696794134791073637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23709371595725513054764849 17782028696794134791073637)
      ·
        refine ⟨3334130380648900273326307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17782028696794134791073637 3334130380648900273326307)
        ·
          refine ⟨5001195570973350409989461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334130380648900273326307 5001195570973350409989461)
          ·
            refine ⟨7325970074667993764633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5001195570973350409989461 7325970074667993764633)
            ·
              rfl

theorem cell21_866737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 11].length) (baseStart_866737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866737 prefixEnd_866737 := by exact prefixLift 866737
  have htrace : WordTrace (prefixWord ++ tailWord_866737) baseStart_866737 baseEnd_866737 := by
    simpa [prefixWord, tailWord_866737, baseEnd_866737] using wordTrace_append hprefix tailTrace_866737
  have hstable : (prefixWord ++ tailWord_866737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866737).length < 2 ^ (prefixWord ++ tailWord_866737).sum := by decide
  have hdescent : baseEnd_866737 < baseStart_866737 := by decide
  rcases family_descends (prefixWord ++ tailWord_866737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866743 : List Nat := [1, 1, 3, 1, 3, 5, 2, 2, 3]
def baseStart_866743 : Nat := 118140960795 + 866743 * 2 ^ 59
def prefixEnd_866743 : Nat := 4983230072969 + 3 ^ 40 * 866743 * 2
def baseEnd_866743 : Nat := 197802561297781154545079

theorem tailTrace_866743 : CollatzResearch.WordTrace tailWord_866743 prefixEnd_866743 197802561297781154545079 := by
  unfold tailWord_866743
  simp only [CollatzResearch.WordTrace]
  refine ⟨31612714298945613764404883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21075142865963742509603255 31612714298945613764404883)
  ·
    refine ⟨47419071448418420646607325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31612714298945613764404883 47419071448418420646607325)
    ·
      refine ⟨17782151793156907742477747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47419071448418420646607325 17782151793156907742477747)
      ·
        refine ⟨26673227689735361613716621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17782151793156907742477747 26673227689735361613716621)
        ·
          refine ⟨10002460383650760605143733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26673227689735361613716621 10002460383650760605143733)
          ·
            refine ⟨937730660967258806732225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10002460383650760605143733 937730660967258806732225)
            ·
              refine ⟨703297995725444105049169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937730660967258806732225 703297995725444105049169)
              ·
                refine ⟨527473496794083078786877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703297995725444105049169 527473496794083078786877)
                ·
                  refine ⟨197802561297781154545079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527473496794083078786877 197802561297781154545079)
                  ·
                    rfl

theorem cell21_866743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 3].length) (baseStart_866743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866743 prefixEnd_866743 := by exact prefixLift 866743
  have htrace : WordTrace (prefixWord ++ tailWord_866743) baseStart_866743 baseEnd_866743 := by
    simpa [prefixWord, tailWord_866743, baseEnd_866743] using wordTrace_append hprefix tailTrace_866743
  have hstable : (prefixWord ++ tailWord_866743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866743).length < 2 ^ (prefixWord ++ tailWord_866743).sum := by decide
  have hdescent : baseEnd_866743 < baseStart_866743 := by decide
  rcases family_descends (prefixWord ++ tailWord_866743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866802 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_866802 : Nat := 118140960795 + 866802 * 2 ^ 59
def prefixEnd_866802 : Nat := 4983230072969 + 3 ^ 40 * 866802 * 2
def baseEnd_866802 : Nat := 197816025901610163061625

theorem tailTrace_866802 : CollatzResearch.WordTrace tailWord_866802 prefixEnd_866802 197816025901610163061625 := by
  unfold tailWord_866802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7903716551432966710200665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21076577470487911227201773 7903716551432966710200665)
  ·
    refine ⟨5927787413574725032650499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7903716551432966710200665 5927787413574725032650499)
    ·
      refine ⟨8891681120362087548975749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5927787413574725032650499 8891681120362087548975749)
      ·
        refine ⟨1667190210067891415432953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8891681120362087548975749 1667190210067891415432953)
        ·
          refine ⟨1250392657550918561574715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1667190210067891415432953 1250392657550918561574715)
          ·
            refine ⟨1875588986326377842362073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250392657550918561574715 1875588986326377842362073)
            ·
              refine ⟨1406691739744783381771555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875588986326377842362073 1406691739744783381771555)
              ·
                refine ⟨2110037609617175072657333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406691739744783381771555 2110037609617175072657333)
                ·
                  refine ⟨197816025901610163061625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2110037609617175072657333 197816025901610163061625)
                  ·
                    rfl

theorem cell21_866802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_866802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866802 prefixEnd_866802 := by exact prefixLift 866802
  have htrace : WordTrace (prefixWord ++ tailWord_866802) baseStart_866802 baseEnd_866802 := by
    simpa [prefixWord, tailWord_866802, baseEnd_866802] using wordTrace_append hprefix tailTrace_866802
  have hstable : (prefixWord ++ tailWord_866802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866802).length < 2 ^ (prefixWord ++ tailWord_866802).sum := by decide
  have hdescent : baseEnd_866802 < baseStart_866802 := by decide
  rcases family_descends (prefixWord ++ tailWord_866802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866813 : List Nat := [1, 4, 1, 1, 1, 3, 2, 8]
def baseStart_866813 : Nat := 118140960795 + 866813 * 2 ^ 59
def prefixEnd_866813 : Nat := 4983230072969 + 3 ^ 40 * 866813 * 2
def baseEnd_866813 : Nat := 65939512083825529459423

theorem tailTrace_866813 : CollatzResearch.WordTrace tailWord_866813 prefixEnd_866813 65939512083825529459423 := by
  unfold tailWord_866813
  simp only [CollatzResearch.WordTrace]
  refine ⟨31615267408692015719453093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21076844939128010479635395 31615267408692015719453093)
  ·
    refine ⟨5927862639129752947397455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31615267408692015719453093 5927862639129752947397455)
    ·
      refine ⟨8891793958694629421096183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5927862639129752947397455 8891793958694629421096183)
      ·
        refine ⟨13337690938041944131644275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8891793958694629421096183 13337690938041944131644275)
        ·
          refine ⟨20006536407062916197466413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13337690938041944131644275 20006536407062916197466413)
          ·
            refine ⟨7502451152648593574049905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20006536407062916197466413 7502451152648593574049905)
            ·
              refine ⟨5626838364486445180537429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7502451152648593574049905 5626838364486445180537429)
              ·
                refine ⟨65939512083825529459423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5626838364486445180537429 65939512083825529459423)
                ·
                  rfl

theorem cell21_866813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 8].length) (baseStart_866813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866813 prefixEnd_866813 := by exact prefixLift 866813
  have htrace : WordTrace (prefixWord ++ tailWord_866813) baseStart_866813 baseEnd_866813 := by
    simpa [prefixWord, tailWord_866813, baseEnd_866813] using wordTrace_append hprefix tailTrace_866813
  have hstable : (prefixWord ++ tailWord_866813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866813).length < 2 ^ (prefixWord ++ tailWord_866813).sum := by decide
  have hdescent : baseEnd_866813 < baseStart_866813 := by decide
  rcases family_descends (prefixWord ++ tailWord_866813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866822 : List Nat := [6, 2, 1, 1, 1, 3, 2, 5]
def baseStart_866822 : Nat := 118140960795 + 866822 * 2 ^ 59
def prefixEnd_866822 : Nat := 4983230072969 + 3 ^ 40 * 866822 * 2
def baseEnd_866822 : Nat := 65940196724698190909417

theorem tailTrace_866822 : CollatzResearch.WordTrace tailWord_866822 prefixEnd_866822 65940196724698190909417 := by
  unfold tailWord_866822
  simp only [CollatzResearch.WordTrace]
  refine ⟨987987364551856570516585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21077063777106273504353813 987987364551856570516585)
  ·
    refine ⟨740990523413892427887439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 987987364551856570516585 740990523413892427887439)
    ·
      refine ⟨1111485785120838641831159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 740990523413892427887439 1111485785120838641831159)
      ·
        refine ⟨1667228677681257962746739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1111485785120838641831159 1667228677681257962746739)
        ·
          refine ⟨2500843016521886944120109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667228677681257962746739 2500843016521886944120109)
          ·
            refine ⟨937816131195707604045041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2500843016521886944120109 937816131195707604045041)
            ·
              refine ⟨703362098396780703033781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937816131195707604045041 703362098396780703033781)
              ·
                refine ⟨65940196724698190909417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 703362098396780703033781 65940196724698190909417)
                ·
                  rfl

theorem cell21_866822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_866822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866822 prefixEnd_866822 := by exact prefixLift 866822
  have htrace : WordTrace (prefixWord ++ tailWord_866822) baseStart_866822 baseEnd_866822 := by
    simpa [prefixWord, tailWord_866822, baseEnd_866822] using wordTrace_append hprefix tailTrace_866822
  have hstable : (prefixWord ++ tailWord_866822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866822).length < 2 ^ (prefixWord ++ tailWord_866822).sum := by decide
  have hdescent : baseEnd_866822 < baseStart_866822 := by decide
  rcases family_descends (prefixWord ++ tailWord_866822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866830 : List Nat := [4, 1, 1, 2, 3, 2, 1, 7]
def baseStart_866830 : Nat := 118140960795 + 866830 * 2 ^ 59
def prefixEnd_866830 : Nat := 4983230072969 + 3 ^ 40 * 866830 * 2
def baseEnd_866830 : Nat := 65940805294362778864967

theorem tailTrace_866830 : CollatzResearch.WordTrace tailWord_866830 prefixEnd_866830 65940805294362778864967 := by
  unfold tailWord_866830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3951985931203803452852743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21077258299753618415214629 3951985931203803452852743)
  ·
    refine ⟨5927978896805705179279115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3951985931203803452852743 5927978896805705179279115)
    ·
      refine ⟨8891968345208557768918673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5927978896805705179279115 8891968345208557768918673)
      ·
        refine ⟨6668976258906418326689005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8891968345208557768918673 6668976258906418326689005)
        ·
          refine ⟨2500866097089906872508377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6668976258906418326689005 2500866097089906872508377)
          ·
            refine ⟨1875649572817430154381283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500866097089906872508377 1875649572817430154381283)
            ·
              refine ⟨2813474359226145231571925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875649572817430154381283 2813474359226145231571925)
              ·
                refine ⟨65940805294362778864967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2813474359226145231571925 65940805294362778864967)
                ·
                  rfl

theorem cell21_866830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_866830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866830 prefixEnd_866830 := by exact prefixLift 866830
  have htrace : WordTrace (prefixWord ++ tailWord_866830) baseStart_866830 baseEnd_866830 := by
    simpa [prefixWord, tailWord_866830, baseEnd_866830] using wordTrace_append hprefix tailTrace_866830
  have hstable : (prefixWord ++ tailWord_866830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866830).length < 2 ^ (prefixWord ++ tailWord_866830).sum := by decide
  have hdescent : baseEnd_866830 < baseStart_866830 := by decide
  rcases family_descends (prefixWord ++ tailWord_866830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866836 : List Nat := [2, 4, 3, 1, 1, 3, 1, 3, 3]
def baseStart_866836 : Nat := 118140960795 + 866836 * 2 ^ 59
def prefixEnd_866836 : Nat := 4983230072969 + 3 ^ 40 * 866836 * 2
def baseEnd_866836 : Nat := 197823785164833659494889

theorem tailTrace_866836 : CollatzResearch.WordTrace tailWord_866836 prefixEnd_866836 197823785164833659494889 := by
  unfold tailWord_866836
  simp only [CollatzResearch.WordTrace]
  refine ⟨15808053143804345323770181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21077404191739127098360241 15808053143804345323770181)
  ·
    refine ⟨2964009964463314748206909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15808053143804345323770181 2964009964463314748206909)
    ·
      refine ⟨1111503736673743030577591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2964009964463314748206909 1111503736673743030577591)
      ·
        refine ⟨1667255605010614545866387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1111503736673743030577591 1667255605010614545866387)
        ·
          refine ⟨2500883407515921818799581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667255605010614545866387 2500883407515921818799581)
          ·
            refine ⟨937831277818470682049843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2500883407515921818799581 937831277818470682049843)
            ·
              refine ⟨1406746916727706023074765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937831277818470682049843 1406746916727706023074765)
              ·
                refine ⟨527530093772889758653037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1406746916727706023074765 527530093772889758653037)
                ·
                  refine ⟨197823785164833659494889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527530093772889758653037 197823785164833659494889)
                  ·
                    rfl

theorem cell21_866836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_866836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866836 prefixEnd_866836 := by exact prefixLift 866836
  have htrace : WordTrace (prefixWord ++ tailWord_866836) baseStart_866836 baseEnd_866836 := by
    simpa [prefixWord, tailWord_866836, baseEnd_866836] using wordTrace_append hprefix tailTrace_866836
  have hstable : (prefixWord ++ tailWord_866836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866836).length < 2 ^ (prefixWord ++ tailWord_866836).sum := by decide
  have hdescent : baseEnd_866836 < baseStart_866836 := by decide
  rcases family_descends (prefixWord ++ tailWord_866836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866999 : List Nat := [1, 1, 3, 1, 6, 2, 2, 5]
def baseStart_866999 : Nat := 118140960795 + 866999 * 2 ^ 59
def prefixEnd_866999 : Nat := 4983230072969 + 3 ^ 40 * 866999 * 2
def baseEnd_866999 : Nat := 65953661328527199425963

theorem tailTrace_866999 : CollatzResearch.WordTrace tailWord_866999 prefixEnd_866999 65953661328527199425963 := by
  unfold tailWord_866999
  simp only [CollatzResearch.WordTrace]
  refine ⟨31622051386018169485724051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21081367590678779657149367 31622051386018169485724051)
  ·
    refine ⟨47433077079027254228586077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31622051386018169485724051 47433077079027254228586077)
    ·
      refine ⟨17787403904635220335719779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47433077079027254228586077 17787403904635220335719779)
      ·
        refine ⟨26681105856952830503579669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17787403904635220335719779 26681105856952830503579669)
        ·
          refine ⟨1250676837044663929855297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26681105856952830503579669 1250676837044663929855297)
          ·
            refine ⟨938007627783497947391473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1250676837044663929855297 938007627783497947391473)
            ·
              refine ⟨703505720837623460543605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 938007627783497947391473 703505720837623460543605)
              ·
                refine ⟨65953661328527199425963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 703505720837623460543605 65953661328527199425963)
                ·
                  rfl

theorem cell21_866999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 5].length) (baseStart_866999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_866999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_866999 prefixEnd_866999 := by exact prefixLift 866999
  have htrace : WordTrace (prefixWord ++ tailWord_866999) baseStart_866999 baseEnd_866999 := by
    simpa [prefixWord, tailWord_866999, baseEnd_866999] using wordTrace_append hprefix tailTrace_866999
  have hstable : (prefixWord ++ tailWord_866999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866999).length < 2 ^ (prefixWord ++ tailWord_866999).sum := by decide
  have hdescent : baseEnd_866999 < baseStart_866999 := by decide
  rcases family_descends (prefixWord ++ tailWord_866999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867041 : List Nat := [1, 2, 3, 1, 4, 1, 1, 8]
def baseStart_867041 : Nat := 118140960795 + 867041 * 2 ^ 59
def prefixEnd_867041 : Nat := 4983230072969 + 3 ^ 40 * 867041 * 2
def baseEnd_867041 : Nat := 65956856319266286192601

theorem tailTrace_867041 : CollatzResearch.WordTrace tailWord_867041 prefixEnd_867041 65956856319266286192601 := by
  unfold tailWord_867041
  simp only [CollatzResearch.WordTrace]
  refine ⟨31623583251866010658752977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21082388834577340439168651 31623583251866010658752977)
  ·
    refine ⟨23717687438899507994064733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31623583251866010658752977 23717687438899507994064733)
    ·
      refine ⟨8894132789587315497774275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23717687438899507994064733 8894132789587315497774275)
      ·
        refine ⟨13341199184380973246661413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8894132789587315497774275 13341199184380973246661413)
        ·
          refine ⟨2501474847071432483749015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13341199184380973246661413 2501474847071432483749015)
          ·
            refine ⟨3752212270607148725623523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501474847071432483749015 3752212270607148725623523)
            ·
              refine ⟨5628318405910723088435285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752212270607148725623523 5628318405910723088435285)
              ·
                refine ⟨65956856319266286192601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5628318405910723088435285 65956856319266286192601)
                ·
                  rfl

theorem cell21_867041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 8].length) (baseStart_867041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867041 prefixEnd_867041 := by exact prefixLift 867041
  have htrace : WordTrace (prefixWord ++ tailWord_867041) baseStart_867041 baseEnd_867041 := by
    simpa [prefixWord, tailWord_867041, baseEnd_867041] using wordTrace_append hprefix tailTrace_867041
  have hstable : (prefixWord ++ tailWord_867041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867041).length < 2 ^ (prefixWord ++ tailWord_867041).sum := by decide
  have hdescent : baseEnd_867041 < baseStart_867041 := by decide
  rcases family_descends (prefixWord ++ tailWord_867041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867044 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 4]
def baseStart_867044 : Nat := 118140960795 + 867044 * 2 ^ 59
def prefixEnd_867044 : Nat := 4983230072969 + 3 ^ 40 * 867044 * 2
def baseEnd_867044 : Nat := 197871253598671520027797

theorem tailTrace_867044 : CollatzResearch.WordTrace tailWord_867044 prefixEnd_867044 197871253598671520027797 := by
  unfold tailWord_867044
  simp only [CollatzResearch.WordTrace]
  refine ⟨15811846335427571085556093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21082461780570094780741457 15811846335427571085556093)
  ·
    refine ⟨5929442375785339157083535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15811846335427571085556093 5929442375785339157083535)
    ·
      refine ⟨8894163563678008735625303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5929442375785339157083535 8894163563678008735625303)
      ·
        refine ⟨13341245345517013103437955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8894163563678008735625303 13341245345517013103437955)
        ·
          refine ⟨20011868018275519655156933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13341245345517013103437955 20011868018275519655156933)
          ·
            refine ⟨3752225253426659935341925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20011868018275519655156933 3752225253426659935341925)
            ·
              refine ⟨703542235017498737876611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3752225253426659935341925 703542235017498737876611)
              ·
                refine ⟨1055313352526248106814917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703542235017498737876611 1055313352526248106814917)
                ·
                  refine ⟨197871253598671520027797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055313352526248106814917 197871253598671520027797)
                  ·
                    rfl

theorem cell21_867044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_867044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867044 prefixEnd_867044 := by exact prefixLift 867044
  have htrace : WordTrace (prefixWord ++ tailWord_867044) baseStart_867044 baseEnd_867044 := by
    simpa [prefixWord, tailWord_867044, baseEnd_867044] using wordTrace_append hprefix tailTrace_867044
  have hstable : (prefixWord ++ tailWord_867044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867044).length < 2 ^ (prefixWord ++ tailWord_867044).sum := by decide
  have hdescent : baseEnd_867044 < baseStart_867044 := by decide
  rcases family_descends (prefixWord ++ tailWord_867044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867103 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 4]
def baseStart_867103 : Nat := 118140960795 + 867103 * 2 ^ 59
def prefixEnd_867103 : Nat := 4983230072969 + 3 ^ 40 * 867103 * 2
def baseEnd_867103 : Nat := 197884718202500528544343

theorem tailTrace_867103 : CollatzResearch.WordTrace tailWord_867103 prefixEnd_867103 197884718202500528544343 := by
  unfold tailWord_867103
  simp only [CollatzResearch.WordTrace]
  refine ⟨31625844577641395247509963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21083896385094263498339975 31625844577641395247509963)
  ·
    refine ⟨47438766866462092871264945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31625844577641395247509963 47438766866462092871264945)
    ·
      refine ⟨35579075149846569653448709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47438766866462092871264945 35579075149846569653448709)
      ·
        refine ⟨6671076590596231810021633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35579075149846569653448709 6671076590596231810021633)
        ·
          refine ⟨5003307442947173857516225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6671076590596231810021633 5003307442947173857516225)
          ·
            refine ⟨3752480582210380393137169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5003307442947173857516225 3752480582210380393137169)
            ·
              refine ⟨2814360436657785294852877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3752480582210380393137169 2814360436657785294852877)
              ·
                refine ⟨1055385163746669485569829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2814360436657785294852877 1055385163746669485569829)
                ·
                  refine ⟨197884718202500528544343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1055385163746669485569829 197884718202500528544343)
                  ·
                    rfl

theorem cell21_867103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 4].length) (baseStart_867103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867103 prefixEnd_867103 := by exact prefixLift 867103
  have htrace : WordTrace (prefixWord ++ tailWord_867103) baseStart_867103 baseEnd_867103 := by
    simpa [prefixWord, tailWord_867103, baseEnd_867103] using wordTrace_append hprefix tailTrace_867103
  have hstable : (prefixWord ++ tailWord_867103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867103).length < 2 ^ (prefixWord ++ tailWord_867103).sum := by decide
  have hdescent : baseEnd_867103 < baseStart_867103 := by decide
  rcases family_descends (prefixWord ++ tailWord_867103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867134 : List Nat := [4, 2, 1, 2, 3, 1, 8]
def baseStart_867134 : Nat := 118140960795 + 867134 * 2 ^ 59
def prefixEnd_867134 : Nat := 4983230072969 + 3 ^ 40 * 867134 * 2
def baseEnd_867134 : Nat := 21987976980539040391957

theorem tailTrace_867134 : CollatzResearch.WordTrace tailWord_867134 prefixEnd_867134 21987976980539040391957 := by
  unfold tailWord_867134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3953371905066135942736057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21084650160352725027925637 3953371905066135942736057)
  ·
    refine ⟨2965028928799601957052043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3953371905066135942736057 2965028928799601957052043)
    ·
      refine ⟨4447543393199402935578065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2965028928799601957052043 4447543393199402935578065)
      ·
        refine ⟨3335657544899552201683549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4447543393199402935578065 3335657544899552201683549)
        ·
          refine ⟨1250871579337332075631331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3335657544899552201683549 1250871579337332075631331)
          ·
            refine ⟨1876307369005998113446997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250871579337332075631331 1876307369005998113446997)
            ·
              refine ⟨21987976980539040391957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1876307369005998113446997 21987976980539040391957)
              ·
                rfl

theorem cell21_867134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 8].length) (baseStart_867134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867134 prefixEnd_867134 := by exact prefixLift 867134
  have htrace : WordTrace (prefixWord ++ tailWord_867134) baseStart_867134 baseEnd_867134 := by
    simpa [prefixWord, tailWord_867134, baseEnd_867134] using wordTrace_append hprefix tailTrace_867134
  have hstable : (prefixWord ++ tailWord_867134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867134).length < 2 ^ (prefixWord ++ tailWord_867134).sum := by decide
  have hdescent : baseEnd_867134 < baseStart_867134 := by decide
  rcases family_descends (prefixWord ++ tailWord_867134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867148 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 5]
def baseStart_867148 : Nat := 118140960795 + 867148 * 2 ^ 59
def prefixEnd_867148 : Nat := 4983230072969 + 3 ^ 40 * 867148 * 2
def baseEnd_867148 : Nat := 197894987815590450294251

theorem tailTrace_867148 : CollatzResearch.WordTrace tailWord_867148 prefixEnd_867148 197894987815590450294251 := by
  unfold tailWord_867148
  simp only [CollatzResearch.WordTrace]
  refine ⟨15813742931239183966449049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21084990574985578621932065 15813742931239183966449049)
  ·
    refine ⟨11860307198429387974836787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15813742931239183966449049 11860307198429387974836787)
    ·
      refine ⟨17790460797644081962255181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11860307198429387974836787 17790460797644081962255181)
      ·
        refine ⟨6671422799116530735845693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17790460797644081962255181 6671422799116530735845693)
        ·
          refine ⟨2501783549668699025942135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6671422799116530735845693 2501783549668699025942135)
          ·
            refine ⟨3752675324503048538913203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501783549668699025942135 3752675324503048538913203)
            ·
              refine ⟨5629012986754572808369805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3752675324503048538913203 5629012986754572808369805)
              ·
                refine ⟨2110879870032964803138677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5629012986754572808369805 2110879870032964803138677)
                ·
                  refine ⟨197894987815590450294251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2110879870032964803138677 197894987815590450294251)
                  ·
                    rfl

theorem cell21_867148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_867148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867148 prefixEnd_867148 := by exact prefixLift 867148
  have htrace : WordTrace (prefixWord ++ tailWord_867148) baseStart_867148 baseEnd_867148 := by
    simpa [prefixWord, tailWord_867148, baseEnd_867148] using wordTrace_append hprefix tailTrace_867148
  have hstable : (prefixWord ++ tailWord_867148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867148).length < 2 ^ (prefixWord ++ tailWord_867148).sum := by decide
  have hdescent : baseEnd_867148 < baseStart_867148 := by decide
  rcases family_descends (prefixWord ++ tailWord_867148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867193 : List Nat := [1, 2, 1, 3, 2, 5, 7]
def baseStart_867193 : Nat := 118140960795 + 867193 * 2 ^ 59
def prefixEnd_867193 : Nat := 4983230072969 + 3 ^ 40 * 867193 * 2
def baseEnd_867193 : Nat := 21989473047631152449351

theorem tailTrace_867193 : CollatzResearch.WordTrace tailWord_867193 prefixEnd_867193 21989473047631152449351 := by
  unfold tailWord_867193
  simp only [CollatzResearch.WordTrace]
  refine ⟨31629127147315340618286233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21086084764876893745524155 31629127147315340618286233)
  ·
    refine ⟨23721845360486505463714675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31629127147315340618286233 23721845360486505463714675)
    ·
      refine ⟨35582768040729758195572013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23721845360486505463714675 35582768040729758195572013)
      ·
        refine ⟨13343538015273659323339505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35582768040729758195572013 13343538015273659323339505)
        ·
          refine ⟨10007653511455244492504629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13343538015273659323339505 10007653511455244492504629)
          ·
            refine ⟨938217516698929171172309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10007653511455244492504629 938217516698929171172309)
            ·
              refine ⟨21989473047631152449351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 938217516698929171172309 21989473047631152449351)
              ·
                rfl

theorem cell21_867193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 7].length) (baseStart_867193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867193 prefixEnd_867193 := by exact prefixLift 867193
  have htrace : WordTrace (prefixWord ++ tailWord_867193) baseStart_867193 baseEnd_867193 := by
    simpa [prefixWord, tailWord_867193, baseEnd_867193] using wordTrace_append hprefix tailTrace_867193
  have hstable : (prefixWord ++ tailWord_867193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867193).length < 2 ^ (prefixWord ++ tailWord_867193).sum := by decide
  have hdescent : baseEnd_867193 < baseStart_867193 := by decide
  rcases family_descends (prefixWord ++ tailWord_867193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867210 : List Nat := [3, 1, 2, 4, 1, 2, 2, 6]
def baseStart_867210 : Nat := 118140960795 + 867210 * 2 ^ 59
def prefixEnd_867210 : Nat := 4983230072969 + 3 ^ 40 * 867210 * 2
def baseEnd_867210 : Nat := 65969712353430706753597

theorem tailTrace_867210 : CollatzResearch.WordTrace tailWord_867210 prefixEnd_867210 65969712353430706753597 := by
  unfold tailWord_867210
  simp only [CollatzResearch.WordTrace]
  refine ⟨7907436797063438130413771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21086498125502501681103389 7907436797063438130413771)
  ·
    refine ⟨11861155195595157195620657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7907436797063438130413771 11861155195595157195620657)
    ·
      refine ⟨8895866396696367896715493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11861155195595157195620657 8895866396696367896715493)
      ·
        refine ⟨1667974949380568980634155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8895866396696367896715493 1667974949380568980634155)
        ·
          refine ⟨2501962424070853470951233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667974949380568980634155 2501962424070853470951233)
          ·
            refine ⟨1876471818053140103213425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2501962424070853470951233 1876471818053140103213425)
            ·
              refine ⟨1407353863539855077410069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1876471818053140103213425 1407353863539855077410069)
              ·
                refine ⟨65969712353430706753597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1407353863539855077410069 65969712353430706753597)
                ·
                  rfl

theorem cell21_867210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 6].length) (baseStart_867210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867210 prefixEnd_867210 := by exact prefixLift 867210
  have htrace : WordTrace (prefixWord ++ tailWord_867210) baseStart_867210 baseEnd_867210 := by
    simpa [prefixWord, tailWord_867210, baseEnd_867210] using wordTrace_append hprefix tailTrace_867210
  have hstable : (prefixWord ++ tailWord_867210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867210).length < 2 ^ (prefixWord ++ tailWord_867210).sum := by decide
  have hdescent : baseEnd_867210 < baseStart_867210 := by decide
  rcases family_descends (prefixWord ++ tailWord_867210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867421 : List Nat := [1, 4, 4, 1, 11]
def baseStart_867421 : Nat := 118140960795 + 867421 * 2 ^ 59
def prefixEnd_867421 : Nat := 4983230072969 + 3 ^ 40 * 867421 * 2
def baseEnd_867421 : Nat := 2443917162160526447453

theorem tailTrace_867421 : CollatzResearch.WordTrace tailWord_867421 prefixEnd_867421 2443917162160526447453 := by
  unfold tailWord_867421
  simp only [CollatzResearch.WordTrace]
  refine ⟨31637442990489335557586117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21091628660326223705057411 31637442990489335557586117)
  ·
    refine ⟨5932020560716750417047397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31637442990489335557586117 5932020560716750417047397)
    ·
      refine ⟨1112253855134390703196387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5932020560716750417047397 1112253855134390703196387)
      ·
        refine ⟨1668380782701586054794581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112253855134390703196387 1668380782701586054794581)
        ·
          refine ⟨2443917162160526447453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1668380782701586054794581 2443917162160526447453)
          ·
            rfl

theorem cell21_867421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 11].length) (baseStart_867421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867421 prefixEnd_867421 := by exact prefixLift 867421
  have htrace : WordTrace (prefixWord ++ tailWord_867421) baseStart_867421 baseEnd_867421 := by
    simpa [prefixWord, tailWord_867421, baseEnd_867421] using wordTrace_append hprefix tailTrace_867421
  have hstable : (prefixWord ++ tailWord_867421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867421).length < 2 ^ (prefixWord ++ tailWord_867421).sum := by decide
  have hdescent : baseEnd_867421 < baseStart_867421 := by decide
  rcases family_descends (prefixWord ++ tailWord_867421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867438 : List Nat := [4, 1, 2, 2, 1, 4, 1, 6]
def baseStart_867438 : Nat := 118140960795 + 867438 * 2 ^ 59
def prefixEnd_867438 : Nat := 4983230072969 + 3 ^ 40 * 867438 * 2
def baseEnd_867438 : Nat := 65987056588871463486775

theorem tailTrace_867438 : CollatzResearch.WordTrace tailWord_867438 prefixEnd_867438 65987056588871463486775 := by
  unfold tailWord_867438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954757878928468432619371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21092042020951831640636645 3954757878928468432619371)
  ·
    refine ⟨5932136818392702648929057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3954757878928468432619371 5932136818392702648929057)
    ·
      refine ⟨4449102613794526986696793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5932136818392702648929057 4449102613794526986696793)
      ·
        refine ⟨3336826960345895240022595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4449102613794526986696793 3336826960345895240022595)
        ·
          refine ⟨5005240440518842860033893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3336826960345895240022595 5005240440518842860033893)
          ·
            refine ⟨938482582597283036256355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5005240440518842860033893 938482582597283036256355)
            ·
              refine ⟨1407723873895924554384533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938482582597283036256355 1407723873895924554384533)
              ·
                refine ⟨65987056588871463486775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1407723873895924554384533 65987056588871463486775)
                ·
                  rfl

theorem cell21_867438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_867438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867438 prefixEnd_867438 := by exact prefixLift 867438
  have htrace : WordTrace (prefixWord ++ tailWord_867438) baseStart_867438 baseEnd_867438 := by
    simpa [prefixWord, tailWord_867438, baseEnd_867438] using wordTrace_append hprefix tailTrace_867438
  have hstable : (prefixWord ++ tailWord_867438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867438).length < 2 ^ (prefixWord ++ tailWord_867438).sum := by decide
  have hdescent : baseEnd_867438 < baseStart_867438 := by decide
  rcases family_descends (prefixWord ++ tailWord_867438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867466 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_867466 : Nat := 118140960795 + 867466 * 2 ^ 59
def prefixEnd_867466 : Nat := 4983230072969 + 3 ^ 40 * 867466 * 2
def baseEnd_867466 : Nat := 197967559748092563993601

theorem tailTrace_867466 : CollatzResearch.WordTrace tailWord_867466 prefixEnd_867466 197967559748092563993601 := by
  unfold tailWord_867466
  simp only [CollatzResearch.WordTrace]
  refine ⟨7909771068831577060743563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21092722850217538828649501 7909771068831577060743563)
  ·
    refine ⟨11864656603247365591115345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7909771068831577060743563 11864656603247365591115345)
    ·
      refine ⟨8898492452435524193336509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11864656603247365591115345 8898492452435524193336509)
      ·
        refine ⟨3336934669663321572501191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8898492452435524193336509 3336934669663321572501191)
        ·
          refine ⟨5005402004494982358751787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3336934669663321572501191 5005402004494982358751787)
          ·
            refine ⟨7508103006742473538127681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5005402004494982358751787 7508103006742473538127681)
            ·
              refine ⟨5631077255056855153595761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7508103006742473538127681 5631077255056855153595761)
              ·
                refine ⟨4223307941292641365196821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5631077255056855153595761 4223307941292641365196821)
                ·
                  refine ⟨197967559748092563993601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4223307941292641365196821 197967559748092563993601)
                  ·
                    rfl

theorem cell21_867466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_867466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867466 prefixEnd_867466 := by exact prefixLift 867466
  have htrace : WordTrace (prefixWord ++ tailWord_867466) baseStart_867466 baseEnd_867466 := by
    simpa [prefixWord, tailWord_867466, baseEnd_867466] using wordTrace_append hprefix tailTrace_867466
  have hstable : (prefixWord ++ tailWord_867466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867466).length < 2 ^ (prefixWord ++ tailWord_867466).sum := by decide
  have hdescent : baseEnd_867466 < baseStart_867466 := by decide
  rcases family_descends (prefixWord ++ tailWord_867466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867486 : List Nat := [4, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_867486 : Nat := 118140960795 + 867486 * 2 ^ 59
def prefixEnd_867486 : Nat := 4983230072969 + 3 ^ 40 * 867486 * 2
def baseEnd_867486 : Nat := 197972124020576973660227

theorem tailTrace_867486 : CollatzResearch.WordTrace tailWord_867486 prefixEnd_867486 197972124020576973660227 := by
  unfold tailWord_867486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954976716906731457337789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21093209156835901105801541 3954976716906731457337789)
  ·
    refine ⟨1483116268840024296501671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3954976716906731457337789 1483116268840024296501671)
    ·
      refine ⟨2224674403260036444752507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1483116268840024296501671 2224674403260036444752507)
      ·
        refine ⟨3337011604890054667128761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224674403260036444752507 3337011604890054667128761)
        ·
          refine ⟨2502758703667541000346571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3337011604890054667128761 2502758703667541000346571)
          ·
            refine ⟨3754138055501311500519857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502758703667541000346571 3754138055501311500519857)
            ·
              refine ⟨2815603541625983625389893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3754138055501311500519857 2815603541625983625389893)
              ·
                refine ⟨527925664054871929760605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2815603541625983625389893 527925664054871929760605)
                ·
                  refine ⟨197972124020576973660227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 527925664054871929760605 197972124020576973660227)
                  ·
                    rfl

theorem cell21_867486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_867486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867486 prefixEnd_867486 := by exact prefixLift 867486
  have htrace : WordTrace (prefixWord ++ tailWord_867486) baseStart_867486 baseEnd_867486 := by
    simpa [prefixWord, tailWord_867486, baseEnd_867486] using wordTrace_append hprefix tailTrace_867486
  have hstable : (prefixWord ++ tailWord_867486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867486).length < 2 ^ (prefixWord ++ tailWord_867486).sum := by decide
  have hdescent : baseEnd_867486 < baseStart_867486 := by decide
  rcases family_descends (prefixWord ++ tailWord_867486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867511 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 5]
def baseStart_867511 : Nat := 118140960795 + 867511 * 2 ^ 59
def prefixEnd_867511 : Nat := 4983230072969 + 3 ^ 40 * 867511 * 2
def baseEnd_867511 : Nat := 197977829361182485743509

theorem tailTrace_867511 : CollatzResearch.WordTrace tailWord_867511 prefixEnd_867511 197977829361182485743509 := by
  unfold tailWord_867511
  simp only [CollatzResearch.WordTrace]
  refine ⟨31640725560163280928362387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21093817040108853952241591 31640725560163280928362387)
  ·
    refine ⟨47461088340244921392543581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31640725560163280928362387 47461088340244921392543581)
    ·
      refine ⟨17797908127591845522203843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47461088340244921392543581 17797908127591845522203843)
      ·
        refine ⟨26696862191387768283305765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17797908127591845522203843 26696862191387768283305765)
        ·
          refine ⟨5005661660885206553119831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26696862191387768283305765 5005661660885206553119831)
          ·
            refine ⟨7508492491327809829679747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5005661660885206553119831 7508492491327809829679747)
            ·
              refine ⟨11262738736991714744519621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7508492491327809829679747 11262738736991714744519621)
              ·
                refine ⟨2111763513185946514597429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11262738736991714744519621 2111763513185946514597429)
                ·
                  refine ⟨197977829361182485743509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2111763513185946514597429 197977829361182485743509)
                  ·
                    rfl

theorem cell21_867511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_867511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867511 prefixEnd_867511 := by exact prefixLift 867511
  have htrace : WordTrace (prefixWord ++ tailWord_867511) baseStart_867511 baseEnd_867511 := by
    simpa [prefixWord, tailWord_867511, baseEnd_867511] using wordTrace_append hprefix tailTrace_867511
  have hstable : (prefixWord ++ tailWord_867511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867511).length < 2 ^ (prefixWord ++ tailWord_867511).sum := by decide
  have hdescent : baseEnd_867511 < baseStart_867511 := by decide
  rcases family_descends (prefixWord ++ tailWord_867511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867556 : List Nat := [2, 3, 1, 1, 1, 2, 3, 8]
def baseStart_867556 : Nat := 118140960795 + 867556 * 2 ^ 59
def prefixEnd_867556 : Nat := 4983230072969 + 3 ^ 40 * 867556 * 2
def baseEnd_867556 : Nat := 65996032991424135831139

theorem tailTrace_867556 : CollatzResearch.WordTrace tailWord_867556 prefixEnd_867556 65996032991424135831139 := by
  unfold tailWord_867556
  simp only [CollatzResearch.WordTrace]
  refine ⟨15821183422500126806875261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21094911230000169075833681 15821183422500126806875261)
  ·
    refine ⟨5932943783437547552578223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15821183422500126806875261 5932943783437547552578223)
    ·
      refine ⟨8899415675156321328867335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5932943783437547552578223 8899415675156321328867335)
      ·
        refine ⟨13349123512734481993301003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8899415675156321328867335 13349123512734481993301003)
        ·
          refine ⟨20023685269101722989951505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13349123512734481993301003 20023685269101722989951505)
          ·
            refine ⟨15017763951826292242463629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20023685269101722989951505 15017763951826292242463629)
            ·
              refine ⟨5631661481934859590923861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15017763951826292242463629 5631661481934859590923861)
              ·
                refine ⟨65996032991424135831139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5631661481934859590923861 65996032991424135831139)
                ·
                  rfl

theorem cell21_867556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 8].length) (baseStart_867556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867556 prefixEnd_867556 := by exact prefixLift 867556
  have htrace : WordTrace (prefixWord ++ tailWord_867556) baseStart_867556 baseEnd_867556 := by
    simpa [prefixWord, tailWord_867556, baseEnd_867556] using wordTrace_append hprefix tailTrace_867556
  have hstable : (prefixWord ++ tailWord_867556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867556).length < 2 ^ (prefixWord ++ tailWord_867556).sum := by decide
  have hdescent : baseEnd_867556 < baseStart_867556 := by decide
  rcases family_descends (prefixWord ++ tailWord_867556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867649 : List Nat := [1, 2, 5, 2, 1, 2, 8]
def baseStart_867649 : Nat := 118140960795 + 867649 * 2 ^ 59
def prefixEnd_867649 : Nat := 4983230072969 + 3 ^ 40 * 867649 * 2
def baseEnd_867649 : Nat := 22001035871258323604803

theorem tailTrace_867649 : CollatzResearch.WordTrace tailWord_867649 prefixEnd_867649 22001035871258323604803 := by
  unfold tailWord_867649
  simp only [CollatzResearch.WordTrace]
  refine ⟨31645758833663330496886001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21097172555775553664590667 31645758833663330496886001)
  ·
    refine ⟨23734319125247497872664501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31645758833663330496886001 23734319125247497872664501)
    ·
      refine ⟨2225092417991952925562297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23734319125247497872664501 2225092417991952925562297)
      ·
        refine ⟨1668819313493964694171723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2225092417991952925562297 1668819313493964694171723)
        ·
          refine ⟨2503228970240947041257585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668819313493964694171723 2503228970240947041257585)
          ·
            refine ⟨1877421727680710280943189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2503228970240947041257585 1877421727680710280943189)
            ·
              refine ⟨22001035871258323604803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1877421727680710280943189 22001035871258323604803)
              ·
                rfl

theorem cell21_867649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 8].length) (baseStart_867649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867649 prefixEnd_867649 := by exact prefixLift 867649
  have htrace : WordTrace (prefixWord ++ tailWord_867649) baseStart_867649 baseEnd_867649 := by
    simpa [prefixWord, tailWord_867649, baseEnd_867649] using wordTrace_append hprefix tailTrace_867649
  have hstable : (prefixWord ++ tailWord_867649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867649).length < 2 ^ (prefixWord ++ tailWord_867649).sum := by decide
  have hdescent : baseEnd_867649 < baseStart_867649 := by decide
  rcases family_descends (prefixWord ++ tailWord_867649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867652 : List Nat := [2, 3, 4, 1, 1, 1, 3, 2, 4]
def baseStart_867652 : Nat := 118140960795 + 867652 * 2 ^ 59
def prefixEnd_867652 : Nat := 4983230072969 + 3 ^ 40 * 867652 * 2
def baseEnd_867652 : Nat := 198010007482197573893221

theorem tailTrace_867652 : CollatzResearch.WordTrace tailWord_867652 prefixEnd_867652 198010007482197573893221 := by
  unfold tailWord_867652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15822934126326231004622605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21097245501768308006163473 15822934126326231004622605)
  ·
    refine ⟨5933600297372336626733477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15822934126326231004622605 5933600297372336626733477)
    ·
      refine ⟨1112550055757313117512527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5933600297372336626733477 1112550055757313117512527)
      ·
        refine ⟨1668825083635969676268791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112550055757313117512527 1668825083635969676268791)
        ·
          refine ⟨2503237625453954514403187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668825083635969676268791 2503237625453954514403187)
          ·
            refine ⟨3754856438180931771604781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2503237625453954514403187 3754856438180931771604781)
            ·
              refine ⟨1408071164317849414351793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3754856438180931771604781 1408071164317849414351793)
              ·
                refine ⟨1056053373238387060763845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408071164317849414351793 1056053373238387060763845)
                ·
                  refine ⟨198010007482197573893221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056053373238387060763845 198010007482197573893221)
                  ·
                    rfl

theorem cell21_867652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_867652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867652 prefixEnd_867652 := by exact prefixLift 867652
  have htrace : WordTrace (prefixWord ++ tailWord_867652) baseStart_867652 baseEnd_867652 := by
    simpa [prefixWord, tailWord_867652, baseEnd_867652] using wordTrace_append hprefix tailTrace_867652
  have hstable : (prefixWord ++ tailWord_867652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867652).length < 2 ^ (prefixWord ++ tailWord_867652).sum := by decide
  have hdescent : baseEnd_867652 < baseStart_867652 := by decide
  rcases family_descends (prefixWord ++ tailWord_867652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867714 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 5]
def baseStart_867714 : Nat := 118140960795 + 867714 * 2 ^ 59
def prefixEnd_867714 : Nat := 4983230072969 + 3 ^ 40 * 867714 * 2
def baseEnd_867714 : Nat := 198024156726899243859761

theorem tailTrace_867714 : CollatzResearch.WordTrace tailWord_867714 prefixEnd_867714 198024156726899243859761 := by
  unfold tailWord_867714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7912032394606961649500549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21098753052285231065334797 7912032394606961649500549)
  ·
    refine ⟨1483506073988805309281353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7912032394606961649500549 1483506073988805309281353)
    ·
      refine ⟨1112629555491603981961015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1483506073988805309281353 1112629555491603981961015)
      ·
        refine ⟨1668944333237405972941523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112629555491603981961015 1668944333237405972941523)
        ·
          refine ⟨2503416499856108959412285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668944333237405972941523 2503416499856108959412285)
          ·
            refine ⟨938781187446040859779607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2503416499856108959412285 938781187446040859779607)
            ·
              refine ⟨1408171781169061289669411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938781187446040859779607 1408171781169061289669411)
              ·
                refine ⟨2112257671753591934504117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408171781169061289669411 2112257671753591934504117)
                ·
                  refine ⟨198024156726899243859761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2112257671753591934504117 198024156726899243859761)
                  ·
                    rfl

theorem cell21_867714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_867714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867714 prefixEnd_867714 := by exact prefixLift 867714
  have htrace : WordTrace (prefixWord ++ tailWord_867714) baseStart_867714 baseEnd_867714 := by
    simpa [prefixWord, tailWord_867714, baseEnd_867714] using wordTrace_append hprefix tailTrace_867714
  have hstable : (prefixWord ++ tailWord_867714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867714).length < 2 ^ (prefixWord ++ tailWord_867714).sum := by decide
  have hdescent : baseEnd_867714 < baseStart_867714 := by decide
  rcases family_descends (prefixWord ++ tailWord_867714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867801 : List Nat := [1, 2, 1, 2, 4, 3, 3, 5]
def baseStart_867801 : Nat := 118140960795 + 867801 * 2 ^ 59
def prefixEnd_867801 : Nat := 4983230072969 + 3 ^ 40 * 867801 * 2
def baseEnd_867801 : Nat := 66014670437402141969861

theorem tailTrace_867801 : CollatzResearch.WordTrace tailWord_867801 prefixEnd_867801 66014670437402141969861 := by
  unfold tailWord_867801
  simp only [CollatzResearch.WordTrace]
  refine ⟨31651302729112660456419257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21100868486075106970946171 31651302729112660456419257)
  ·
    refine ⟨23738477046834495342314443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31651302729112660456419257 23738477046834495342314443)
    ·
      refine ⟨35607715570251743013471665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23738477046834495342314443 35607715570251743013471665)
      ·
        refine ⟨26705786677688807260103749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35607715570251743013471665 26705786677688807260103749)
        ·
          refine ⟨5007335002066651361269453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26705786677688807260103749 5007335002066651361269453)
          ·
            refine ⟨1877750625774994260476045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5007335002066651361269453 1877750625774994260476045)
            ·
              refine ⟨704156484665622847678517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1877750625774994260476045 704156484665622847678517)
              ·
                refine ⟨66014670437402141969861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 704156484665622847678517 66014670437402141969861)
                ·
                  rfl

theorem cell21_867801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 5].length) (baseStart_867801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867801 prefixEnd_867801 := by exact prefixLift 867801
  have htrace : WordTrace (prefixWord ++ tailWord_867801) baseStart_867801 baseEnd_867801 := by
    simpa [prefixWord, tailWord_867801, baseEnd_867801] using wordTrace_append hprefix tailTrace_867801
  have hstable : (prefixWord ++ tailWord_867801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867801).length < 2 ^ (prefixWord ++ tailWord_867801).sum := by decide
  have hdescent : baseEnd_867801 < baseStart_867801 := by decide
  rcases family_descends (prefixWord ++ tailWord_867801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867821 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 4]
def baseStart_867821 : Nat := 118140960795 + 867821 * 2 ^ 59
def prefixEnd_867821 : Nat := 4983230072969 + 3 ^ 40 * 867821 * 2
def baseEnd_867821 : Nat := 198048575584690835576209

theorem tailTrace_867821 : CollatzResearch.WordTrace tailWord_867821 prefixEnd_867821 198048575584690835576209 := by
  unfold tailWord_867821
  simp only [CollatzResearch.WordTrace]
  refine ⟨31652032189040203872147317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21101354792693469248098211 31652032189040203872147317)
  ·
    refine ⟨2967378017722519113013811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31652032189040203872147317 2967378017722519113013811)
    ·
      refine ⟨4451067026583778669520717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967378017722519113013811 4451067026583778669520717)
      ·
        refine ⟨1669150134968917001070269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4451067026583778669520717 1669150134968917001070269)
        ·
          refine ⟨625931300613343875401351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1669150134968917001070269 625931300613343875401351)
          ·
            refine ⟨938896950920015813102027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625931300613343875401351 938896950920015813102027)
            ·
              refine ⟨1408345426380023719653041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938896950920015813102027 1408345426380023719653041)
              ·
                refine ⟨1056259069785017789739781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408345426380023719653041 1056259069785017789739781)
                ·
                  refine ⟨198048575584690835576209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1056259069785017789739781 198048575584690835576209)
                  ·
                    rfl

theorem cell21_867821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_867821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867821 prefixEnd_867821 := by exact prefixLift 867821
  have htrace : WordTrace (prefixWord ++ tailWord_867821) baseStart_867821 baseEnd_867821 := by
    simpa [prefixWord, tailWord_867821, baseEnd_867821] using wordTrace_append hprefix tailTrace_867821
  have hstable : (prefixWord ++ tailWord_867821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867821).length < 2 ^ (prefixWord ++ tailWord_867821).sum := by decide
  have hdescent : baseEnd_867821 < baseStart_867821 := by decide
  rcases family_descends (prefixWord ++ tailWord_867821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867832 : List Nat := [2, 1, 2, 1, 1, 5, 2, 4, 3]
def baseStart_867832 : Nat := 118140960795 + 867832 * 2 ^ 59
def prefixEnd_867832 : Nat := 4983230072969 + 3 ^ 40 * 867832 * 2
def baseEnd_867832 : Nat := 198051085934557260892853

theorem tailTrace_867832 : CollatzResearch.WordTrace tailWord_867832 prefixEnd_867832 198051085934557260892853 := by
  unfold tailWord_867832
  simp only [CollatzResearch.WordTrace]
  refine ⟨15826216696000176375398875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21101622261333568500531833 15826216696000176375398875)
  ·
    refine ⟨23739325044000264563098313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15826216696000176375398875 23739325044000264563098313)
    ·
      refine ⟨17804493783000198422323735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23739325044000264563098313 17804493783000198422323735)
      ·
        refine ⟨26706740674500297633485603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17804493783000198422323735 26706740674500297633485603)
        ·
          refine ⟨40060111011750446450228405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26706740674500297633485603 40060111011750446450228405)
          ·
            refine ⟨3755635407351604354708913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40060111011750446450228405 3755635407351604354708913)
            ·
              refine ⟨2816726555513703266031685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755635407351604354708913 2816726555513703266031685)
              ·
                refine ⟨528136229158819362380941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2816726555513703266031685 528136229158819362380941)
                ·
                  refine ⟨198051085934557260892853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528136229158819362380941 198051085934557260892853)
                  ·
                    rfl

theorem cell21_867832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 4, 3].length) (baseStart_867832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867832 prefixEnd_867832 := by exact prefixLift 867832
  have htrace : WordTrace (prefixWord ++ tailWord_867832) baseStart_867832 baseEnd_867832 := by
    simpa [prefixWord, tailWord_867832, baseEnd_867832] using wordTrace_append hprefix tailTrace_867832
  have hstable : (prefixWord ++ tailWord_867832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867832).length < 2 ^ (prefixWord ++ tailWord_867832).sum := by decide
  have hdescent : baseEnd_867832 < baseStart_867832 := by decide
  rcases family_descends (prefixWord ++ tailWord_867832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867891 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 5]
def baseStart_867891 : Nat := 118140960795 + 867891 * 2 ^ 59
def prefixEnd_867891 : Nat := 4983230072969 + 3 ^ 40 * 867891 * 2
def baseEnd_867891 : Nat := 198064550538386269409399

theorem tailTrace_867891 : CollatzResearch.WordTrace tailWord_867891 prefixEnd_867891 198064550538386269409399 := by
  unfold tailWord_867891
  simp only [CollatzResearch.WordTrace]
  refine ⟨31654585298786605827195527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21103056865857737218130351 31654585298786605827195527)
  ·
    refine ⟨47481877948179908740793291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31654585298786605827195527 47481877948179908740793291)
    ·
      refine ⟨71222816922269863111189937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47481877948179908740793291 71222816922269863111189937)
      ·
        refine ⟨53417112691702397333392453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71222816922269863111189937 53417112691702397333392453)
        ·
          refine ⟨10015708629694199500011085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53417112691702397333392453 10015708629694199500011085)
          ·
            refine ⟨3755890736135324812504157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10015708629694199500011085 3755890736135324812504157)
            ·
              refine ⟨1408459026050746804689059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3755890736135324812504157 1408459026050746804689059)
              ·
                refine ⟨2112688539076120207033589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408459026050746804689059 2112688539076120207033589)
                ·
                  refine ⟨198064550538386269409399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2112688539076120207033589 198064550538386269409399)
                  ·
                    rfl

theorem cell21_867891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 5].length) (baseStart_867891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867891 prefixEnd_867891 := by exact prefixLift 867891
  have htrace : WordTrace (prefixWord ++ tailWord_867891) baseStart_867891 baseEnd_867891 := by
    simpa [prefixWord, tailWord_867891, baseEnd_867891] using wordTrace_append hprefix tailTrace_867891
  have hstable : (prefixWord ++ tailWord_867891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867891).length < 2 ^ (prefixWord ++ tailWord_867891).sum := by decide
  have hdescent : baseEnd_867891 < baseStart_867891 := by decide
  rcases family_descends (prefixWord ++ tailWord_867891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867894 : List Nat := [5, 1, 2, 1, 3, 1, 2, 6]
def baseStart_867894 : Nat := 118140960795 + 867894 * 2 ^ 59
def prefixEnd_867894 : Nat := 4983230072969 + 3 ^ 40 * 867894 * 2
def baseEnd_867894 : Nat := 66021745059752976953131

theorem tailTrace_867894 : CollatzResearch.WordTrace tailWord_867894 prefixEnd_867894 66021745059752976953131 := by
  unfold tailWord_867894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978418419860983583722171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21103129811850491559703157 1978418419860983583722171)
  ·
    refine ⟨2967627629791475375583257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978418419860983583722171 2967627629791475375583257)
    ·
      refine ⟨2225720722343606531687443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2967627629791475375583257 2225720722343606531687443)
      ·
        refine ⟨3338581083515409797531165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2225720722343606531687443 3338581083515409797531165)
        ·
          refine ⟨1251967906318278674074187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3338581083515409797531165 1251967906318278674074187)
          ·
            refine ⟨1877951859477418011111281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251967906318278674074187 1877951859477418011111281)
            ·
              refine ⟨1408463894608063508333461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1877951859477418011111281 1408463894608063508333461)
              ·
                refine ⟨66021745059752976953131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1408463894608063508333461 66021745059752976953131)
                ·
                  rfl

theorem cell21_867894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_867894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_867894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_867894 prefixEnd_867894 := by exact prefixLift 867894
  have htrace : WordTrace (prefixWord ++ tailWord_867894) baseStart_867894 baseEnd_867894 := by
    simpa [prefixWord, tailWord_867894, baseEnd_867894] using wordTrace_append hprefix tailTrace_867894
  have hstable : (prefixWord ++ tailWord_867894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867894).length < 2 ^ (prefixWord ++ tailWord_867894).sum := by decide
  have hdescent : baseEnd_867894 < baseStart_867894 := by decide
  rcases family_descends (prefixWord ++ tailWord_867894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868057 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 6]
def baseStart_868057 : Nat := 118140960795 + 868057 * 2 ^ 59
def prefixEnd_868057 : Nat := 4983230072969 + 3 ^ 40 * 868057 * 2
def baseEnd_868057 : Nat := 198102434000006869642393

theorem tailTrace_868057 : CollatzResearch.WordTrace tailWord_868057 prefixEnd_868057 198102434000006869642393 := by
  unfold tailWord_868057
  simp only [CollatzResearch.WordTrace]
  refine ⟨31660639816185216177738425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21107093210790144118492283 31660639816185216177738425)
  ·
    refine ⟨23745479862138912133303819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31660639816185216177738425 23745479862138912133303819)
    ·
      refine ⟨35618219793208368199955729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23745479862138912133303819 35618219793208368199955729)
      ·
        refine ⟨26713664844906276149966797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35618219793208368199955729 26713664844906276149966797)
        ·
          refine ⟨10017624316839853556237549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26713664844906276149966797 10017624316839853556237549)
          ·
            refine ⟨3756609118814945083589081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10017624316839853556237549 3756609118814945083589081)
            ·
              refine ⟨2817456839111208812691811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3756609118814945083589081 2817456839111208812691811)
              ·
                refine ⟨4226185258666813219037717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2817456839111208812691811 4226185258666813219037717)
                ·
                  refine ⟨198102434000006869642393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4226185258666813219037717 198102434000006869642393)
                  ·
                    rfl

theorem cell21_868057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_868057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868057 prefixEnd_868057 := by exact prefixLift 868057
  have htrace : WordTrace (prefixWord ++ tailWord_868057) baseStart_868057 baseEnd_868057 := by
    simpa [prefixWord, tailWord_868057, baseEnd_868057] using wordTrace_append hprefix tailTrace_868057
  have hstable : (prefixWord ++ tailWord_868057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868057).length < 2 ^ (prefixWord ++ tailWord_868057).sum := by decide
  have hdescent : baseEnd_868057 < baseStart_868057 := by decide
  rcases family_descends (prefixWord ++ tailWord_868057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868271 : List Nat := [1, 1, 2, 1, 2, 2, 4, 5, 3]
def baseStart_868271 : Nat := 118140960795 + 868271 * 2 ^ 59
def prefixEnd_868271 : Nat := 4983230072969 + 3 ^ 40 * 868271 * 2
def baseEnd_868271 : Nat := 198151271715590053075289

theorem tailTrace_868271 : CollatzResearch.WordTrace tailWord_868271 prefixEnd_868271 198151271715590053075289 := by
  unfold tailWord_868271
  simp only [CollatzResearch.WordTrace]
  refine ⟨31668445037409930726028667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21112296691606620484019111 31668445037409930726028667)
  ·
    refine ⟨47502667556114896089043001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31668445037409930726028667 47502667556114896089043001)
    ·
      refine ⟨35627000667086172066782251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47502667556114896089043001 35627000667086172066782251)
      ·
        refine ⟨53440501000629258100173377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35627000667086172066782251 53440501000629258100173377)
        ·
          refine ⟨40080375750471943575130033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53440501000629258100173377 40080375750471943575130033)
          ·
            refine ⟨30060281812853957681347525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40080375750471943575130033 30060281812853957681347525)
            ·
              refine ⟨5636302839910117065252661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30060281812853957681347525 5636302839910117065252661)
              ·
                refine ⟨528403391241573474867437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5636302839910117065252661 528403391241573474867437)
                ·
                  refine ⟨198151271715590053075289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528403391241573474867437 198151271715590053075289)
                  ·
                    rfl

theorem cell21_868271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 3].length) (baseStart_868271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868271 prefixEnd_868271 := by exact prefixLift 868271
  have htrace : WordTrace (prefixWord ++ tailWord_868271) baseStart_868271 baseEnd_868271 := by
    simpa [prefixWord, tailWord_868271, baseEnd_868271] using wordTrace_append hprefix tailTrace_868271
  have hstable : (prefixWord ++ tailWord_868271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868271).length < 2 ^ (prefixWord ++ tailWord_868271).sum := by decide
  have hdescent : baseEnd_868271 < baseStart_868271 := by decide
  rcases family_descends (prefixWord ++ tailWord_868271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868322 : List Nat := [3, 3, 3, 1, 2, 1, 2, 3, 3]
def baseStart_868322 : Nat := 118140960795 + 868322 * 2 ^ 59
def prefixEnd_868322 : Nat := 4983230072969 + 3 ^ 40 * 868322 * 2
def baseEnd_868322 : Nat := 198162910610425297725185

theorem tailTrace_868322 : CollatzResearch.WordTrace tailWord_868322 prefixEnd_868322 198162910610425297725185 := by
  unfold tailWord_868322
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917576290056291609033805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21113536773483444290756813 7917576290056291609033805)
  ·
    refine ⟨2969091108771109353387677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7917576290056291609033805 2969091108771109353387677)
    ·
      refine ⟨1113409165789166007520379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2969091108771109353387677 1113409165789166007520379)
      ·
        refine ⟨1670113748683749011280569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113409165789166007520379 1670113748683749011280569)
        ·
          refine ⟨1252585311512811758460427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670113748683749011280569 1252585311512811758460427)
          ·
            refine ⟨1878877967269217637690641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252585311512811758460427 1878877967269217637690641)
            ·
              refine ⟨1409158475451913228267981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878877967269217637690641 1409158475451913228267981)
              ·
                refine ⟨528434428294467460600493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1409158475451913228267981 528434428294467460600493)
                ·
                  refine ⟨198162910610425297725185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528434428294467460600493 198162910610425297725185)
                  ·
                    rfl

theorem cell21_868322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_868322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868322 prefixEnd_868322 := by exact prefixLift 868322
  have htrace : WordTrace (prefixWord ++ tailWord_868322) baseStart_868322 baseEnd_868322 := by
    simpa [prefixWord, tailWord_868322, baseEnd_868322] using wordTrace_append hprefix tailTrace_868322
  have hstable : (prefixWord ++ tailWord_868322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868322).length < 2 ^ (prefixWord ++ tailWord_868322).sum := by decide
  have hdescent : baseEnd_868322 < baseStart_868322 := by decide
  rcases family_descends (prefixWord ++ tailWord_868322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868330 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 7]
def baseStart_868330 : Nat := 118140960795 + 868330 * 2 ^ 59
def prefixEnd_868330 : Nat := 4983230072969 + 3 ^ 40 * 868330 * 2
def baseEnd_868330 : Nat := 198164736319419061591835

theorem tailTrace_868330 : CollatzResearch.WordTrace tailWord_868330 prefixEnd_868330 198164736319419061591835 := by
  unfold tailWord_868330
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917649236049045950606611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21113731296130789201617629 7917649236049045950606611)
  ·
    refine ⟨11876473854073568925909917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7917649236049045950606611 11876473854073568925909917)
    ·
      refine ⟨4453677695277588347216219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11876473854073568925909917 4453677695277588347216219)
      ·
        refine ⟨6680516542916382520824329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4453677695277588347216219 6680516542916382520824329)
        ·
          refine ⟨5010387407187286890618247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6680516542916382520824329 5010387407187286890618247)
          ·
            refine ⟨7515581110780930335927371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5010387407187286890618247 7515581110780930335927371)
            ·
              refine ⟨11273371666171395503891057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7515581110780930335927371 11273371666171395503891057)
              ·
                refine ⟨8455028749628546627918293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11273371666171395503891057 8455028749628546627918293)
                ·
                  refine ⟨198164736319419061591835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8455028749628546627918293 198164736319419061591835)
                  ·
                    rfl

theorem cell21_868330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_868330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868330 prefixEnd_868330 := by exact prefixLift 868330
  have htrace : WordTrace (prefixWord ++ tailWord_868330) baseStart_868330 baseEnd_868330 := by
    simpa [prefixWord, tailWord_868330, baseEnd_868330] using wordTrace_append hprefix tailTrace_868330
  have hstable : (prefixWord ++ tailWord_868330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868330).length < 2 ^ (prefixWord ++ tailWord_868330).sum := by decide
  have hdescent : baseEnd_868330 < baseStart_868330 := by decide
  rcases family_descends (prefixWord ++ tailWord_868330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868333 : List Nat := [1, 5, 1, 4, 1, 1, 8]
def baseStart_868333 : Nat := 118140960795 + 868333 * 2 ^ 59
def prefixEnd_868333 : Nat := 4983230072969 + 3 ^ 40 * 868333 * 2
def baseEnd_868333 : Nat := 22018380106699080337981

theorem tailTrace_868333 : CollatzResearch.WordTrace tailWord_868333 prefixEnd_868333 22018380106699080337981 := by
  unfold tailWord_868333
  simp only [CollatzResearch.WordTrace]
  refine ⟨31670706363185315314785653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21113804242123543543190435 31670706363185315314785653)
  ·
    refine ⟨2969128721548623310761155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31670706363185315314785653 2969128721548623310761155)
    ·
      refine ⟨4453693082322934966141733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2969128721548623310761155 4453693082322934966141733)
      ·
        refine ⟨835067452935550306151575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4453693082322934966141733 835067452935550306151575)
        ·
          refine ⟨1252601179403325459227363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835067452935550306151575 1252601179403325459227363)
          ·
            refine ⟨1878901769104988188841045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252601179403325459227363 1878901769104988188841045)
            ·
              refine ⟨22018380106699080337981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1878901769104988188841045 22018380106699080337981)
              ·
                rfl

theorem cell21_868333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 8].length) (baseStart_868333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868333 prefixEnd_868333 := by exact prefixLift 868333
  have htrace : WordTrace (prefixWord ++ tailWord_868333) baseStart_868333 baseEnd_868333 := by
    simpa [prefixWord, tailWord_868333, baseEnd_868333] using wordTrace_append hprefix tailTrace_868333
  have hstable : (prefixWord ++ tailWord_868333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868333).length < 2 ^ (prefixWord ++ tailWord_868333).sum := by decide
  have hdescent : baseEnd_868333 < baseStart_868333 := by decide
  rcases family_descends (prefixWord ++ tailWord_868333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868347 : List Nat := [1, 1, 1, 1, 1, 3, 6, 4, 3]
def baseStart_868347 : Nat := 118140960795 + 868347 * 2 ^ 59
def prefixEnd_868347 : Nat := 4983230072969 + 3 ^ 40 * 868347 * 2
def baseEnd_868347 : Nat := 198168615951030809808467

theorem tailTrace_868347 : CollatzResearch.WordTrace tailWord_868347 prefixEnd_868347 198168615951030809808467 := by
  unfold tailWord_868347
  simp only [CollatzResearch.WordTrace]
  refine ⟨31671216985134595705795295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21114144656756397137196863 31671216985134595705795295)
  ·
    refine ⟨47506825477701893558692943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31671216985134595705795295 47506825477701893558692943)
    ·
      refine ⟨71260238216552840338039415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47506825477701893558692943 71260238216552840338039415)
      ·
        refine ⟨106890357324829260507059123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71260238216552840338039415 106890357324829260507059123)
        ·
          refine ⟨160335535987243890760588685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106890357324829260507059123 160335535987243890760588685)
          ·
            refine ⟨60125825995216459035220757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160335535987243890760588685 60125825995216459035220757)
            ·
              refine ⟨2818398093525771517275973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60125825995216459035220757 2818398093525771517275973)
              ·
                refine ⟨528449642536082159489245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2818398093525771517275973 528449642536082159489245)
                ·
                  refine ⟨198168615951030809808467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528449642536082159489245 198168615951030809808467)
                  ·
                    rfl

theorem cell21_868347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 4, 3].length) (baseStart_868347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868347 prefixEnd_868347 := by exact prefixLift 868347
  have htrace : WordTrace (prefixWord ++ tailWord_868347) baseStart_868347 baseEnd_868347 := by
    simpa [prefixWord, tailWord_868347, baseEnd_868347] using wordTrace_append hprefix tailTrace_868347
  have hstable : (prefixWord ++ tailWord_868347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868347).length < 2 ^ (prefixWord ++ tailWord_868347).sum := by decide
  have hdescent : baseEnd_868347 < baseStart_868347 := by decide
  rcases family_descends (prefixWord ++ tailWord_868347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868381 : List Nat := [1, 4, 2, 2, 2, 3, 1, 3, 3]
def baseStart_868381 : Nat := 118140960795 + 868381 * 2 ^ 59
def prefixEnd_868381 : Nat := 4983230072969 + 3 ^ 40 * 868381 * 2
def baseEnd_868381 : Nat := 198176375214254306241731

theorem tailTrace_868381 : CollatzResearch.WordTrace tailWord_868381 prefixEnd_868381 198176375214254306241731 := by
  unfold tailWord_868381
  simp only [CollatzResearch.WordTrace]
  refine ⟨31672457067011419512532997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21114971378007613008355331 31672457067011419512532997)
  ·
    refine ⟨5938585700064641158599937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31672457067011419512532997 5938585700064641158599937)
    ·
      refine ⟨4453939275048480868949953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5938585700064641158599937 4453939275048480868949953)
      ·
        refine ⟨3340454456286360651712465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4453939275048480868949953 3340454456286360651712465)
        ·
          refine ⟨2505340842214770488784349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3340454456286360651712465 2505340842214770488784349)
          ·
            refine ⟨939502815830538933294131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2505340842214770488784349 939502815830538933294131)
            ·
              refine ⟨1409254223745808399941197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939502815830538933294131 1409254223745808399941197)
              ·
                refine ⟨528470333904678149977949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1409254223745808399941197 528470333904678149977949)
                ·
                  refine ⟨198176375214254306241731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528470333904678149977949 198176375214254306241731)
                  ·
                    rfl

theorem cell21_868381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_868381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868381 prefixEnd_868381 := by exact prefixLift 868381
  have htrace : WordTrace (prefixWord ++ tailWord_868381) baseStart_868381 baseEnd_868381 := by
    simpa [prefixWord, tailWord_868381, baseEnd_868381] using wordTrace_append hprefix tailTrace_868381
  have hstable : (prefixWord ++ tailWord_868381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868381).length < 2 ^ (prefixWord ++ tailWord_868381).sum := by decide
  have hdescent : baseEnd_868381 < baseStart_868381 := by decide
  rcases family_descends (prefixWord ++ tailWord_868381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868496 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_868496 : Nat := 118140960795 + 868496 * 2 ^ 59
def prefixEnd_868496 : Nat := 4983230072969 + 3 ^ 40 * 868496 * 2
def baseEnd_868496 : Nat := 198202619781039661824829

theorem tailTrace_868496 : CollatzResearch.WordTrace tailWord_868496 prefixEnd_868496 198202619781039661824829 := by
  unfold tailWord_868496
  simp only [CollatzResearch.WordTrace]
  refine ⟨15838325730797397076484671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21117767641063196101979561 15838325730797397076484671)
  ·
    refine ⟨23757488596196095614727007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15838325730797397076484671 23757488596196095614727007)
    ·
      refine ⟨35636232894294143422090511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23757488596196095614727007 35636232894294143422090511)
      ·
        refine ⟨53454349341441215133135767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35636232894294143422090511 53454349341441215133135767)
        ·
          refine ⟨80181524012161822699703651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53454349341441215133135767 80181524012161822699703651)
          ·
            refine ⟨120272286018242734049555477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80181524012161822699703651 120272286018242734049555477)
            ·
              refine ⟨5637763407105128158572913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120272286018242734049555477 5637763407105128158572913)
              ·
                refine ⟨4228322555328846118929685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5637763407105128158572913 4228322555328846118929685)
                ·
                  refine ⟨198202619781039661824829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4228322555328846118929685 198202619781039661824829)
                  ·
                    rfl

theorem cell21_868496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_868496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868496 prefixEnd_868496 := by exact prefixLift 868496
  have htrace : WordTrace (prefixWord ++ tailWord_868496) baseStart_868496 baseEnd_868496 := by
    simpa [prefixWord, tailWord_868496, baseEnd_868496] using wordTrace_append hprefix tailTrace_868496
  have hstable : (prefixWord ++ tailWord_868496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868496).length < 2 ^ (prefixWord ++ tailWord_868496).sum := by decide
  have hdescent : baseEnd_868496 < baseStart_868496 := by decide
  rcases family_descends (prefixWord ++ tailWord_868496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868513 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 6]
def baseStart_868513 : Nat := 118140960795 + 868513 * 2 ^ 59
def prefixEnd_868513 : Nat := 4983230072969 + 3 ^ 40 * 868513 * 2
def baseEnd_868513 : Nat := 198206499412651410041461

theorem tailTrace_868513 : CollatzResearch.WordTrace tailWord_868513 prefixEnd_868513 198206499412651410041461 := by
  unfold tailWord_868513
  simp only [CollatzResearch.WordTrace]
  refine ⟨31677271502533206056338193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21118181001688804037558795 31677271502533206056338193)
  ·
    refine ⟨23757953626899904542253645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31677271502533206056338193 23757953626899904542253645)
    ·
      refine ⟨8909232610087464203345117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23757953626899904542253645 8909232610087464203345117)
      ·
        refine ⟨3340962228782799076254419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8909232610087464203345117 3340962228782799076254419)
        ·
          refine ⟨5011443343174198614381629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3340962228782799076254419 5011443343174198614381629)
          ·
            refine ⟨1879291253690324480393111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5011443343174198614381629 1879291253690324480393111)
            ·
              refine ⟨2818936880535486720589667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879291253690324480393111 2818936880535486720589667)
              ·
                refine ⟨4228405320803230080884501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818936880535486720589667 4228405320803230080884501)
                ·
                  refine ⟨198206499412651410041461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4228405320803230080884501 198206499412651410041461)
                  ·
                    rfl

theorem cell21_868513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_868513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868513 prefixEnd_868513 := by exact prefixLift 868513
  have htrace : WordTrace (prefixWord ++ tailWord_868513) baseStart_868513 baseEnd_868513 := by
    simpa [prefixWord, tailWord_868513, baseEnd_868513] using wordTrace_append hprefix tailTrace_868513
  have hstable : (prefixWord ++ tailWord_868513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868513).length < 2 ^ (prefixWord ++ tailWord_868513).sum := by decide
  have hdescent : baseEnd_868513 < baseStart_868513 := by decide
  rcases family_descends (prefixWord ++ tailWord_868513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868530 : List Nat := [3, 2, 1, 1, 1, 3, 5, 1, 4]
def baseStart_868530 : Nat := 118140960795 + 868530 * 2 ^ 59
def prefixEnd_868530 : Nat := 4983230072969 + 3 ^ 40 * 868530 * 2
def baseEnd_868530 : Nat := 198210379044263158258093

theorem tailTrace_868530 : CollatzResearch.WordTrace tailWord_868530 prefixEnd_868530 198210379044263158258093 := by
  unfold tailWord_868530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7919472885867904489926761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21118594362314411973138029 7919472885867904489926761)
  ·
    refine ⟨5939604664400928367445071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7919472885867904489926761 5939604664400928367445071)
    ·
      refine ⟨8909406996601392551167607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5939604664400928367445071 8909406996601392551167607)
      ·
        refine ⟨13364110494902088826751411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8909406996601392551167607 13364110494902088826751411)
        ·
          refine ⟨20046165742353133240127117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13364110494902088826751411 20046165742353133240127117)
          ·
            refine ⟨7517312153382424965047669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20046165742353133240127117 7517312153382424965047669)
            ·
              refine ⟨704748014379602340473219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7517312153382424965047669 704748014379602340473219)
              ·
                refine ⟨1057122021569403510709829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704748014379602340473219 1057122021569403510709829)
                ·
                  refine ⟨198210379044263158258093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1057122021569403510709829 198210379044263158258093)
                  ·
                    rfl

theorem cell21_868530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_868530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868530 prefixEnd_868530 := by exact prefixLift 868530
  have htrace : WordTrace (prefixWord ++ tailWord_868530) baseStart_868530 baseEnd_868530 := by
    simpa [prefixWord, tailWord_868530, baseEnd_868530] using wordTrace_append hprefix tailTrace_868530
  have hstable : (prefixWord ++ tailWord_868530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868530).length < 2 ^ (prefixWord ++ tailWord_868530).sum := by decide
  have hdescent : baseEnd_868530 < baseStart_868530 := by decide
  rcases family_descends (prefixWord ++ tailWord_868530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868544 : List Nat := [2, 1, 1, 2, 5, 1, 4, 5]
def baseStart_868544 : Nat := 118140960795 + 868544 * 2 ^ 59
def prefixEnd_868544 : Nat := 4983230072969 + 3 ^ 40 * 868544 * 2
def baseEnd_868544 : Nat := 66071191345000748341577

theorem tailTrace_868544 : CollatzResearch.WordTrace tailWord_868544 prefixEnd_868544 66071191345000748341577 := by
  unfold tailWord_868544
  simp only [CollatzResearch.WordTrace]
  refine ⟨15839201082710449175358343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21118934776947265567144457 15839201082710449175358343)
  ·
    refine ⟨23758801624065673763037515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15839201082710449175358343 23758801624065673763037515)
    ·
      refine ⟨35638202436098510644556273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23758801624065673763037515 35638202436098510644556273)
      ·
        refine ⟨26728651827073882983417205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35638202436098510644556273 26728651827073882983417205)
        ·
          refine ⟨2505811108788176529695363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26728651827073882983417205 2505811108788176529695363)
          ·
            refine ⟨3758716663182264794543045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505811108788176529695363 3758716663182264794543045)
            ·
              refine ⟨704759374346674648976821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3758716663182264794543045 704759374346674648976821)
              ·
                refine ⟨66071191345000748341577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 704759374346674648976821 66071191345000748341577)
                ·
                  rfl

theorem cell21_868544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_868544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868544 prefixEnd_868544 := by exact prefixLift 868544
  have htrace : WordTrace (prefixWord ++ tailWord_868544) baseStart_868544 baseEnd_868544 := by
    simpa [prefixWord, tailWord_868544, baseEnd_868544] using wordTrace_append hprefix tailTrace_868544
  have hstable : (prefixWord ++ tailWord_868544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868544).length < 2 ^ (prefixWord ++ tailWord_868544).sum := by decide
  have hdescent : baseEnd_868544 < baseStart_868544 := by decide
  rcases family_descends (prefixWord ++ tailWord_868544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868637 : List Nat := [1, 4, 2, 3, 2, 2, 1, 6]
def baseStart_868637 : Nat := 118140960795 + 868637 * 2 ^ 59
def prefixEnd_868637 : Nat := 4983230072969 + 3 ^ 40 * 868637 * 2
def baseEnd_868637 : Nat := 66078265967351583324847

theorem tailTrace_868637 : CollatzResearch.WordTrace tailWord_868637 prefixEnd_868637 66078265967351583324847 := by
  unfold tailWord_868637
  simp only [CollatzResearch.WordTrace]
  refine ⟨31681794154083975233852165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21121196102722650155901443 31681794154083975233852165)
  ·
    refine ⟨5940336403890745356347281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31681794154083975233852165 5940336403890745356347281)
    ·
      refine ⟨4455252302918059017260461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5940336403890745356347281 4455252302918059017260461)
      ·
        refine ⟨1670719613594272131472673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4455252302918059017260461 1670719613594272131472673)
        ·
          refine ⟨1253039710195704098604505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670719613594272131472673 1253039710195704098604505)
          ·
            refine ⟨939779782646778073953379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253039710195704098604505 939779782646778073953379)
            ·
              refine ⟨1409669673970167110930069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939779782646778073953379 1409669673970167110930069)
              ·
                refine ⟨66078265967351583324847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1409669673970167110930069 66078265967351583324847)
                ·
                  rfl

theorem cell21_868637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 6].length) (baseStart_868637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868637 prefixEnd_868637 := by exact prefixLift 868637
  have htrace : WordTrace (prefixWord ++ tailWord_868637) baseStart_868637 baseEnd_868637 := by
    simpa [prefixWord, tailWord_868637, baseEnd_868637] using wordTrace_append hprefix tailTrace_868637
  have hstable : (prefixWord ++ tailWord_868637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868637).length < 2 ^ (prefixWord ++ tailWord_868637).sum := by decide
  have hdescent : baseEnd_868637 < baseStart_868637 := by decide
  rcases family_descends (prefixWord ++ tailWord_868637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868654 : List Nat := [4, 1, 3, 3, 1, 1, 3, 5]
def baseStart_868654 : Nat := 118140960795 + 868654 * 2 ^ 59
def prefixEnd_868654 : Nat := 4983230072969 + 3 ^ 40 * 868654 * 2
def baseEnd_868654 : Nat := 66079559177888832730391

theorem tailTrace_868654 : CollatzResearch.WordTrace tailWord_868654 prefixEnd_868654 66079559177888832730391 := by
  unfold tailWord_868654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960301774377798392152627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21121609463348258091480677 3960301774377798392152627)
  ·
    refine ⟨5940452661566697588228941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3960301774377798392152627 5940452661566697588228941)
    ·
      refine ⟨2227669748087511595585853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5940452661566697588228941 2227669748087511595585853)
      ·
        refine ⟨835376155532816848344695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2227669748087511595585853 835376155532816848344695)
        ·
          refine ⟨1253064233299225272517043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835376155532816848344695 1253064233299225272517043)
          ·
            refine ⟨1879596349948837908775565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253064233299225272517043 1879596349948837908775565)
            ·
              refine ⟨704848631230814215790837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1879596349948837908775565 704848631230814215790837)
              ·
                refine ⟨66079559177888832730391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 704848631230814215790837 66079559177888832730391)
                ·
                  rfl

theorem cell21_868654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_868654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868654 prefixEnd_868654 := by exact prefixLift 868654
  have htrace : WordTrace (prefixWord ++ tailWord_868654) baseStart_868654 baseEnd_868654 := by
    simpa [prefixWord, tailWord_868654, baseEnd_868654] using wordTrace_append hprefix tailTrace_868654
  have hstable : (prefixWord ++ tailWord_868654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868654).length < 2 ^ (prefixWord ++ tailWord_868654).sum := by decide
  have hdescent : baseEnd_868654 < baseStart_868654 := by decide
  rcases family_descends (prefixWord ++ tailWord_868654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868744 : List Nat := [2, 1, 3, 3, 1, 1, 5, 2, 3]
def baseStart_868744 : Nat := 118140960795 + 868744 * 2 ^ 59
def prefixEnd_868744 : Nat := 4983230072969 + 3 ^ 40 * 868744 * 2
def baseEnd_868744 : Nat := 198259216759846341690989

theorem tailTrace_868744 : CollatzResearch.WordTrace tailWord_868744 prefixEnd_868744 198259216759846341690989 := by
  unfold tailWord_868744
  simp only [CollatzResearch.WordTrace]
  refine ⟨15842848382348166253998643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21123797843130888338664857 15842848382348166253998643)
  ·
    refine ⟨23764272573522249380997965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15842848382348166253998643 23764272573522249380997965)
    ·
      refine ⟨8911602215070843517874237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23764272573522249380997965 8911602215070843517874237)
      ·
        refine ⟨3341850830651566319202839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8911602215070843517874237 3341850830651566319202839)
        ·
          refine ⟨5012776245977349478804259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341850830651566319202839 5012776245977349478804259)
          ·
            refine ⟨7519164368966024218206389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012776245977349478804259 7519164368966024218206389)
            ·
              refine ⟨704921659590564770456849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7519164368966024218206389 704921659590564770456849)
              ·
                refine ⟨528691244692923577842637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704921659590564770456849 528691244692923577842637)
                ·
                  refine ⟨198259216759846341690989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528691244692923577842637 198259216759846341690989)
                  ·
                    rfl

theorem cell21_868744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 3].length) (baseStart_868744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868744 prefixEnd_868744 := by exact prefixLift 868744
  have htrace : WordTrace (prefixWord ++ tailWord_868744) baseStart_868744 baseEnd_868744 := by
    simpa [prefixWord, tailWord_868744, baseEnd_868744] using wordTrace_append hprefix tailTrace_868744
  have hstable : (prefixWord ++ tailWord_868744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868744).length < 2 ^ (prefixWord ++ tailWord_868744).sum := by decide
  have hdescent : baseEnd_868744 < baseStart_868744 := by decide
  rcases family_descends (prefixWord ++ tailWord_868744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868958 : List Nat := [4, 4, 1, 2, 2, 8]
def baseStart_868958 : Nat := 118140960795 + 868958 * 2 ^ 59
def prefixEnd_868958 : Nat := 4983230072969 + 3 ^ 40 * 868958 * 2
def baseEnd_868958 : Nat := 7344742758349241671255

theorem tailTrace_868958 : CollatzResearch.WordTrace tailWord_868958 prefixEnd_868958 7344742758349241671255 := by
  unfold tailWord_868958
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961687748240130882035941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21129001323947364704191685 3961687748240130882035941)
  ·
    refine ⟨742816452795024540381739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3961687748240130882035941 742816452795024540381739)
    ·
      refine ⟨1114224679192536810572609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742816452795024540381739 1114224679192536810572609)
      ·
        refine ⟨835668509394402607929457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1114224679192536810572609 835668509394402607929457)
        ·
          refine ⟨626751382045801955947093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 835668509394402607929457 626751382045801955947093)
          ·
            refine ⟨7344742758349241671255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 626751382045801955947093 7344742758349241671255)
            ·
              rfl

theorem cell21_868958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 8].length) (baseStart_868958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868958 prefixEnd_868958 := by exact prefixLift 868958
  have htrace : WordTrace (prefixWord ++ tailWord_868958) baseStart_868958 baseEnd_868958 := by
    simpa [prefixWord, tailWord_868958, baseEnd_868958] using wordTrace_append hprefix tailTrace_868958
  have hstable : (prefixWord ++ tailWord_868958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868958).length < 2 ^ (prefixWord ++ tailWord_868958).sum := by decide
  have hdescent : baseEnd_868958 < baseStart_868958 := by decide
  rcases family_descends (prefixWord ++ tailWord_868958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868997 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 7]
def baseStart_868997 : Nat := 118140960795 + 868997 * 2 ^ 59
def prefixEnd_868997 : Nat := 4983230072969 + 3 ^ 40 * 868997 * 2
def baseEnd_868997 : Nat := 198316954806774123973805

theorem tailTrace_868997 : CollatzResearch.WordTrace tailWord_868997 prefixEnd_868997 198316954806774123973805 := by
  unfold tailWord_868997
  simp only [CollatzResearch.WordTrace]
  refine ⟨31694924432779756716957245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21129949621853171144638163 31694924432779756716957245)
  ·
    refine ⟨11885596662292408768858967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31694924432779756716957245 11885596662292408768858967)
    ·
      refine ⟨17828394993438613153288451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11885596662292408768858967 17828394993438613153288451)
      ·
        refine ⟨26742592490157919729932677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17828394993438613153288451 26742592490157919729932677)
        ·
          refine ⟨5014236091904609949362377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26742592490157919729932677 5014236091904609949362377)
          ·
            refine ⟨3760677068928457462021783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5014236091904609949362377 3760677068928457462021783)
            ·
              refine ⟨5641015603392686193032675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3760677068928457462021783 5641015603392686193032675)
              ·
                refine ⟨8461523405089029289549013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5641015603392686193032675 8461523405089029289549013)
                ·
                  refine ⟨198316954806774123973805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8461523405089029289549013 198316954806774123973805)
                  ·
                    rfl

theorem cell21_868997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_868997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_868997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_868997 prefixEnd_868997 := by exact prefixLift 868997
  have htrace : WordTrace (prefixWord ++ tailWord_868997) baseStart_868997 baseEnd_868997 := by
    simpa [prefixWord, tailWord_868997, baseEnd_868997] using wordTrace_append hprefix tailTrace_868997
  have hstable : (prefixWord ++ tailWord_868997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868997).length < 2 ^ (prefixWord ++ tailWord_868997).sum := by decide
  have hdescent : baseEnd_868997 < baseStart_868997 := by decide
  rcases family_descends (prefixWord ++ tailWord_868997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869011 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 8]
def baseStart_869011 : Nat := 118140960795 + 869011 * 2 ^ 59
def prefixEnd_869011 : Nat := 4983230072969 + 3 ^ 40 * 869011 * 2
def baseEnd_869011 : Nat := 198320149797513210740443

theorem tailTrace_869011 : CollatzResearch.WordTrace tailWord_869011 prefixEnd_869011 198320149797513210740443 := by
  unfold tailWord_869011
  simp only [CollatzResearch.WordTrace]
  refine ⟨31695435054729037107966887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21130290036486024738644591 31695435054729037107966887)
  ·
    refine ⟨47543152582093555661950331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31695435054729037107966887 47543152582093555661950331)
    ·
      refine ⟨71314728873140333492925497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47543152582093555661950331 71314728873140333492925497)
      ·
        refine ⟨53486046654855250119694123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71314728873140333492925497 53486046654855250119694123)
        ·
          refine ⟨80229069982282875179541185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53486046654855250119694123 80229069982282875179541185)
          ·
            refine ⟨60171802486712156384655889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80229069982282875179541185 60171802486712156384655889)
            ·
              refine ⟨45128851865034117288491917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60171802486712156384655889 45128851865034117288491917)
              ·
                refine ⟨16923319449387793983184469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45128851865034117288491917 16923319449387793983184469)
                ·
                  refine ⟨198320149797513210740443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16923319449387793983184469 198320149797513210740443)
                  ·
                    rfl

theorem cell21_869011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_869011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869011 prefixEnd_869011 := by exact prefixLift 869011
  have htrace : WordTrace (prefixWord ++ tailWord_869011) baseStart_869011 baseEnd_869011 := by
    simpa [prefixWord, tailWord_869011, baseEnd_869011] using wordTrace_append hprefix tailTrace_869011
  have hstable : (prefixWord ++ tailWord_869011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869011).length < 2 ^ (prefixWord ++ tailWord_869011).sum := by decide
  have hdescent : baseEnd_869011 < baseStart_869011 := by decide
  rcases family_descends (prefixWord ++ tailWord_869011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869028 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 6]
def baseStart_869028 : Nat := 118140960795 + 869028 * 2 ^ 59
def prefixEnd_869028 : Nat := 4983230072969 + 3 ^ 40 * 869028 * 2
def baseEnd_869028 : Nat := 198324029429124958957075

theorem tailTrace_869028 : CollatzResearch.WordTrace tailWord_869028 prefixEnd_869028 198324029429124958957075 := by
  unfold tailWord_869028
  simp only [CollatzResearch.WordTrace]
  refine ⟨15848027547833724505667869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21130703397111632674223825 15848027547833724505667869)
  ·
    refine ⟨5943010330437646689625451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15848027547833724505667869 5943010330437646689625451)
    ·
      refine ⟨8914515495656470034438177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5943010330437646689625451 8914515495656470034438177)
      ·
        refine ⟨6685886621742352525828633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8914515495656470034438177 6685886621742352525828633)
        ·
          refine ⟨5014414966306764394371475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6685886621742352525828633 5014414966306764394371475)
          ·
            refine ⟨7521622449460146591557213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014414966306764394371475 7521622449460146591557213)
            ·
              refine ⟨2820608418547554971833955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7521622449460146591557213 2820608418547554971833955)
              ·
                refine ⟨4230912627821332457750933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820608418547554971833955 4230912627821332457750933)
                ·
                  refine ⟨198324029429124958957075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4230912627821332457750933 198324029429124958957075)
                  ·
                    rfl

theorem cell21_869028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_869028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869028 prefixEnd_869028 := by exact prefixLift 869028
  have htrace : WordTrace (prefixWord ++ tailWord_869028) baseStart_869028 baseEnd_869028 := by
    simpa [prefixWord, tailWord_869028, baseEnd_869028] using wordTrace_append hprefix tailTrace_869028
  have hstable : (prefixWord ++ tailWord_869028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869028).length < 2 ^ (prefixWord ++ tailWord_869028).sum := by decide
  have hdescent : baseEnd_869028 < baseStart_869028 := by decide
  rcases family_descends (prefixWord ++ tailWord_869028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869042 : List Nat := [3, 2, 1, 1, 1, 2, 1, 10]
def baseStart_869042 : Nat := 118140960795 + 869042 * 2 ^ 59
def prefixEnd_869042 : Nat := 4983230072969 + 3 ^ 40 * 869042 * 2
def baseEnd_869042 : Nat := 66109074806621348574571

theorem tailTrace_869042 : CollatzResearch.WordTrace tailWord_869042 prefixEnd_869042 66109074806621348574571 := by
  unfold tailWord_869042
  simp only [CollatzResearch.WordTrace]
  refine ⟨7924141429404182350586345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21131043811744486268230253 7924141429404182350586345)
  ·
    refine ⟨5943106072053136762939759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7924141429404182350586345 5943106072053136762939759)
    ·
      refine ⟨8914659108079705144409639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5943106072053136762939759 8914659108079705144409639)
      ·
        refine ⟨13371988662119557716614459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8914659108079705144409639 13371988662119557716614459)
        ·
          refine ⟨20057982993179336574921689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13371988662119557716614459 20057982993179336574921689)
          ·
            refine ⟨15043487244884502431191267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20057982993179336574921689 15043487244884502431191267)
            ·
              refine ⟨22565230867326753646786901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15043487244884502431191267 22565230867326753646786901)
              ·
                refine ⟨66109074806621348574571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22565230867326753646786901 66109074806621348574571)
                ·
                  rfl

theorem cell21_869042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_869042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869042 prefixEnd_869042 := by exact prefixLift 869042
  have htrace : WordTrace (prefixWord ++ tailWord_869042) baseStart_869042 baseEnd_869042 := by
    simpa [prefixWord, tailWord_869042, baseEnd_869042] using wordTrace_append hprefix tailTrace_869042
  have hstable : (prefixWord ++ tailWord_869042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869042).length < 2 ^ (prefixWord ++ tailWord_869042).sum := by decide
  have hdescent : baseEnd_869042 < baseStart_869042 := by decide
  rcases family_descends (prefixWord ++ tailWord_869042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869076 : List Nat := [2, 4, 1, 3, 2, 2, 7]
def baseStart_869076 : Nat := 118140960795 + 869076 * 2 ^ 59
def prefixEnd_869076 : Nat := 4983230072969 + 3 ^ 40 * 869076 * 2
def baseEnd_869076 : Nat := 22037220409231949128553

theorem tailTrace_869076 : CollatzResearch.WordTrace tailWord_869076 prefixEnd_869076 22037220409231949128553 := by
  unfold tailWord_869076
  simp only [CollatzResearch.WordTrace]
  refine ⟨15848902899746776604541541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21131870532995702139388721 15848902899746776604541541)
  ·
    refine ⟨2971669293702520613351539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15848902899746776604541541 2971669293702520613351539)
    ·
      refine ⟨4457503940553780920027309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971669293702520613351539 4457503940553780920027309)
      ·
        refine ⟨1671563977707667845010241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4457503940553780920027309 1671563977707667845010241)
        ·
          refine ⟨1253672983280750883757681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1671563977707667845010241 1253672983280750883757681)
          ·
            refine ⟨940254737460563162818261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1253672983280750883757681 940254737460563162818261)
            ·
              refine ⟨22037220409231949128553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 940254737460563162818261 22037220409231949128553)
              ·
                rfl

theorem cell21_869076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 7].length) (baseStart_869076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869076 prefixEnd_869076 := by exact prefixLift 869076
  have htrace : WordTrace (prefixWord ++ tailWord_869076) baseStart_869076 baseEnd_869076 := by
    simpa [prefixWord, tailWord_869076, baseEnd_869076] using wordTrace_append hprefix tailTrace_869076
  have hstable : (prefixWord ++ tailWord_869076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869076).length < 2 ^ (prefixWord ++ tailWord_869076).sum := by decide
  have hdescent : baseEnd_869076 < baseStart_869076 := by decide
  rcases family_descends (prefixWord ++ tailWord_869076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869104 : List Nat := [2, 1, 1, 1, 3, 1, 5, 3, 4]
def baseStart_869104 : Nat := 118140960795 + 869104 * 2 ^ 59
def prefixEnd_869104 : Nat := 4983230072969 + 3 ^ 40 * 869104 * 2
def baseEnd_869104 : Nat := 198341373664565715690253

theorem tailTrace_869104 : CollatzResearch.WordTrace tailWord_869104 prefixEnd_869104 198341373664565715690253 := by
  unfold tailWord_869104
  simp only [CollatzResearch.WordTrace]
  refine ⟨15849413521696056995551183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21132551362261409327401577 15849413521696056995551183)
  ·
    refine ⟨23774120282544085493326775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15849413521696056995551183 23774120282544085493326775)
    ·
      refine ⟨35661180423816128239990163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23774120282544085493326775 35661180423816128239990163)
      ·
        refine ⟨53491770635724192359985245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35661180423816128239990163 53491770635724192359985245)
        ·
          refine ⟨20059413988396572134994467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53491770635724192359985245 20059413988396572134994467)
          ·
            refine ⟨30089120982594858202491701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20059413988396572134994467 30089120982594858202491701)
            ·
              refine ⟨2820855092118267956483597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30089120982594858202491701 2820855092118267956483597)
              ·
                refine ⟨1057820659544350483681349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2820855092118267956483597 1057820659544350483681349)
                ·
                  refine ⟨198341373664565715690253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1057820659544350483681349 198341373664565715690253)
                  ·
                    rfl

theorem cell21_869104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 4].length) (baseStart_869104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869104 prefixEnd_869104 := by exact prefixLift 869104
  have htrace : WordTrace (prefixWord ++ tailWord_869104) baseStart_869104 baseEnd_869104 := by
    simpa [prefixWord, tailWord_869104, baseEnd_869104] using wordTrace_append hprefix tailTrace_869104
  have hstable : (prefixWord ++ tailWord_869104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869104).length < 2 ^ (prefixWord ++ tailWord_869104).sum := by decide
  have hdescent : baseEnd_869104 < baseStart_869104 := by decide
  rcases family_descends (prefixWord ++ tailWord_869104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869166 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_869166 : Nat := 118140960795 + 869166 * 2 ^ 59
def prefixEnd_869166 : Nat := 4983230072969 + 3 ^ 40 * 869166 * 2
def baseEnd_869166 : Nat := 198355522909267385656793

theorem tailTrace_869166 : CollatzResearch.WordTrace tailWord_869166 prefixEnd_869166 198355522909267385656793 := by
  unfold tailWord_869166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962636046145937322482419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21134058912778332386572901 3962636046145937322482419)
  ·
    refine ⟨5943954069218905983723629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3962636046145937322482419 5943954069218905983723629)
    ·
      refine ⟨2228982775957089743896361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5943954069218905983723629 2228982775957089743896361)
      ·
        refine ⟨1671737081967817307922271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2228982775957089743896361 1671737081967817307922271)
        ·
          refine ⟨2507605622951725961883407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671737081967817307922271 2507605622951725961883407)
          ·
            refine ⟨3761408434427588942825111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507605622951725961883407 3761408434427588942825111)
            ·
              refine ⟨5642112651641383414237667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3761408434427588942825111 5642112651641383414237667)
              ·
                refine ⟨8463168977462075121356501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5642112651641383414237667 8463168977462075121356501)
                ·
                  refine ⟨198355522909267385656793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8463168977462075121356501 198355522909267385656793)
                  ·
                    rfl

theorem cell21_869166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_869166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869166 prefixEnd_869166 := by exact prefixLift 869166
  have htrace : WordTrace (prefixWord ++ tailWord_869166) baseStart_869166 baseEnd_869166 := by
    simpa [prefixWord, tailWord_869166, baseEnd_869166] using wordTrace_append hprefix tailTrace_869166
  have hstable : (prefixWord ++ tailWord_869166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869166).length < 2 ^ (prefixWord ++ tailWord_869166).sum := by decide
  have hdescent : baseEnd_869166 < baseStart_869166 := by decide
  rcases family_descends (prefixWord ++ tailWord_869166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869183 : List Nat := [1, 1, 2, 2, 5, 2, 2, 3, 3]
def baseStart_869183 : Nat := 118140960795 + 869183 * 2 ^ 59
def prefixEnd_869183 : Nat := 4983230072969 + 3 ^ 40 * 869183 * 2
def baseEnd_869183 : Nat := 198359402540879133873425

theorem tailTrace_869183 : CollatzResearch.WordTrace tailWord_869183 prefixEnd_869183 198359402540879133873425 := by
  unfold tailWord_869183
  simp only [CollatzResearch.WordTrace]
  refine ⟨31701708410105910483228203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21134472273403940322152135 31701708410105910483228203)
  ·
    refine ⟨47552562615158865724842305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31701708410105910483228203 47552562615158865724842305)
    ·
      refine ⟨35664421961369149293631729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47552562615158865724842305 35664421961369149293631729)
      ·
        refine ⟨26748316471026861970223797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35664421961369149293631729 26748316471026861970223797)
        ·
          refine ⟨2507654669158768309708481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26748316471026861970223797 2507654669158768309708481)
          ·
            refine ⟨1880741001869076232281361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2507654669158768309708481 1880741001869076232281361)
            ·
              refine ⟨1410555751401807174211021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1880741001869076232281361 1410555751401807174211021)
              ·
                refine ⟨528958406775677690329133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1410555751401807174211021 528958406775677690329133)
                ·
                  refine ⟨198359402540879133873425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528958406775677690329133 198359402540879133873425)
                  ·
                    rfl

theorem cell21_869183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 3].length) (baseStart_869183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869183 prefixEnd_869183 := by exact prefixLift 869183
  have htrace : WordTrace (prefixWord ++ tailWord_869183) baseStart_869183 baseEnd_869183 := by
    simpa [prefixWord, tailWord_869183, baseEnd_869183] using wordTrace_append hprefix tailTrace_869183
  have hstable : (prefixWord ++ tailWord_869183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869183).length < 2 ^ (prefixWord ++ tailWord_869183).sum := by decide
  have hdescent : baseEnd_869183 < baseStart_869183 := by decide
  rcases family_descends (prefixWord ++ tailWord_869183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869256 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 6]
def baseStart_869256 : Nat := 118140960795 + 869256 * 2 ^ 59
def prefixEnd_869256 : Nat := 4983230072969 + 3 ^ 40 * 869256 * 2
def baseEnd_869256 : Nat := 198376062135447229156609

theorem tailTrace_869256 : CollatzResearch.WordTrace tailWord_869256 prefixEnd_869256 198376062135447229156609 := by
  unfold tailWord_869256
  simp only [CollatzResearch.WordTrace]
  refine ⟨15852185469420721975317811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21136247292560962633757081 15852185469420721975317811)
  ·
    refine ⟨23778278204131082962976717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15852185469420721975317811 23778278204131082962976717)
    ·
      refine ⟨8916854326549156111116269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23778278204131082962976717 8916854326549156111116269)
      ·
        refine ⟨3343820372455933541668601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8916854326549156111116269 3343820372455933541668601)
        ·
          refine ⟨2507865279341950156251451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3343820372455933541668601 2507865279341950156251451)
          ·
            refine ⟨3761797919012925234377177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507865279341950156251451 3761797919012925234377177)
            ·
              refine ⟨2821348439259693925782883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3761797919012925234377177 2821348439259693925782883)
              ·
                refine ⟨4232022658889540888674325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2821348439259693925782883 4232022658889540888674325)
                ·
                  refine ⟨198376062135447229156609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4232022658889540888674325 198376062135447229156609)
                  ·
                    rfl

theorem cell21_869256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_869256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869256 prefixEnd_869256 := by exact prefixLift 869256
  have htrace : WordTrace (prefixWord ++ tailWord_869256) baseStart_869256 baseEnd_869256 := by
    simpa [prefixWord, tailWord_869256, baseEnd_869256] using wordTrace_append hprefix tailTrace_869256
  have hstable : (prefixWord ++ tailWord_869256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869256).length < 2 ^ (prefixWord ++ tailWord_869256).sum := by decide
  have hdescent : baseEnd_869256 < baseStart_869256 := by decide
  rcases family_descends (prefixWord ++ tailWord_869256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869360 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_869360 : Nat := 118140960795 + 869360 * 2 ^ 59
def prefixEnd_869360 : Nat := 4983230072969 + 3 ^ 40 * 869360 * 2
def baseEnd_869360 : Nat := 198399796352366159423063

theorem tailTrace_869360 : CollatzResearch.WordTrace tailWord_869360 prefixEnd_869360 198399796352366159423063 := by
  unfold tailWord_869360
  simp only [CollatzResearch.WordTrace]
  refine ⟨15854082065232334856210767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21138776086976446474947689 15854082065232334856210767)
  ·
    refine ⟨23781123097848502284316151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15854082065232334856210767 23781123097848502284316151)
    ·
      refine ⟨35671684646772753426474227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23781123097848502284316151 35671684646772753426474227)
      ·
        refine ⟨53507526970159130139711341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35671684646772753426474227 53507526970159130139711341)
        ·
          refine ⟨20065322613809673802391753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53507526970159130139711341 20065322613809673802391753)
          ·
            refine ⟨15048991960357255351793815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20065322613809673802391753 15048991960357255351793815)
            ·
              refine ⟨22573487940535883027690723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15048991960357255351793815 22573487940535883027690723)
              ·
                refine ⟨33860231910803824541536085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22573487940535883027690723 33860231910803824541536085)
                ·
                  refine ⟨198399796352366159423063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33860231910803824541536085 198399796352366159423063)
                  ·
                    rfl

theorem cell21_869360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_869360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869360 prefixEnd_869360 := by exact prefixLift 869360
  have htrace : WordTrace (prefixWord ++ tailWord_869360) baseStart_869360 baseEnd_869360 := by
    simpa [prefixWord, tailWord_869360, baseEnd_869360] using wordTrace_append hprefix tailTrace_869360
  have hstable : (prefixWord ++ tailWord_869360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869360).length < 2 ^ (prefixWord ++ tailWord_869360).sum := by decide
  have hdescent : baseEnd_869360 < baseStart_869360 := by decide
  rcases family_descends (prefixWord ++ tailWord_869360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869366 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_869366 : Nat := 118140960795 + 869366 * 2 ^ 59
def prefixEnd_869366 : Nat := 4983230072969 + 3 ^ 40 * 869366 * 2
def baseEnd_869366 : Nat := 198401165634111482323051

theorem tailTrace_869366 : CollatzResearch.WordTrace tailWord_869366 prefixEnd_869366 198401165634111482323051 := by
  unfold tailWord_869366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1981773935527683296071247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21138921978961955158093301 1981773935527683296071247)
  ·
    refine ⟨2972660903291524944106871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1981773935527683296071247 2972660903291524944106871)
    ·
      refine ⟨4458991354937287416160307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2972660903291524944106871 4458991354937287416160307)
      ·
        refine ⟨6688487032405931124240461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4458991354937287416160307 6688487032405931124240461)
        ·
          refine ⟨2508182637152224171590173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6688487032405931124240461 2508182637152224171590173)
          ·
            refine ⟨940568488932084064346315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2508182637152224171590173 940568488932084064346315)
            ·
              refine ⟨1410852733398126096519473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940568488932084064346315 1410852733398126096519473)
              ·
                refine ⟨1058139550048594572389605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1410852733398126096519473 1058139550048594572389605)
                ·
                  refine ⟨198401165634111482323051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1058139550048594572389605 198401165634111482323051)
                  ·
                    rfl

theorem cell21_869366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_869366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869366 prefixEnd_869366 := by exact prefixLift 869366
  have htrace : WordTrace (prefixWord ++ tailWord_869366) baseStart_869366 baseEnd_869366 := by
    simpa [prefixWord, tailWord_869366, baseEnd_869366] using wordTrace_append hprefix tailTrace_869366
  have hstable : (prefixWord ++ tailWord_869366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869366).length < 2 ^ (prefixWord ++ tailWord_869366).sum := by decide
  have hdescent : baseEnd_869366 < baseStart_869366 := by decide
  rcases family_descends (prefixWord ++ tailWord_869366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869377 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 5]
def baseStart_869377 : Nat := 118140960795 + 869377 * 2 ^ 59
def prefixEnd_869377 : Nat := 4983230072969 + 3 ^ 40 * 869377 * 2
def baseEnd_869377 : Nat := 198403675983977907639695

theorem tailTrace_869377 : CollatzResearch.WordTrace tailWord_869377 prefixEnd_869377 198403675983977907639695 := by
  unfold tailWord_869377
  simp only [CollatzResearch.WordTrace]
  refine ⟨31708784171403081615790385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21139189447602054410526923 31708784171403081615790385)
  ·
    refine ⟨23781588128552311211842789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31708784171403081615790385 23781588128552311211842789)
    ·
      refine ⟨4459047774103558352220523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23781588128552311211842789 4459047774103558352220523)
      ·
        refine ⟨6688571661155337528330785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4459047774103558352220523 6688571661155337528330785)
        ·
          refine ⟨5016428745866503146248089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6688571661155337528330785 5016428745866503146248089)
          ·
            refine ⟨3762321559399877359686067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5016428745866503146248089 3762321559399877359686067)
            ·
              refine ⟨5643482339099816039529101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762321559399877359686067 5643482339099816039529101)
              ·
                refine ⟨2116305877162431014823413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5643482339099816039529101 2116305877162431014823413)
                ·
                  refine ⟨198403675983977907639695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2116305877162431014823413 198403675983977907639695)
                  ·
                    rfl

theorem cell21_869377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 5].length) (baseStart_869377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869377 prefixEnd_869377 := by exact prefixLift 869377
  have htrace : WordTrace (prefixWord ++ tailWord_869377) baseStart_869377 baseEnd_869377 := by
    simpa [prefixWord, tailWord_869377, baseEnd_869377] using wordTrace_append hprefix tailTrace_869377
  have hstable : (prefixWord ++ tailWord_869377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869377).length < 2 ^ (prefixWord ++ tailWord_869377).sum := by decide
  have hdescent : baseEnd_869377 < baseStart_869377 := by decide
  rcases family_descends (prefixWord ++ tailWord_869377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869411 : List Nat := [1, 1, 1, 4, 3, 4, 1, 3, 3]
def baseStart_869411 : Nat := 118140960795 + 869411 * 2 ^ 59
def prefixEnd_869411 : Nat := 4983230072969 + 3 ^ 40 * 869411 * 2
def baseEnd_869411 : Nat := 198411435247201404072959

theorem tailTrace_869411 : CollatzResearch.WordTrace tailWord_869411 prefixEnd_869411 198411435247201404072959 := by
  unfold tailWord_869411
  simp only [CollatzResearch.WordTrace]
  refine ⟨31710024253279905422528087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21140016168853270281685391 31710024253279905422528087)
  ·
    refine ⟨47565036379919858133792131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31710024253279905422528087 47565036379919858133792131)
    ·
      refine ⟨71347554569879787200688197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47565036379919858133792131 71347554569879787200688197)
      ·
        refine ⟨13377666481852460100129037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71347554569879787200688197 13377666481852460100129037)
        ·
          refine ⟨5016624930694672537548389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13377666481852460100129037 5016624930694672537548389)
          ·
            refine ⟨940617174505251100790323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5016624930694672537548389 940617174505251100790323)
            ·
              refine ⟨1410925761757876651185485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940617174505251100790323 1410925761757876651185485)
              ·
                refine ⟨529097160659203744194557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1410925761757876651185485 529097160659203744194557)
                ·
                  refine ⟨198411435247201404072959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529097160659203744194557 198411435247201404072959)
                  ·
                    rfl

theorem cell21_869411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 3, 3].length) (baseStart_869411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869411 prefixEnd_869411 := by exact prefixLift 869411
  have htrace : WordTrace (prefixWord ++ tailWord_869411) baseStart_869411 baseEnd_869411 := by
    simpa [prefixWord, tailWord_869411, baseEnd_869411] using wordTrace_append hprefix tailTrace_869411
  have hstable : (prefixWord ++ tailWord_869411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869411).length < 2 ^ (prefixWord ++ tailWord_869411).sum := by decide
  have hdescent : baseEnd_869411 < baseStart_869411 := by decide
  rcases family_descends (prefixWord ++ tailWord_869411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869481 : List Nat := [1, 2, 1, 1, 1, 15]
def baseStart_869481 : Nat := 118140960795 + 869481 * 2 ^ 59
def prefixEnd_869481 : Nat := 4983230072969 + 3 ^ 40 * 869481 * 2
def baseEnd_869481 : Nat := 7349163340773956959487

theorem tailTrace_869481 : CollatzResearch.WordTrace tailWord_869481 prefixEnd_869481 7349163340773956959487 := by
  unfold tailWord_869481
  simp only [CollatzResearch.WordTrace]
  refine ⟨31712577363026307377576297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21141718242017538251717531 31712577363026307377576297)
  ·
    refine ⟨23784433022269730533182223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31712577363026307377576297 23784433022269730533182223)
    ·
      refine ⟨35676649533404595799773335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23784433022269730533182223 35676649533404595799773335)
      ·
        refine ⟨53514974300106893699660003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35676649533404595799773335 53514974300106893699660003)
        ·
          refine ⟨80272461450160340549490005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53514974300106893699660003 80272461450160340549490005)
          ·
            refine ⟨7349163340773956959487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 80272461450160340549490005 7349163340773956959487)
            ·
              rfl

theorem cell21_869481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 15].length) (baseStart_869481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869481 prefixEnd_869481 := by exact prefixLift 869481
  have htrace : WordTrace (prefixWord ++ tailWord_869481) baseStart_869481 baseEnd_869481 := by
    simpa [prefixWord, tailWord_869481, baseEnd_869481] using wordTrace_append hprefix tailTrace_869481
  have hstable : (prefixWord ++ tailWord_869481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869481).length < 2 ^ (prefixWord ++ tailWord_869481).sum := by decide
  have hdescent : baseEnd_869481 < baseStart_869481 := by decide
  rcases family_descends (prefixWord ++ tailWord_869481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869484 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 4]
def baseStart_869484 : Nat := 118140960795 + 869484 * 2 ^ 59
def prefixEnd_869484 : Nat := 4983230072969 + 3 ^ 40 * 869484 * 2
def baseEnd_869484 : Nat := 198428094841769499356143

theorem tailTrace_869484 : CollatzResearch.WordTrace tailWord_869484 prefixEnd_869484 198428094841769499356143 := by
  unfold tailWord_869484
  simp only [CollatzResearch.WordTrace]
  refine ⟨15856343391007719444967753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21141791188010292593290337 15856343391007719444967753)
  ·
    refine ⟨11892257543255789583725815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15856343391007719444967753 11892257543255789583725815)
    ·
      refine ⟨17838386314883684375588723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11892257543255789583725815 17838386314883684375588723)
      ·
        refine ⟨26757579472325526563383085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17838386314883684375588723 26757579472325526563383085)
        ·
          refine ⟨10034092302122072461268657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26757579472325526563383085 10034092302122072461268657)
          ·
            refine ⟨7525569226591554345951493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10034092302122072461268657 7525569226591554345951493)
            ·
              refine ⟨1411044229985916439865905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7525569226591554345951493 1411044229985916439865905)
              ·
                refine ⟨1058283172489437329899429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411044229985916439865905 1058283172489437329899429)
                ·
                  refine ⟨198428094841769499356143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1058283172489437329899429 198428094841769499356143)
                  ·
                    rfl

theorem cell21_869484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_869484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869484 prefixEnd_869484 := by exact prefixLift 869484
  have htrace : WordTrace (prefixWord ++ tailWord_869484) baseStart_869484 baseEnd_869484 := by
    simpa [prefixWord, tailWord_869484, baseEnd_869484] using wordTrace_append hprefix tailTrace_869484
  have hstable : (prefixWord ++ tailWord_869484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869484).length < 2 ^ (prefixWord ++ tailWord_869484).sum := by decide
  have hdescent : baseEnd_869484 < baseStart_869484 := by decide
  rcases family_descends (prefixWord ++ tailWord_869484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869546 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_869546 : Nat := 118140960795 + 869546 * 2 ^ 59
def prefixEnd_869546 : Nat := 4983230072969 + 3 ^ 40 * 869546 * 2
def baseEnd_869546 : Nat := 198442244086471169322683

theorem tailTrace_869546 : CollatzResearch.WordTrace tailWord_869546 prefixEnd_869546 198442244086471169322683 := by
  unfold tailWord_869546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928737026947705869673123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21143298738527215652461661 7928737026947705869673123)
  ·
    refine ⟨11893105540421558804509685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7928737026947705869673123 11893105540421558804509685)
    ·
      refine ⟨1114978644414521137922783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11893105540421558804509685 1114978644414521137922783)
      ·
        refine ⟨1672467966621781706884175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114978644414521137922783 1672467966621781706884175)
        ·
          refine ⟨2508701949932672560326263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672467966621781706884175 2508701949932672560326263)
          ·
            refine ⟨3763052924899008840489395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508701949932672560326263 3763052924899008840489395)
            ·
              refine ⟨5644579387348513260734093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763052924899008840489395 5644579387348513260734093)
              ·
                refine ⟨2116717270255692472775285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5644579387348513260734093 2116717270255692472775285)
                ·
                  refine ⟨198442244086471169322683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2116717270255692472775285 198442244086471169322683)
                  ·
                    rfl

theorem cell21_869546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_869546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869546 prefixEnd_869546 := by exact prefixLift 869546
  have htrace : WordTrace (prefixWord ++ tailWord_869546) baseStart_869546 baseEnd_869546 := by
    simpa [prefixWord, tailWord_869546, baseEnd_869546] using wordTrace_append hprefix tailTrace_869546
  have hstable : (prefixWord ++ tailWord_869546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869546).length < 2 ^ (prefixWord ++ tailWord_869546).sum := by decide
  have hdescent : baseEnd_869546 < baseStart_869546 := by decide
  rcases family_descends (prefixWord ++ tailWord_869546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869681 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 5]
def baseStart_869681 : Nat := 118140960795 + 869681 * 2 ^ 59
def prefixEnd_869681 : Nat := 4983230072969 + 3 ^ 40 * 869681 * 2
def baseEnd_869681 : Nat := 198473052925740934572407

theorem tailTrace_869681 : CollatzResearch.WordTrace tailWord_869681 prefixEnd_869681 198473052925740934572407 := by
  unfold tailWord_869681
  simp only [CollatzResearch.WordTrace]
  refine ⟨31719871962301741534856897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21146581308201161023237931 31719871962301741534856897)
  ·
    refine ⟨23789903971726306151142673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31719871962301741534856897 23789903971726306151142673)
    ·
      refine ⟨17842427978794729613357005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23789903971726306151142673 17842427978794729613357005)
      ·
        refine ⟨6690910492048023605008877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17842427978794729613357005 6690910492048023605008877)
        ·
          refine ⟨2509091434518008851878329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6690910492048023605008877 2509091434518008851878329)
          ·
            refine ⟨1881818575888506638908747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2509091434518008851878329 1881818575888506638908747)
            ·
              refine ⟨2822727863832759958363121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881818575888506638908747 2822727863832759958363121)
              ·
                refine ⟨2117045897874569968772341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2822727863832759958363121 2117045897874569968772341)
                ·
                  refine ⟨198473052925740934572407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2117045897874569968772341 198473052925740934572407)
                  ·
                    rfl

theorem cell21_869681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_869681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869681 prefixEnd_869681 := by exact prefixLift 869681
  have htrace : WordTrace (prefixWord ++ tailWord_869681) baseStart_869681 baseEnd_869681 := by
    simpa [prefixWord, tailWord_869681, baseEnd_869681] using wordTrace_append hprefix tailTrace_869681
  have hstable : (prefixWord ++ tailWord_869681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869681).length < 2 ^ (prefixWord ++ tailWord_869681).sum := by decide
  have hdescent : baseEnd_869681 < baseStart_869681 := by decide
  rcases family_descends (prefixWord ++ tailWord_869681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869771 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 4]
def baseStart_869771 : Nat := 118140960795 + 869771 * 2 ^ 59
def prefixEnd_869771 : Nat := 4983230072969 + 3 ^ 40 * 869771 * 2
def baseEnd_869771 : Nat := 198493592151920778072223

theorem tailTrace_869771 : CollatzResearch.WordTrace tailWord_869771 prefixEnd_869771 198493592151920778072223 := by
  unfold tailWord_869771
  simp only [CollatzResearch.WordTrace]
  refine ⟨31723154531975686905633167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21148769687983791270422111 31723154531975686905633167)
  ·
    refine ⟨47584731797963530358449751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31723154531975686905633167 47584731797963530358449751)
    ·
      refine ⟨71377097696945295537674627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47584731797963530358449751 71377097696945295537674627)
      ·
        refine ⟨107065646545417943306511941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71377097696945295537674627 107065646545417943306511941)
        ·
          refine ⟨20074808727265864369970989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 107065646545417943306511941 20074808727265864369970989)
          ·
            refine ⟨7528053272724699138739121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20074808727265864369970989 7528053272724699138739121)
            ·
              refine ⟨5646039954543524354054341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7528053272724699138739121 5646039954543524354054341)
              ·
                refine ⟨1058632491476910816385189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5646039954543524354054341 1058632491476910816385189)
                ·
                  refine ⟨198493592151920778072223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1058632491476910816385189 198493592151920778072223)
                  ·
                    rfl

theorem cell21_869771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 4].length) (baseStart_869771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869771 prefixEnd_869771 := by exact prefixLift 869771
  have htrace : WordTrace (prefixWord ++ tailWord_869771) baseStart_869771 baseEnd_869771 := by
    simpa [prefixWord, tailWord_869771, baseEnd_869771] using wordTrace_append hprefix tailTrace_869771
  have hstable : (prefixWord ++ tailWord_869771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869771).length < 2 ^ (prefixWord ++ tailWord_869771).sum := by decide
  have hdescent : baseEnd_869771 < baseStart_869771 := by decide
  rcases family_descends (prefixWord ++ tailWord_869771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869785 : List Nat := [1, 2, 1, 2, 1, 5, 1, 8]
def baseStart_869785 : Nat := 118140960795 + 869785 * 2 ^ 59
def prefixEnd_869785 : Nat := 4983230072969 + 3 ^ 40 * 869785 * 2
def baseEnd_869785 : Nat := 66165595714219954946287

theorem tailTrace_869785 : CollatzResearch.WordTrace tailWord_869785 prefixEnd_869785 66165595714219954946287 := by
  unfold tailWord_869785
  simp only [CollatzResearch.WordTrace]
  refine ⟨31723665153924967296642809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21149110102616644864428539 31723665153924967296642809)
  ·
    refine ⟨23792748865443725472482107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31723665153924967296642809 23792748865443725472482107)
    ·
      refine ⟨35689123298165588208723161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23792748865443725472482107 35689123298165588208723161)
      ·
        refine ⟨26766842473624191156542371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35689123298165588208723161 26766842473624191156542371)
        ·
          refine ⟨40150263710436286734813557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26766842473624191156542371 40150263710436286734813557)
          ·
            refine ⟨3764087222853401881388771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40150263710436286734813557 3764087222853401881388771)
            ·
              refine ⟨5646130834280102822083157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3764087222853401881388771 5646130834280102822083157)
              ·
                refine ⟨66165595714219954946287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5646130834280102822083157 66165595714219954946287)
                ·
                  rfl

theorem cell21_869785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 8].length) (baseStart_869785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869785 prefixEnd_869785 := by exact prefixLift 869785
  have htrace : WordTrace (prefixWord ++ tailWord_869785) baseStart_869785 baseEnd_869785 := by
    simpa [prefixWord, tailWord_869785, baseEnd_869785] using wordTrace_append hprefix tailTrace_869785
  have hstable : (prefixWord ++ tailWord_869785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869785).length < 2 ^ (prefixWord ++ tailWord_869785).sum := by decide
  have hdescent : baseEnd_869785 < baseStart_869785 := by decide
  rcases family_descends (prefixWord ++ tailWord_869785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869878 : List Nat := [5, 1, 1, 1, 2, 3, 8]
def baseStart_869878 : Nat := 118140960795 + 869878 * 2 ^ 59
def prefixEnd_869878 : Nat := 4983230072969 + 3 ^ 40 * 869878 * 2
def baseEnd_869878 : Nat := 22057556778856929976519

theorem tailTrace_869878 : CollatzResearch.WordTrace tailWord_869878 prefixEnd_869878 22057556778856929976519 := by
  unfold tailWord_869878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1982941071411752761236143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21151371428392029453185525 1982941071411752761236143)
  ·
    refine ⟨2974411607117629141854215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1982941071411752761236143 2974411607117629141854215)
    ·
      refine ⟨4461617410676443712781323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974411607117629141854215 4461617410676443712781323)
      ·
        refine ⟨6692426116014665569171985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4461617410676443712781323 6692426116014665569171985)
        ·
          refine ⟨5019319587010999176878989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6692426116014665569171985 5019319587010999176878989)
          ·
            refine ⟨1882244845129124691329621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5019319587010999176878989 1882244845129124691329621)
            ·
              refine ⟨22057556778856929976519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1882244845129124691329621 22057556778856929976519)
              ·
                rfl

theorem cell21_869878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 8].length) (baseStart_869878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869878 prefixEnd_869878 := by exact prefixLift 869878
  have htrace : WordTrace (prefixWord ++ tailWord_869878) baseStart_869878 baseEnd_869878 := by
    simpa [prefixWord, tailWord_869878, baseEnd_869878] using wordTrace_append hprefix tailTrace_869878
  have hstable : (prefixWord ++ tailWord_869878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869878).length < 2 ^ (prefixWord ++ tailWord_869878).sum := by decide
  have hdescent : baseEnd_869878 < baseStart_869878 := by decide
  rcases family_descends (prefixWord ++ tailWord_869878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869912 : List Nat := [2, 1, 2, 3, 5, 1, 2, 5]
def baseStart_869912 : Nat := 118140960795 + 869912 * 2 ^ 59
def prefixEnd_869912 : Nat := 4983230072969 + 3 ^ 40 * 869912 * 2
def baseEnd_869912 : Nat := 66175256757645288740645

theorem tailTrace_869912 : CollatzResearch.WordTrace tailWord_869912 prefixEnd_869912 66175256757645288740645 := by
  unfold tailWord_869912
  simp only [CollatzResearch.WordTrace]
  refine ⟨15864148612232433993257995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21152198149643245324343993 15864148612232433993257995)
  ·
    refine ⟨23796222918348650989886993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15864148612232433993257995 23796222918348650989886993)
    ·
      refine ⟨17847167188761488242415245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23796222918348650989886993 17847167188761488242415245)
      ·
        refine ⟨6692687695785558090905717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17847167188761488242415245 6692687695785558090905717)
        ·
          refine ⟨627439471479896071022411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6692687695785558090905717 627439471479896071022411)
          ·
            refine ⟨941159207219844106533617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627439471479896071022411 941159207219844106533617)
            ·
              refine ⟨705869405414883079900213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941159207219844106533617 705869405414883079900213)
              ·
                refine ⟨66175256757645288740645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 705869405414883079900213 66175256757645288740645)
                ·
                  rfl

theorem cell21_869912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 5].length) (baseStart_869912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869912 prefixEnd_869912 := by exact prefixLift 869912
  have htrace : WordTrace (prefixWord ++ tailWord_869912) baseStart_869912 baseEnd_869912 := by
    simpa [prefixWord, tailWord_869912, baseEnd_869912] using wordTrace_append hprefix tailTrace_869912
  have hstable : (prefixWord ++ tailWord_869912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869912).length < 2 ^ (prefixWord ++ tailWord_869912).sum := by decide
  have hdescent : baseEnd_869912 < baseStart_869912 := by decide
  rcases family_descends (prefixWord ++ tailWord_869912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869918 : List Nat := [4, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_869918 : Nat := 118140960795 + 869918 * 2 ^ 59
def prefixEnd_869918 : Nat := 4983230072969 + 3 ^ 40 * 869918 * 2
def baseEnd_869918 : Nat := 198527139554681189121923

theorem tailTrace_869918 : CollatzResearch.WordTrace tailWord_869918 prefixEnd_869918 198527139554681189121923 := by
  unfold tailWord_869918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966064507805391376404301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21152344041628754007489605 3966064507805391376404301)
  ·
    refine ⟨1487274190427021766151613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3966064507805391376404301 1487274190427021766151613)
    ·
      refine ⟨557727821410133162306855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1487274190427021766151613 557727821410133162306855)
      ·
        refine ⟨836591732115199743460283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557727821410133162306855 836591732115199743460283)
        ·
          refine ⟨1254887598172799615190425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836591732115199743460283 1254887598172799615190425)
          ·
            refine ⟨941165698629599711392819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1254887598172799615190425 941165698629599711392819)
            ·
              refine ⟨1411748547944399567089229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941165698629599711392819 1411748547944399567089229)
              ·
                refine ⟨529405705479149837658461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1411748547944399567089229 529405705479149837658461)
                ·
                  refine ⟨198527139554681189121923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529405705479149837658461 198527139554681189121923)
                  ·
                    rfl

theorem cell21_869918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_869918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869918 prefixEnd_869918 := by exact prefixLift 869918
  have htrace : WordTrace (prefixWord ++ tailWord_869918) baseStart_869918 baseEnd_869918 := by
    simpa [prefixWord, tailWord_869918, baseEnd_869918] using wordTrace_append hprefix tailTrace_869918
  have hstable : (prefixWord ++ tailWord_869918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869918).length < 2 ^ (prefixWord ++ tailWord_869918).sum := by decide
  have hdescent : baseEnd_869918 < baseStart_869918 := by decide
  rcases family_descends (prefixWord ++ tailWord_869918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869985 : List Nat := [1, 2, 3, 1, 1, 3, 2, 5, 3]
def baseStart_869985 : Nat := 118140960795 + 869985 * 2 ^ 59
def prefixEnd_869985 : Nat := 4983230072969 + 3 ^ 40 * 869985 * 2
def baseEnd_869985 : Nat := 198542429867503961505119

theorem tailTrace_869985 : CollatzResearch.WordTrace tailWord_869985 prefixEnd_869985 198542429867503961505119 := by
  unfold tailWord_869985
  simp only [CollatzResearch.WordTrace]
  refine ⟨31730959753200401453923409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21153973168800267635948939 31730959753200401453923409)
  ·
    refine ⟨23798219814900301090442557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31730959753200401453923409 23798219814900301090442557)
    ·
      refine ⟨8924332430587612908915959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23798219814900301090442557 8924332430587612908915959)
      ·
        refine ⟨13386498645881419363373939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8924332430587612908915959 13386498645881419363373939)
        ·
          refine ⟨20079747968822129045060909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13386498645881419363373939 20079747968822129045060909)
          ·
            refine ⟨7529905488308298391897841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20079747968822129045060909 7529905488308298391897841)
            ·
              refine ⟨5647429116231223793923381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7529905488308298391897841 5647429116231223793923381)
              ·
                refine ⟨529446479646677230680317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5647429116231223793923381 529446479646677230680317)
                ·
                  refine ⟨198542429867503961505119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529446479646677230680317 198542429867503961505119)
                  ·
                    rfl

theorem cell21_869985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 5, 3].length) (baseStart_869985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_869985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_869985 prefixEnd_869985 := by exact prefixLift 869985
  have htrace : WordTrace (prefixWord ++ tailWord_869985) baseStart_869985 baseEnd_869985 := by
    simpa [prefixWord, tailWord_869985, baseEnd_869985] using wordTrace_append hprefix tailTrace_869985
  have hstable : (prefixWord ++ tailWord_869985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869985).length < 2 ^ (prefixWord ++ tailWord_869985).sum := by decide
  have hdescent : baseEnd_869985 < baseStart_869985 := by decide
  rcases family_descends (prefixWord ++ tailWord_869985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870002 : List Nat := [3, 2, 1, 2, 3, 2, 1, 4, 3]
def baseStart_870002 : Nat := 118140960795 + 870002 * 2 ^ 59
def prefixEnd_870002 : Nat := 4983230072969 + 3 ^ 40 * 870002 * 2
def baseEnd_870002 : Nat := 198546309499115709721751

theorem tailTrace_870002 : CollatzResearch.WordTrace tailWord_870002 prefixEnd_870002 198546309499115709721751 := by
  unfold tailWord_870002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7932894948534703339323065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21154386529425875571528173 7932894948534703339323065)
  ·
    refine ⟨5949671211401027504492299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7932894948534703339323065 5949671211401027504492299)
    ·
      refine ⟨8924506817101541256738449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5949671211401027504492299 8924506817101541256738449)
      ·
        refine ⟨6693380112826155942553837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8924506817101541256738449 6693380112826155942553837)
        ·
          refine ⟨2510017542309808478457689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6693380112826155942553837 2510017542309808478457689)
          ·
            refine ⟨1882513156732356358843267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2510017542309808478457689 1882513156732356358843267)
            ·
              refine ⟨2823769735098534538264901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882513156732356358843267 2823769735098534538264901)
              ·
                refine ⟨529456825330975225924669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2823769735098534538264901 529456825330975225924669)
                ·
                  refine ⟨198546309499115709721751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529456825330975225924669 198546309499115709721751)
                  ·
                    rfl

theorem cell21_870002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 4, 3].length) (baseStart_870002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870002 prefixEnd_870002 := by exact prefixLift 870002
  have htrace : WordTrace (prefixWord ++ tailWord_870002) baseStart_870002 baseEnd_870002 := by
    simpa [prefixWord, tailWord_870002, baseEnd_870002] using wordTrace_append hprefix tailTrace_870002
  have hstable : (prefixWord ++ tailWord_870002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870002).length < 2 ^ (prefixWord ++ tailWord_870002).sum := by decide
  have hdescent : baseEnd_870002 < baseStart_870002 := by decide
  rcases family_descends (prefixWord ++ tailWord_870002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870050 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_870050 : Nat := 118140960795 + 870050 * 2 ^ 59
def prefixEnd_870050 : Nat := 4983230072969 + 3 ^ 40 * 870050 * 2
def baseEnd_870050 : Nat := 198557263753078292921653

theorem tailTrace_870050 : CollatzResearch.WordTrace tailWord_870050 prefixEnd_870050 198557263753078292921653 := by
  unfold tailWord_870050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7933332624491229388759901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21155553665309945036693069 7933332624491229388759901)
  ·
    refine ⟨2974999734184211020784963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7933332624491229388759901 2974999734184211020784963)
    ·
      refine ⟨4462499601276316531177445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974999734184211020784963 4462499601276316531177445)
      ·
        refine ⟨836718675239309349595771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4462499601276316531177445 836718675239309349595771)
        ·
          refine ⟨1255078012858964024393657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836718675239309349595771 1255078012858964024393657)
          ·
            refine ⟨941308509644223018295243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255078012858964024393657 941308509644223018295243)
            ·
              refine ⟨1411962764466334527442865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941308509644223018295243 1411962764466334527442865)
              ·
                refine ⟨1058972073349750895582149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411962764466334527442865 1058972073349750895582149)
                ·
                  refine ⟨198557263753078292921653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1058972073349750895582149 198557263753078292921653)
                  ·
                    rfl

theorem cell21_870050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_870050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870050 prefixEnd_870050 := by exact prefixLift 870050
  have htrace : WordTrace (prefixWord ++ tailWord_870050) baseStart_870050 baseEnd_870050 := by
    simpa [prefixWord, tailWord_870050, baseEnd_870050] using wordTrace_append hprefix tailTrace_870050
  have hstable : (prefixWord ++ tailWord_870050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870050).length < 2 ^ (prefixWord ++ tailWord_870050).sum := by decide
  have hdescent : baseEnd_870050 < baseStart_870050 := by decide
  rcases family_descends (prefixWord ++ tailWord_870050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870061 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 5]
def baseStart_870061 : Nat := 118140960795 + 870061 * 2 ^ 59
def prefixEnd_870061 : Nat := 4983230072969 + 3 ^ 40 * 870061 * 2
def baseEnd_870061 : Nat := 198559774102944718238297

theorem tailTrace_870061 : CollatzResearch.WordTrace tailWord_870061 prefixEnd_870061 198559774102944718238297 := by
  unfold tailWord_870061
  simp only [CollatzResearch.WordTrace]
  refine ⟨31733731700925066433690037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21155821133950044289126691 31733731700925066433690037)
  ·
    refine ⟨2975037346961724978158441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31733731700925066433690037 2975037346961724978158441)
    ·
      refine ⟨2231278010221293733618831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2975037346961724978158441 2231278010221293733618831)
      ·
        refine ⟨3346917015331940600428247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2231278010221293733618831 3346917015331940600428247)
        ·
          refine ⟨5020375522997910900642371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346917015331940600428247 5020375522997910900642371)
          ·
            refine ⟨7530563284496866350963557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5020375522997910900642371 7530563284496866350963557)
            ·
              refine ⟨1411980615843162440805667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7530563284496866350963557 1411980615843162440805667)
              ·
                refine ⟨2117970923764743661208501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411980615843162440805667 2117970923764743661208501)
                ·
                  refine ⟨198559774102944718238297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2117970923764743661208501 198559774102944718238297)
                  ·
                    rfl

theorem cell21_870061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_870061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870061 prefixEnd_870061 := by exact prefixLift 870061
  have htrace : WordTrace (prefixWord ++ tailWord_870061) baseStart_870061 baseEnd_870061 := by
    simpa [prefixWord, tailWord_870061, baseEnd_870061] using wordTrace_append hprefix tailTrace_870061
  have hstable : (prefixWord ++ tailWord_870061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870061).length < 2 ^ (prefixWord ++ tailWord_870061).sum := by decide
  have hdescent : baseEnd_870061 < baseStart_870061 := by decide
  rcases family_descends (prefixWord ++ tailWord_870061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870157 : List Nat := [1, 7, 2, 1, 2, 8]
def baseStart_870157 : Nat := 118140960795 + 870157 * 2 ^ 59
def prefixEnd_870157 : Nat := 4983230072969 + 3 ^ 40 * 870157 * 2
def baseEnd_870157 : Nat := 7354877133735921653263

theorem tailTrace_870157 : CollatzResearch.WordTrace tailWord_870157 prefixEnd_870157 7354877133735921653263 := by
  unfold tailWord_870157
  simp only [CollatzResearch.WordTrace]
  refine ⟨31737233108577274829184725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21158155405718183219456483 31737233108577274829184725)
  ·
    refine ⟨743841400982279878809017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31737233108577274829184725 743841400982279878809017)
    ·
      refine ⟨557881050736709909106763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 743841400982279878809017 557881050736709909106763)
      ·
        refine ⟨836821576105064863660145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557881050736709909106763 836821576105064863660145)
        ·
          refine ⟨627616182078798647745109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 836821576105064863660145 627616182078798647745109)
          ·
            refine ⟨7354877133735921653263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 627616182078798647745109 7354877133735921653263)
            ·
              rfl

theorem cell21_870157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 8].length) (baseStart_870157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870157 prefixEnd_870157 := by exact prefixLift 870157
  have htrace : WordTrace (prefixWord ++ tailWord_870157) baseStart_870157 baseEnd_870157 := by
    simpa [prefixWord, tailWord_870157, baseEnd_870157] using wordTrace_append hprefix tailTrace_870157
  have hstable : (prefixWord ++ tailWord_870157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870157).length < 2 ^ (prefixWord ++ tailWord_870157).sum := by decide
  have hdescent : baseEnd_870157 < baseStart_870157 := by decide
  rcases family_descends (prefixWord ++ tailWord_870157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870213 : List Nat := [1, 3, 1, 1, 1, 2, 6, 3, 3]
def baseStart_870213 : Nat := 118140960795 + 870213 * 2 ^ 59
def prefixEnd_870213 : Nat := 4983230072969 + 3 ^ 40 * 870213 * 2
def baseEnd_870213 : Nat := 198594462573826231704653

theorem tailTrace_870213 : CollatzResearch.WordTrace tailWord_870213 prefixEnd_870213 198594462573826231704653 := by
  unfold tailWord_870213
  simp only [CollatzResearch.WordTrace]
  refine ⟨31739275596374396393223293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21159517064249597595482195 31739275596374396393223293)
  ·
    refine ⟨11902228348640398647458735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31739275596374396393223293 11902228348640398647458735)
    ·
      refine ⟨17853342522960597971188103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11902228348640398647458735 17853342522960597971188103)
      ·
        refine ⟨26780013784440896956782155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17853342522960597971188103 26780013784440896956782155)
        ·
          refine ⟨40170020676661345435173233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26780013784440896956782155 40170020676661345435173233)
          ·
            refine ⟨30127515507496009076379925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40170020676661345435173233 30127515507496009076379925)
            ·
              refine ⟨1412227289413875425455309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30127515507496009076379925 1412227289413875425455309)
              ·
                refine ⟨529585233530203284545741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1412227289413875425455309 529585233530203284545741)
                ·
                  refine ⟨198594462573826231704653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529585233530203284545741 198594462573826231704653)
                  ·
                    rfl

theorem cell21_870213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_870213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870213 prefixEnd_870213 := by exact prefixLift 870213
  have htrace : WordTrace (prefixWord ++ tailWord_870213) baseStart_870213 baseEnd_870213 := by
    simpa [prefixWord, tailWord_870213, baseEnd_870213] using wordTrace_append hprefix tailTrace_870213
  have hstable : (prefixWord ++ tailWord_870213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870213).length < 2 ^ (prefixWord ++ tailWord_870213).sum := by decide
  have hdescent : baseEnd_870213 < baseStart_870213 := by decide
  rcases family_descends (prefixWord ++ tailWord_870213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870365 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 5]
def baseStart_870365 : Nat := 118140960795 + 870365 * 2 ^ 59
def prefixEnd_870365 : Nat := 4983230072969 + 3 ^ 40 * 870365 * 2
def baseEnd_870365 : Nat := 198629151044707745171009

theorem tailTrace_870365 : CollatzResearch.WordTrace tailWord_870365 prefixEnd_870365 198629151044707745171009 := by
  unfold tailWord_870365
  simp only [CollatzResearch.WordTrace]
  refine ⟨31744819491823726352756549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21163212994549150901837699 31744819491823726352756549)
  ·
    refine ⟨5952153654716948691141853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31744819491823726352756549 5952153654716948691141853)
    ·
      refine ⟨2232057620518855759178195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5952153654716948691141853 2232057620518855759178195)
      ·
        refine ⟨3348086430778283638767293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2232057620518855759178195 3348086430778283638767293)
        ·
          refine ⟨1255532411541856364537735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3348086430778283638767293 1255532411541856364537735)
          ·
            refine ⟨1883298617312784546806603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255532411541856364537735 1883298617312784546806603)
            ·
              refine ⟨2824947925969176820209905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883298617312784546806603 2824947925969176820209905)
              ·
                refine ⟨2118710944476882615157429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824947925969176820209905 2118710944476882615157429)
                ·
                  refine ⟨198629151044707745171009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2118710944476882615157429 198629151044707745171009)
                  ·
                    rfl

theorem cell21_870365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_870365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870365 prefixEnd_870365 := by exact prefixLift 870365
  have htrace : WordTrace (prefixWord ++ tailWord_870365) baseStart_870365 baseEnd_870365 := by
    simpa [prefixWord, tailWord_870365, baseEnd_870365] using wordTrace_append hprefix tailTrace_870365
  have hstable : (prefixWord ++ tailWord_870365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870365).length < 2 ^ (prefixWord ++ tailWord_870365).sum := by decide
  have hdescent : baseEnd_870365 < baseStart_870365 := by decide
  rcases family_descends (prefixWord ++ tailWord_870365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870382 : List Nat := [4, 1, 2, 1, 3, 2, 2, 3, 3]
def baseStart_870382 : Nat := 118140960795 + 870382 * 2 ^ 59
def prefixEnd_870382 : Nat := 4983230072969 + 3 ^ 40 * 870382 * 2
def baseEnd_870382 : Nat := 198633030676319493387641

theorem tailTrace_870382 : CollatzResearch.WordTrace tailWord_870382 prefixEnd_870382 198633030676319493387641 := by
  unfold tailWord_870382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968179941595267282015675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21163626355174758837416933 3968179941595267282015675)
  ·
    refine ⟨5952269912392900923023513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3968179941595267282015675 5952269912392900923023513)
    ·
      refine ⟨4464202434294675692267635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5952269912392900923023513 4464202434294675692267635)
      ·
        refine ⟨6696303651442013538401453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4464202434294675692267635 6696303651442013538401453)
        ·
          refine ⟨2511113869290755076900545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6696303651442013538401453 2511113869290755076900545)
          ·
            refine ⟨1883335401968066307675409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2511113869290755076900545 1883335401968066307675409)
            ·
              refine ⟨1412501551476049730756557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883335401968066307675409 1412501551476049730756557)
              ·
                refine ⟨529688081803518649033709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1412501551476049730756557 529688081803518649033709)
                ·
                  refine ⟨198633030676319493387641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529688081803518649033709 198633030676319493387641)
                  ·
                    rfl

theorem cell21_870382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_870382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870382 prefixEnd_870382 := by exact prefixLift 870382
  have htrace : WordTrace (prefixWord ++ tailWord_870382) baseStart_870382 baseEnd_870382 := by
    simpa [prefixWord, tailWord_870382, baseEnd_870382] using wordTrace_append hprefix tailTrace_870382
  have hstable : (prefixWord ++ tailWord_870382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870382).length < 2 ^ (prefixWord ++ tailWord_870382).sum := by decide
  have hdescent : baseEnd_870382 < baseStart_870382 := by decide
  rcases family_descends (prefixWord ++ tailWord_870382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870610 : List Nat := [3, 2, 2, 2, 1, 4, 1, 3, 3]
def baseStart_870610 : Nat := 118140960795 + 870610 * 2 ^ 59
def prefixEnd_870610 : Nat := 4983230072969 + 3 ^ 40 * 870610 * 2
def baseEnd_870610 : Nat := 198685063382641763587175

theorem tailTrace_870610 : CollatzResearch.WordTrace tailWord_870610 prefixEnd_870610 198685063382641763587175 := by
  unfold tailWord_870610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7938438843984033298856321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21169170250624088796950189 7938438843984033298856321)
  ·
    refine ⟨5953829132988024974142241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7938438843984033298856321 5953829132988024974142241)
    ·
      refine ⟨4465371849741018730606681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5953829132988024974142241 4465371849741018730606681)
      ·
        refine ⟨3349028887305764047955011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4465371849741018730606681 3349028887305764047955011)
        ·
          refine ⟨5023543330958646071932517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3349028887305764047955011 5023543330958646071932517)
          ·
            refine ⟨941914374554746138487347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5023543330958646071932517 941914374554746138487347)
            ·
              refine ⟨1412871561832119207731021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941914374554746138487347 1412871561832119207731021)
              ·
                refine ⟨529826835687044702899133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1412871561832119207731021 529826835687044702899133)
                ·
                  refine ⟨198685063382641763587175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529826835687044702899133 198685063382641763587175)
                  ·
                    rfl

theorem cell21_870610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_870610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870610 prefixEnd_870610 := by exact prefixLift 870610
  have htrace : WordTrace (prefixWord ++ tailWord_870610) baseStart_870610 baseEnd_870610 := by
    simpa [prefixWord, tailWord_870610, baseEnd_870610] using wordTrace_append hprefix tailTrace_870610
  have hstable : (prefixWord ++ tailWord_870610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870610).length < 2 ^ (prefixWord ++ tailWord_870610).sum := by decide
  have hdescent : baseEnd_870610 < baseStart_870610 := by decide
  rcases family_descends (prefixWord ++ tailWord_870610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870621 : List Nat := [1, 4, 3, 2, 1, 1, 9]
def baseStart_870621 : Nat := 118140960795 + 870621 * 2 ^ 59
def prefixEnd_870621 : Nat := 4983230072969 + 3 ^ 40 * 870621 * 2
def baseEnd_870621 : Nat := 22076397081389798767091

theorem tailTrace_870621 : CollatzResearch.WordTrace tailWord_870621 prefixEnd_870621 22076397081389798767091 := by
  unfold tailWord_870621
  simp only [CollatzResearch.WordTrace]
  refine ⟨31754156578896282074075717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21169437719264188049383811 31754156578896282074075717)
  ·
    refine ⟨5953904358543052888889197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31754156578896282074075717 5953904358543052888889197)
    ·
      refine ⟨2232714134453644833333449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5953904358543052888889197 2232714134453644833333449)
      ·
        refine ⟨1674535600840233625000087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2232714134453644833333449 1674535600840233625000087)
        ·
          refine ⟨2511803401260350437500131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1674535600840233625000087 2511803401260350437500131)
          ·
            refine ⟨3767705101890525656250197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2511803401260350437500131 3767705101890525656250197)
            ·
              refine ⟨22076397081389798767091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3767705101890525656250197 22076397081389798767091)
              ·
                rfl

theorem cell21_870621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 9].length) (baseStart_870621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870621 prefixEnd_870621 := by exact prefixLift 870621
  have htrace : WordTrace (prefixWord ++ tailWord_870621) baseStart_870621 baseEnd_870621 := by
    simpa [prefixWord, tailWord_870621, baseEnd_870621] using wordTrace_append hprefix tailTrace_870621
  have hstable : (prefixWord ++ tailWord_870621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870621).length < 2 ^ (prefixWord ++ tailWord_870621).sum := by decide
  have hdescent : baseEnd_870621 < baseStart_870621 := by decide
  rcases family_descends (prefixWord ++ tailWord_870621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870627 : List Nat := [1, 1, 1, 8, 1, 1, 3, 2, 3]
def baseStart_870627 : Nat := 118140960795 + 870627 * 2 ^ 59
def prefixEnd_870627 : Nat := 4983230072969 + 3 ^ 40 * 870627 * 2
def baseEnd_870627 : Nat := 198688943014253511803807

theorem tailTrace_870627 : CollatzResearch.WordTrace tailWord_870627 prefixEnd_870627 198688943014253511803807 := by
  unfold tailWord_870627
  simp only [CollatzResearch.WordTrace]
  refine ⟨31754375416874545098794135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21169583611249696732529423 31754375416874545098794135)
  ·
    refine ⟨47631563125311817648191203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31754375416874545098794135 47631563125311817648191203)
    ·
      refine ⟨71447344687967726472286805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47631563125311817648191203 71447344687967726472286805)
      ·
        refine ⟨837273570562121794597111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 71447344687967726472286805 837273570562121794597111)
        ·
          refine ⟨1255910355843182691895667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837273570562121794597111 1255910355843182691895667)
          ·
            refine ⟨1883865533764774037843501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1255910355843182691895667 1883865533764774037843501)
            ·
              refine ⟨706449575161790264191313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1883865533764774037843501 706449575161790264191313)
              ·
                refine ⟨529837181371342698143485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 706449575161790264191313 529837181371342698143485)
                ·
                  refine ⟨198688943014253511803807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529837181371342698143485 198688943014253511803807)
                  ·
                    rfl

theorem cell21_870627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 3].length) (baseStart_870627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870627 prefixEnd_870627 := by exact prefixLift 870627
  have htrace : WordTrace (prefixWord ++ tailWord_870627) baseStart_870627 baseEnd_870627 := by
    simpa [prefixWord, tailWord_870627, baseEnd_870627] using wordTrace_append hprefix tailTrace_870627
  have hstable : (prefixWord ++ tailWord_870627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870627).length < 2 ^ (prefixWord ++ tailWord_870627).sum := by decide
  have hdescent : baseEnd_870627 < baseStart_870627 := by decide
  rcases family_descends (prefixWord ++ tailWord_870627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870649 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 8]
def baseStart_870649 : Nat := 118140960795 + 870649 * 2 ^ 59
def prefixEnd_870649 : Nat := 4983230072969 + 3 ^ 40 * 870649 * 2
def baseEnd_870649 : Nat := 198693963713986362437095

theorem tailTrace_870649 : CollatzResearch.WordTrace tailWord_870649 prefixEnd_870649 198693963713986362437095 := by
  unfold tailWord_870649
  simp only [CollatzResearch.WordTrace]
  refine ⟨31755177822794842856095001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21170118548529895237396667 31755177822794842856095001)
  ·
    refine ⟨23816383367096132142071251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31755177822794842856095001 23816383367096132142071251)
    ·
      refine ⟨35724575050644198213106877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23816383367096132142071251 35724575050644198213106877)
      ·
        refine ⟨13396715643991574329915079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35724575050644198213106877 13396715643991574329915079)
        ·
          refine ⟨20095073465987361494872619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13396715643991574329915079 20095073465987361494872619)
          ·
            refine ⟨30142610198981042242308929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20095073465987361494872619 30142610198981042242308929)
            ·
              refine ⟨22606957649235781681731697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30142610198981042242308929 22606957649235781681731697)
              ·
                refine ⟨16955218236926836261298773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22606957649235781681731697 16955218236926836261298773)
                ·
                  refine ⟨198693963713986362437095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16955218236926836261298773 198693963713986362437095)
                  ·
                    rfl

theorem cell21_870649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 8].length) (baseStart_870649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870649 prefixEnd_870649 := by exact prefixLift 870649
  have htrace : WordTrace (prefixWord ++ tailWord_870649) baseStart_870649 baseEnd_870649 := by
    simpa [prefixWord, tailWord_870649, baseEnd_870649] using wordTrace_append hprefix tailTrace_870649
  have hstable : (prefixWord ++ tailWord_870649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870649).length < 2 ^ (prefixWord ++ tailWord_870649).sum := by decide
  have hdescent : baseEnd_870649 < baseStart_870649 := by decide
  rcases family_descends (prefixWord ++ tailWord_870649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870728 : List Nat := [2, 1, 3, 1, 1, 2, 3, 5, 3]
def baseStart_870728 : Nat := 118140960795 + 870728 * 2 ^ 59
def prefixEnd_870728 : Nat := 4983230072969 + 3 ^ 40 * 870728 * 2
def baseEnd_870728 : Nat := 198711992590299780620267

theorem tailTrace_870728 : CollatzResearch.WordTrace tailWord_870728 prefixEnd_870728 198711992590299780620267 := by
  unfold tailWord_870728
  simp only [CollatzResearch.WordTrace]
  refine ⟨15879029594754319674110419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21172039459672426232147225 15879029594754319674110419)
  ·
    refine ⟨23818544392131479511165629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15879029594754319674110419 23818544392131479511165629)
    ·
      refine ⟨8931954147049304816687111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23818544392131479511165629 8931954147049304816687111)
      ·
        refine ⟨13397931220573957225030667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8931954147049304816687111 13397931220573957225030667)
        ·
          refine ⟨20096896830860935837546001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13397931220573957225030667 20096896830860935837546001)
          ·
            refine ⟨15072672623145701878159501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20096896830860935837546001 15072672623145701878159501)
            ·
              refine ⟨5652252233679638204309813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15072672623145701878159501 5652252233679638204309813)
              ·
                refine ⟨529898646907466081654045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5652252233679638204309813 529898646907466081654045)
                ·
                  refine ⟨198711992590299780620267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 529898646907466081654045 198711992590299780620267)
                  ·
                    rfl

theorem cell21_870728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 3].length) (baseStart_870728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870728 prefixEnd_870728 := by exact prefixLift 870728
  have htrace : WordTrace (prefixWord ++ tailWord_870728) baseStart_870728 baseEnd_870728 := by
    simpa [prefixWord, tailWord_870728, baseEnd_870728] using wordTrace_append hprefix tailTrace_870728
  have hstable : (prefixWord ++ tailWord_870728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870728).length < 2 ^ (prefixWord ++ tailWord_870728).sum := by decide
  have hdescent : baseEnd_870728 < baseStart_870728 := by decide
  rcases family_descends (prefixWord ++ tailWord_870728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870756 : List Nat := [2, 3, 1, 1, 3, 1, 2, 8]
def baseStart_870756 : Nat := 118140960795 + 870756 * 2 ^ 59
def prefixEnd_870756 : Nat := 4983230072969 + 3 ^ 40 * 870756 * 2
def baseEnd_870756 : Nat := 66239460857259318051181

theorem tailTrace_870756 : CollatzResearch.WordTrace tailWord_870756 prefixEnd_870756 66239460857259318051181 := by
  unfold tailWord_870756
  simp only [CollatzResearch.WordTrace]
  refine ⟨15879540216703600065120061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21172720288938133420160081 15879540216703600065120061)
  ·
    refine ⟨5954827581263850024420023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15879540216703600065120061 5954827581263850024420023)
    ·
      refine ⟨8932241371895775036630035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5954827581263850024420023 8932241371895775036630035)
      ·
        refine ⟨13398362057843662554945053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8932241371895775036630035 13398362057843662554945053)
        ·
          refine ⟨5024385771691373458104395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13398362057843662554945053 5024385771691373458104395)
          ·
            refine ⟨7536578657537060187156593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5024385771691373458104395 7536578657537060187156593)
            ·
              refine ⟨5652433993152795140367445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7536578657537060187156593 5652433993152795140367445)
              ·
                refine ⟨66239460857259318051181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5652433993152795140367445 66239460857259318051181)
                ·
                  rfl

theorem cell21_870756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_870756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870756 prefixEnd_870756 := by exact prefixLift 870756
  have htrace : WordTrace (prefixWord ++ tailWord_870756) baseStart_870756 baseEnd_870756 := by
    simpa [prefixWord, tailWord_870756, baseEnd_870756] using wordTrace_append hprefix tailTrace_870756
  have hstable : (prefixWord ++ tailWord_870756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870756).length < 2 ^ (prefixWord ++ tailWord_870756).sum := by decide
  have hdescent : baseEnd_870756 < baseStart_870756 := by decide
  rcases family_descends (prefixWord ++ tailWord_870756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870773 : List Nat := [1, 3, 4, 1, 2, 2, 1, 7]
def baseStart_870773 : Nat := 118140960795 + 870773 * 2 ^ 59
def prefixEnd_870773 : Nat := 4983230072969 + 3 ^ 40 * 870773 * 2
def baseEnd_870773 : Nat := 66240754067796567456725

theorem tailTrace_870773 : CollatzResearch.WordTrace tailWord_870773 prefixEnd_870773 66240754067796567456725 := by
  unfold tailWord_870773
  simp only [CollatzResearch.WordTrace]
  refine ⟨31759700474345612033608973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21173133649563741355739315 31759700474345612033608973)
  ·
    refine ⟨11909887677879604512603365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31759700474345612033608973 11909887677879604512603365)
    ·
      refine ⟨2233103939602425846113131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11909887677879604512603365 2233103939602425846113131)
      ·
        refine ⟨3349655909403638769169697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233103939602425846113131 3349655909403638769169697)
        ·
          refine ⟨2512241932052729076877273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3349655909403638769169697 2512241932052729076877273)
          ·
            refine ⟨1884181449039546807657955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2512241932052729076877273 1884181449039546807657955)
            ·
              refine ⟨2826272173559320211486933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884181449039546807657955 2826272173559320211486933)
              ·
                refine ⟨66240754067796567456725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2826272173559320211486933 66240754067796567456725)
                ·
                  rfl

theorem cell21_870773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 7].length) (baseStart_870773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870773 prefixEnd_870773 := by exact prefixLift 870773
  have htrace : WordTrace (prefixWord ++ tailWord_870773) baseStart_870773 baseEnd_870773 := by
    simpa [prefixWord, tailWord_870773, baseEnd_870773] using wordTrace_append hprefix tailTrace_870773
  have hstable : (prefixWord ++ tailWord_870773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870773).length < 2 ^ (prefixWord ++ tailWord_870773).sum := by decide
  have hdescent : baseEnd_870773 < baseStart_870773 := by decide
  rcases family_descends (prefixWord ++ tailWord_870773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870852 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_870852 : Nat := 118140960795 + 870852 * 2 ^ 59
def prefixEnd_870852 : Nat := 4983230072969 + 3 ^ 40 * 870852 * 2
def baseEnd_870852 : Nat := 198740291079703120553347

theorem tailTrace_870852 : CollatzResearch.WordTrace tailWord_870852 prefixEnd_870852 198740291079703120553347 := by
  unfold tailWord_870852
  simp only [CollatzResearch.WordTrace]
  refine ⟨15881290920529704262867405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21175054560706272350489873 15881290920529704262867405)
  ·
    refine ⟨5955484095198639098575277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15881290920529704262867405 5955484095198639098575277)
    ·
      refine ⟨2233306535699489661965729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5955484095198639098575277 2233306535699489661965729)
      ·
        refine ⟨1674979901774617246474297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2233306535699489661965729 1674979901774617246474297)
        ·
          refine ⟨1256234926330962934855723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1674979901774617246474297 1256234926330962934855723)
          ·
            refine ⟨1884352389496444402283585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256234926330962934855723 1884352389496444402283585)
            ·
              refine ⟨1413264292122333301712689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884352389496444402283585 1413264292122333301712689)
              ·
                refine ⟨1059948219091749976284517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1413264292122333301712689 1059948219091749976284517)
                ·
                  refine ⟨198740291079703120553347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1059948219091749976284517 198740291079703120553347)
                  ·
                    rfl

theorem cell21_870852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_870852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_870852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_870852 prefixEnd_870852 := by exact prefixLift 870852
  have htrace : WordTrace (prefixWord ++ tailWord_870852) baseStart_870852 baseEnd_870852 := by
    simpa [prefixWord, tailWord_870852, baseEnd_870852] using wordTrace_append hprefix tailTrace_870852
  have hstable : (prefixWord ++ tailWord_870852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870852).length < 2 ^ (prefixWord ++ tailWord_870852).sum := by decide
  have hdescent : baseEnd_870852 < baseStart_870852 := by decide
  rcases family_descends (prefixWord ++ tailWord_870852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871066 : List Nat := [3, 1, 1, 6, 1, 1, 2, 3, 3]
def baseStart_871066 : Nat := 118140960795 + 871066 * 2 ^ 59
def prefixEnd_871066 : Nat := 4983230072969 + 3 ^ 40 * 871066 * 2
def baseEnd_871066 : Nat := 198789128795286303986243

theorem tailTrace_871066 : CollatzResearch.WordTrace tailWord_871066 prefixEnd_871066 198789128795286303986243 := by
  unfold tailWord_871066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942596765571030768506263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21180258041522748716016701 7942596765571030768506263)
  ·
    refine ⟨11913895148356546152759395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7942596765571030768506263 11913895148356546152759395)
    ·
      refine ⟨17870842722534819229139093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11913895148356546152759395 17870842722534819229139093)
      ·
        refine ⟨837695752618819651365895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17870842722534819229139093 837695752618819651365895)
        ·
          refine ⟨1256543628928229477048843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837695752618819651365895 1256543628928229477048843)
          ·
            refine ⟨1884815443392344215573265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256543628928229477048843 1884815443392344215573265)
            ·
              refine ⟨1413611582544258161679949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884815443392344215573265 1413611582544258161679949)
              ·
                refine ⟨530104343454096810629981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1413611582544258161679949 530104343454096810629981)
                ·
                  refine ⟨198789128795286303986243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530104343454096810629981 198789128795286303986243)
                  ·
                    rfl

theorem cell21_871066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_871066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871066 prefixEnd_871066 := by exact prefixLift 871066
  have htrace : WordTrace (prefixWord ++ tailWord_871066) baseStart_871066 baseEnd_871066 := by
    simpa [prefixWord, tailWord_871066, baseEnd_871066] using wordTrace_append hprefix tailTrace_871066
  have hstable : (prefixWord ++ tailWord_871066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871066).length < 2 ^ (prefixWord ++ tailWord_871066).sum := by decide
  have hdescent : baseEnd_871066 < baseStart_871066 := by decide
  rcases family_descends (prefixWord ++ tailWord_871066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871091 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 5]
def baseStart_871091 : Nat := 118140960795 + 871091 * 2 ^ 59
def prefixEnd_871091 : Nat := 4983230072969 + 3 ^ 40 * 871091 * 2
def baseEnd_871091 : Nat := 198794834135891816069525

theorem tailTrace_871091 : CollatzResearch.WordTrace tailWord_871091 prefixEnd_871091 198794834135891816069525 := by
  unfold tailWord_871091
  simp only [CollatzResearch.WordTrace]
  refine ⟨31771298887193552343685127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21180865924795701562456751 31771298887193552343685127)
  ·
    refine ⟨47656948330790328515527691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31771298887193552343685127 47656948330790328515527691)
    ·
      refine ⟨71485422496185492773291537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47656948330790328515527691 71485422496185492773291537)
      ·
        refine ⟨53614066872139119579968653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71485422496185492773291537 53614066872139119579968653)
        ·
          refine ⟨20105275077052169842488245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53614066872139119579968653 20105275077052169842488245)
          ·
            refine ⟨1884869538473640922733273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20105275077052169842488245 1884869538473640922733273)
            ·
              refine ⟨1413652153855230692049955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1884869538473640922733273 1413652153855230692049955)
              ·
                refine ⟨2120478230782846038074933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413652153855230692049955 2120478230782846038074933)
                ·
                  refine ⟨198794834135891816069525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2120478230782846038074933 198794834135891816069525)
                  ·
                    rfl

theorem cell21_871091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 5].length) (baseStart_871091 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871091 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871091 prefixEnd_871091 := by exact prefixLift 871091
  have htrace : WordTrace (prefixWord ++ tailWord_871091) baseStart_871091 baseEnd_871091 := by
    simpa [prefixWord, tailWord_871091, baseEnd_871091] using wordTrace_append hprefix tailTrace_871091
  have hstable : (prefixWord ++ tailWord_871091).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871091).length < 2 ^ (prefixWord ++ tailWord_871091).sum := by decide
  have hdescent : baseEnd_871091 < baseStart_871091 := by decide
  rcases family_descends (prefixWord ++ tailWord_871091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871257 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 6]
def baseStart_871257 : Nat := 118140960795 + 871257 * 2 ^ 59
def prefixEnd_871257 : Nat := 4983230072969 + 3 ^ 40 * 871257 * 2
def baseEnd_871257 : Nat := 198832717597512416302519

theorem tailTrace_871257 : CollatzResearch.WordTrace tailWord_871257 prefixEnd_871257 198832717597512416302519 := by
  unfold tailWord_871257
  simp only [CollatzResearch.WordTrace]
  refine ⟨31777353404592162694228025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21184902269728108462818683 31777353404592162694228025)
  ·
    refine ⟨23833015053444122020671019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31777353404592162694228025 23833015053444122020671019)
    ·
      refine ⟨35749522580166183031006529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23833015053444122020671019 35749522580166183031006529)
      ·
        refine ⟨26812141935124637273254897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35749522580166183031006529 26812141935124637273254897)
        ·
          refine ⟨20109106451343477954941173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26812141935124637273254897 20109106451343477954941173)
          ·
            refine ⟨1885228729813451058275735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20109106451343477954941173 1885228729813451058275735)
            ·
              refine ⟨2827843094720176587413603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1885228729813451058275735 2827843094720176587413603)
              ·
                refine ⟨4241764642080264881120405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2827843094720176587413603 4241764642080264881120405)
                ·
                  refine ⟨198832717597512416302519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4241764642080264881120405 198832717597512416302519)
                  ·
                    rfl

theorem cell21_871257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_871257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871257 prefixEnd_871257 := by exact prefixLift 871257
  have htrace : WordTrace (prefixWord ++ tailWord_871257) baseStart_871257 baseEnd_871257 := by
    simpa [prefixWord, tailWord_871257, baseEnd_871257] using wordTrace_append hprefix tailTrace_871257
  have hstable : (prefixWord ++ tailWord_871257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871257).length < 2 ^ (prefixWord ++ tailWord_871257).sum := by decide
  have hdescent : baseEnd_871257 < baseStart_871257 := by decide
  rcases family_descends (prefixWord ++ tailWord_871257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871260 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_871260 : Nat := 118140960795 + 871260 * 2 ^ 59
def prefixEnd_871260 : Nat := 4983230072969 + 3 ^ 40 * 871260 * 2
def baseEnd_871260 : Nat := 198833402238385077752513

theorem tailTrace_871260 : CollatzResearch.WordTrace tailWord_871260 prefixEnd_871260 198833402238385077752513 := by
  unfold tailWord_871260
  simp only [CollatzResearch.WordTrace]
  refine ⟨15888731411790647103293617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21184975215720862804391489 15888731411790647103293617)
  ·
    refine ⟨11916548558842985327470213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15888731411790647103293617 11916548558842985327470213)
    ·
      refine ⟨2234352854783059748900665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11916548558842985327470213 2234352854783059748900665)
      ·
        refine ⟨1675764641087294811675499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2234352854783059748900665 1675764641087294811675499)
        ·
          refine ⟨2513646961630942217513249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1675764641087294811675499 2513646961630942217513249)
          ·
            refine ⟨1885235221223206663134937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2513646961630942217513249 1885235221223206663134937)
            ·
              refine ⟨1413926415917404997351203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885235221223206663134937 1413926415917404997351203)
              ·
                refine ⟨2120889623876107496026805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1413926415917404997351203 2120889623876107496026805)
                ·
                  refine ⟨198833402238385077752513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2120889623876107496026805 198833402238385077752513)
                  ·
                    rfl

theorem cell21_871260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_871260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871260 prefixEnd_871260 := by exact prefixLift 871260
  have htrace : WordTrace (prefixWord ++ tailWord_871260) baseStart_871260 baseEnd_871260 := by
    simpa [prefixWord, tailWord_871260, baseEnd_871260] using wordTrace_append hprefix tailTrace_871260
  have hstable : (prefixWord ++ tailWord_871260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871260).length < 2 ^ (prefixWord ++ tailWord_871260).sum := by decide
  have hdescent : baseEnd_871260 < baseStart_871260 := by decide
  rcases family_descends (prefixWord ++ tailWord_871260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871364 : List Nat := [2, 3, 3, 3, 10]
def baseStart_871364 : Nat := 118140960795 + 871364 * 2 ^ 59
def prefixEnd_871364 : Nat := 4983230072969 + 3 ^ 40 * 871364 * 2
def baseEnd_871364 : Nat := 2455026375991407506407

theorem tailTrace_871364 : CollatzResearch.WordTrace tailWord_871364 prefixEnd_871364 2455026375991407506407 := by
  unfold tailWord_871364
  simp only [CollatzResearch.WordTrace]
  refine ⟨15890628007602259984186573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21187504010136346645582097 15890628007602259984186573)
  ·
    refine ⟨5958985502850847494069965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15890628007602259984186573 5958985502850847494069965)
    ·
      refine ⟨2234619563569067810276237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5958985502850847494069965 2234619563569067810276237)
      ·
        refine ⟨837982336338400428853589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2234619563569067810276237 837982336338400428853589)
        ·
          refine ⟨2455026375991407506407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 837982336338400428853589 2455026375991407506407)
          ·
            rfl

theorem cell21_871364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 10].length) (baseStart_871364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871364 prefixEnd_871364 := by exact prefixLift 871364
  have htrace : WordTrace (prefixWord ++ tailWord_871364) baseStart_871364 baseEnd_871364 := by
    simpa [prefixWord, tailWord_871364, baseEnd_871364] using wordTrace_append hprefix tailTrace_871364
  have hstable : (prefixWord ++ tailWord_871364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871364).length < 2 ^ (prefixWord ++ tailWord_871364).sum := by decide
  have hdescent : baseEnd_871364 < baseStart_871364 := by decide
  rcases family_descends (prefixWord ++ tailWord_871364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871381 : List Nat := [1, 3, 2, 3, 3, 2, 1, 6]
def baseStart_871381 : Nat := 118140960795 + 871381 * 2 ^ 59
def prefixEnd_871381 : Nat := 4983230072969 + 3 ^ 40 * 871381 * 2
def baseEnd_871381 : Nat := 66287005362305252078533

theorem tailTrace_871381 : CollatzResearch.WordTrace tailWord_871381 prefixEnd_871381 66287005362305252078533 := by
  unfold tailWord_871381
  simp only [CollatzResearch.WordTrace]
  refine ⟨31781876056142931871741997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21187917370761954581161331 31781876056142931871741997)
  ·
    refine ⟨11918203521053599451903249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31781876056142931871741997 11918203521053599451903249)
    ·
      refine ⟨8938652640790199588927437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11918203521053599451903249 8938652640790199588927437)
      ·
        refine ⟨3351994740296324845847789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8938652640790199588927437 3351994740296324845847789)
        ·
          refine ⟨1256998027611121817192921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3351994740296324845847789 1256998027611121817192921)
          ·
            refine ⟨942748520708341362894691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1256998027611121817192921 942748520708341362894691)
            ·
              refine ⟨1414122781062512044342037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 942748520708341362894691 1414122781062512044342037)
              ·
                refine ⟨66287005362305252078533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1414122781062512044342037 66287005362305252078533)
                ·
                  rfl

theorem cell21_871381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 6].length) (baseStart_871381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871381 prefixEnd_871381 := by exact prefixLift 871381
  have htrace : WordTrace (prefixWord ++ tailWord_871381) baseStart_871381 baseEnd_871381 := by
    simpa [prefixWord, tailWord_871381, baseEnd_871381] using wordTrace_append hprefix tailTrace_871381
  have hstable : (prefixWord ++ tailWord_871381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871381).length < 2 ^ (prefixWord ++ tailWord_871381).sum := by decide
  have hdescent : baseEnd_871381 < baseStart_871381 := by decide
  rcases family_descends (prefixWord ++ tailWord_871381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871392 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_871392 : Nat := 118140960795 + 871392 * 2 ^ 59
def prefixEnd_871392 : Nat := 4983230072969 + 3 ^ 40 * 871392 * 2
def baseEnd_871392 : Nat := 198863526436782181552243

theorem tailTrace_871392 : CollatzResearch.WordTrace tailWord_871392 prefixEnd_871392 198863526436782181552243 := by
  unfold tailWord_871392
  simp only [CollatzResearch.WordTrace]
  refine ⟨15891138629551540375196215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21188184839402053833594953 15891138629551540375196215)
  ·
    refine ⟨23836707944327310562794323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15891138629551540375196215 23836707944327310562794323)
    ·
      refine ⟨35755061916490965844191485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23836707944327310562794323 35755061916490965844191485)
      ·
        refine ⟨13408148218684112191571807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35755061916490965844191485 13408148218684112191571807)
        ·
          refine ⟨20112222328026168287357711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13408148218684112191571807 20112222328026168287357711)
          ·
            refine ⟨30168333492039252431036567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20112222328026168287357711 30168333492039252431036567)
            ·
              refine ⟨45252500238058878646554851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30168333492039252431036567 45252500238058878646554851)
              ·
                refine ⟨67878750357088317969832277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45252500238058878646554851 67878750357088317969832277)
                ·
                  refine ⟨198863526436782181552243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 67878750357088317969832277 198863526436782181552243)
                  ·
                    rfl

theorem cell21_871392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_871392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871392 prefixEnd_871392 := by exact prefixLift 871392
  have htrace : WordTrace (prefixWord ++ tailWord_871392) baseStart_871392 baseEnd_871392 := by
    simpa [prefixWord, tailWord_871392, baseEnd_871392] using wordTrace_append hprefix tailTrace_871392
  have hstable : (prefixWord ++ tailWord_871392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871392).length < 2 ^ (prefixWord ++ tailWord_871392).sum := by decide
  have hdescent : baseEnd_871392 < baseStart_871392 := by decide
  rcases family_descends (prefixWord ++ tailWord_871392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871457 : List Nat := [1, 2, 3, 2, 3, 3, 2, 5]
def baseStart_871457 : Nat := 118140960795 + 871457 * 2 ^ 59
def prefixEnd_871457 : Nat := 4983230072969 + 3 ^ 40 * 871457 * 2
def baseEnd_871457 : Nat := 66292786774118837656259

theorem tailTrace_871457 : CollatzResearch.WordTrace tailWord_871457 prefixEnd_871457 66292786774118837656259 := by
  unfold tailWord_871457
  simp only [CollatzResearch.WordTrace]
  refine ⟨31784648003867596851508625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21189765335911731234339083 31784648003867596851508625)
  ·
    refine ⟨23838486002900697638631469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31784648003867596851508625 23838486002900697638631469)
    ·
      refine ⟨8939432251087761614486801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23838486002900697638631469 8939432251087761614486801)
      ·
        refine ⟨6704574188315821210865101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8939432251087761614486801 6704574188315821210865101)
        ·
          refine ⟨2514215320618432954074413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6704574188315821210865101 2514215320618432954074413)
          ·
            refine ⟨942830745231912357777905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2514215320618432954074413 942830745231912357777905)
            ·
              refine ⟨707123058923934268333429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942830745231912357777905 707123058923934268333429)
              ·
                refine ⟨66292786774118837656259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 707123058923934268333429 66292786774118837656259)
                ·
                  rfl

theorem cell21_871457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 5].length) (baseStart_871457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871457 prefixEnd_871457 := by exact prefixLift 871457
  have htrace : WordTrace (prefixWord ++ tailWord_871457) baseStart_871457 baseEnd_871457 := by
    simpa [prefixWord, tailWord_871457, baseEnd_871457] using wordTrace_append hprefix tailTrace_871457
  have hstable : (prefixWord ++ tailWord_871457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871457).length < 2 ^ (prefixWord ++ tailWord_871457).sum := by decide
  have hdescent : baseEnd_871457 < baseStart_871457 := by decide
  rcases family_descends (prefixWord ++ tailWord_871457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871468 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_871468 : Nat := 118140960795 + 871468 * 2 ^ 59
def prefixEnd_871468 : Nat := 4983230072969 + 3 ^ 40 * 871468 * 2
def baseEnd_871468 : Nat := 198880870672222938285421

theorem tailTrace_871468 : CollatzResearch.WordTrace tailWord_871468 prefixEnd_871468 198880870672222938285421 := by
  unfold tailWord_871468
  simp only [CollatzResearch.WordTrace]
  refine ⟨15892524603413872865079529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21190032804551830486772705 15892524603413872865079529)
  ·
    refine ⟨11919393452560404648809647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15892524603413872865079529 11919393452560404648809647)
    ·
      refine ⟨17879090178840606973214471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11919393452560404648809647 17879090178840606973214471)
      ·
        refine ⟨26818635268260910459821707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17879090178840606973214471 26818635268260910459821707)
        ·
          refine ⟨40227952902391365689732561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26818635268260910459821707 40227952902391365689732561)
          ·
            refine ⟨30170964676793524267299421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40227952902391365689732561 30170964676793524267299421)
            ·
              refine ⟨11314111753797571600237283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30170964676793524267299421 11314111753797571600237283)
              ·
                refine ⟨16971167630696357400355925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11314111753797571600237283 16971167630696357400355925)
                ·
                  refine ⟨198880870672222938285421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16971167630696357400355925 198880870672222938285421)
                  ·
                    rfl

theorem cell21_871468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_871468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871468 prefixEnd_871468 := by exact prefixLift 871468
  have htrace : WordTrace (prefixWord ++ tailWord_871468) baseStart_871468 baseEnd_871468 := by
    simpa [prefixWord, tailWord_871468, baseEnd_871468] using wordTrace_append hprefix tailTrace_871468
  have hstable : (prefixWord ++ tailWord_871468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871468).length < 2 ^ (prefixWord ++ tailWord_871468).sum := by decide
  have hdescent : baseEnd_871468 < baseStart_871468 := by decide
  rcases family_descends (prefixWord ++ tailWord_871468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871485 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 6]
def baseStart_871485 : Nat := 118140960795 + 871485 * 2 ^ 59
def prefixEnd_871485 : Nat := 4983230072969 + 3 ^ 40 * 871485 * 2
def baseEnd_871485 : Nat := 198884750303834686502053

theorem tailTrace_871485 : CollatzResearch.WordTrace tailWord_871485 prefixEnd_871485 198884750303834686502053 := by
  unfold tailWord_871485
  simp only [CollatzResearch.WordTrace]
  refine ⟨31785669247766157633527909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21190446165177438422351939 31785669247766157633527909)
  ·
    refine ⟨5959812983956154556286483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31785669247766157633527909 5959812983956154556286483)
    ·
      refine ⟨8939719475934231834429725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5959812983956154556286483 8939719475934231834429725)
      ·
        refine ⟨3352394803475336937911147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8939719475934231834429725 3352394803475336937911147)
        ·
          refine ⟨5028592205213005406866721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352394803475336937911147 5028592205213005406866721)
          ·
            refine ⟨3771444153909754055150041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5028592205213005406866721 3771444153909754055150041)
            ·
              refine ⟨2828583115432315541362531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3771444153909754055150041 2828583115432315541362531)
              ·
                refine ⟨4242874673148473312043797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2828583115432315541362531 4242874673148473312043797)
                ·
                  refine ⟨198884750303834686502053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4242874673148473312043797 198884750303834686502053)
                  ·
                    rfl

theorem cell21_871485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_871485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871485 prefixEnd_871485 := by exact prefixLift 871485
  have htrace : WordTrace (prefixWord ++ tailWord_871485) baseStart_871485 baseEnd_871485 := by
    simpa [prefixWord, tailWord_871485, baseEnd_871485] using wordTrace_append hprefix tailTrace_871485
  have hstable : (prefixWord ++ tailWord_871485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871485).length < 2 ^ (prefixWord ++ tailWord_871485).sum := by decide
  have hdescent : baseEnd_871485 < baseStart_871485 := by decide
  rcases family_descends (prefixWord ++ tailWord_871485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871488 : List Nat := [2, 1, 1, 2, 2, 3, 5, 2, 3]
def baseStart_871488 : Nat := 118140960795 + 871488 * 2 ^ 59
def prefixEnd_871488 : Nat := 4983230072969 + 3 ^ 40 * 871488 * 2
def baseEnd_871488 : Nat := 198885434944707347952047

theorem tailTrace_871488 : CollatzResearch.WordTrace tailWord_871488 prefixEnd_871488 198885434944707347952047 := by
  unfold tailWord_871488
  simp only [CollatzResearch.WordTrace]
  refine ⟨15892889333377644572943559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21190519111170192763924745 15892889333377644572943559)
  ·
    refine ⟨23839334000066466859415339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15892889333377644572943559 23839334000066466859415339)
    ·
      refine ⟨35759001000099700289123009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23839334000066466859415339 35759001000099700289123009)
      ·
        refine ⟨26819250750074775216842257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35759001000099700289123009 26819250750074775216842257)
        ·
          refine ⟨20114438062556081412631693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26819250750074775216842257 20114438062556081412631693)
          ·
            refine ⟨7542914273458530529736885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20114438062556081412631693 7542914273458530529736885)
            ·
              refine ⟨707148213136737237162833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7542914273458530529736885 707148213136737237162833)
              ·
                refine ⟨530361159852552927872125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707148213136737237162833 530361159852552927872125)
                ·
                  refine ⟨198885434944707347952047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530361159852552927872125 198885434944707347952047)
                  ·
                    rfl

theorem cell21_871488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 3].length) (baseStart_871488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871488 prefixEnd_871488 := by exact prefixLift 871488
  have htrace : WordTrace (prefixWord ++ tailWord_871488) baseStart_871488 baseEnd_871488 := by
    simpa [prefixWord, tailWord_871488, baseEnd_871488] using wordTrace_append hprefix tailTrace_871488
  have hstable : (prefixWord ++ tailWord_871488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871488).length < 2 ^ (prefixWord ++ tailWord_871488).sum := by decide
  have hdescent : baseEnd_871488 < baseStart_871488 := by decide
  rcases family_descends (prefixWord ++ tailWord_871488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871544 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 6]
def baseStart_871544 : Nat := 118140960795 + 871544 * 2 ^ 59
def prefixEnd_871544 : Nat := 4983230072969 + 3 ^ 40 * 871544 * 2
def baseEnd_871544 : Nat := 198898214907663695018599

theorem tailTrace_871544 : CollatzResearch.WordTrace tailWord_871544 prefixEnd_871544 198898214907663695018599 := by
  unfold tailWord_871544
  simp only [CollatzResearch.WordTrace]
  refine ⟨15893910577276205354962843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21191880769701607139950457 15893910577276205354962843)
  ·
    refine ⟨23840865865914308032444265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15893910577276205354962843 23840865865914308032444265)
    ·
      refine ⟨17880649399435731024333199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23840865865914308032444265 17880649399435731024333199)
      ·
        refine ⟨26820974099153596536499799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17880649399435731024333199 26820974099153596536499799)
        ·
          refine ⟨40231461148730394804749699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26820974099153596536499799 40231461148730394804749699)
          ·
            refine ⟨60347191723095592207124549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40231461148730394804749699 60347191723095592207124549)
            ·
              refine ⟨11315098448080423538835853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60347191723095592207124549 11315098448080423538835853)
              ·
                refine ⟨4243161918030158827063445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11315098448080423538835853 4243161918030158827063445)
                ·
                  refine ⟨198898214907663695018599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4243161918030158827063445 198898214907663695018599)
                  ·
                    rfl

theorem cell21_871544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_871544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871544 prefixEnd_871544 := by exact prefixLift 871544
  have htrace : WordTrace (prefixWord ++ tailWord_871544) baseStart_871544 baseEnd_871544 := by
    simpa [prefixWord, tailWord_871544, baseEnd_871544] using wordTrace_append hprefix tailTrace_871544
  have hstable : (prefixWord ++ tailWord_871544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871544).length < 2 ^ (prefixWord ++ tailWord_871544).sum := by decide
  have hdescent : baseEnd_871544 < baseStart_871544 := by decide
  rcases family_descends (prefixWord ++ tailWord_871544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871561 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 4]
def baseStart_871561 : Nat := 118140960795 + 871561 * 2 ^ 59
def prefixEnd_871561 : Nat := 4983230072969 + 3 ^ 40 * 871561 * 2
def baseEnd_871561 : Nat := 198902094539275443235231

theorem tailTrace_871561 : CollatzResearch.WordTrace tailWord_871561 prefixEnd_871561 198902094539275443235231 := by
  unfold tailWord_871561
  simp only [CollatzResearch.WordTrace]
  refine ⟨31788441195490822613294537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21192294130327215075529691 31788441195490822613294537)
  ·
    refine ⟨23841330896618116959970903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31788441195490822613294537 23841330896618116959970903)
    ·
      refine ⟨35761996344927175439956355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23841330896618116959970903 35761996344927175439956355)
      ·
        refine ⟨53642994517390763159934533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35761996344927175439956355 53642994517390763159934533)
        ·
          refine ⟨10058061472010768092487725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53642994517390763159934533 10058061472010768092487725)
          ·
            refine ⟨3771773052004038034682897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10058061472010768092487725 3771773052004038034682897)
            ·
              refine ⟨2828829789003028526012173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3771773052004038034682897 2828829789003028526012173)
              ·
                refine ⟨1060811170876135697254565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2828829789003028526012173 1060811170876135697254565)
                ·
                  refine ⟨198902094539275443235231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1060811170876135697254565 198902094539275443235231)
                  ·
                    rfl

theorem cell21_871561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 4].length) (baseStart_871561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871561 prefixEnd_871561 := by exact prefixLift 871561
  have htrace : WordTrace (prefixWord ++ tailWord_871561) baseStart_871561 baseEnd_871561 := by
    simpa [prefixWord, tailWord_871561, baseEnd_871561] using wordTrace_append hprefix tailTrace_871561
  have hstable : (prefixWord ++ tailWord_871561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871561).length < 2 ^ (prefixWord ++ tailWord_871561).sum := by decide
  have hdescent : baseEnd_871561 < baseStart_871561 := by decide
  rcases family_descends (prefixWord ++ tailWord_871561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871637 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 6]
def baseStart_871637 : Nat := 118140960795 + 871637 * 2 ^ 59
def prefixEnd_871637 : Nat := 4983230072969 + 3 ^ 40 * 871637 * 2
def baseEnd_871637 : Nat := 198919438774716199968409

theorem tailTrace_871637 : CollatzResearch.WordTrace tailWord_871637 prefixEnd_871637 198919438774716199968409 := by
  unfold tailWord_871637
  simp only [CollatzResearch.WordTrace]
  refine ⟨31791213143215487593061165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21194142095476991728707443 31791213143215487593061165)
  ·
    refine ⟨11921704928705807847397937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31791213143215487593061165 11921704928705807847397937)
    ·
      refine ⟨8941278696529355885548453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11921704928705807847397937 8941278696529355885548453)
      ·
        refine ⟨1676489755599254228540335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8941278696529355885548453 1676489755599254228540335)
        ·
          refine ⟨2514734633398881342810503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676489755599254228540335 2514734633398881342810503)
          ·
            refine ⟨3772101950098322014215755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2514734633398881342810503 3772101950098322014215755)
            ·
              refine ⟨5658152925147483021323633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3772101950098322014215755 5658152925147483021323633)
              ·
                refine ⟨4243614693860612265992725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5658152925147483021323633 4243614693860612265992725)
                ·
                  refine ⟨198919438774716199968409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4243614693860612265992725 198919438774716199968409)
                  ·
                    rfl

theorem cell21_871637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_871637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871637 prefixEnd_871637 := by exact prefixLift 871637
  have htrace : WordTrace (prefixWord ++ tailWord_871637) baseStart_871637 baseEnd_871637 := by
    simpa [prefixWord, tailWord_871637, baseEnd_871637] using wordTrace_append hprefix tailTrace_871637
  have hstable : (prefixWord ++ tailWord_871637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871637).length < 2 ^ (prefixWord ++ tailWord_871637).sum := by decide
  have hdescent : baseEnd_871637 < baseStart_871637 := by decide
  rcases family_descends (prefixWord ++ tailWord_871637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871809 : List Nat := [1, 2, 4, 3, 2, 2, 1, 3, 3]
def baseStart_871809 : Nat := 118140960795 + 871809 * 2 ^ 59
def prefixEnd_871809 : Nat := 4983230072969 + 3 ^ 40 * 871809 * 2
def baseEnd_871809 : Nat := 198958691518082123101391

theorem tailTrace_871809 : CollatzResearch.WordTrace tailWord_871809 prefixEnd_871809 198958691518082123101391 := by
  unfold tailWord_871809
  simp only [CollatzResearch.WordTrace]
  refine ⟨31797486498592360968322481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21198324332394907312214987 31797486498592360968322481)
  ·
    refine ⟨23848114873944270726241861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31797486498592360968322481 23848114873944270726241861)
    ·
      refine ⟨4471521538864550761170349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23848114873944270726241861 4471521538864550761170349)
      ·
        refine ⟨1676820577074206535438881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4471521538864550761170349 1676820577074206535438881)
        ·
          refine ⟨1257615432805654901579161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1676820577074206535438881 1257615432805654901579161)
          ·
            refine ⟨943211574604241176184371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1257615432805654901579161 943211574604241176184371)
            ·
              refine ⟨1414817361906361764276557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943211574604241176184371 1414817361906361764276557)
              ·
                refine ⟨530556510714885661603709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1414817361906361764276557 530556510714885661603709)
                ·
                  refine ⟨198958691518082123101391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530556510714885661603709 198958691518082123101391)
                  ·
                    rfl

theorem cell21_871809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 3].length) (baseStart_871809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871809 prefixEnd_871809 := by exact prefixLift 871809
  have htrace : WordTrace (prefixWord ++ tailWord_871809) baseStart_871809 baseEnd_871809 := by
    simpa [prefixWord, tailWord_871809, baseEnd_871809] using wordTrace_append hprefix tailTrace_871809
  have hstable : (prefixWord ++ tailWord_871809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871809).length < 2 ^ (prefixWord ++ tailWord_871809).sum := by decide
  have hdescent : baseEnd_871809 < baseStart_871809 := by decide
  rcases family_descends (prefixWord ++ tailWord_871809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_871826 : List Nat := [3, 2, 3, 3, 1, 1, 3, 2, 3]
def baseStart_871826 : Nat := 118140960795 + 871826 * 2 ^ 59
def prefixEnd_871826 : Nat := 4983230072969 + 3 ^ 40 * 871826 * 2
def baseEnd_871826 : Nat := 198962571149693871318023

theorem tailTrace_871826 : CollatzResearch.WordTrace tailWord_871826 prefixEnd_871826 198962571149693871318023 := by
  unfold tailWord_871826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7949526634882693217922833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21198737693020515247794221 7949526634882693217922833)
  ·
    refine ⟨5962144976162019913442125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7949526634882693217922833 5962144976162019913442125)
    ·
      refine ⟨2235804366060757467540797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5962144976162019913442125 2235804366060757467540797)
      ·
        refine ⟨838426637272784050327799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2235804366060757467540797 838426637272784050327799)
        ·
          refine ⟨1257639955909176075491699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838426637272784050327799 1257639955909176075491699)
          ·
            refine ⟨1886459933863764113237549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1257639955909176075491699 1886459933863764113237549)
            ·
              refine ⟨707422475198911542464081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1886459933863764113237549 707422475198911542464081)
              ·
                refine ⟨530566856399183656848061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707422475198911542464081 530566856399183656848061)
                ·
                  refine ⟨198962571149693871318023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530566856399183656848061 198962571149693871318023)
                  ·
                    rfl

theorem cell21_871826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_871826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_871826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_871826 prefixEnd_871826 := by exact prefixLift 871826
  have htrace : WordTrace (prefixWord ++ tailWord_871826) baseStart_871826 baseEnd_871826 := by
    simpa [prefixWord, tailWord_871826, baseEnd_871826] using wordTrace_append hprefix tailTrace_871826
  have hstable : (prefixWord ++ tailWord_871826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_871826).length < 2 ^ (prefixWord ++ tailWord_871826).sum := by decide
  have hdescent : baseEnd_871826 < baseStart_871826 := by decide
  rcases family_descends (prefixWord ++ tailWord_871826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872000 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 4]
def baseStart_872000 : Nat := 118140960795 + 872000 * 2 ^ 59
def prefixEnd_872000 : Nat := 4983230072969 + 3 ^ 40 * 872000 * 2
def baseEnd_872000 : Nat := 199002280320308235417667

theorem tailTrace_872000 : CollatzResearch.WordTrace tailWord_872000 prefixEnd_872000 199002280320308235417667 := by
  unfold tailWord_872000
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902226420450200294262727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21202968560600267059016969 15902226420450200294262727)
  ·
    refine ⟨23853339630675300441394091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15902226420450200294262727 23853339630675300441394091)
    ·
      refine ⟨35780009446012950662091137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23853339630675300441394091 35780009446012950662091137)
      ·
        refine ⟨26835007084509712996568353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35780009446012950662091137 26835007084509712996568353)
        ·
          refine ⟨20126255313382284747426265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26835007084509712996568353 20126255313382284747426265)
          ·
            refine ⟨15094691485036713560569699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20126255313382284747426265 15094691485036713560569699)
            ·
              refine ⟨22642037227555070340854549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15094691485036713560569699 22642037227555070340854549)
              ·
                refine ⟨1061345495041643922227557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22642037227555070340854549 1061345495041643922227557)
                ·
                  refine ⟨199002280320308235417667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1061345495041643922227557 199002280320308235417667)
                  ·
                    rfl

theorem cell21_872000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_872000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872000 prefixEnd_872000 := by exact prefixLift 872000
  have htrace : WordTrace (prefixWord ++ tailWord_872000) baseStart_872000 baseEnd_872000 := by
    simpa [prefixWord, tailWord_872000, baseEnd_872000] using wordTrace_append hprefix tailTrace_872000
  have hstable : (prefixWord ++ tailWord_872000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872000).length < 2 ^ (prefixWord ++ tailWord_872000).sum := by decide
  have hdescent : baseEnd_872000 < baseStart_872000 := by decide
  rcases family_descends (prefixWord ++ tailWord_872000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872076 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_872076 : Nat := 118140960795 + 872076 * 2 ^ 59
def prefixEnd_872076 : Nat := 4983230072969 + 3 ^ 40 * 872076 * 2
def baseEnd_872076 : Nat := 199019624555748992150845

theorem tailTrace_872076 : CollatzResearch.WordTrace tailWord_872076 prefixEnd_872076 199019624555748992150845 := by
  unfold tailWord_872076
  simp only [CollatzResearch.WordTrace]
  refine ⟨15903612394312532784146041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21204816525750043712194721 15903612394312532784146041)
  ·
    refine ⟨11927709295734399588109531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15903612394312532784146041 11927709295734399588109531)
    ·
      refine ⟨17891563943601599382164297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11927709295734399588109531 17891563943601599382164297)
      ·
        refine ⟨13418672957701199536623223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17891563943601599382164297 13418672957701199536623223)
        ·
          refine ⟨20128009436551799304934835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13418672957701199536623223 20128009436551799304934835)
          ·
            refine ⟨30192014154827698957402253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20128009436551799304934835 30192014154827698957402253)
            ·
              refine ⟨11322005308060387109025845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30192014154827698957402253 11322005308060387109025845)
              ·
                refine ⟨1061437997630661291471173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11322005308060387109025845 1061437997630661291471173)
                ·
                  refine ⟨199019624555748992150845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1061437997630661291471173 199019624555748992150845)
                  ·
                    rfl

theorem cell21_872076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_872076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872076 prefixEnd_872076 := by exact prefixLift 872076
  have htrace : WordTrace (prefixWord ++ tailWord_872076) baseStart_872076 baseEnd_872076 := by
    simpa [prefixWord, tailWord_872076, baseEnd_872076] using wordTrace_append hprefix tailTrace_872076
  have hstable : (prefixWord ++ tailWord_872076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872076).length < 2 ^ (prefixWord ++ tailWord_872076).sum := by decide
  have hdescent : baseEnd_872076 < baseStart_872076 := by decide
  rcases family_descends (prefixWord ++ tailWord_872076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872110 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_872110 : Nat := 118140960795 + 872110 * 2 ^ 59
def prefixEnd_872110 : Nat := 4983230072969 + 3 ^ 40 * 872110 * 2
def baseEnd_872110 : Nat := 199027383818972488584109

theorem tailTrace_872110 : CollatzResearch.WordTrace tailWord_872110 prefixEnd_872110 199027383818972488584109 := by
  unfold tailWord_872110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3976058108812736171878723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21205643247001259583353189 3976058108812736171878723)
  ·
    refine ⟨5964087163219104257818085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3976058108812736171878723 5964087163219104257818085)
    ·
      refine ⟨1118266343103582048340891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5964087163219104257818085 1118266343103582048340891)
      ·
        refine ⟨1677399514655373072511337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118266343103582048340891 1677399514655373072511337)
        ·
          refine ⟨1258049635991529804383503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1677399514655373072511337 1258049635991529804383503)
          ·
            refine ⟨1887074453987294706575255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258049635991529804383503 1887074453987294706575255)
            ·
              refine ⟨2830611680980942059862883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887074453987294706575255 2830611680980942059862883)
              ·
                refine ⟨4245917521471413089794325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2830611680980942059862883 4245917521471413089794325)
                ·
                  refine ⟨199027383818972488584109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4245917521471413089794325 199027383818972488584109)
                  ·
                    rfl

theorem cell21_872110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_872110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872110 prefixEnd_872110 := by exact prefixLift 872110
  have htrace : WordTrace (prefixWord ++ tailWord_872110) baseStart_872110 baseEnd_872110 := by
    simpa [prefixWord, tailWord_872110, baseEnd_872110] using wordTrace_append hprefix tailTrace_872110
  have hstable : (prefixWord ++ tailWord_872110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872110).length < 2 ^ (prefixWord ++ tailWord_872110).sum := by decide
  have hdescent : baseEnd_872110 < baseStart_872110 := by decide
  rcases family_descends (prefixWord ++ tailWord_872110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872121 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 5]
def baseStart_872121 : Nat := 118140960795 + 872121 * 2 ^ 59
def prefixEnd_872121 : Nat := 4983230072969 + 3 ^ 40 * 872121 * 2
def baseEnd_872121 : Nat := 199029894168838913900753

theorem tailTrace_872121 : CollatzResearch.WordTrace tailWord_872121 prefixEnd_872121 199029894168838913900753 := by
  unfold tailWord_872121
  simp only [CollatzResearch.WordTrace]
  refine ⟨31808866073462038253680217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21205910715641358835786811 31808866073462038253680217)
  ·
    refine ⟨23856649555096528690260163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31808866073462038253680217 23856649555096528690260163)
    ·
      refine ⟨35784974332644793035390245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23856649555096528690260163 35784974332644793035390245)
      ·
        refine ⟨6709682687370898694135671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35784974332644793035390245 6709682687370898694135671)
        ·
          refine ⟨10064524031056348041203507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6709682687370898694135671 10064524031056348041203507)
          ·
            refine ⟨15096786046584522061805261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10064524031056348041203507 15096786046584522061805261)
            ·
              refine ⟨5661294767469195773176973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15096786046584522061805261 5661294767469195773176973)
              ·
                refine ⟨2122985537800948414941365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5661294767469195773176973 2122985537800948414941365)
                ·
                  refine ⟨199029894168838913900753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2122985537800948414941365 199029894168838913900753)
                  ·
                    rfl

theorem cell21_872121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_872121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872121 prefixEnd_872121 := by exact prefixLift 872121
  have htrace : WordTrace (prefixWord ++ tailWord_872121) baseStart_872121 baseEnd_872121 := by
    simpa [prefixWord, tailWord_872121, baseEnd_872121] using wordTrace_append hprefix tailTrace_872121
  have hstable : (prefixWord ++ tailWord_872121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872121).length < 2 ^ (prefixWord ++ tailWord_872121).sum := by decide
  have hdescent : baseEnd_872121 < baseStart_872121 := by decide
  rcases family_descends (prefixWord ++ tailWord_872121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872141 : List Nat := [1, 6, 2, 1, 1, 1, 4, 5]
def baseStart_872141 : Nat := 118140960795 + 872141 * 2 ^ 59
def prefixEnd_872141 : Nat := 4983230072969 + 3 ^ 40 * 872141 * 2
def baseEnd_872141 : Nat := 66344819480441107855793

theorem tailTrace_872141 : CollatzResearch.WordTrace tailWord_872141 prefixEnd_872141 66344819480441107855793 := by
  unfold tailWord_872141
  simp only [CollatzResearch.WordTrace]
  refine ⟨31809595533389581669408277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21206397022259721112938851 31809595533389581669408277)
  ·
    refine ⟨1491074790627636640753513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31809595533389581669408277 1491074790627636640753513)
    ·
      refine ⟨1118306092970727480565135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1491074790627636640753513 1118306092970727480565135)
      ·
        refine ⟨1677459139456091220847703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118306092970727480565135 1677459139456091220847703)
        ·
          refine ⟨2516188709184136831271555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677459139456091220847703 2516188709184136831271555)
          ·
            refine ⟨3774283063776205246907333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2516188709184136831271555 3774283063776205246907333)
            ·
              refine ⟨707678074458038483795125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3774283063776205246907333 707678074458038483795125)
              ·
                refine ⟨66344819480441107855793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 707678074458038483795125 66344819480441107855793)
                ·
                  rfl

theorem cell21_872141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 5].length) (baseStart_872141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872141 prefixEnd_872141 := by exact prefixLift 872141
  have htrace : WordTrace (prefixWord ++ tailWord_872141) baseStart_872141 baseEnd_872141 := by
    simpa [prefixWord, tailWord_872141, baseEnd_872141] using wordTrace_append hprefix tailTrace_872141
  have hstable : (prefixWord ++ tailWord_872141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872141).length < 2 ^ (prefixWord ++ tailWord_872141).sum := by decide
  have hdescent : baseEnd_872141 < baseStart_872141 := by decide
  rcases family_descends (prefixWord ++ tailWord_872141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_872211 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 6]
def baseStart_872211 : Nat := 118140960795 + 872211 * 2 ^ 59
def prefixEnd_872211 : Nat := 4983230072969 + 3 ^ 40 * 872211 * 2
def baseEnd_872211 : Nat := 199050433395018757400569

theorem tailTrace_872211 : CollatzResearch.WordTrace tailWord_872211 prefixEnd_872211 199050433395018757400569 := by
  unfold tailWord_872211
  simp only [CollatzResearch.WordTrace]
  refine ⟨31812148643135983624456487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21208099095423989082970991 31812148643135983624456487)
  ·
    refine ⟨47718222964703975436684731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31812148643135983624456487 47718222964703975436684731)
    ·
      refine ⟨71577334447055963155027097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47718222964703975436684731 71577334447055963155027097)
      ·
        refine ⟨53683000835291972366270323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71577334447055963155027097 53683000835291972366270323)
        ·
          refine ⟨80524501252937958549405485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53683000835291972366270323 80524501252937958549405485)
          ·
            refine ⟨30196687969851734456027057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80524501252937958549405485 30196687969851734456027057)
            ·
              refine ⟨22647515977388800842020293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30196687969851734456027057 22647515977388800842020293)
              ·
                refine ⟨4246409245760400157878805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22647515977388800842020293 4246409245760400157878805)
                ·
                  refine ⟨199050433395018757400569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4246409245760400157878805 199050433395018757400569)
                  ·
                    rfl

theorem cell21_872211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_872211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_872211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_872211 prefixEnd_872211 := by exact prefixLift 872211
  have htrace : WordTrace (prefixWord ++ tailWord_872211) baseStart_872211 baseEnd_872211 := by
    simpa [prefixWord, tailWord_872211, baseEnd_872211] using wordTrace_append hprefix tailTrace_872211
  have hstable : (prefixWord ++ tailWord_872211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_872211).length < 2 ^ (prefixWord ++ tailWord_872211).sum := by decide
  have hdescent : baseEnd_872211 < baseStart_872211 := by decide
  rcases family_descends (prefixWord ++ tailWord_872211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
