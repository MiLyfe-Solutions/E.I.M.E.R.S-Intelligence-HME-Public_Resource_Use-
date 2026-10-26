import V185TrunkScan23Chunk1316

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7800183 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 7]
def baseStart_7800183 : Nat := 118140960795 + 7800183 * 2 ^ 59
def prefixEnd_7800183 : Nat := 4983230072969 + 3 ^ 40 * 7800183 * 2
def baseEnd_7800183 : Nat := 445027008003262275760013

theorem tailTrace_7800183 : CollatzResearch.WordTrace tailWord_7800183 prefixEnd_7800183 445027008003262275760013 := by
  unfold tailWord_7800183
  simp only [CollatzResearch.WordTrace]
  refine ⟨284496046300276631042421203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189664030866851087361614135 284496046300276631042421203)
  ·
    refine ⟨426744069450414946563631805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284496046300276631042421203 426744069450414946563631805)
    ·
      refine ⟨160029026043905604961361927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426744069450414946563631805 160029026043905604961361927)
      ·
        refine ⟨240043539065858407442042891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160029026043905604961361927 240043539065858407442042891)
        ·
          refine ⟨360065308598787611163064337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240043539065858407442042891 360065308598787611163064337)
          ·
            refine ⟨270048981449090708372298253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360065308598787611163064337 270048981449090708372298253)
            ·
              refine ⟨101268368043409015639611845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270048981449090708372298253 101268368043409015639611845)
              ·
                refine ⟨18987819008139190432427221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101268368043409015639611845 18987819008139190432427221)
                ·
                  refine ⟨445027008003262275760013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18987819008139190432427221 445027008003262275760013)
                  ·
                    rfl

theorem cell23_7800183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 7].length) (baseStart_7800183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800183 prefixEnd_7800183 := by exact prefixLift 7800183
  have htrace : WordTrace (prefixWord ++ tailWord_7800183) baseStart_7800183 baseEnd_7800183 := by
    simpa [prefixWord, tailWord_7800183, baseEnd_7800183] using wordTrace_append hprefix tailTrace_7800183
  have hstable : (prefixWord ++ tailWord_7800183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800183).length < 2 ^ (prefixWord ++ tailWord_7800183).sum := by decide
  have hdescent : baseEnd_7800183 < baseStart_7800183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800243 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 2, 8]
def baseStart_7800243 : Nat := 118140960795 + 7800243 * 2 ^ 59
def prefixEnd_7800243 : Nat := 4983230072969 + 3 ^ 40 * 7800243 * 2
def baseEnd_7800243 : Nat := 1335091293622876749029947

theorem tailTrace_7800243 : CollatzResearch.WordTrace tailWord_7800243 prefixEnd_7800243 1335091293622876749029947 := by
  unfold tailWord_7800243
  simp only [CollatzResearch.WordTrace]
  refine ⟨284498234680059261289605383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189665489786706174193070255 284498234680059261289605383)
  ·
    refine ⟨426747352020088891934408075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284498234680059261289605383 426747352020088891934408075)
    ·
      refine ⟨640121028030133337901612113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426747352020088891934408075 640121028030133337901612113)
      ·
        refine ⟨480090771022600003426209085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640121028030133337901612113 480090771022600003426209085)
        ·
          refine ⟨180034039133475001284828407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480090771022600003426209085 180034039133475001284828407)
          ·
            refine ⟨270051058700212501927242611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180034039133475001284828407 270051058700212501927242611)
            ·
              refine ⟨405076588050318752890863917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270051058700212501927242611 405076588050318752890863917)
              ·
                refine ⟨151903720518869532334073969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405076588050318752890863917 151903720518869532334073969)
                ·
                  refine ⟨113927790389152149250555477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151903720518869532334073969 113927790389152149250555477)
                  ·
                    refine ⟨1335091293622876749029947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113927790389152149250555477 1335091293622876749029947)
                    ·
                      rfl

theorem cell23_7800243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 8].length) (baseStart_7800243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800243 prefixEnd_7800243 := by exact prefixLift 7800243
  have htrace : WordTrace (prefixWord ++ tailWord_7800243) baseStart_7800243 baseEnd_7800243 := by
    simpa [prefixWord, tailWord_7800243, baseEnd_7800243] using wordTrace_append hprefix tailTrace_7800243
  have hstable : (prefixWord ++ tailWord_7800243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800243).length < 2 ^ (prefixWord ++ tailWord_7800243).sum := by decide
  have hdescent : baseEnd_7800243 < baseStart_7800243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800277 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 3, 4]
def baseStart_7800277 : Nat := 118140960795 + 7800277 * 2 ^ 59
def prefixEnd_7800277 : Nat := 4983230072969 + 3 ^ 40 * 7800277 * 2
def baseEnd_7800277 : Nat := 1335097113070294371354895

theorem tailTrace_7800277 : CollatzResearch.WordTrace tailWord_7800277 prefixEnd_7800277 1335097113070294371354895 := by
  unfold tailWord_7800277
  simp only [CollatzResearch.WordTrace]
  refine ⟨284499474761936085096343085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189666316507957390064228723 284499474761936085096343085)
  ·
    refine ⟨106687303035726031911128657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284499474761936085096343085 106687303035726031911128657)
    ·
      refine ⟨80015477276794523933346493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106687303035726031911128657 80015477276794523933346493)
      ·
        refine ⟨30005803978797946475004935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80015477276794523933346493 30005803978797946475004935)
        ·
          refine ⟨45008705968196919712507403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30005803978797946475004935 45008705968196919712507403)
          ·
            refine ⟨67513058952295379568761105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45008705968196919712507403 67513058952295379568761105)
            ·
              refine ⟨50634794214221534676570829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67513058952295379568761105 50634794214221534676570829)
              ·
                refine ⟨18988047830333075503714061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50634794214221534676570829 18988047830333075503714061)
                ·
                  refine ⟨7120517936374903313892773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18988047830333075503714061 7120517936374903313892773)
                  ·
                    refine ⟨1335097113070294371354895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7120517936374903313892773 1335097113070294371354895)
                    ·
                      rfl

theorem cell23_7800277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_7800277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800277 prefixEnd_7800277 := by exact prefixLift 7800277
  have htrace : WordTrace (prefixWord ++ tailWord_7800277) baseStart_7800277 baseEnd_7800277 := by
    simpa [prefixWord, tailWord_7800277, baseEnd_7800277] using wordTrace_append hprefix tailTrace_7800277
  have hstable : (prefixWord ++ tailWord_7800277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800277).length < 2 ^ (prefixWord ++ tailWord_7800277).sum := by decide
  have hdescent : baseEnd_7800277 < baseStart_7800277 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800300 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 3]
def baseStart_7800300 : Nat := 118140960795 + 7800300 * 2 ^ 59
def prefixEnd_7800300 : Nat := 4983230072969 + 3 ^ 40 * 7800300 * 2
def baseEnd_7800300 : Nat := 4005303149265936524077079

theorem tailTrace_7800300 : CollatzResearch.WordTrace tailWord_7800300 prefixEnd_7800300 4005303149265936524077079 := by
  unfold tailWord_7800300
  simp only [CollatzResearch.WordTrace]
  refine ⟨142250156820426380012215177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189666875760568506682953569 142250156820426380012215177)
  ·
    refine ⟨106687617615319785009161383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142250156820426380012215177 106687617615319785009161383)
    ·
      refine ⟨160031426422979677513742075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106687617615319785009161383 160031426422979677513742075)
      ·
        refine ⟨240047139634469516270613113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160031426422979677513742075 240047139634469516270613113)
        ·
          refine ⟨180035354725852137202959835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240047139634469516270613113 180035354725852137202959835)
          ·
            refine ⟨270053032088778205804439753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180035354725852137202959835 270053032088778205804439753)
            ·
              refine ⟨202539774066583654353329815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270053032088778205804439753 202539774066583654353329815)
              ·
                refine ⟨303809661099875481529994723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202539774066583654353329815 303809661099875481529994723)
                ·
                  refine ⟨455714491649813222294992085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303809661099875481529994723 455714491649813222294992085)
                  ·
                    refine ⟨10680808398042497397538877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 455714491649813222294992085 10680808398042497397538877)
                    ·
                      refine ⟨4005303149265936524077079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10680808398042497397538877 4005303149265936524077079)
                      ·
                        rfl

theorem cell23_7800300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_7800300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800300 prefixEnd_7800300 := by exact prefixLift 7800300
  have htrace : WordTrace (prefixWord ++ tailWord_7800300) baseStart_7800300 baseEnd_7800300 := by
    simpa [prefixWord, tailWord_7800300, baseEnd_7800300] using wordTrace_append hprefix tailTrace_7800300
  have hstable : (prefixWord ++ tailWord_7800300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800300).length < 2 ^ (prefixWord ++ tailWord_7800300).sum := by decide
  have hdescent : baseEnd_7800300 < baseStart_7800300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800301 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_7800301 : Nat := 118140960795 + 7800301 * 2 ^ 59
def prefixEnd_7800301 : Nat := 4983230072969 + 3 ^ 40 * 7800301 * 2
def baseEnd_7800301 : Nat := 4005303662746591020164575

theorem tailTrace_7800301 : CollatzResearch.WordTrace tailWord_7800301 prefixEnd_7800301 4005303662746591020164575 := by
  unfold tailWord_7800301
  simp only [CollatzResearch.WordTrace]
  refine ⟨284500350113849137195216757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189666900075899424796811171 284500350113849137195216757)
  ·
    refine ⟨26671907823173356612051571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284500350113849137195216757 26671907823173356612051571)
    ·
      refine ⟨40007861734760034918077357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26671907823173356612051571 40007861734760034918077357)
      ·
        refine ⟨15002948150535013094279009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40007861734760034918077357 15002948150535013094279009)
        ·
          refine ⟨11252211112901259820709257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15002948150535013094279009 11252211112901259820709257)
          ·
            refine ⟨8439158334675944865531943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11252211112901259820709257 8439158334675944865531943)
            ·
              refine ⟨12658737502013917298297915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8439158334675944865531943 12658737502013917298297915)
              ·
                refine ⟨18988106253020875947446873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12658737502013917298297915 18988106253020875947446873)
                ·
                  refine ⟨14241079689765656960585155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18988106253020875947446873 14241079689765656960585155)
                  ·
                    refine ⟨21361619534648485440877733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14241079689765656960585155 21361619534648485440877733)
                    ·
                      refine ⟨4005303662746591020164575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21361619534648485440877733 4005303662746591020164575)
                      ·
                        rfl

theorem cell23_7800301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_7800301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800301 prefixEnd_7800301 := by exact prefixLift 7800301
  have htrace : WordTrace (prefixWord ++ tailWord_7800301) baseStart_7800301 baseEnd_7800301 := by
    simpa [prefixWord, tailWord_7800301, baseEnd_7800301] using wordTrace_append hprefix tailTrace_7800301
  have hstable : (prefixWord ++ tailWord_7800301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800301).length < 2 ^ (prefixWord ++ tailWord_7800301).sum := by decide
  have hdescent : baseEnd_7800301 < baseStart_7800301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800304 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 3]
def baseStart_7800304 : Nat := 118140960795 + 7800304 * 2 ^ 59
def prefixEnd_7800304 : Nat := 4983230072969 + 3 ^ 40 * 7800304 * 2
def baseEnd_7800304 : Nat := 4005305203188554508427061

theorem tailTrace_7800304 : CollatzResearch.WordTrace tailWord_7800304 prefixEnd_7800304 4005305203188554508427061 := by
  unfold tailWord_7800304
  simp only [CollatzResearch.WordTrace]
  refine ⟨142250229766419134353787983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189666973021892179138383977 142250229766419134353787983)
  ·
    refine ⟨213375344649628701530681975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142250229766419134353787983 213375344649628701530681975)
    ·
      refine ⟨320063016974443052296022963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213375344649628701530681975 320063016974443052296022963)
      ·
        refine ⟨480094525461664578444034445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320063016974443052296022963 480094525461664578444034445)
        ·
          refine ⟨180035447048124216916512917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480094525461664578444034445 180035447048124216916512917)
          ·
            refine ⟨8439161580380822667961543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180035447048124216916512917 8439161580380822667961543)
            ·
              refine ⟨12658742370571234001942315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8439161580380822667961543 12658742370571234001942315)
              ·
                refine ⟨18988113555856851002913473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12658742370571234001942315 18988113555856851002913473)
                ·
                  refine ⟨14241085166892638252185105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18988113555856851002913473 14241085166892638252185105)
                  ·
                    refine ⟨10680813875169478689138829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14241085166892638252185105 10680813875169478689138829)
                    ·
                      refine ⟨4005305203188554508427061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10680813875169478689138829 4005305203188554508427061)
                      ·
                        rfl

theorem cell23_7800304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 3].length) (baseStart_7800304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800304 prefixEnd_7800304 := by exact prefixLift 7800304
  have htrace : WordTrace (prefixWord ++ tailWord_7800304) baseStart_7800304 baseEnd_7800304 := by
    simpa [prefixWord, tailWord_7800304, baseEnd_7800304] using wordTrace_append hprefix tailTrace_7800304
  have hstable : (prefixWord ++ tailWord_7800304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800304).length < 2 ^ (prefixWord ++ tailWord_7800304).sum := by decide
  have hdescent : baseEnd_7800304 < baseStart_7800304 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800357 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 1, 8, 2]
def baseStart_7800357 : Nat := 118140960795 + 7800357 * 2 ^ 59
def prefixEnd_7800357 : Nat := 4983230072969 + 3 ^ 40 * 7800357 * 2
def baseEnd_7800357 : Nat := 4005332417663242801064317

theorem tailTrace_7800357 : CollatzResearch.WordTrace tailWord_7800357 prefixEnd_7800357 4005332417663242801064317 := by
  unfold tailWord_7800357
  simp only [CollatzResearch.WordTrace]
  refine ⟨284502392601646258759255325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189668261734430839172836883 284502392601646258759255325)
  ·
    refine ⟨106688397225617347034720747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284502392601646258759255325 106688397225617347034720747)
    ·
      refine ⟨160032595838426020552081121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106688397225617347034720747 160032595838426020552081121)
      ·
        refine ⟨120024446878819515414060841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160032595838426020552081121 120024446878819515414060841)
        ·
          refine ⟨90018335159114636560545631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120024446878819515414060841 90018335159114636560545631)
          ·
            refine ⟨135027502738671954840818447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90018335159114636560545631 135027502738671954840818447)
            ·
              refine ⟨202541254108007932261227671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135027502738671954840818447 202541254108007932261227671)
              ·
                refine ⟨303811881162011898391841507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202541254108007932261227671 303811881162011898391841507)
                ·
                  refine ⟨455717821743017847587762261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303811881162011898391841507 455717821743017847587762261)
                  ·
                    refine ⟨5340443223550990401419089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 455717821743017847587762261 5340443223550990401419089)
                    ·
                      refine ⟨4005332417663242801064317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340443223550990401419089 4005332417663242801064317)
                      ·
                        rfl

theorem cell23_7800357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 8, 2].length) (baseStart_7800357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800357 prefixEnd_7800357 := by exact prefixLift 7800357
  have htrace : WordTrace (prefixWord ++ tailWord_7800357) baseStart_7800357 baseEnd_7800357 := by
    simpa [prefixWord, tailWord_7800357, baseEnd_7800357] using wordTrace_append hprefix tailTrace_7800357
  have hstable : (prefixWord ++ tailWord_7800357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800357).length < 2 ^ (prefixWord ++ tailWord_7800357).sum := by decide
  have hdescent : baseEnd_7800357 < baseStart_7800357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800377 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7800377 : Nat := 118140960795 + 7800377 * 2 ^ 59
def prefixEnd_7800377 : Nat := 4983230072969 + 3 ^ 40 * 7800377 * 2
def baseEnd_7800377 : Nat := 4005342687276332722814225

theorem tailTrace_7800377 : CollatzResearch.WordTrace tailWord_7800377 prefixEnd_7800377 4005342687276332722814225 := by
  unfold tailWord_7800377
  simp only [CollatzResearch.WordTrace]
  refine ⟨284503122061573802174983385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189668748041049201449988923 284503122061573802174983385)
  ·
    refine ⟨213377341546180351631237539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284503122061573802174983385 213377341546180351631237539)
    ·
      refine ⟨320066012319270527446856309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213377341546180351631237539 320066012319270527446856309)
      ·
        refine ⟨30006188654931611948142779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320066012319270527446856309 30006188654931611948142779)
        ·
          refine ⟨45009282982397417922214169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30006188654931611948142779 45009282982397417922214169)
          ·
            refine ⟨33756962236798063441660627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45009282982397417922214169 33756962236798063441660627)
            ·
              refine ⟨50635443355197095162490941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33756962236798063441660627 50635443355197095162490941)
              ·
                refine ⟨18988291258198910685934103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50635443355197095162490941 18988291258198910685934103)
                ·
                  refine ⟨28482436887298366028901155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18988291258198910685934103 28482436887298366028901155)
                  ·
                    refine ⟨42723655330947549043351733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28482436887298366028901155 42723655330947549043351733)
                    ·
                      refine ⟨4005342687276332722814225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42723655330947549043351733 4005342687276332722814225)
                      ·
                        rfl

theorem cell23_7800377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7800377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800377 prefixEnd_7800377 := by exact prefixLift 7800377
  have htrace : WordTrace (prefixWord ++ tailWord_7800377) baseStart_7800377 baseEnd_7800377 := by
    simpa [prefixWord, tailWord_7800377, baseEnd_7800377] using wordTrace_append hprefix tailTrace_7800377
  have hstable : (prefixWord ++ tailWord_7800377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800377).length < 2 ^ (prefixWord ++ tailWord_7800377).sum := by decide
  have hdescent : baseEnd_7800377 < baseStart_7800377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800400 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 6]
def baseStart_7800400 : Nat := 118140960795 + 7800400 * 2 ^ 59
def prefixEnd_7800400 : Nat := 4983230072969 + 3 ^ 40 * 7800400 * 2
def baseEnd_7800400 : Nat := 4005354497331386132826619

theorem tailTrace_7800400 : CollatzResearch.WordTrace tailWord_7800400 prefixEnd_7800400 4005354497331386132826619 := by
  unfold tailWord_7800400
  simp only [CollatzResearch.WordTrace]
  refine ⟨142251980470245238551535327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189669307293660318068713769 142251980470245238551535327)
  ·
    refine ⟨213377970705367857827302991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142251980470245238551535327 213377970705367857827302991)
    ·
      refine ⟨320066956058051786740954487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213377970705367857827302991 320066956058051786740954487)
      ·
        refine ⟨480100434087077680111431731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320066956058051786740954487 480100434087077680111431731)
        ·
          refine ⟨720150651130616520167147597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480100434087077680111431731 720150651130616520167147597)
          ·
            refine ⟨270056494173981195062680349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 720150651130616520167147597 270056494173981195062680349)
            ·
              refine ⟨101271185315242948148505131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270056494173981195062680349 101271185315242948148505131)
              ·
                refine ⟨151906777972864422222757697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101271185315242948148505131 151906777972864422222757697)
                ·
                  refine ⟨113930083479648316667068273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151906777972864422222757697 113930083479648316667068273)
                  ·
                    refine ⟨85447562609736237500301205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113930083479648316667068273 85447562609736237500301205)
                    ·
                      refine ⟨4005354497331386132826619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85447562609736237500301205 4005354497331386132826619)
                      ·
                        rfl

theorem cell23_7800400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_7800400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800400 prefixEnd_7800400 := by exact prefixLift 7800400
  have htrace : WordTrace (prefixWord ++ tailWord_7800400) baseStart_7800400 baseEnd_7800400 := by
    simpa [prefixWord, tailWord_7800400, baseEnd_7800400] using wordTrace_append hprefix tailTrace_7800400
  have hstable : (prefixWord ++ tailWord_7800400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800400).length < 2 ^ (prefixWord ++ tailWord_7800400).sum := by decide
  have hdescent : baseEnd_7800400 < baseStart_7800400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800424 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_7800424 : Nat := 118140960795 + 7800424 * 2 ^ 59
def prefixEnd_7800424 : Nat := 4983230072969 + 3 ^ 40 * 7800424 * 2
def baseEnd_7800424 : Nat := 4005366820867094038926509

theorem tailTrace_7800424 : CollatzResearch.WordTrace tailWord_7800424 prefixEnd_7800424 4005366820867094038926509 := by
  unfold tailWord_7800424
  simp only [CollatzResearch.WordTrace]
  refine ⟨142252418146201764600972163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189669890861602352801296217 142252418146201764600972163)
  ·
    refine ⟨213378627219302646901458245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142252418146201764600972163 213378627219302646901458245)
    ·
      refine ⟨40008492603619246294023421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213378627219302646901458245 40008492603619246294023421)
      ·
        refine ⟨15003184726357217360258783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40008492603619246294023421 15003184726357217360258783)
        ·
          refine ⟨22504777089535826040388175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15003184726357217360258783 22504777089535826040388175)
          ·
            refine ⟨33757165634303739060582263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22504777089535826040388175 33757165634303739060582263)
            ·
              refine ⟨50635748451455608590873395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33757165634303739060582263 50635748451455608590873395)
              ·
                refine ⟨75953622677183412886310093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50635748451455608590873395 75953622677183412886310093)
                ·
                  refine ⟨28482608503943779832366285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75953622677183412886310093 28482608503943779832366285)
                  ·
                    refine ⟨10680978188978917437137357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28482608503943779832366285 10680978188978917437137357)
                    ·
                      refine ⟨4005366820867094038926509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10680978188978917437137357 4005366820867094038926509)
                      ·
                        rfl

theorem cell23_7800424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_7800424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800424 prefixEnd_7800424 := by exact prefixLift 7800424
  have htrace : WordTrace (prefixWord ++ tailWord_7800424) baseStart_7800424 baseEnd_7800424 := by
    simpa [prefixWord, tailWord_7800424, baseEnd_7800424] using wordTrace_append hprefix tailTrace_7800424
  have hstable : (prefixWord ++ tailWord_7800424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800424).length < 2 ^ (prefixWord ++ tailWord_7800424).sum := by decide
  have hdescent : baseEnd_7800424 < baseStart_7800424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800441 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 2, 1, 3]
def baseStart_7800441 : Nat := 118140960795 + 7800441 * 2 ^ 59
def prefixEnd_7800441 : Nat := 4983230072969 + 3 ^ 40 * 7800441 * 2
def baseEnd_7800441 : Nat := 4005375550038220472413931

theorem tailTrace_7800441 : CollatzResearch.WordTrace tailWord_7800441 prefixEnd_7800441 4005375550038220472413931 := by
  unfold tailWord_7800441
  simp only [CollatzResearch.WordTrace]
  refine ⟨284505456333341941105313177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189670304222227960736875451 284505456333341941105313177)
  ·
    refine ⟨213379092250006455828984883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284505456333341941105313177 213379092250006455828984883)
    ·
      refine ⟨320068638375009683743477325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213379092250006455828984883 320068638375009683743477325)
      ·
        refine ⟨120025739390628631403803997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320068638375009683743477325 120025739390628631403803997)
        ·
          refine ⟨45009652271485736776426499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120025739390628631403803997 45009652271485736776426499)
          ·
            refine ⟨67514478407228605164639749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45009652271485736776426499 67514478407228605164639749)
            ·
              refine ⟨12658964701355363468369953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67514478407228605164639749 12658964701355363468369953)
              ·
                refine ⟨9494223526016522601277465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12658964701355363468369953 9494223526016522601277465)
                ·
                  refine ⟨7120667644512391950958099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9494223526016522601277465 7120667644512391950958099)
                  ·
                    refine ⟨10681001466768587926437149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7120667644512391950958099 10681001466768587926437149)
                    ·
                      refine ⟨4005375550038220472413931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10681001466768587926437149 4005375550038220472413931)
                      ·
                        rfl

theorem cell23_7800441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_7800441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800441 prefixEnd_7800441 := by exact prefixLift 7800441
  have htrace : WordTrace (prefixWord ++ tailWord_7800441) baseStart_7800441 baseEnd_7800441 := by
    simpa [prefixWord, tailWord_7800441, baseEnd_7800441] using wordTrace_append hprefix tailTrace_7800441
  have hstable : (prefixWord ++ tailWord_7800441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800441).length < 2 ^ (prefixWord ++ tailWord_7800441).sum := by decide
  have hdescent : baseEnd_7800441 < baseStart_7800441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800477 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_7800477 : Nat := 118140960795 + 7800477 * 2 ^ 59
def prefixEnd_7800477 : Nat := 4983230072969 + 3 ^ 40 * 7800477 * 2
def baseEnd_7800477 : Nat := 4005394035341782331563765

theorem tailTrace_7800477 : CollatzResearch.WordTrace tailWord_7800477 prefixEnd_7800477 4005394035341782331563765 := by
  unfold tailWord_7800477
  simp only [CollatzResearch.WordTrace]
  refine ⟨284506769361211519253623685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189671179574141012835749123 284506769361211519253623685)
  ·
    refine ⟨53345019255227159860054441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284506769361211519253623685 53345019255227159860054441)
    ·
      refine ⟨40008764441420369895040831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53345019255227159860054441 40008764441420369895040831)
      ·
        refine ⟨60013146662130554842561247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40008764441420369895040831 60013146662130554842561247)
        ·
          refine ⟨90019719993195832263841871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60013146662130554842561247 90019719993195832263841871)
          ·
            refine ⟨135029579989793748395762807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90019719993195832263841871 135029579989793748395762807)
            ·
              refine ⟨202544369984690622593644211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135029579989793748395762807 202544369984690622593644211)
              ·
                refine ⟨303816554977035933890466317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202544369984690622593644211 303816554977035933890466317)
                ·
                  refine ⟨113931208116388475208924869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303816554977035933890466317 113931208116388475208924869)
                  ·
                    refine ⟨21362101521822839101673413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113931208116388475208924869 21362101521822839101673413)
                    ·
                      refine ⟨4005394035341782331563765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21362101521822839101673413 4005394035341782331563765)
                      ·
                        rfl

theorem cell23_7800477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_7800477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800477 prefixEnd_7800477 := by exact prefixLift 7800477
  have htrace : WordTrace (prefixWord ++ tailWord_7800477) baseStart_7800477 baseEnd_7800477 := by
    simpa [prefixWord, tailWord_7800477, baseEnd_7800477] using wordTrace_append hprefix tailTrace_7800477
  have hstable : (prefixWord ++ tailWord_7800477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800477).length < 2 ^ (prefixWord ++ tailWord_7800477).sum := by decide
  have hdescent : baseEnd_7800477 < baseStart_7800477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800481 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 1, 4, 2]
def baseStart_7800481 : Nat := 118140960795 + 7800481 * 2 ^ 59
def prefixEnd_7800481 : Nat := 4983230072969 + 3 ^ 40 * 7800481 * 2
def baseEnd_7800481 : Nat := 4005396089264400315913747

theorem tailTrace_7800481 : CollatzResearch.WordTrace tailWord_7800481 prefixEnd_7800481 4005396089264400315913747 := by
  unfold tailWord_7800481
  simp only [CollatzResearch.WordTrace]
  refine ⟨284506915253197027936769297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189671276835464685291179531 284506915253197027936769297)
  ·
    refine ⟨213380186439897770952576973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284506915253197027936769297 213380186439897770952576973)
    ·
      refine ⟨80017569914961664107216365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213380186439897770952576973 80017569914961664107216365)
      ·
        refine ⟨30006588718110624040206137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80017569914961664107216365 30006588718110624040206137)
        ·
          refine ⟨22504941538582968030154603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30006588718110624040206137 22504941538582968030154603)
          ·
            refine ⟨33757412307874452045231905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22504941538582968030154603 33757412307874452045231905)
            ·
              refine ⟨25318059230905839033923929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33757412307874452045231905 25318059230905839033923929)
              ·
                refine ⟨18988544423179379275442947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25318059230905839033923929 18988544423179379275442947)
                ·
                  refine ⟨28482816634769068913164421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18988544423179379275442947 28482816634769068913164421)
                  ·
                    refine ⟨5340528119019200421218329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28482816634769068913164421 5340528119019200421218329)
                    ·
                      refine ⟨4005396089264400315913747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340528119019200421218329 4005396089264400315913747)
                      ·
                        rfl

theorem cell23_7800481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_7800481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800481 prefixEnd_7800481 := by exact prefixLift 7800481
  have htrace : WordTrace (prefixWord ++ tailWord_7800481) baseStart_7800481 baseEnd_7800481 := by
    simpa [prefixWord, tailWord_7800481, baseEnd_7800481] using wordTrace_append hprefix tailTrace_7800481
  have hstable : (prefixWord ++ tailWord_7800481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800481).length < 2 ^ (prefixWord ++ tailWord_7800481).sum := by decide
  have hdescent : baseEnd_7800481 < baseStart_7800481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800498 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2]
def baseStart_7800498 : Nat := 118140960795 + 7800498 * 2 ^ 59
def prefixEnd_7800498 : Nat := 4983230072969 + 3 ^ 40 * 7800498 * 2
def baseEnd_7800498 : Nat := 4005404818435526749401169

theorem tailTrace_7800498 : CollatzResearch.WordTrace tailWord_7800498 prefixEnd_7800498 4005404818435526749401169 := by
  unfold tailWord_7800498
  simp only [CollatzResearch.WordTrace]
  refine ⟨71126883823533859960034537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189671690196090293226758765 71126883823533859960034537)
  ·
    refine ⟨53345162867650394970025903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71126883823533859960034537 53345162867650394970025903)
    ·
      refine ⟨80017744301475592455038855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53345162867650394970025903 80017744301475592455038855)
      ·
        refine ⟨120026616452213388682558283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80017744301475592455038855 120026616452213388682558283)
        ·
          refine ⟨180039924678320083023837425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120026616452213388682558283 180039924678320083023837425)
          ·
            refine ⟨135029943508740062267878069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180039924678320083023837425 135029943508740062267878069)
            ·
              refine ⟨12659057203944380837613569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135029943508740062267878069 12659057203944380837613569)
              ·
                refine ⟨9494292902958285628210177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12659057203944380837613569 9494292902958285628210177)
                ·
                  refine ⟨7120719677218714221157633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9494292902958285628210177 7120719677218714221157633)
                  ·
                    refine ⟨5340539757914035665868225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7120719677218714221157633 5340539757914035665868225)
                    ·
                      refine ⟨4005404818435526749401169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340539757914035665868225 4005404818435526749401169)
                      ·
                        rfl

theorem cell23_7800498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_7800498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800498 prefixEnd_7800498 := by exact prefixLift 7800498
  have htrace : WordTrace (prefixWord ++ tailWord_7800498) baseStart_7800498 baseEnd_7800498 := by
    simpa [prefixWord, tailWord_7800498, baseEnd_7800498] using wordTrace_append hprefix tailTrace_7800498
  have hstable : (prefixWord ++ tailWord_7800498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800498).length < 2 ^ (prefixWord ++ tailWord_7800498).sum := by decide
  have hdescent : baseEnd_7800498 < baseStart_7800498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800517 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 4, 5]
def baseStart_7800517 : Nat := 118140960795 + 7800517 * 2 ^ 59
def prefixEnd_7800517 : Nat := 4983230072969 + 3 ^ 40 * 7800517 * 2
def baseEnd_7800517 : Nat := 1335138191522654058354527

theorem tailTrace_7800517 : CollatzResearch.WordTrace tailWord_7800517 prefixEnd_7800517 1335138191522654058354527 := by
  unfold tailWord_7800517
  simp only [CollatzResearch.WordTrace]
  refine ⟨284508228281066606085079805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189672152187377737390053203 284508228281066606085079805)
  ·
    refine ⟨106690585605399977281904927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284508228281066606085079805 106690585605399977281904927)
    ·
      refine ⟨160035878408099965922857391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106690585605399977281904927 160035878408099965922857391)
      ·
        refine ⟨240053817612149948884286087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160035878408099965922857391 240053817612149948884286087)
        ·
          refine ⟨360080726418224923326429131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240053817612149948884286087 360080726418224923326429131)
          ·
            refine ⟨540121089627337384989643697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360080726418224923326429131 540121089627337384989643697)
            ·
              refine ⟨405090817220503038742232773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540121089627337384989643697 405090817220503038742232773)
              ·
                refine ⟨75954528228844319764168645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405090817220503038742232773 75954528228844319764168645)
                ·
                  refine ⟨14241474042908309955781621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75954528228844319764168645 14241474042908309955781621)
                  ·
                    refine ⟨1335138191522654058354527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14241474042908309955781621 1335138191522654058354527)
                    ·
                      rfl

theorem cell23_7800517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_7800517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800517 prefixEnd_7800517 := by exact prefixLift 7800517
  have htrace : WordTrace (prefixWord ++ tailWord_7800517) baseStart_7800517 baseEnd_7800517 := by
    simpa [prefixWord, tailWord_7800517, baseEnd_7800517] using wordTrace_append hprefix tailTrace_7800517
  have hstable : (prefixWord ++ tailWord_7800517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800517).length < 2 ^ (prefixWord ++ tailWord_7800517).sum := by decide
  have hdescent : baseEnd_7800517 < baseStart_7800517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800554 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_7800554 : Nat := 118140960795 + 7800554 * 2 ^ 59
def prefixEnd_7800554 : Nat := 4983230072969 + 3 ^ 40 * 7800554 * 2
def baseEnd_7800554 : Nat := 4005433573352178530300911

theorem tailTrace_7800554 : CollatzResearch.WordTrace tailWord_7800554 prefixEnd_7800554 4005433573352178530300911 := by
  unfold tailWord_7800554
  simp only [CollatzResearch.WordTrace]
  refine ⟨71127394445483140351044179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189673051854621707602784477 71127394445483140351044179)
  ·
    refine ⟨106691091668224710526566269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71127394445483140351044179 106691091668224710526566269)
    ·
      refine ⟨40009159375584266447462351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106691091668224710526566269 40009159375584266447462351)
      ·
        refine ⟨60013739063376399671193527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40009159375584266447462351 60013739063376399671193527)
        ·
          refine ⟨90020608595064599506790291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60013739063376399671193527 90020608595064599506790291)
          ·
            refine ⟨135030912892596899260185437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90020608595064599506790291 135030912892596899260185437)
            ·
              refine ⟨50636592334723837222569539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135030912892596899260185437 50636592334723837222569539)
              ·
                refine ⟨75954888502085755833854309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50636592334723837222569539 75954888502085755833854309)
                ·
                  refine ⟨14241541594141079218847683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75954888502085755833854309 14241541594141079218847683)
                  ·
                    refine ⟨21362312391211618828271525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14241541594141079218847683 21362312391211618828271525)
                    ·
                      refine ⟨4005433573352178530300911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21362312391211618828271525 4005433573352178530300911)
                      ·
                        rfl

theorem cell23_7800554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_7800554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800554 prefixEnd_7800554 := by exact prefixLift 7800554
  have htrace : WordTrace (prefixWord ++ tailWord_7800554) baseStart_7800554 baseEnd_7800554 := by
    simpa [prefixWord, tailWord_7800554, baseEnd_7800554] using wordTrace_append hprefix tailTrace_7800554
  have hstable : (prefixWord ++ tailWord_7800554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800554).length < 2 ^ (prefixWord ++ tailWord_7800554).sum := by decide
  have hdescent : baseEnd_7800554 < baseStart_7800554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800567 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 6]
def baseStart_7800567 : Nat := 118140960795 + 7800567 * 2 ^ 59
def prefixEnd_7800567 : Nat := 4983230072969 + 3 ^ 40 * 7800567 * 2
def baseEnd_7800567 : Nat := 4005440248600686979438351

theorem tailTrace_7800567 : CollatzResearch.WordTrace tailWord_7800567 prefixEnd_7800567 4005440248600686979438351 := by
  unfold tailWord_7800567
  simp only [CollatzResearch.WordTrace]
  refine ⟨284510051930885464624399955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189673367953923643082933303 284510051930885464624399955)
  ·
    refine ⟨426765077896328196936599933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284510051930885464624399955 426765077896328196936599933)
    ·
      refine ⟨160036904211123073851224975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426765077896328196936599933 160036904211123073851224975)
      ·
        refine ⟨240055356316684610776837463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160036904211123073851224975 240055356316684610776837463)
        ·
          refine ⟨360083034475026916165256195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240055356316684610776837463 360083034475026916165256195)
          ·
            refine ⟨540124551712540374247884293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360083034475026916165256195 540124551712540374247884293)
            ·
              refine ⟨101273353446101320171478305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540124551712540374247884293 101273353446101320171478305)
              ·
                refine ⟨75955015084575990128608729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101273353446101320171478305 75955015084575990128608729)
                ·
                  refine ⟨56966261313431992596456547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75955015084575990128608729 56966261313431992596456547)
                  ·
                    refine ⟨85449391970147988894684821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56966261313431992596456547 85449391970147988894684821)
                    ·
                      refine ⟨4005440248600686979438351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85449391970147988894684821 4005440248600686979438351)
                      ·
                        rfl

theorem cell23_7800567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_7800567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800567 prefixEnd_7800567 := by exact prefixLift 7800567
  have htrace : WordTrace (prefixWord ++ tailWord_7800567) baseStart_7800567 baseEnd_7800567 := by
    simpa [prefixWord, tailWord_7800567, baseEnd_7800567] using wordTrace_append hprefix tailTrace_7800567
  have hstable : (prefixWord ++ tailWord_7800567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800567).length < 2 ^ (prefixWord ++ tailWord_7800567).sum := by decide
  have hdescent : baseEnd_7800567 < baseStart_7800567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800617 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 7]
def baseStart_7800617 : Nat := 118140960795 + 7800617 * 2 ^ 59
def prefixEnd_7800617 : Nat := 4983230072969 + 3 ^ 40 * 7800617 * 2
def baseEnd_7800617 : Nat := 4005465922633411783813121

theorem tailTrace_7800617 : CollatzResearch.WordTrace tailWord_7800617 prefixEnd_7800617 4005465922633411783813121 := by
  unfold tailWord_7800617
  simp only [CollatzResearch.WordTrace]
  refine ⟨284511875580704323163720105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189674583720469548775813403 284511875580704323163720105)
  ·
    refine ⟨213383906685528242372790079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284511875580704323163720105 213383906685528242372790079)
    ·
      refine ⟨320075860028292363559185119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213383906685528242372790079 320075860028292363559185119)
      ·
        refine ⟨480113790042438545338777679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320075860028292363559185119 480113790042438545338777679)
        ·
          refine ⟨720170685063657818008166519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480113790042438545338777679 720170685063657818008166519)
          ·
            refine ⟨1080256027595486727012249779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720170685063657818008166519 1080256027595486727012249779)
            ·
              refine ⟨1620384041393230090518374669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080256027595486727012249779 1620384041393230090518374669)
              ·
                refine ⟨607644015522461283944390501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1620384041393230090518374669 607644015522461283944390501)
                ·
                  refine ⟨113933252910461490739573219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 607644015522461283944390501 113933252910461490739573219)
                  ·
                    refine ⟨170899879365692236109359829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113933252910461490739573219 170899879365692236109359829)
                    ·
                      refine ⟨4005465922633411783813121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170899879365692236109359829 4005465922633411783813121)
                      ·
                        rfl

theorem cell23_7800617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_7800617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800617 prefixEnd_7800617 := by exact prefixLift 7800617
  have htrace : WordTrace (prefixWord ++ tailWord_7800617) baseStart_7800617 baseEnd_7800617 := by
    simpa [prefixWord, tailWord_7800617, baseEnd_7800617] using wordTrace_append hprefix tailTrace_7800617
  have hstable : (prefixWord ++ tailWord_7800617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800617).length < 2 ^ (prefixWord ++ tailWord_7800617).sum := by decide
  have hdescent : baseEnd_7800617 < baseStart_7800617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800638 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_7800638 : Nat := 118140960795 + 7800638 * 2 ^ 59
def prefixEnd_7800638 : Nat := 4983230072969 + 3 ^ 40 * 7800638 * 2
def baseEnd_7800638 : Nat := 4005476705727156201650525

theorem tailTrace_7800638 : CollatzResearch.WordTrace tailWord_7800638 prefixEnd_7800638 4005476705727156201650525 := by
  unfold tailWord_7800638
  simp only [CollatzResearch.WordTrace]
  refine ⟨35564080189203530468779321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189675094342418829166823045 35564080189203530468779321)
  ·
    refine ⟨26673060141902647851584491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35564080189203530468779321 26673060141902647851584491)
    ·
      refine ⟨40009590212853971777376737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26673060141902647851584491 40009590212853971777376737)
      ·
        refine ⟨30007192659640478833032553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40009590212853971777376737 30007192659640478833032553)
        ·
          refine ⟨22505394494730359124774415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30007192659640478833032553 22505394494730359124774415)
          ·
            refine ⟨33758091742095538687161623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22505394494730359124774415 33758091742095538687161623)
            ·
              refine ⟨50637137613143308030742435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33758091742095538687161623 50637137613143308030742435)
              ·
                refine ⟨75955706419714962046113653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50637137613143308030742435 75955706419714962046113653)
                ·
                  refine ⟨7120847476848277691823155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75955706419714962046113653 7120847476848277691823155)
                  ·
                    refine ⟨10681271215272416537734733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7120847476848277691823155 10681271215272416537734733)
                    ·
                      refine ⟨4005476705727156201650525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10681271215272416537734733 4005476705727156201650525)
                      ·
                        rfl

theorem cell23_7800638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_7800638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800638 prefixEnd_7800638 := by exact prefixLift 7800638
  have htrace : WordTrace (prefixWord ++ tailWord_7800638) baseStart_7800638 baseEnd_7800638 := by
    simpa [prefixWord, tailWord_7800638, baseEnd_7800638] using wordTrace_append hprefix tailTrace_7800638
  have hstable : (prefixWord ++ tailWord_7800638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800638).length < 2 ^ (prefixWord ++ tailWord_7800638).sum := by decide
  have hdescent : baseEnd_7800638 < baseStart_7800638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800648 : List Nat := [2, 1, 3, 1, 1, 4, 3, 1, 2, 3, 2]
def baseStart_7800648 : Nat := 118140960795 + 7800648 * 2 ^ 59
def prefixEnd_7800648 : Nat := 4983230072969 + 3 ^ 40 * 7800648 * 2
def baseEnd_7800648 : Nat := 4005481840533701162525479

theorem tailTrace_7800648 : CollatzResearch.WordTrace tailWord_7800648 prefixEnd_7800648 4005481840533701162525479 := by
  unfold tailWord_7800648
  simp only [CollatzResearch.WordTrace]
  refine ⟨142256503121796007729049299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189675337495728010305399065 142256503121796007729049299)
  ·
    refine ⟨213384754682694011593573949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142256503121796007729049299 213384754682694011593573949)
    ·
      refine ⟨80019283006010254347590231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213384754682694011593573949 80019283006010254347590231)
      ·
        refine ⟨120028924509015381521385347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80019283006010254347590231 120028924509015381521385347)
        ·
          refine ⟨180043386763523072282078021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120028924509015381521385347 180043386763523072282078021)
          ·
            refine ⟨33758135018160576052889629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180043386763523072282078021 33758135018160576052889629)
            ·
              refine ⟨12659300631810216019833611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33758135018160576052889629 12659300631810216019833611)
              ·
                refine ⟨18988950947715324029750417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12659300631810216019833611 18988950947715324029750417)
                ·
                  refine ⟨14241713210786493022312813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18988950947715324029750417 14241713210786493022312813)
                  ·
                    refine ⟨5340642454044934883367305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14241713210786493022312813 5340642454044934883367305)
                    ·
                      refine ⟨4005481840533701162525479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340642454044934883367305 4005481840533701162525479)
                      ·
                        rfl

theorem cell23_7800648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_7800648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800648 prefixEnd_7800648 := by exact prefixLift 7800648
  have htrace : WordTrace (prefixWord ++ tailWord_7800648) baseStart_7800648 baseEnd_7800648 := by
    simpa [prefixWord, tailWord_7800648, baseEnd_7800648] using wordTrace_append hprefix tailTrace_7800648
  have hstable : (prefixWord ++ tailWord_7800648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800648).length < 2 ^ (prefixWord ++ tailWord_7800648).sum := by decide
  have hdescent : baseEnd_7800648 < baseStart_7800648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800658 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 1, 5]
def baseStart_7800658 : Nat := 118140960795 + 7800658 * 2 ^ 59
def prefixEnd_7800658 : Nat := 4983230072969 + 3 ^ 40 * 7800658 * 2
def baseEnd_7800658 : Nat := 1335162325113415374466811

theorem tailTrace_7800658 : CollatzResearch.WordTrace tailWord_7800658 prefixEnd_7800658 1335162325113415374466811 := by
  unfold tailWord_7800658
  simp only [CollatzResearch.WordTrace]
  refine ⟨71128342743388946791490657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189675580649037191443975085 71128342743388946791490657)
  ·
    refine ⟨53346257057541710093617993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71128342743388946791490657 53346257057541710093617993)
    ·
      refine ⟨40009692793156282570213495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53346257057541710093617993 40009692793156282570213495)
      ·
        refine ⟨60014539189734423855320243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40009692793156282570213495 60014539189734423855320243)
        ·
          refine ⟨90021808784601635782980365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60014539189734423855320243 90021808784601635782980365)
          ·
            refine ⟨33758178294225613418617637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90021808784601635782980365 33758178294225613418617637)
            ·
              refine ⟨6329658430167302515990807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33758178294225613418617637 6329658430167302515990807)
              ·
                refine ⟨9494487645250953773986211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6329658430167302515990807 9494487645250953773986211)
                ·
                  refine ⟨14241731467876430660979317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9494487645250953773986211 14241731467876430660979317)
                  ·
                    refine ⟨1335162325113415374466811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14241731467876430660979317 1335162325113415374466811)
                    ·
                      rfl

theorem cell23_7800658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_7800658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800658 prefixEnd_7800658 := by exact prefixLift 7800658
  have htrace : WordTrace (prefixWord ++ tailWord_7800658) baseStart_7800658 baseEnd_7800658 := by
    simpa [prefixWord, tailWord_7800658, baseEnd_7800658] using wordTrace_append hprefix tailTrace_7800658
  have hstable : (prefixWord ++ tailWord_7800658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800658).length < 2 ^ (prefixWord ++ tailWord_7800658).sum := by decide
  have hdescent : baseEnd_7800658 < baseStart_7800658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800671 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 4, 4]
def baseStart_7800671 : Nat := 118140960795 + 7800671 * 2 ^ 59
def prefixEnd_7800671 : Nat := 4983230072969 + 3 ^ 40 * 7800671 * 2
def baseEnd_7800671 : Nat := 1335164550196251524179291

theorem tailTrace_7800671 : CollatzResearch.WordTrace tailWord_7800671 prefixEnd_7800671 1335164550196251524179291 := by
  unfold tailWord_7800671
  simp only [CollatzResearch.WordTrace]
  refine ⟨284513845122508690386185867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189675896748339126924123911 284513845122508690386185867)
  ·
    refine ⟨426770767683763035579278801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284513845122508690386185867 426770767683763035579278801)
    ·
      refine ⟨320078075762822276684459101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426770767683763035579278801 320078075762822276684459101)
      ·
        refine ⟨120029278411058353756672163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320078075762822276684459101 120029278411058353756672163)
        ·
          refine ⟨180043917616587530635008245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120029278411058353756672163 180043917616587530635008245)
          ·
            refine ⟨16879117276555080997032023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180043917616587530635008245 16879117276555080997032023)
            ·
              refine ⟨25318675914832621495548035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16879117276555080997032023 25318675914832621495548035)
              ·
                refine ⟨37978013872248932243322053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25318675914832621495548035 37978013872248932243322053)
                ·
                  refine ⟨7120877601046674795622885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37978013872248932243322053 7120877601046674795622885)
                  ·
                    refine ⟨1335164550196251524179291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7120877601046674795622885 1335164550196251524179291)
                    ·
                      rfl

theorem cell23_7800671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 4].length) (baseStart_7800671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800671 prefixEnd_7800671 := by exact prefixLift 7800671
  have htrace : WordTrace (prefixWord ++ tailWord_7800671) baseStart_7800671 baseEnd_7800671 := by
    simpa [prefixWord, tailWord_7800671, baseEnd_7800671] using wordTrace_append hprefix tailTrace_7800671
  have hstable : (prefixWord ++ tailWord_7800671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800671).length < 2 ^ (prefixWord ++ tailWord_7800671).sum := by decide
  have hdescent : baseEnd_7800671 < baseStart_7800671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800718 : List Nat := [4, 1, 1, 5, 1, 2, 9]
def baseStart_7800718 : Nat := 118140960795 + 7800718 * 2 ^ 59
def prefixEnd_7800718 : Nat := 4983230072969 + 3 ^ 40 * 7800718 * 2
def baseEnd_7800718 : Nat := 49450836841722418378397

theorem tailTrace_7800718 : CollatzResearch.WordTrace tailWord_7800718 prefixEnd_7800718 49450836841722418378397 := by
  unfold tailWord_7800718
  simp only [CollatzResearch.WordTrace]
  refine ⟨35564444919167302176643351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189677039568892278275431205 35564444919167302176643351)
  ·
    refine ⟨53346667378750953264965027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35564444919167302176643351 53346667378750953264965027)
    ·
      refine ⟨80020001068126429897447541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53346667378750953264965027 80020001068126429897447541)
      ·
        refine ⟨7501875100136852802885707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80020001068126429897447541 7501875100136852802885707)
        ·
          refine ⟨11252812650205279204328561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7501875100136852802885707 11252812650205279204328561)
          ·
            refine ⟨8439609487653959403246421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11252812650205279204328561 8439609487653959403246421)
            ·
              refine ⟨49450836841722418378397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8439609487653959403246421 49450836841722418378397)
              ·
                rfl

theorem cell23_7800718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 9].length) (baseStart_7800718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800718 prefixEnd_7800718 := by exact prefixLift 7800718
  have htrace : WordTrace (prefixWord ++ tailWord_7800718) baseStart_7800718 baseEnd_7800718 := by
    simpa [prefixWord, tailWord_7800718, baseEnd_7800718] using wordTrace_append hprefix tailTrace_7800718
  have hstable : (prefixWord ++ tailWord_7800718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800718).length < 2 ^ (prefixWord ++ tailWord_7800718).sum := by decide
  have hdescent : baseEnd_7800718 < baseStart_7800718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800768 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 1, 4, 2]
def baseStart_7800768 : Nat := 118140960795 + 7800768 * 2 ^ 59
def prefixEnd_7800768 : Nat := 4983230072969 + 3 ^ 40 * 7800768 * 2
def baseEnd_7800768 : Nat := 4005543458212240693024927

theorem tailTrace_7800768 : CollatzResearch.WordTrace tailWord_7800768 prefixEnd_7800768 4005543458212240693024927 := by
  unfold tailWord_7800768
  simp only [CollatzResearch.WordTrace]
  refine ⟨142258691501578637976233479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189678255335438183968311305 142258691501578637976233479)
  ·
    refine ⟨213388037252367956964350219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142258691501578637976233479 213388037252367956964350219)
    ·
      refine ⟨320082055878551935446525329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213388037252367956964350219 320082055878551935446525329)
      ·
        refine ⟨240061541908913951584893997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320082055878551935446525329 240061541908913951584893997)
        ·
          refine ⟨90023078215842731844335249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240061541908913951584893997 90023078215842731844335249)
          ·
            refine ⟨67517308661882048883251437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90023078215842731844335249 67517308661882048883251437)
            ·
              refine ⟨25318990748205768331219289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67517308661882048883251437 25318990748205768331219289)
              ·
                refine ⟨18989243061154326248414467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25318990748205768331219289 18989243061154326248414467)
                ·
                  refine ⟨28483864591731489372621701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18989243061154326248414467 28483864591731489372621701)
                  ·
                    refine ⟨5340724610949654257366569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28483864591731489372621701 5340724610949654257366569)
                    ·
                      refine ⟨4005543458212240693024927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340724610949654257366569 4005543458212240693024927)
                      ·
                        rfl

theorem cell23_7800768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 1, 4, 2].length) (baseStart_7800768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800768 prefixEnd_7800768 := by exact prefixLift 7800768
  have htrace : WordTrace (prefixWord ++ tailWord_7800768) baseStart_7800768 baseEnd_7800768 := by
    simpa [prefixWord, tailWord_7800768, baseEnd_7800768] using wordTrace_append hprefix tailTrace_7800768
  have hstable : (prefixWord ++ tailWord_7800768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800768).length < 2 ^ (prefixWord ++ tailWord_7800768).sum := by decide
  have hdescent : baseEnd_7800768 < baseStart_7800768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800784 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 7]
def baseStart_7800784 : Nat := 118140960795 + 7800784 * 2 ^ 59
def prefixEnd_7800784 : Nat := 4983230072969 + 3 ^ 40 * 7800784 * 2
def baseEnd_7800784 : Nat := 4005551673902712630424853

theorem tailTrace_7800784 : CollatzResearch.WordTrace tailWord_7800784 prefixEnd_7800784 4005551673902712630424853 := by
  unfold tailWord_7800784
  simp only [CollatzResearch.WordTrace]
  refine ⟨142258983285549655342524703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189678644380732873790032937 142258983285549655342524703)
  ·
    refine ⟨213388474928324483013787055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142258983285549655342524703 213388474928324483013787055)
    ·
      refine ⟨320082712392486724520680583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213388474928324483013787055 320082712392486724520680583)
      ·
        refine ⟨480124068588730086781020875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320082712392486724520680583 480124068588730086781020875)
        ·
          refine ⟨720186102883095130171531313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480124068588730086781020875 720186102883095130171531313)
          ·
            refine ⟨540139577162321347628648485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720186102883095130171531313 540139577162321347628648485)
            ·
              refine ⟨101276170717935252680371591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540139577162321347628648485 101276170717935252680371591)
              ·
                refine ⟨151914256076902879020557387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101276170717935252680371591 151914256076902879020557387)
                ·
                  refine ⟨227871384115354318530836081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151914256076902879020557387 227871384115354318530836081)
                  ·
                    refine ⟨170903538086515738898127061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 227871384115354318530836081 170903538086515738898127061)
                    ·
                      refine ⟨4005551673902712630424853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170903538086515738898127061 4005551673902712630424853)
                      ·
                        rfl

theorem cell23_7800784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_7800784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800784 prefixEnd_7800784 := by exact prefixLift 7800784
  have htrace : WordTrace (prefixWord ++ tailWord_7800784) baseStart_7800784 baseEnd_7800784 := by
    simpa [prefixWord, tailWord_7800784, baseEnd_7800784] using wordTrace_append hprefix tailTrace_7800784
  have hstable : (prefixWord ++ tailWord_7800784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800784).length < 2 ^ (prefixWord ++ tailWord_7800784).sum := by decide
  have hdescent : baseEnd_7800784 < baseStart_7800784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800801 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_7800801 : Nat := 118140960795 + 7800801 * 2 ^ 59
def prefixEnd_7800801 : Nat := 4983230072969 + 3 ^ 40 * 7800801 * 2
def baseEnd_7800801 : Nat := 4005560403073839063912275

theorem tailTrace_7800801 : CollatzResearch.WordTrace tailWord_7800801 prefixEnd_7800801 4005560403073839063912275 := by
  unfold tailWord_7800801
  simp only [CollatzResearch.WordTrace]
  refine ⟨284518586612037722588418257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189679057741358481725612171 284518586612037722588418257)
  ·
    refine ⟨213388939959028291941313693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284518586612037722588418257 213388939959028291941313693)
    ·
      refine ⟨80020852484635609477992635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213388939959028291941313693 80020852484635609477992635)
      ·
        refine ⟨120031278726953414216988953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80020852484635609477992635 120031278726953414216988953)
        ·
          refine ⟨90023459045215060662741715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120031278726953414216988953 90023459045215060662741715)
          ·
            refine ⟨135035188567822590994112573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90023459045215060662741715 135035188567822590994112573)
            ·
              refine ⟨50638195712933471622792215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135035188567822590994112573 50638195712933471622792215)
              ·
                refine ⟨75957293569400207434188323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50638195712933471622792215 75957293569400207434188323)
                ·
                  refine ⟨113935940354100311151282485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75957293569400207434188323 113935940354100311151282485)
                  ·
                    refine ⟨10681494408196904170432733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113935940354100311151282485 10681494408196904170432733)
                    ·
                      refine ⟨4005560403073839063912275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10681494408196904170432733 4005560403073839063912275)
                      ·
                        rfl

theorem cell23_7800801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_7800801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800801 prefixEnd_7800801 := by exact prefixLift 7800801
  have htrace : WordTrace (prefixWord ++ tailWord_7800801) baseStart_7800801 baseEnd_7800801 := by
    simpa [prefixWord, tailWord_7800801, baseEnd_7800801] using wordTrace_append hprefix tailTrace_7800801
  have hstable : (prefixWord ++ tailWord_7800801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800801).length < 2 ^ (prefixWord ++ tailWord_7800801).sum := by decide
  have hdescent : baseEnd_7800801 < baseStart_7800801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800836 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_7800836 : Nat := 118140960795 + 7800836 * 2 ^ 59
def prefixEnd_7800836 : Nat := 4983230072969 + 3 ^ 40 * 7800836 * 2
def baseEnd_7800836 : Nat := 4005578374896746426974615

theorem tailTrace_7800836 : CollatzResearch.WordTrace tailWord_7800836 prefixEnd_7800836 4005578374896746426974615 := by
  unfold tailWord_7800836
  simp only [CollatzResearch.WordTrace]
  refine ⟨142259931583455461782971181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189679908777940615710628241 142259931583455461782971181)
  ·
    refine ⟨53347474343795798168614193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142259931583455461782971181 53347474343795798168614193)
    ·
      refine ⟨40010605757846848626460645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53347474343795798168614193 40010605757846848626460645)
      ·
        refine ⟨7501988579596284117461371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40010605757846848626460645 7501988579596284117461371)
        ·
          refine ⟨11252982869394426176192057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7501988579596284117461371 11252982869394426176192057)
          ·
            refine ⟨8439737152045819632144043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11252982869394426176192057 8439737152045819632144043)
            ·
              refine ⟨12659605728068729448216065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8439737152045819632144043 12659605728068729448216065)
              ·
                refine ⟨9494704296051547086162049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12659605728068729448216065 9494704296051547086162049)
                ·
                  refine ⟨7121028222038660314621537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9494704296051547086162049 7121028222038660314621537)
                  ·
                    refine ⟨5340771166528995235966153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7121028222038660314621537 5340771166528995235966153)
                    ·
                      refine ⟨4005578374896746426974615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340771166528995235966153 4005578374896746426974615)
                      ·
                        rfl

theorem cell23_7800836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_7800836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800836 prefixEnd_7800836 := by exact prefixLift 7800836
  have htrace : WordTrace (prefixWord ++ tailWord_7800836) baseStart_7800836 baseEnd_7800836 := by
    simpa [prefixWord, tailWord_7800836, baseEnd_7800836] using wordTrace_append hprefix tailTrace_7800836
  have hstable : (prefixWord ++ tailWord_7800836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800836).length < 2 ^ (prefixWord ++ tailWord_7800836).sum := by decide
  have hdescent : baseEnd_7800836 < baseStart_7800836 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800881 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 8]
def baseStart_7800881 : Nat := 118140960795 + 7800881 * 2 ^ 59
def prefixEnd_7800881 : Nat := 4983230072969 + 3 ^ 40 * 7800881 * 2
def baseEnd_7800881 : Nat := 445066831280688750101323

theorem tailTrace_7800881 : CollatzResearch.WordTrace tailWord_7800881 prefixEnd_7800881 445066831280688750101323 := by
  unfold tailWord_7800881
  simp only [CollatzResearch.WordTrace]
  refine ⟨284521504451747896251330497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189681002967831930834220331 284521504451747896251330497)
  ·
    refine ⟨213391128338810922188497873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284521504451747896251330497 213391128338810922188497873)
    ·
      refine ⟨160043346254108191641373405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213391128338810922188497873 160043346254108191641373405)
      ·
        refine ⟨60016254845290571865515027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160043346254108191641373405 60016254845290571865515027)
        ·
          refine ⟨90024382267935857798272541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60016254845290571865515027 90024382267935857798272541)
          ·
            refine ⟨33759143350475946674352203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90024382267935857798272541 33759143350475946674352203)
            ·
              refine ⟨50638715025713920011528305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33759143350475946674352203 50638715025713920011528305)
              ·
                refine ⟨37979036269285440008646229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50638715025713920011528305 37979036269285440008646229)
                ·
                  refine ⟨445066831280688750101323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37979036269285440008646229 445066831280688750101323)
                  ·
                    rfl

theorem cell23_7800881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 8].length) (baseStart_7800881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800881 prefixEnd_7800881 := by exact prefixLift 7800881
  have htrace : WordTrace (prefixWord ++ tailWord_7800881) baseStart_7800881 baseEnd_7800881 := by
    simpa [prefixWord, tailWord_7800881, baseEnd_7800881] using wordTrace_append hprefix tailTrace_7800881
  have hstable : (prefixWord ++ tailWord_7800881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800881).length < 2 ^ (prefixWord ++ tailWord_7800881).sum := by decide
  have hdescent : baseEnd_7800881 < baseStart_7800881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800891 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 3]
def baseStart_7800891 : Nat := 118140960795 + 7800891 * 2 ^ 59
def prefixEnd_7800891 : Nat := 4983230072969 + 3 ^ 40 * 7800891 * 2
def baseEnd_7800891 : Nat := 4005606616332743711786861

theorem tailTrace_7800891 : CollatzResearch.WordTrace tailWord_7800891 prefixEnd_7800891 4005606616332743711786861 := by
  unfold tailWord_7800891
  simp only [CollatzResearch.WordTrace]
  refine ⟨284521869181711667959194527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189681246121141111972796351 284521869181711667959194527)
  ·
    refine ⟨426782803772567501938791791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284521869181711667959194527 426782803772567501938791791)
    ·
      refine ⟨640174205658851252908187687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426782803772567501938791791 640174205658851252908187687)
      ·
        refine ⟨960261308488276879362281531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640174205658851252908187687 960261308488276879362281531)
        ·
          refine ⟨1440391962732415319043422297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960261308488276879362281531 1440391962732415319043422297)
          ·
            refine ⟨1080293972049311489282566723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1440391962732415319043422297 1080293972049311489282566723)
            ·
              refine ⟨1620440958073967233923850085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080293972049311489282566723 1620440958073967233923850085)
              ·
                refine ⟨303832679638868856360721891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1620440958073967233923850085 303832679638868856360721891)
                ·
                  refine ⟨455749019458303284541082837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303832679638868856360721891 455749019458303284541082837)
                  ·
                    refine ⟨10681617643553983231431629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 455749019458303284541082837 10681617643553983231431629)
                    ·
                      refine ⟨4005606616332743711786861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10681617643553983231431629 4005606616332743711786861)
                      ·
                        rfl

theorem cell23_7800891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 7, 3].length) (baseStart_7800891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800891 prefixEnd_7800891 := by exact prefixLift 7800891
  have htrace : WordTrace (prefixWord ++ tailWord_7800891) baseStart_7800891 baseEnd_7800891 := by
    simpa [prefixWord, tailWord_7800891, baseEnd_7800891] using wordTrace_append hprefix tailTrace_7800891
  have hstable : (prefixWord ++ tailWord_7800891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800891).length < 2 ^ (prefixWord ++ tailWord_7800891).sum := by decide
  have hdescent : baseEnd_7800891 < baseStart_7800891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800911 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 5, 5]
def baseStart_7800911 : Nat := 118140960795 + 7800911 * 2 ^ 59
def prefixEnd_7800911 : Nat := 4983230072969 + 3 ^ 40 * 7800911 * 2
def baseEnd_7800911 : Nat := 1335205628648611211178923

theorem tailTrace_7800911 : CollatzResearch.WordTrace tailWord_7800911 prefixEnd_7800911 1335205628648611211178923 := by
  unfold tailWord_7800911
  simp only [CollatzResearch.WordTrace]
  refine ⟨284522598641639211374922587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189681732427759474249948391 284522598641639211374922587)
  ·
    refine ⟨426783897962458817062383881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284522598641639211374922587 426783897962458817062383881)
    ·
      refine ⟨320087923471844112796787911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426783897962458817062383881 320087923471844112796787911)
      ·
        refine ⟨480131885207766169195181867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320087923471844112796787911 480131885207766169195181867)
        ·
          refine ⟨720197827811649253792772801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480131885207766169195181867 720197827811649253792772801)
          ·
            refine ⟨540148370858736940344579601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720197827811649253792772801 540148370858736940344579601)
            ·
              refine ⟨405111278144052705258434701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540148370858736940344579601 405111278144052705258434701)
              ·
                refine ⟨151916729304019764471913013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405111278144052705258434701 151916729304019764471913013)
                ·
                  refine ⟨14242193372251852919241845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151916729304019764471913013 14242193372251852919241845)
                  ·
                    refine ⟨1335205628648611211178923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14242193372251852919241845 1335205628648611211178923)
                    ·
                      rfl

theorem cell23_7800911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_7800911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800911 prefixEnd_7800911 := by exact prefixLift 7800911
  have htrace : WordTrace (prefixWord ++ tailWord_7800911) baseStart_7800911 baseEnd_7800911 := by
    simpa [prefixWord, tailWord_7800911, baseEnd_7800911] using wordTrace_append hprefix tailTrace_7800911
  have hstable : (prefixWord ++ tailWord_7800911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800911).length < 2 ^ (prefixWord ++ tailWord_7800911).sum := by decide
  have hdescent : baseEnd_7800911 < baseStart_7800911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800928 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 3, 5]
def baseStart_7800928 : Nat := 118140960795 + 7800928 * 2 ^ 59
def prefixEnd_7800928 : Nat := 4983230072969 + 3 ^ 40 * 7800928 * 2
def baseEnd_7800928 : Nat := 1335208538372320022341397

theorem tailTrace_7800928 : CollatzResearch.WordTrace tailWord_7800928 prefixEnd_7800928 1335208538372320022341397 := by
  unfold tailWord_7800928
  simp only [CollatzResearch.WordTrace]
  refine ⟨142261609341288811639145719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189682145788385082185527625 142261609341288811639145719)
  ·
    refine ⟨213392414011933217458718579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142261609341288811639145719 213392414011933217458718579)
    ·
      refine ⟨320088621017899826188077869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213392414011933217458718579 320088621017899826188077869)
      ·
        refine ⟨120033232881712434820529201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320088621017899826188077869 120033232881712434820529201)
        ·
          refine ⟨90024924661284326115396901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120033232881712434820529201 90024924661284326115396901)
          ·
            refine ⟨16879673373990811146636919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90024924661284326115396901 16879673373990811146636919)
            ·
              refine ⟨25319510060986216719955379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16879673373990811146636919 25319510060986216719955379)
              ·
                refine ⟨37979265091479325079933069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25319510060986216719955379 37979265091479325079933069)
                ·
                  refine ⟨14242224409304746904974901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37979265091479325079933069 14242224409304746904974901)
                  ·
                    refine ⟨1335208538372320022341397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14242224409304746904974901 1335208538372320022341397)
                    ·
                      rfl

theorem cell23_7800928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 5].length) (baseStart_7800928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800928 prefixEnd_7800928 := by exact prefixLift 7800928
  have htrace : WordTrace (prefixWord ++ tailWord_7800928) baseStart_7800928 baseEnd_7800928 := by
    simpa [prefixWord, tailWord_7800928, baseEnd_7800928] using wordTrace_append hprefix tailTrace_7800928
  have hstable : (prefixWord ++ tailWord_7800928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800928).length < 2 ^ (prefixWord ++ tailWord_7800928).sum := by decide
  have hdescent : baseEnd_7800928 < baseStart_7800928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800945 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 1, 5]
def baseStart_7800945 : Nat := 118140960795 + 7800945 * 2 ^ 59
def prefixEnd_7800945 : Nat := 4983230072969 + 3 ^ 40 * 7800945 * 2
def baseEnd_7800945 : Nat := 1335211448096028833503871

theorem tailTrace_7800945 : CollatzResearch.WordTrace tailWord_7800945 prefixEnd_7800945 1335211448096028833503871 := by
  unfold tailWord_7800945
  simp only [CollatzResearch.WordTrace]
  refine ⟨284523838723516035181660289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189682559149010690121106859 284523838723516035181660289)
  ·
    refine ⟨213392879042637026386245217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284523838723516035181660289 213392879042637026386245217)
    ·
      refine ⟨160044659281977769789683913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213392879042637026386245217 160044659281977769789683913)
      ·
        refine ⟨120033494461483327342262935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160044659281977769789683913 120033494461483327342262935)
        ·
          refine ⟨180050241692224991013394403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120033494461483327342262935 180050241692224991013394403)
          ·
            refine ⟨270075362538337486520091605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180050241692224991013394403 270075362538337486520091605)
            ·
              refine ⟨6329891309492284840314647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 270075362538337486520091605 6329891309492284840314647)
              ·
                refine ⟨9494836964238427260471971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6329891309492284840314647 9494836964238427260471971)
                ·
                  refine ⟨14242255446357640890707957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9494836964238427260471971 14242255446357640890707957)
                  ·
                    refine ⟨1335211448096028833503871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14242255446357640890707957 1335211448096028833503871)
                    ·
                      rfl

theorem cell23_7800945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_7800945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800945 prefixEnd_7800945 := by exact prefixLift 7800945
  have htrace : WordTrace (prefixWord ++ tailWord_7800945) baseStart_7800945 baseEnd_7800945 := by
    simpa [prefixWord, tailWord_7800945, baseEnd_7800945] using wordTrace_append hprefix tailTrace_7800945
  have hstable : (prefixWord ++ tailWord_7800945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800945).length < 2 ^ (prefixWord ++ tailWord_7800945).sum := by decide
  have hdescent : baseEnd_7800945 < baseStart_7800945 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7800986 : List Nat := [3, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2]
def baseStart_7800986 : Nat := 118140960795 + 7800986 * 2 ^ 59
def prefixEnd_7800986 : Nat := 4983230072969 + 3 ^ 40 * 7800986 * 2
def baseEnd_7800986 : Nat := 4005655396994920840098925

theorem tailTrace_7800986 : CollatzResearch.WordTrace tailWord_7800986 prefixEnd_7800986 4005655396994920840098925 := by
  unfold tailWord_7800986
  simp only [CollatzResearch.WordTrace]
  refine ⟨71131333529091874795975703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189683556077578332789268541 71131333529091874795975703)
  ·
    refine ⟨106697000293637812193963555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71131333529091874795975703 106697000293637812193963555)
    ·
      refine ⟨160045500440456718290945333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106697000293637812193963555 160045500440456718290945333)
      ·
        refine ⟨15004265666292817339776125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160045500440456718290945333 15004265666292817339776125)
        ·
          refine ⟨5626599624859806502416047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15004265666292817339776125 5626599624859806502416047)
          ·
            refine ⟨8439899437289709753624071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5626599624859806502416047 8439899437289709753624071)
            ·
              refine ⟨12659849155934564630436107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8439899437289709753624071 12659849155934564630436107)
              ·
                refine ⟨18989773733901846945654161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12659849155934564630436107 18989773733901846945654161)
                ·
                  refine ⟨14242330300426385209240621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18989773733901846945654161 14242330300426385209240621)
                  ·
                    refine ⟨5340873862659894453465233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14242330300426385209240621 5340873862659894453465233)
                    ·
                      refine ⟨4005655396994920840098925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340873862659894453465233 4005655396994920840098925)
                      ·
                        rfl

theorem cell23_7800986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_7800986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7800986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7800986 prefixEnd_7800986 := by exact prefixLift 7800986
  have htrace : WordTrace (prefixWord ++ tailWord_7800986) baseStart_7800986 baseEnd_7800986 := by
    simpa [prefixWord, tailWord_7800986, baseEnd_7800986] using wordTrace_append hprefix tailTrace_7800986
  have hstable : (prefixWord ++ tailWord_7800986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7800986).length < 2 ^ (prefixWord ++ tailWord_7800986).sum := by decide
  have hdescent : baseEnd_7800986 < baseStart_7800986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7800986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801009 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 2, 4]
def baseStart_7801009 : Nat := 118140960795 + 7801009 * 2 ^ 59
def prefixEnd_7801009 : Nat := 4983230072969 + 3 ^ 40 * 7801009 * 2
def baseEnd_7801009 : Nat := 1335222402349991416703773

theorem tailTrace_7801009 : CollatzResearch.WordTrace tailWord_7801009 prefixEnd_7801009 1335222402349991416703773 := by
  unfold tailWord_7801009
  simp only [CollatzResearch.WordTrace]
  refine ⟨284526172995284174111990081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189684115330189449407993387 284526172995284174111990081)
  ·
    refine ⟨213394629746463130583992561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284526172995284174111990081 213394629746463130583992561)
    ·
      refine ⟨160045972309847347937994421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213394629746463130583992561 160045972309847347937994421)
      ·
        refine ⟨15004309904048188869186977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160045972309847347937994421 15004309904048188869186977)
        ·
          refine ⟨11253232428036141651890233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15004309904048188869186977 11253232428036141651890233)
          ·
            refine ⟨8439924321027106238917675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11253232428036141651890233 8439924321027106238917675)
            ·
              refine ⟨12659886481540659358376513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8439924321027106238917675 12659886481540659358376513)
              ·
                refine ⟨9494914861155494518782385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12659886481540659358376513 9494914861155494518782385)
                ·
                  refine ⟨7121186145866620889086789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9494914861155494518782385 7121186145866620889086789)
                  ·
                    refine ⟨1335222402349991416703773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7121186145866620889086789 1335222402349991416703773)
                    ·
                      rfl

theorem cell23_7801009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 4].length) (baseStart_7801009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801009 prefixEnd_7801009 := by exact prefixLift 7801009
  have htrace : WordTrace (prefixWord ++ tailWord_7801009) baseStart_7801009 baseEnd_7801009 := by
    simpa [prefixWord, tailWord_7801009, baseEnd_7801009] using wordTrace_append hprefix tailTrace_7801009
  have hstable : (prefixWord ++ tailWord_7801009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801009).length < 2 ^ (prefixWord ++ tailWord_7801009).sum := by decide
  have hdescent : baseEnd_7801009 < baseStart_7801009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801055 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 3, 4, 2]
def baseStart_7801055 : Nat := 118140960795 + 7801055 * 2 ^ 59
def prefixEnd_7801055 : Nat := 4983230072969 + 3 ^ 40 * 7801055 * 2
def baseEnd_7801055 : Nat := 4005690827160081070136107

theorem tailTrace_7801055 : CollatzResearch.WordTrace tailWord_7801055 prefixEnd_7801055 4005690827160081070136107 := by
  unfold tailWord_7801055
  simp only [CollatzResearch.WordTrace]
  refine ⟨284527850753117523968164619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189685233835411682645443079 284527850753117523968164619)
  ·
    refine ⟨426791776129676285952246929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284527850753117523968164619 426791776129676285952246929)
    ·
      refine ⟨320093832097257214464185197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426791776129676285952246929 320093832097257214464185197)
      ·
        refine ⟨120035187036471455424069449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320093832097257214464185197 120035187036471455424069449)
        ·
          refine ⟨90026390277353591568052087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120035187036471455424069449 90026390277353591568052087)
          ·
            refine ⟨135039585416030387352078131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90026390277353591568052087 135039585416030387352078131)
            ·
              refine ⟨202559378124045581028117197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135039585416030387352078131 202559378124045581028117197)
              ·
                refine ⟨75959766796517092885543949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202559378124045581028117197 75959766796517092885543949)
                ·
                  refine ⟨28484912548693909832078981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75959766796517092885543949 28484912548693909832078981)
                  ·
                    refine ⟨5340921102880108093514809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28484912548693909832078981 5340921102880108093514809)
                    ·
                      refine ⟨4005690827160081070136107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340921102880108093514809 4005690827160081070136107)
                      ·
                        rfl

theorem cell23_7801055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_7801055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801055 prefixEnd_7801055 := by exact prefixLift 7801055
  have htrace : WordTrace (prefixWord ++ tailWord_7801055) baseStart_7801055 baseEnd_7801055 := by
    simpa [prefixWord, tailWord_7801055, baseEnd_7801055] using wordTrace_append hprefix tailTrace_7801055
  have hstable : (prefixWord ++ tailWord_7801055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801055).length < 2 ^ (prefixWord ++ tailWord_7801055).sum := by decide
  have hdescent : baseEnd_7801055 < baseStart_7801055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801089 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 2, 2, 2]
def baseStart_7801089 : Nat := 118140960795 + 7801089 * 2 ^ 59
def prefixEnd_7801089 : Nat := 4983230072969 + 3 ^ 40 * 7801089 * 2
def baseEnd_7801089 : Nat := 4005708285502333937110951

theorem tailTrace_7801089 : CollatzResearch.WordTrace tailWord_7801089 prefixEnd_7801089 4005708285502333937110951 := by
  unfold tailWord_7801089
  simp only [CollatzResearch.WordTrace]
  refine ⟨284529090834994347774902321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189686060556662898516601547 284529090834994347774902321)
  ·
    refine ⟨213396818126245760831176741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284529090834994347774902321 213396818126245760831176741)
    ·
      refine ⟨40011903398671080155845639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213396818126245760831176741 40011903398671080155845639)
      ·
        refine ⟨60017855098006620233768459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40011903398671080155845639 60017855098006620233768459)
        ·
          refine ⟨90026782647009930350652689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60017855098006620233768459 90026782647009930350652689)
          ·
            refine ⟨67520086985257447762989517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90026782647009930350652689 67520086985257447762989517)
            ·
              refine ⟨25320032619471542911121069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67520086985257447762989517 25320032619471542911121069)
              ·
                refine ⟨9495012232301828591670401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25320032619471542911121069 9495012232301828591670401)
                ·
                  refine ⟨7121259174226371443752801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9495012232301828591670401 7121259174226371443752801)
                  ·
                    refine ⟨5340944380669778582814601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7121259174226371443752801 5340944380669778582814601)
                    ·
                      refine ⟨4005708285502333937110951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5340944380669778582814601 4005708285502333937110951)
                      ·
                        rfl

theorem cell23_7801089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_7801089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801089 prefixEnd_7801089 := by exact prefixLift 7801089
  have htrace : WordTrace (prefixWord ++ tailWord_7801089) baseStart_7801089 baseEnd_7801089 := by
    simpa [prefixWord, tailWord_7801089, baseEnd_7801089] using wordTrace_append hprefix tailTrace_7801089
  have hstable : (prefixWord ++ tailWord_7801089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801089).length < 2 ^ (prefixWord ++ tailWord_7801089).sum := by decide
  have hdescent : baseEnd_7801089 < baseStart_7801089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801155 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 5, 4]
def baseStart_7801155 : Nat := 118140960795 + 7801155 * 2 ^ 59
def prefixEnd_7801155 : Nat := 4983230072969 + 3 ^ 40 * 7801155 * 2
def baseEnd_7801155 : Nat := 1335247391741843559628549

theorem tailTrace_7801155 : CollatzResearch.WordTrace tailWord_7801155 prefixEnd_7801155 1335247391741843559628549 := by
  unfold tailWord_7801155
  simp only [CollatzResearch.WordTrace]
  refine ⟨284531498052755241046804919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189687665368503494031203279 284531498052755241046804919)
  ·
    refine ⟨426797247079132861570207379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284531498052755241046804919 426797247079132861570207379)
    ·
      refine ⟨640195870618699292355311069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426797247079132861570207379 640195870618699292355311069)
      ·
        refine ⟨240073451482012234633241651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640195870618699292355311069 240073451482012234633241651)
        ·
          refine ⟨360110177223018351949862477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240073451482012234633241651 360110177223018351949862477)
          ·
            refine ⟨135041316458631881981198429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360110177223018351949862477 135041316458631881981198429)
            ·
              refine ⟨50640493671986955742949411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135041316458631881981198429 50640493671986955742949411)
              ·
                refine ⟨75960740507980433614424117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50640493671986955742949411 75960740507980433614424117)
                ·
                  refine ⟨7121319422623165651352261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75960740507980433614424117 7121319422623165651352261)
                  ·
                    refine ⟨1335247391741843559628549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7121319422623165651352261 1335247391741843559628549)
                    ·
                      rfl

theorem cell23_7801155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 4].length) (baseStart_7801155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801155 prefixEnd_7801155 := by exact prefixLift 7801155
  have htrace : WordTrace (prefixWord ++ tailWord_7801155) baseStart_7801155 baseEnd_7801155 := by
    simpa [prefixWord, tailWord_7801155, baseEnd_7801155] using wordTrace_append hprefix tailTrace_7801155
  have hstable : (prefixWord ++ tailWord_7801155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801155).length < 2 ^ (prefixWord ++ tailWord_7801155).sum := by decide
  have hdescent : baseEnd_7801155 < baseStart_7801155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801189 : List Nat := [1, 3, 1, 3, 1, 3, 2, 4, 1, 4]
def baseStart_7801189 : Nat := 118140960795 + 7801189 * 2 ^ 59
def prefixEnd_7801189 : Nat := 4983230072969 + 3 ^ 40 * 7801189 * 2
def baseEnd_7801189 : Nat := 1335253211189261181953497

theorem tailTrace_7801189 : CollatzResearch.WordTrace tailWord_7801189 prefixEnd_7801189 1335253211189261181953497 := by
  unfold tailWord_7801189
  simp only [CollatzResearch.WordTrace]
  refine ⟨284532738134632064853542621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189688492089754709902361747 284532738134632064853542621)
  ·
    refine ⟨106699776800487024320078483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284532738134632064853542621 106699776800487024320078483)
    ·
      refine ⟨160049665200730536480117725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106699776800487024320078483 160049665200730536480117725)
      ·
        refine ⟨60018624450273951180044147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160049665200730536480117725 60018624450273951180044147)
        ·
          refine ⟨90027936675410926770066221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60018624450273951180044147 90027936675410926770066221)
          ·
            refine ⟨33760476253279097538774833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90027936675410926770066221 33760476253279097538774833)
            ·
              refine ⟨25320357189959323154081125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33760476253279097538774833 25320357189959323154081125)
              ·
                refine ⟨4747566973117373091390211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25320357189959323154081125 4747566973117373091390211)
                ·
                  refine ⟨7121350459676059637085317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4747566973117373091390211 7121350459676059637085317)
                  ·
                    refine ⟨1335253211189261181953497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7121350459676059637085317 1335253211189261181953497)
                    ·
                      rfl

theorem cell23_7801189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_7801189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801189 prefixEnd_7801189 := by exact prefixLift 7801189
  have htrace : WordTrace (prefixWord ++ tailWord_7801189) baseStart_7801189 baseEnd_7801189 := by
    simpa [prefixWord, tailWord_7801189, baseEnd_7801189] using wordTrace_append hprefix tailTrace_7801189
  have hstable : (prefixWord ++ tailWord_7801189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801189).length < 2 ^ (prefixWord ++ tailWord_7801189).sum := by decide
  have hdescent : baseEnd_7801189 < baseStart_7801189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801212 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_7801212 : Nat := 118140960795 + 7801212 * 2 ^ 59
def prefixEnd_7801212 : Nat := 4983230072969 + 3 ^ 40 * 7801212 * 2
def baseEnd_7801212 : Nat := 4005771443622836955872885

theorem tailTrace_7801212 : CollatzResearch.WordTrace tailWord_7801212 prefixEnd_7801212 4005771443622836955872885 := by
  unfold tailWord_7801212
  simp only [CollatzResearch.WordTrace]
  refine ⟨142266788506774369890814945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189689051342365826521086593 142266788506774369890814945)
  ·
    refine ⟨106700091380080777418111209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142266788506774369890814945 106700091380080777418111209)
    ·
      refine ⟨80025068535060583063583407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106700091380080777418111209 80025068535060583063583407)
      ·
        refine ⟨120037602802590874595375111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80025068535060583063583407 120037602802590874595375111)
        ·
          refine ⟨180056404203886311893062667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120037602802590874595375111 180056404203886311893062667)
          ·
            refine ⟨270084606305829467839594001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180056404203886311893062667 270084606305829467839594001)
            ·
              refine ⟨202563454729372100879695501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270084606305829467839594001 202563454729372100879695501)
              ·
                refine ⟨75961295523514537829885813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202563454729372100879695501 75961295523514537829885813)
                ·
                  refine ⟨7121371455329487921551795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75961295523514537829885813 7121371455329487921551795)
                  ·
                    refine ⟨10682057182994231882327693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7121371455329487921551795 10682057182994231882327693)
                    ·
                      refine ⟨4005771443622836955872885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10682057182994231882327693 4005771443622836955872885)
                      ·
                        rfl

theorem cell23_7801212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_7801212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801212 prefixEnd_7801212 := by exact prefixLift 7801212
  have htrace : WordTrace (prefixWord ++ tailWord_7801212) baseStart_7801212 baseEnd_7801212 := by
    simpa [prefixWord, tailWord_7801212, baseEnd_7801212] using wordTrace_append hprefix tailTrace_7801212
  have hstable : (prefixWord ++ tailWord_7801212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801212).length < 2 ^ (prefixWord ++ tailWord_7801212).sum := by decide
  have hdescent : baseEnd_7801212 < baseStart_7801212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801269 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_7801269 : Nat := 118140960795 + 7801269 * 2 ^ 59
def prefixEnd_7801269 : Nat := 4983230072969 + 3 ^ 40 * 7801269 * 2
def baseEnd_7801269 : Nat := 4005800712020143232860123

theorem tailTrace_7801269 : CollatzResearch.WordTrace tailWord_7801269 prefixEnd_7801269 4005800712020143232860123 := by
  unfold tailWord_7801269
  simp only [CollatzResearch.WordTrace]
  refine ⟨284535655974342238516454861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189690437316228159010969907 284535655974342238516454861)
  ·
    refine ⟨106700870990378339443670573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284535655974342238516454861 106700870990378339443670573)
    ·
      refine ⟨40012826621391877291376465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106700870990378339443670573 40012826621391877291376465)
      ·
        refine ⟨30009619966043907968532349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40012826621391877291376465 30009619966043907968532349)
        ·
          refine ⟨11253607487266465488199631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30009619966043907968532349 11253607487266465488199631)
          ·
            refine ⟨16880411230899698232299447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11253607487266465488199631 16880411230899698232299447)
            ·
              refine ⟨25320616846349547348449171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16880411230899698232299447 25320616846349547348449171)
              ·
                refine ⟨37980925269524321022673757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25320616846349547348449171 37980925269524321022673757)
                ·
                  refine ⟨14242846976071620383502659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37980925269524321022673757 14242846976071620383502659)
                  ·
                    refine ⟨21364270464107430575253989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14242846976071620383502659 21364270464107430575253989)
                    ·
                      refine ⟨4005800712020143232860123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21364270464107430575253989 4005800712020143232860123)
                      ·
                        rfl

theorem cell23_7801269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_7801269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801269 prefixEnd_7801269 := by exact prefixLift 7801269
  have htrace : WordTrace (prefixWord ++ tailWord_7801269) baseStart_7801269 baseEnd_7801269 := by
    simpa [prefixWord, tailWord_7801269, baseEnd_7801269] using wordTrace_append hprefix tailTrace_7801269
  have hstable : (prefixWord ++ tailWord_7801269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801269).length < 2 ^ (prefixWord ++ tailWord_7801269).sum := by decide
  have hdescent : baseEnd_7801269 < baseStart_7801269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801292 : List Nat := [2, 2, 1, 4, 4, 10]
def baseStart_7801292 : Nat := 118140960795 + 7801292 * 2 ^ 59
def prefixEnd_7801292 : Nat := 4983230072969 + 3 ^ 40 * 7801292 * 2
def baseEnd_7801292 : Nat := 16484825193725089065319

theorem tailTrace_7801292 : CollatzResearch.WordTrace tailWord_7801292 prefixEnd_7801292 16484825193725089065319 := by
  unfold tailWord_7801292
  simp only [CollatzResearch.WordTrace]
  refine ⟨142268247426629456722271065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189690996568839275629694753 142268247426629456722271065)
  ·
    refine ⟨106701185569972092541703299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142268247426629456722271065 106701185569972092541703299)
    ·
      refine ⟨160051778354958138812554949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106701185569972092541703299 160051778354958138812554949)
      ·
        refine ⟨30009708441554651027354053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160051778354958138812554949 30009708441554651027354053)
        ·
          refine ⟨5626820332791497067628885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30009708441554651027354053 5626820332791497067628885)
          ·
            refine ⟨16484825193725089065319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5626820332791497067628885 16484825193725089065319)
            ·
              rfl

theorem cell23_7801292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 10].length) (baseStart_7801292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801292 prefixEnd_7801292 := by exact prefixLift 7801292
  have htrace : WordTrace (prefixWord ++ tailWord_7801292) baseStart_7801292 baseEnd_7801292 := by
    simpa [prefixWord, tailWord_7801292, baseEnd_7801292] using wordTrace_append hprefix tailTrace_7801292
  have hstable : (prefixWord ++ tailWord_7801292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801292).length < 2 ^ (prefixWord ++ tailWord_7801292).sum := by decide
  have hdescent : baseEnd_7801292 < baseStart_7801292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801305 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 1, 9]
def baseStart_7801305 : Nat := 118140960795 + 7801305 * 2 ^ 59
def prefixEnd_7801305 : Nat := 4983230072969 + 3 ^ 40 * 7801305 * 2
def baseEnd_7801305 : Nat := 1335273065774568364003319

theorem tailTrace_7801305 : CollatzResearch.WordTrace tailWord_7801305 prefixEnd_7801305 1335273065774568364003319 := by
  unfold tailWord_7801305
  simp only [CollatzResearch.WordTrace]
  refine ⟨284536969002211816664765369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189691312668141211109843579 284536969002211816664765369)
  ·
    refine ⟨213402726751658862498574027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284536969002211816664765369 213402726751658862498574027)
    ·
      refine ⟨320104090127488293747861041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213402726751658862498574027 320104090127488293747861041)
      ·
        refine ⟨240078067595616220310895781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320104090127488293747861041 240078067595616220310895781)
        ·
          refine ⟨45014637674178041308292959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240078067595616220310895781 45014637674178041308292959)
          ·
            refine ⟨67521956511267061962439439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45014637674178041308292959 67521956511267061962439439)
            ·
              refine ⟨101282934766900592943659159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67521956511267061962439439 101282934766900592943659159)
              ·
                refine ⟨151924402150350889415488739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101282934766900592943659159 151924402150350889415488739)
                ·
                  refine ⟨227886603225526334123233109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151924402150350889415488739 227886603225526334123233109)
                  ·
                    refine ⟨1335273065774568364003319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 227886603225526334123233109 1335273065774568364003319)
                    ·
                      rfl

theorem cell23_7801305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 9].length) (baseStart_7801305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801305 prefixEnd_7801305 := by exact prefixLift 7801305
  have htrace : WordTrace (prefixWord ++ tailWord_7801305) baseStart_7801305 baseEnd_7801305 := by
    simpa [prefixWord, tailWord_7801305, baseEnd_7801305] using wordTrace_append hprefix tailTrace_7801305
  have hstable : (prefixWord ++ tailWord_7801305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801305).length < 2 ^ (prefixWord ++ tailWord_7801305).sum := by decide
  have hdescent : baseEnd_7801305 < baseStart_7801305 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801319 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_7801319 : Nat := 118140960795 + 7801319 * 2 ^ 59
def prefixEnd_7801319 : Nat := 4983230072969 + 3 ^ 40 * 7801319 * 2
def baseEnd_7801319 : Nat := 4005826386052868037234893

theorem tailTrace_7801319 : CollatzResearch.WordTrace tailWord_7801319 prefixEnd_7801319 4005826386052868037234893 := by
  unfold tailWord_7801319
  simp only [CollatzResearch.WordTrace]
  refine ⟨284537479624161097055775011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189691653082774064703850007 284537479624161097055775011)
  ·
    refine ⟨426806219436241645583662517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284537479624161097055775011 426806219436241645583662517)
    ·
      refine ⟨40013083072147654273468361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 426806219436241645583662517 40013083072147654273468361)
      ·
        refine ⟨30009812304110740705101271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40013083072147654273468361 30009812304110740705101271)
        ·
          refine ⟨45014718456166111057651907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30009812304110740705101271 45014718456166111057651907)
          ·
            refine ⟨67522077684249166586477861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45014718456166111057651907 67522077684249166586477861)
            ·
              refine ⟨12660389565796718734964599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67522077684249166586477861 12660389565796718734964599)
              ·
                refine ⟨18990584348695078102446899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12660389565796718734964599 18990584348695078102446899)
                ·
                  refine ⟨28485876523042617153670349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18990584348695078102446899 28485876523042617153670349)
                  ·
                    refine ⟨10682203696140981432626381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28485876523042617153670349 10682203696140981432626381)
                    ·
                      refine ⟨4005826386052868037234893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10682203696140981432626381 4005826386052868037234893)
                      ·
                        rfl

theorem cell23_7801319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_7801319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801319 prefixEnd_7801319 := by exact prefixLift 7801319
  have htrace : WordTrace (prefixWord ++ tailWord_7801319) baseStart_7801319 baseEnd_7801319 := by
    simpa [prefixWord, tailWord_7801319, baseEnd_7801319] using wordTrace_append hprefix tailTrace_7801319
  have hstable : (prefixWord ++ tailWord_7801319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801319).length < 2 ^ (prefixWord ++ tailWord_7801319).sum := by decide
  have hdescent : baseEnd_7801319 < baseStart_7801319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801329 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 3, 3, 2]
def baseStart_7801329 : Nat := 118140960795 + 7801329 * 2 ^ 59
def prefixEnd_7801329 : Nat := 4983230072969 + 3 ^ 40 * 7801329 * 2
def baseEnd_7801329 : Nat := 4005831520859412998109847

theorem tailTrace_7801329 : CollatzResearch.WordTrace tailWord_7801329 prefixEnd_7801329 4005831520859412998109847 := by
  unfold tailWord_7801329
  simp only [CollatzResearch.WordTrace]
  refine ⟨284537844354124868763639041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189691896236083245842426027 284537844354124868763639041)
  ·
    refine ⟨213403383265593651572729281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284537844354124868763639041 213403383265593651572729281)
    ·
      refine ⟨160052537449195238679546961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213403383265593651572729281 160052537449195238679546961)
      ·
        refine ⟨120039403086896429009660221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160052537449195238679546961 120039403086896429009660221)
        ·
          refine ⟨45014776157586160878622583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120039403086896429009660221 45014776157586160878622583)
          ·
            refine ⟨67522164236379241317933875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45014776157586160878622583 67522164236379241317933875)
            ·
              refine ⟨101283246354568861976900813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67522164236379241317933875 101283246354568861976900813)
              ·
                refine ⟨37981217382963323241337805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101283246354568861976900813 37981217382963323241337805)
                ·
                  refine ⟨14242956518611246215501677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37981217382963323241337805 14242956518611246215501677)
                  ·
                    refine ⟨5341108694479217330813129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14242956518611246215501677 5341108694479217330813129)
                    ·
                      refine ⟨4005831520859412998109847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341108694479217330813129 4005831520859412998109847)
                      ·
                        rfl

theorem cell23_7801329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_7801329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801329 prefixEnd_7801329 := by exact prefixLift 7801329
  have htrace : WordTrace (prefixWord ++ tailWord_7801329) baseStart_7801329 baseEnd_7801329 := by
    simpa [prefixWord, tailWord_7801329, baseEnd_7801329] using wordTrace_append hprefix tailTrace_7801329
  have hstable : (prefixWord ++ tailWord_7801329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801329).length < 2 ^ (prefixWord ++ tailWord_7801329).sum := by decide
  have hdescent : baseEnd_7801329 < baseStart_7801329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801380 : List Nat := [2, 3, 1, 5, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7801380 : Nat := 118140960795 + 7801380 * 2 ^ 59
def prefixEnd_7801380 : Nat := 4983230072969 + 3 ^ 40 * 7801380 * 2
def baseEnd_7801380 : Nat := 4005857708372792298572113

theorem tailTrace_7801380 : CollatzResearch.WordTrace tailWord_7801380 prefixEnd_7801380 4005857708372792298572113 := by
  unfold tailWord_7801380
  simp only [CollatzResearch.WordTrace]
  refine ⟨142269852238470052236872797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189693136317960069649163729 142269852238470052236872797)
  ·
    refine ⟨53351194589426269588827299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142269852238470052236872797 53351194589426269588827299)
    ·
      refine ⟨80026791884139404383240949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53351194589426269588827299 80026791884139404383240949)
      ·
        refine ⟨7502511739138069160928839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80026791884139404383240949 7502511739138069160928839)
        ·
          refine ⟨11253767608707103741393259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7502511739138069160928839 11253767608707103741393259)
          ·
            refine ⟨16880651413060655612089889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11253767608707103741393259 16880651413060655612089889)
            ·
              refine ⟨12660488559795491709067417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16880651413060655612089889 12660488559795491709067417)
              ·
                refine ⟨9495366419846618781800563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12660488559795491709067417 9495366419846618781800563)
                ·
                  refine ⟨14243049629769928172700845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9495366419846618781800563 14243049629769928172700845)
                  ·
                    refine ⟨5341143611163723064762817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14243049629769928172700845 5341143611163723064762817)
                    ·
                      refine ⟨4005857708372792298572113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341143611163723064762817 4005857708372792298572113)
                      ·
                        rfl

theorem cell23_7801380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7801380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801380 prefixEnd_7801380 := by exact prefixLift 7801380
  have htrace : WordTrace (prefixWord ++ tailWord_7801380) baseStart_7801380 baseEnd_7801380 := by
    simpa [prefixWord, tailWord_7801380, baseEnd_7801380] using wordTrace_append hprefix tailTrace_7801380
  have hstable : (prefixWord ++ tailWord_7801380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801380).length < 2 ^ (prefixWord ++ tailWord_7801380).sum := by decide
  have hdescent : baseEnd_7801380 < baseStart_7801380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801392 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 3]
def baseStart_7801392 : Nat := 118140960795 + 7801392 * 2 ^ 59
def prefixEnd_7801392 : Nat := 4983230072969 + 3 ^ 40 * 7801392 * 2
def baseEnd_7801392 : Nat := 4005863870140646251622057

theorem tailTrace_7801392 : CollatzResearch.WordTrace tailWord_7801392 prefixEnd_7801392 4005863870140646251622057 := by
  unfold tailWord_7801392
  simp only [CollatzResearch.WordTrace]
  refine ⟨142270071076448315261591215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189693428101931087015454953 142270071076448315261591215)
  ·
    refine ⟨213405106614672472892386823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142270071076448315261591215 213405106614672472892386823)
    ·
      refine ⟨320107659922008709338580235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213405106614672472892386823 320107659922008709338580235)
      ·
        refine ⟨480161489883013064007870353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320107659922008709338580235 480161489883013064007870353)
        ·
          refine ⟨360121117412259798005902765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480161489883013064007870353 360121117412259798005902765)
          ·
            refine ⟨135045419029597424252213537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360121117412259798005902765 135045419029597424252213537)
            ·
              refine ⟨101284064272198068189160153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135045419029597424252213537 101284064272198068189160153)
              ·
                refine ⟨75963048204148551141870115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101284064272198068189160153 75963048204148551141870115)
                ·
                  refine ⟨113944572306222826712805173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75963048204148551141870115 113944572306222826712805173)
                  ·
                    refine ⟨10682303653708390004325485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113944572306222826712805173 10682303653708390004325485)
                    ·
                      refine ⟨4005863870140646251622057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10682303653708390004325485 4005863870140646251622057)
                      ·
                        rfl

theorem cell23_7801392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 3].length) (baseStart_7801392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801392 prefixEnd_7801392 := by exact prefixLift 7801392
  have htrace : WordTrace (prefixWord ++ tailWord_7801392) baseStart_7801392 baseEnd_7801392 := by
    simpa [prefixWord, tailWord_7801392, baseEnd_7801392] using wordTrace_append hprefix tailTrace_7801392
  have hstable : (prefixWord ++ tailWord_7801392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801392).length < 2 ^ (prefixWord ++ tailWord_7801392).sum := by decide
  have hdescent : baseEnd_7801392 < baseStart_7801392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801422 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_7801422 : Nat := 118140960795 + 7801422 * 2 ^ 59
def prefixEnd_7801422 : Nat := 4983230072969 + 3 ^ 40 * 7801422 * 2
def baseEnd_7801422 : Nat := 4005879274560281134246919

theorem tailTrace_7801422 : CollatzResearch.WordTrace tailWord_7801422 prefixEnd_7801422 4005879274560281134246919 := by
  unfold tailWord_7801422
  simp only [CollatzResearch.WordTrace]
  refine ⟨35567654542848493205846815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189694157561858630431183013 35567654542848493205846815)
  ·
    refine ⟨53351481814272739808770223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35567654542848493205846815 53351481814272739808770223)
    ·
      refine ⟨80027222721409109713155335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53351481814272739808770223 80027222721409109713155335)
      ·
        refine ⟨120040834082113664569733003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80027222721409109713155335 120040834082113664569733003)
        ·
          refine ⟨180061251123170496854599505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120040834082113664569733003 180061251123170496854599505)
          ·
            refine ⟨135045938342377872640949629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180061251123170496854599505 135045938342377872640949629)
            ·
              refine ⟨50642226878391702240356111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135045938342377872640949629 50642226878391702240356111)
              ·
                refine ⟨75963340317587553360534167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50642226878391702240356111 75963340317587553360534167)
                ·
                  refine ⟨113945010476381330040801251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75963340317587553360534167 113945010476381330040801251)
                  ·
                    refine ⟨170917515714571995061201877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113945010476381330040801251 170917515714571995061201877)
                    ·
                      refine ⟨4005879274560281134246919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 170917515714571995061201877 4005879274560281134246919)
                      ·
                        rfl

theorem cell23_7801422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_7801422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801422 prefixEnd_7801422 := by exact prefixLift 7801422
  have htrace : WordTrace (prefixWord ++ tailWord_7801422) baseStart_7801422 baseEnd_7801422 := by
    simpa [prefixWord, tailWord_7801422, baseEnd_7801422] using wordTrace_append hprefix tailTrace_7801422
  have hstable : (prefixWord ++ tailWord_7801422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801422).length < 2 ^ (prefixWord ++ tailWord_7801422).sum := by decide
  have hdescent : baseEnd_7801422 < baseStart_7801422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801432 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_7801432 : Nat := 118140960795 + 7801432 * 2 ^ 59
def prefixEnd_7801432 : Nat := 4983230072969 + 3 ^ 40 * 7801432 * 2
def baseEnd_7801432 : Nat := 4005884409366826095121873

theorem tailTrace_7801432 : CollatzResearch.WordTrace tailWord_7801432 prefixEnd_7801432 4005884409366826095121873 := by
  unfold tailWord_7801432
  simp only [CollatzResearch.WordTrace]
  refine ⟨142270800536375858677319275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189694400715167811569759033 142270800536375858677319275)
  ·
    refine ⟨213406200804563788015978913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142270800536375858677319275 213406200804563788015978913)
    ·
      refine ⟨160054650603422841011984185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213406200804563788015978913 160054650603422841011984185)
      ·
        refine ⟨120040987952567130758988139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160054650603422841011984185 120040987952567130758988139)
        ·
          refine ⟨180061481928850696138482209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120040987952567130758988139 180061481928850696138482209)
          ·
            refine ⟨135046111446638022103861657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180061481928850696138482209 135046111446638022103861657)
            ·
              refine ⟨101284583584978516577896243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135046111446638022103861657 101284583584978516577896243)
              ·
                refine ⟨151926875377467774866844365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101284583584978516577896243 151926875377467774866844365)
                ·
                  refine ⟨56972578266550415575066637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 151926875377467774866844365 56972578266550415575066637)
                  ·
                    refine ⟨21364716849956405840649989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56972578266550415575066637 21364716849956405840649989)
                    ·
                      refine ⟨4005884409366826095121873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21364716849956405840649989 4005884409366826095121873)
                      ·
                        rfl

theorem cell23_7801432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_7801432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801432 prefixEnd_7801432 := by exact prefixLift 7801432
  have htrace : WordTrace (prefixWord ++ tailWord_7801432) baseStart_7801432 baseEnd_7801432 := by
    simpa [prefixWord, tailWord_7801432, baseEnd_7801432] using wordTrace_append hprefix tailTrace_7801432
  have hstable : (prefixWord ++ tailWord_7801432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801432).length < 2 ^ (prefixWord ++ tailWord_7801432).sum := by decide
  have hdescent : baseEnd_7801432 < baseStart_7801432 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801449 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 4, 4, 2]
def baseStart_7801449 : Nat := 118140960795 + 7801449 * 2 ^ 59
def prefixEnd_7801449 : Nat := 4983230072969 + 3 ^ 40 * 7801449 * 2
def baseEnd_7801449 : Nat := 4005893138537952528609295

theorem tailTrace_7801449 : CollatzResearch.WordTrace tailWord_7801449 prefixEnd_7801449 4005893138537952528609295 := by
  unfold tailWord_7801449
  simp only [CollatzResearch.WordTrace]
  refine ⟨284542221113690129258007401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189694814075793419505338267 284542221113690129258007401)
  ·
    refine ⟨213406665835267596943505551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284542221113690129258007401 213406665835267596943505551)
    ·
      refine ⟨320109998752901395415258327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213406665835267596943505551 320109998752901395415258327)
      ·
        refine ⟨480164998129352093122887491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320109998752901395415258327 480164998129352093122887491)
        ·
          refine ⟨720247497194028139684331237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480164998129352093122887491 720247497194028139684331237)
          ·
            refine ⟨135046405723880276190812107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 720247497194028139684331237 135046405723880276190812107)
            ·
              refine ⟨202569608585820414286218161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135046405723880276190812107 202569608585820414286218161)
              ·
                refine ⟨151927206439365310714663621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202569608585820414286218161 151927206439365310714663621)
                ·
                  refine ⟨28486351207380995758999429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151927206439365310714663621 28486351207380995758999429)
                  ·
                    refine ⟨5341190851383936704812393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28486351207380995758999429 5341190851383936704812393)
                    ·
                      refine ⟨4005893138537952528609295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341190851383936704812393 4005893138537952528609295)
                      ·
                        rfl

theorem cell23_7801449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 4, 2].length) (baseStart_7801449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801449 prefixEnd_7801449 := by exact prefixLift 7801449
  have htrace : WordTrace (prefixWord ++ tailWord_7801449) baseStart_7801449 baseEnd_7801449 := by
    simpa [prefixWord, tailWord_7801449, baseEnd_7801449] using wordTrace_append hprefix tailTrace_7801449
  have hstable : (prefixWord ++ tailWord_7801449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801449).length < 2 ^ (prefixWord ++ tailWord_7801449).sum := by decide
  have hdescent : baseEnd_7801449 < baseStart_7801449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801533 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 3, 1, 3]
def baseStart_7801533 : Nat := 118140960795 + 7801533 * 2 ^ 59
def prefixEnd_7801533 : Nat := 4983230072969 + 3 ^ 40 * 7801533 * 2
def baseEnd_7801533 : Nat := 4005936270912930199958909

theorem tailTrace_7801533 : CollatzResearch.WordTrace tailWord_7801533 prefixEnd_7801533 4005936270912930199958909 := by
  unfold tailWord_7801533
  simp only [CollatzResearch.WordTrace]
  refine ⟨284545284845385811604065253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189696856563590541069376835 284545284845385811604065253)
  ·
    refine ⟨53352240908509839675762235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284545284845385811604065253 53352240908509839675762235)
    ·
      refine ⟨80028361362764759513643353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53352240908509839675762235 80028361362764759513643353)
      ·
        refine ⟨60021271022073569635232515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80028361362764759513643353 60021271022073569635232515)
        ·
          refine ⟨90031906533110354452848773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60021271022073569635232515 90031906533110354452848773)
          ·
            refine ⟨16880982474958191459909145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90031906533110354452848773 16880982474958191459909145)
            ·
              refine ⟨12660736856218643594931859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16880982474958191459909145 12660736856218643594931859)
              ·
                refine ⟨18991105284327965392397789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12660736856218643594931859 18991105284327965392397789)
                ·
                  refine ⟨7121664481622987022149171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18991105284327965392397789 7121664481622987022149171)
                  ·
                    refine ⟨10682496722434480533223757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7121664481622987022149171 10682496722434480533223757)
                    ·
                      refine ⟨4005936270912930199958909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10682496722434480533223757 4005936270912930199958909)
                      ·
                        rfl

theorem cell23_7801533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_7801533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801533 prefixEnd_7801533 := by exact prefixLift 7801533
  have htrace : WordTrace (prefixWord ++ tailWord_7801533) baseStart_7801533 baseEnd_7801533 := by
    simpa [prefixWord, tailWord_7801533, baseEnd_7801533] using wordTrace_append hprefix tailTrace_7801533
  have hstable : (prefixWord ++ tailWord_7801533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801533).length < 2 ^ (prefixWord ++ tailWord_7801533).sum := by decide
  have hdescent : baseEnd_7801533 < baseStart_7801533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801623 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 3]
def baseStart_7801623 : Nat := 118140960795 + 7801623 * 2 ^ 59
def prefixEnd_7801623 : Nat := 4983230072969 + 3 ^ 40 * 7801623 * 2
def baseEnd_7801623 : Nat := 4005982484171834847833495

theorem tailTrace_7801623 : CollatzResearch.WordTrace tailWord_7801623 prefixEnd_7801623 4005982484171834847833495 := by
  unfold tailWord_7801623
  simp only [CollatzResearch.WordTrace]
  refine ⟨284548567415059756974841523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189699044943373171316561015 284548567415059756974841523)
  ·
    refine ⟨426822851122589635462262285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284548567415059756974841523 426822851122589635462262285)
    ·
      refine ⟨160058569170971113298348357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426822851122589635462262285 160058569170971113298348357)
      ·
        refine ⟨30010981719557083743440317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160058569170971113298348357 30010981719557083743440317)
        ·
          refine ⟨11254118144833906403790119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30010981719557083743440317 11254118144833906403790119)
          ·
            refine ⟨16881177217250859605685179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11254118144833906403790119 16881177217250859605685179)
            ·
              refine ⟨25321765825876289408527769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16881177217250859605685179 25321765825876289408527769)
              ·
                refine ⟨18991324369407217056395827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25321765825876289408527769 18991324369407217056395827)
                ·
                  refine ⟨28486986554110825584593741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18991324369407217056395827 28486986554110825584593741)
                  ·
                    refine ⟨10682619957791559594222653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28486986554110825584593741 10682619957791559594222653)
                    ·
                      refine ⟨4005982484171834847833495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10682619957791559594222653 4005982484171834847833495)
                      ·
                        rfl

theorem cell23_7801623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_7801623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801623 prefixEnd_7801623 := by exact prefixLift 7801623
  have htrace : WordTrace (prefixWord ++ tailWord_7801623) baseStart_7801623 baseEnd_7801623 := by
    simpa [prefixWord, tailWord_7801623, baseEnd_7801623] using wordTrace_append hprefix tailTrace_7801623
  have hstable : (prefixWord ++ tailWord_7801623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801623).length < 2 ^ (prefixWord ++ tailWord_7801623).sum := by decide
  have hdescent : baseEnd_7801623 < baseStart_7801623 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801640 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_7801640 : Nat := 118140960795 + 7801640 * 2 ^ 59
def prefixEnd_7801640 : Nat := 4983230072969 + 3 ^ 40 * 7801640 * 2
def baseEnd_7801640 : Nat := 4005991213342961281320917

theorem tailTrace_7801640 : CollatzResearch.WordTrace tailWord_7801640 prefixEnd_7801640 4005991213342961281320917 := by
  unfold tailWord_7801640
  simp only [CollatzResearch.WordTrace]
  refine ⟨142274593727999084439105187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189699458303998779252140249 142274593727999084439105187)
  ·
    refine ⟨213411890591998626658657781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142274593727999084439105187 213411890591998626658657781)
    ·
      refine ⟨20007364742999871249249167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213411890591998626658657781 20007364742999871249249167)
      ·
        refine ⟨30011047114499806873873751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20007364742999871249249167 30011047114499806873873751)
        ·
          refine ⟨45016570671749710310810627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30011047114499806873873751 45016570671749710310810627)
          ·
            refine ⟨67524856007624565466215941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45016570671749710310810627 67524856007624565466215941)
            ·
              refine ⟨12660910501429606024915489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67524856007624565466215941 12660910501429606024915489)
              ·
                refine ⟨9495682876072204518686617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12660910501429606024915489 9495682876072204518686617)
                ·
                  refine ⟨7121762157054153389014963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9495682876072204518686617 7121762157054153389014963)
                  ·
                    refine ⟨10682643235581230083522445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7121762157054153389014963 10682643235581230083522445)
                    ·
                      refine ⟨4005991213342961281320917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10682643235581230083522445 4005991213342961281320917)
                      ·
                        rfl

theorem cell23_7801640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_7801640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801640 prefixEnd_7801640 := by exact prefixLift 7801640
  have htrace : WordTrace (prefixWord ++ tailWord_7801640) baseStart_7801640 baseEnd_7801640 := by
    simpa [prefixWord, tailWord_7801640, baseEnd_7801640] using wordTrace_append hprefix tailTrace_7801640
  have hstable : (prefixWord ++ tailWord_7801640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801640).length < 2 ^ (prefixWord ++ tailWord_7801640).sum := by decide
  have hdescent : baseEnd_7801640 < baseStart_7801640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801663 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 1, 4, 2]
def baseStart_7801663 : Nat := 118140960795 + 7801663 * 2 ^ 59
def prefixEnd_7801663 : Nat := 4983230072969 + 3 ^ 40 * 7801663 * 2
def baseEnd_7801663 : Nat := 4006003023398014691333311

theorem tailTrace_7801663 : CollatzResearch.WordTrace tailWord_7801663 prefixEnd_7801663 4006003023398014691333311 := by
  unfold tailWord_7801663
  simp only [CollatzResearch.WordTrace]
  refine ⟨284550026334914843806297643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189700017556609895870865095 284550026334914843806297643)
  ·
    refine ⟨426825039502372265709446465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284550026334914843806297643 426825039502372265709446465)
    ·
      refine ⟨320118779626779199282084849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426825039502372265709446465 320118779626779199282084849)
      ·
        refine ⟨240089084720084399461563637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320118779626779199282084849 240089084720084399461563637)
        ·
          refine ⟨22508351692507912449521591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240089084720084399461563637 22508351692507912449521591)
          ·
            refine ⟨33762527538761868674282387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22508351692507912449521591 33762527538761868674282387)
            ·
              refine ⟨50643791308142803011423581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33762527538761868674282387 50643791308142803011423581)
              ·
                refine ⟨18991421740553551129283843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50643791308142803011423581 18991421740553551129283843)
                ·
                  refine ⟨28487132610830326693925765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18991421740553551129283843 28487132610830326693925765)
                  ·
                    refine ⟨5341337364530686255111081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28487132610830326693925765 5341337364530686255111081)
                    ·
                      refine ⟨4006003023398014691333311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341337364530686255111081 4006003023398014691333311)
                      ·
                        rfl

theorem cell23_7801663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_7801663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801663 prefixEnd_7801663 := by exact prefixLift 7801663
  have htrace : WordTrace (prefixWord ++ tailWord_7801663) baseStart_7801663 baseEnd_7801663 := by
    simpa [prefixWord, tailWord_7801663, baseEnd_7801663] using wordTrace_append hprefix tailTrace_7801663
  have hstable : (prefixWord ++ tailWord_7801663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801663).length < 2 ^ (prefixWord ++ tailWord_7801663).sum := by decide
  have hdescent : baseEnd_7801663 < baseStart_7801663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801684 : List Nat := [2, 4, 1, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_7801684 : Nat := 118140960795 + 7801684 * 2 ^ 59
def prefixEnd_7801684 : Nat := 4983230072969 + 3 ^ 40 * 7801684 * 2
def baseEnd_7801684 : Nat := 4006013806491759109170715

theorem tailTrace_7801684 : CollatzResearch.WordTrace tailWord_7801684 prefixEnd_7801684 4006013806491759109170715 := by
  unfold tailWord_7801684
  simp only [CollatzResearch.WordTrace]
  refine ⟨142275396133919382196406053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189700528178559176261874737 142275396133919382196406053)
  ·
    refine ⟨26676636775109884161826135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142275396133919382196406053 26676636775109884161826135)
    ·
      refine ⟨40014955162664826242739203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26676636775109884161826135 40014955162664826242739203)
      ·
        refine ⟨60022432743997239364108805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40014955162664826242739203 60022432743997239364108805)
        ·
          refine ⟨11254206139499482380770401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60022432743997239364108805 11254206139499482380770401)
          ·
            refine ⟨8440654604624611785577801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11254206139499482380770401 8440654604624611785577801)
            ·
              refine ⟨6330490953468458839183351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8440654604624611785577801 6330490953468458839183351)
              ·
                refine ⟨9495736430202688258775027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330490953468458839183351 9495736430202688258775027)
                ·
                  refine ⟨14243604645304032388162541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9495736430202688258775027 14243604645304032388162541)
                  ·
                    refine ⟨5341351741989012145560953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14243604645304032388162541 5341351741989012145560953)
                    ·
                      refine ⟨4006013806491759109170715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341351741989012145560953 4006013806491759109170715)
                      ·
                        rfl

theorem cell23_7801684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_7801684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801684 prefixEnd_7801684 := by exact prefixLift 7801684
  have htrace : WordTrace (prefixWord ++ tailWord_7801684) baseStart_7801684 baseEnd_7801684 := by
    simpa [prefixWord, tailWord_7801684, baseEnd_7801684] using wordTrace_append hprefix tailTrace_7801684
  have hstable : (prefixWord ++ tailWord_7801684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801684).length < 2 ^ (prefixWord ++ tailWord_7801684).sum := by decide
  have hdescent : baseEnd_7801684 < baseStart_7801684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801696 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 3]
def baseStart_7801696 : Nat := 118140960795 + 7801696 * 2 ^ 59
def prefixEnd_7801696 : Nat := 4983230072969 + 3 ^ 40 * 7801696 * 2
def baseEnd_7801696 : Nat := 4006019968259613062220659

theorem tailTrace_7801696 : CollatzResearch.WordTrace tailWord_7801696 prefixEnd_7801696 4006019968259613062220659 := by
  unfold tailWord_7801696
  simp only [CollatzResearch.WordTrace]
  refine ⟨142275614971897645221124471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189700819962530193628165961 142275614971897645221124471)
  ·
    refine ⟨213413422457846467831686707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142275614971897645221124471 213413422457846467831686707)
    ·
      refine ⟨320120133686769701747530061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213413422457846467831686707 320120133686769701747530061)
      ·
        refine ⟨120045050132538638155323773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320120133686769701747530061 120045050132538638155323773)
        ·
          refine ⟨45016893799701989308246415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120045050132538638155323773 45016893799701989308246415)
          ·
            refine ⟨67525340699552983962369623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45016893799701989308246415 67525340699552983962369623)
            ·
              refine ⟨101288011049329475943554435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67525340699552983962369623 101288011049329475943554435)
              ·
                refine ⟨151932016573994213915331653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101288011049329475943554435 151932016573994213915331653)
                ·
                  refine ⟨28487253107623915109124685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151932016573994213915331653 28487253107623915109124685)
                  ·
                    refine ⟨10682719915358968165921757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28487253107623915109124685 10682719915358968165921757)
                    ·
                      refine ⟨4006019968259613062220659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10682719915358968165921757 4006019968259613062220659)
                      ·
                        rfl

theorem cell23_7801696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_7801696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801696 prefixEnd_7801696 := by exact prefixLift 7801696
  have htrace : WordTrace (prefixWord ++ tailWord_7801696) baseStart_7801696 baseEnd_7801696 := by
    simpa [prefixWord, tailWord_7801696, baseEnd_7801696] using wordTrace_append hprefix tailTrace_7801696
  have hstable : (prefixWord ++ tailWord_7801696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801696).length < 2 ^ (prefixWord ++ tailWord_7801696).sum := by decide
  have hdescent : baseEnd_7801696 < baseStart_7801696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801703 : List Nat := [1, 1, 5, 1, 2, 2, 2, 4, 5]
def baseStart_7801703 : Nat := 118140960795 + 7801703 * 2 ^ 59
def prefixEnd_7801703 : Nat := 4983230072969 + 3 ^ 40 * 7801703 * 2
def baseEnd_7801703 : Nat := 445113729180466059425903

theorem tailTrace_7801703 : CollatzResearch.WordTrace tailWord_7801703 prefixEnd_7801703 445113729180466059425903 := by
  unfold tailWord_7801703
  simp only [CollatzResearch.WordTrace]
  refine ⟨284551485254769930637753763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189700990169846620425169175 284551485254769930637753763)
  ·
    refine ⟨426827227882154895956630645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284551485254769930637753763 426827227882154895956630645)
    ·
      refine ⟨40015052613952021495934123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 426827227882154895956630645 40015052613952021495934123)
      ·
        refine ⟨60022578920928032243901185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40015052613952021495934123 60022578920928032243901185)
        ·
          refine ⟨45016934190696024182925889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60022578920928032243901185 45016934190696024182925889)
          ·
            refine ⟨33762700643022018137194417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45016934190696024182925889 33762700643022018137194417)
            ·
              refine ⟨25322025482266513602895813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33762700643022018137194417 25322025482266513602895813)
              ·
                refine ⟨4747879777924971300542965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25322025482266513602895813 4747879777924971300542965)
                ·
                  refine ⟨445113729180466059425903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4747879777924971300542965 445113729180466059425903)
                  ·
                    rfl

theorem cell23_7801703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 5].length) (baseStart_7801703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801703 prefixEnd_7801703 := by exact prefixLift 7801703
  have htrace : WordTrace (prefixWord ++ tailWord_7801703) baseStart_7801703 baseEnd_7801703 := by
    simpa [prefixWord, tailWord_7801703, baseEnd_7801703] using wordTrace_append hprefix tailTrace_7801703
  have hstable : (prefixWord ++ tailWord_7801703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801703).length < 2 ^ (prefixWord ++ tailWord_7801703).sum := by decide
  have hdescent : baseEnd_7801703 < baseStart_7801703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801763 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 3, 4]
def baseStart_7801763 : Nat := 118140960795 + 7801763 * 2 ^ 59
def prefixEnd_7801763 : Nat := 4983230072969 + 3 ^ 40 * 7801763 * 2
def baseEnd_7801763 : Nat := 1335351457154488100027617

theorem tailTrace_7801763 : CollatzResearch.WordTrace tailWord_7801763 prefixEnd_7801763 1335351457154488100027617 := by
  unfold tailWord_7801763
  simp only [CollatzResearch.WordTrace]
  refine ⟨284553673634552560884937943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189702449089701707256625295 284553673634552560884937943)
  ·
    refine ⟨426830510451828841327406915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284553673634552560884937943 426830510451828841327406915)
    ·
      refine ⟨640245765677743261991110373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426830510451828841327406915 640245765677743261991110373)
      ·
        refine ⟨120046081064576861623333195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 640245765677743261991110373 120046081064576861623333195)
        ·
          refine ⟨180069121596865292434999793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120046081064576861623333195 180069121596865292434999793)
          ·
            refine ⟨135051841197648969326249845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180069121596865292434999793 135051841197648969326249845)
            ·
              refine ⟨12661110112279590874335923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135051841197648969326249845 12661110112279590874335923)
              ·
                refine ⟨18991665168419386311503885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12661110112279590874335923 18991665168419386311503885)
                ·
                  refine ⟨7121874438157269866813957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18991665168419386311503885 7121874438157269866813957)
                  ·
                    refine ⟨1335351457154488100027617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7121874438157269866813957 1335351457154488100027617)
                    ·
                      rfl

theorem cell23_7801763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 4].length) (baseStart_7801763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801763 prefixEnd_7801763 := by exact prefixLift 7801763
  have htrace : WordTrace (prefixWord ++ tailWord_7801763) baseStart_7801763 baseEnd_7801763 := by
    simpa [prefixWord, tailWord_7801763, baseEnd_7801763] using wordTrace_append hprefix tailTrace_7801763
  have hstable : (prefixWord ++ tailWord_7801763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801763).length < 2 ^ (prefixWord ++ tailWord_7801763).sum := by decide
  have hdescent : baseEnd_7801763 < baseStart_7801763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801790 : List Nat := [4, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_7801790 : Nat := 118140960795 + 7801790 * 2 ^ 59
def prefixEnd_7801790 : Nat := 4983230072969 + 3 ^ 40 * 7801790 * 2
def baseEnd_7801790 : Nat := 4006068235441135694445227

theorem tailTrace_7801790 : CollatzResearch.WordTrace tailWord_7801790 prefixEnd_7801790 4006068235441135694445227 := by
  unfold tailWord_7801790
  simp only [CollatzResearch.WordTrace]
  refine ⟨35569332300681843062021353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189703105603636496330780549 35569332300681843062021353)
  ·
    refine ⟨26676999225511382296516015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35569332300681843062021353 26676999225511382296516015)
    ·
      refine ⟨40015498838267073444774023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26676999225511382296516015 40015498838267073444774023)
      ·
        refine ⟨60023248257400610167161035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40015498838267073444774023 60023248257400610167161035)
        ·
          refine ⟨90034872386100915250741553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60023248257400610167161035 90034872386100915250741553)
          ·
            refine ⟨67526154289575686438056165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90034872386100915250741553 67526154289575686438056165)
            ·
              refine ⟨12661153929295441207135531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67526154289575686438056165 12661153929295441207135531)
              ·
                refine ⟨18991730893943161810703297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12661153929295441207135531 18991730893943161810703297)
                ·
                  refine ⟨14243798170457371358027473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18991730893943161810703297 14243798170457371358027473)
                  ·
                    refine ⟨10682848627843028518520605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14243798170457371358027473 10682848627843028518520605)
                    ·
                      refine ⟨4006068235441135694445227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10682848627843028518520605 4006068235441135694445227)
                      ·
                        rfl

theorem cell23_7801790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_7801790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801790 prefixEnd_7801790 := by exact prefixLift 7801790
  have htrace : WordTrace (prefixWord ++ tailWord_7801790) baseStart_7801790 baseEnd_7801790 := by
    simpa [prefixWord, tailWord_7801790, baseEnd_7801790] using wordTrace_append hprefix tailTrace_7801790
  have hstable : (prefixWord ++ tailWord_7801790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801790).length < 2 ^ (prefixWord ++ tailWord_7801790).sum := by decide
  have hdescent : baseEnd_7801790 < baseStart_7801790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801810 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 6]
def baseStart_7801810 : Nat := 118140960795 + 7801810 * 2 ^ 59
def prefixEnd_7801810 : Nat := 4983230072969 + 3 ^ 40 * 7801810 * 2
def baseEnd_7801810 : Nat := 445119833894913957355015

theorem tailTrace_7801810 : CollatzResearch.WordTrace tailWord_7801810 prefixEnd_7801810 445119833894913957355015 := by
  unfold tailWord_7801810
  simp only [CollatzResearch.WordTrace]
  refine ⟨71138846966345571977974721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189703591910254858607932589 71138846966345571977974721)
  ·
    refine ⟨53354135224759178983481041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71138846966345571977974721 53354135224759178983481041)
    ·
      refine ⟨40015601418569384237610781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53354135224759178983481041 40015601418569384237610781)
      ·
        refine ⟨15005850531963519089104043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40015601418569384237610781 15005850531963519089104043)
        ·
          refine ⟨22508775797945278633656065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15005850531963519089104043 22508775797945278633656065)
          ·
            refine ⟨16881581848458958975242049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22508775797945278633656065 16881581848458958975242049)
            ·
              refine ⟨12661186386344219231431537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16881581848458958975242049 12661186386344219231431537)
              ·
                refine ⟨9495889789758164423573653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12661186386344219231431537 9495889789758164423573653)
                ·
                  refine ⟨445119833894913957355015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9495889789758164423573653 445119833894913957355015)
                  ·
                    rfl

theorem cell23_7801810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_7801810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801810 prefixEnd_7801810 := by exact prefixLift 7801810
  have htrace : WordTrace (prefixWord ++ tailWord_7801810) baseStart_7801810 baseEnd_7801810 := by
    simpa [prefixWord, tailWord_7801810, baseEnd_7801810] using wordTrace_append hprefix tailTrace_7801810
  have hstable : (prefixWord ++ tailWord_7801810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801810).length < 2 ^ (prefixWord ++ tailWord_7801810).sum := by decide
  have hdescent : baseEnd_7801810 < baseStart_7801810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801814 : List Nat := [5, 2, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_7801814 : Nat := 118140960795 + 7801814 * 2 ^ 59
def prefixEnd_7801814 : Nat := 4983230072969 + 3 ^ 40 * 7801814 * 2
def baseEnd_7801814 : Nat := 1335360186325614533515039

theorem tailTrace_7801814 : CollatzResearch.WordTrace tailWord_7801814 prefixEnd_7801814 1335360186325614533515039 := by
  unfold tailWord_7801814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17784720859835487287190281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189703689171578531063362997 17784720859835487287190281)
  ·
    refine ⟨13338540644876615465392711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17784720859835487287190281 13338540644876615465392711)
    ·
      refine ⟨20007810967314923198089067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13338540644876615465392711 20007810967314923198089067)
      ·
        refine ⟨30011716450972384797133601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20007810967314923198089067 30011716450972384797133601)
        ·
          refine ⟨22508787338229288597850201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30011716450972384797133601 22508787338229288597850201)
          ·
            refine ⟨16881590503671966448387651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22508787338229288597850201 16881590503671966448387651)
            ·
              refine ⟨25322385755507949672581477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16881590503671966448387651 25322385755507949672581477)
              ·
                refine ⟨4747947329157740563609027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25322385755507949672581477 4747947329157740563609027)
                ·
                  refine ⟨7121920993736610845413541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4747947329157740563609027 7121920993736610845413541)
                  ·
                    refine ⟨1335360186325614533515039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7121920993736610845413541 1335360186325614533515039)
                    ·
                      rfl

theorem cell23_7801814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_7801814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801814 prefixEnd_7801814 := by exact prefixLift 7801814
  have htrace : WordTrace (prefixWord ++ tailWord_7801814) baseStart_7801814 baseEnd_7801814 := by
    simpa [prefixWord, tailWord_7801814, baseEnd_7801814] using wordTrace_append hprefix tailTrace_7801814
  have hstable : (prefixWord ++ tailWord_7801814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801814).length < 2 ^ (prefixWord ++ tailWord_7801814).sum := by decide
  have hdescent : baseEnd_7801814 < baseStart_7801814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801853 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_7801853 : Nat := 118140960795 + 7801853 * 2 ^ 59
def prefixEnd_7801853 : Nat := 4983230072969 + 3 ^ 40 * 7801853 * 2
def baseEnd_7801853 : Nat := 1335366861574122982652479

theorem tailTrace_7801853 : CollatzResearch.WordTrace tailWord_7801853 prefixEnd_7801853 1335366861574122982652479 := by
  unfold tailWord_7801853
  simp only [CollatzResearch.WordTrace]
  refine ⟨284556956204226506255714213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189704637469484337503809475 284556956204226506255714213)
  ·
    refine ⟨53354429288292469922946415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284556956204226506255714213 53354429288292469922946415)
    ·
      refine ⟨80031643932438704884419623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53354429288292469922946415 80031643932438704884419623)
      ·
        refine ⟨120047465898658057326629435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80031643932438704884419623 120047465898658057326629435)
        ·
          refine ⟨180071198847987085989944153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120047465898658057326629435 180071198847987085989944153)
          ·
            refine ⟨135053399135990314492458115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180071198847987085989944153 135053399135990314492458115)
            ·
              refine ⟨202580098703985471738687173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135053399135990314492458115 202580098703985471738687173)
              ·
                refine ⟨37983768506997275951003845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202580098703985471738687173 37983768506997275951003845)
                ·
                  refine ⟨7121956595061989240813221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37983768506997275951003845 7121956595061989240813221)
                  ·
                    refine ⟨1335366861574122982652479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7121956595061989240813221 1335366861574122982652479)
                    ·
                      rfl

theorem cell23_7801853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_7801853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801853 prefixEnd_7801853 := by exact prefixLift 7801853
  have htrace : WordTrace (prefixWord ++ tailWord_7801853) baseStart_7801853 baseEnd_7801853 := by
    simpa [prefixWord, tailWord_7801853, baseEnd_7801853] using wordTrace_append hprefix tailTrace_7801853
  have hstable : (prefixWord ++ tailWord_7801853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801853).length < 2 ^ (prefixWord ++ tailWord_7801853).sum := by decide
  have hdescent : baseEnd_7801853 < baseStart_7801853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801856 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_7801856 : Nat := 118140960795 + 7801856 * 2 ^ 59
def prefixEnd_7801856 : Nat := 4983230072969 + 3 ^ 40 * 7801856 * 2
def baseEnd_7801856 : Nat := 4006102125164332436219923

theorem tailTrace_7801856 : CollatzResearch.WordTrace tailWord_7801856 prefixEnd_7801856 4006102125164332436219923 := by
  unfold tailWord_7801856
  simp only [CollatzResearch.WordTrace]
  refine ⟨142278532811607818884036711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189704710415477091845382281 142278532811607818884036711)
  ·
    refine ⟨213417799217411728326055067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142278532811607818884036711 213417799217411728326055067)
    ·
      refine ⟨320126698826117592489082601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213417799217411728326055067 320126698826117592489082601)
      ·
        refine ⟨240095024119588194366811951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320126698826117592489082601 240095024119588194366811951)
        ·
          refine ⟨360142536179382291550217927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240095024119588194366811951 360142536179382291550217927)
          ·
            refine ⟨540213804269073437325326891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360142536179382291550217927 540213804269073437325326891)
            ·
              refine ⟨810320706403610155987990337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540213804269073437325326891 810320706403610155987990337)
              ·
                refine ⟨607740529802707616990992753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810320706403610155987990337 607740529802707616990992753)
                ·
                  refine ⟨455805397352030712743244565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607740529802707616990992753 455805397352030712743244565)
                  ·
                    refine ⟨21365878000876439659839589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 455805397352030712743244565 21365878000876439659839589)
                    ·
                      refine ⟨4006102125164332436219923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21365878000876439659839589 4006102125164332436219923)
                      ·
                        rfl

theorem cell23_7801856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_7801856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801856 prefixEnd_7801856 := by exact prefixLift 7801856
  have htrace : WordTrace (prefixWord ++ tailWord_7801856) baseStart_7801856 baseEnd_7801856 := by
    simpa [prefixWord, tailWord_7801856, baseEnd_7801856] using wordTrace_append hprefix tailTrace_7801856
  have hstable : (prefixWord ++ tailWord_7801856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801856).length < 2 ^ (prefixWord ++ tailWord_7801856).sum := by decide
  have hdescent : baseEnd_7801856 < baseStart_7801856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801857 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 1, 5]
def baseStart_7801857 : Nat := 118140960795 + 7801857 * 2 ^ 59
def prefixEnd_7801857 : Nat := 4983230072969 + 3 ^ 40 * 7801857 * 2
def baseEnd_7801857 : Nat := 1335367546214995644102473

theorem tailTrace_7801857 : CollatzResearch.WordTrace tailWord_7801857 prefixEnd_7801857 1335367546214995644102473 := by
  unfold tailWord_7801857
  simp only [CollatzResearch.WordTrace]
  refine ⟨284557102096212014938859825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189704734730808009959239883 284557102096212014938859825)
  ·
    refine ⟨213417826572159011204144869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284557102096212014938859825 213417826572159011204144869)
    ·
      refine ⟨40015842482279814600777163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213417826572159011204144869 40015842482279814600777163)
      ·
        refine ⟨60023763723419721901165745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40015842482279814600777163 60023763723419721901165745)
        ·
          refine ⟨45017822792564791425874309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60023763723419721901165745 45017822792564791425874309)
          ·
            refine ⟨8440841773605898392351433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45017822792564791425874309 8440841773605898392351433)
            ·
              refine ⟨6330631330204423794263575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8440841773605898392351433 6330631330204423794263575)
              ·
                refine ⟨9495946995306635691395363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330631330204423794263575 9495946995306635691395363)
                ·
                  refine ⟨14243920492959953537093045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9495946995306635691395363 14243920492959953537093045)
                  ·
                    refine ⟨1335367546214995644102473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14243920492959953537093045 1335367546214995644102473)
                    ·
                      rfl

theorem cell23_7801857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_7801857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801857 prefixEnd_7801857 := by exact prefixLift 7801857
  have htrace : WordTrace (prefixWord ++ tailWord_7801857) baseStart_7801857 baseEnd_7801857 := by
    simpa [prefixWord, tailWord_7801857, baseEnd_7801857] using wordTrace_append hprefix tailTrace_7801857
  have hstable : (prefixWord ++ tailWord_7801857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801857).length < 2 ^ (prefixWord ++ tailWord_7801857).sum := by decide
  have hdescent : baseEnd_7801857 < baseStart_7801857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801863 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_7801863 : Nat := 118140960795 + 7801863 * 2 ^ 59
def prefixEnd_7801863 : Nat := 4983230072969 + 3 ^ 40 * 7801863 * 2
def baseEnd_7801863 : Nat := 4006105719528913908832391

theorem tailTrace_7801863 : CollatzResearch.WordTrace tailWord_7801863 prefixEnd_7801863 4006105719528913908832391 := by
  unfold tailWord_7801863
  simp only [CollatzResearch.WordTrace]
  refine ⟨284557320934190277963578243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189704880622793518642385495 284557320934190277963578243)
  ·
    refine ⟨426835981401285416945367365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284557320934190277963578243 426835981401285416945367365)
    ·
      refine ⟨80031746512741015677256381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426835981401285416945367365 80031746512741015677256381)
      ·
        refine ⟨30011904942277880878971143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80031746512741015677256381 30011904942277880878971143)
        ·
          refine ⟨45017857413416821318456715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30011904942277880878971143 45017857413416821318456715)
          ·
            refine ⟨67526786120125231977685073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45017857413416821318456715 67526786120125231977685073)
            ·
              refine ⟨50645089590093923983263805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67526786120125231977685073 50645089590093923983263805)
              ·
                refine ⟨18991908596285221493723927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50645089590093923983263805 18991908596285221493723927)
                ·
                  refine ⟨28487862894427832240585891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18991908596285221493723927 28487862894427832240585891)
                  ·
                    refine ⟨42731794341641748360878837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28487862894427832240585891 42731794341641748360878837)
                    ·
                      refine ⟨4006105719528913908832391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42731794341641748360878837 4006105719528913908832391)
                      ·
                        rfl

theorem cell23_7801863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_7801863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801863 prefixEnd_7801863 := by exact prefixLift 7801863
  have htrace : WordTrace (prefixWord ++ tailWord_7801863) baseStart_7801863 baseEnd_7801863 := by
    simpa [prefixWord, tailWord_7801863, baseEnd_7801863] using wordTrace_append hprefix tailTrace_7801863
  have hstable : (prefixWord ++ tailWord_7801863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801863).length < 2 ^ (prefixWord ++ tailWord_7801863).sum := by decide
  have hdescent : baseEnd_7801863 < baseStart_7801863 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801870 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_7801870 : Nat := 118140960795 + 7801870 * 2 ^ 59
def prefixEnd_7801870 : Nat := 4983230072969 + 3 ^ 40 * 7801870 * 2
def baseEnd_7801870 : Nat := 1335369771297831793814953

theorem tailTrace_7801870 : CollatzResearch.WordTrace tailWord_7801870 prefixEnd_7801870 1335369771297831793814953 := by
  unfold tailWord_7801870
  simp only [CollatzResearch.WordTrace]
  refine ⟨35569697030645614769885383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189705050830109945439388709 35569697030645614769885383)
  ·
    refine ⟨53354545545968422154828075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35569697030645614769885383 53354545545968422154828075)
    ·
      refine ⟨80031818318952633232242113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53354545545968422154828075 80031818318952633232242113)
      ·
        refine ⟨60023863739214474924181585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80031818318952633232242113 60023863739214474924181585)
        ·
          refine ⟨45017897804410856193136189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60023863739214474924181585 45017897804410856193136189)
          ·
            refine ⟨16881711676654071072426071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45017897804410856193136189 16881711676654071072426071)
            ·
              refine ⟨25322567514981106608639107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16881711676654071072426071 25322567514981106608639107)
              ·
                refine ⟨37983851272471659912958661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25322567514981106608639107 37983851272471659912958661)
                ·
                  refine ⟨7121972113588436233679749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37983851272471659912958661 7121972113588436233679749)
                  ·
                    refine ⟨1335369771297831793814953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7121972113588436233679749 1335369771297831793814953)
                    ·
                      rfl

theorem cell23_7801870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_7801870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801870 prefixEnd_7801870 := by exact prefixLift 7801870
  have htrace : WordTrace (prefixWord ++ tailWord_7801870) baseStart_7801870 baseEnd_7801870 := by
    simpa [prefixWord, tailWord_7801870, baseEnd_7801870] using wordTrace_append hprefix tailTrace_7801870
  have hstable : (prefixWord ++ tailWord_7801870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801870).length < 2 ^ (prefixWord ++ tailWord_7801870).sum := by decide
  have hdescent : baseEnd_7801870 < baseStart_7801870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801877 : List Nat := [1, 3, 2, 1, 4, 1, 1, 3, 3, 2, 2]
def baseStart_7801877 : Nat := 118140960795 + 7801877 * 2 ^ 59
def prefixEnd_7801877 : Nat := 4983230072969 + 3 ^ 40 * 7801877 * 2
def baseEnd_7801877 : Nat := 4006112908258076854057327

theorem tailTrace_7801877 : CollatzResearch.WordTrace tailWord_7801877 prefixEnd_7801877 4006112908258076854057327 := by
  unfold tailWord_7801877
  simp only [CollatzResearch.WordTrace]
  refine ⟨284557831556139558354587885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189705221037426372236391923 284557831556139558354587885)
  ·
    refine ⟨106709186833552334382970457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284557831556139558354587885 106709186833552334382970457)
    ·
      refine ⟨80031890125164250787227843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106709186833552334382970457 80031890125164250787227843)
      ·
        refine ⟨120047835187746376180841765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80031890125164250787227843 120047835187746376180841765)
        ·
          refine ⟨22508969097702445533907831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120047835187746376180841765 22508969097702445533907831)
          ·
            refine ⟨33763453646553668300861747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22508969097702445533907831 33763453646553668300861747)
            ·
              refine ⟨50645180469830502451292621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33763453646553668300861747 50645180469830502451292621)
              ·
                refine ⟨18991942676186438419234733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50645180469830502451292621 18991942676186438419234733)
                ·
                  refine ⟨7121978503569914407213025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18991942676186438419234733 7121978503569914407213025)
                  ·
                    refine ⟨5341483877677435805409769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7121978503569914407213025 5341483877677435805409769)
                    ·
                      refine ⟨4006112908258076854057327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341483877677435805409769 4006112908258076854057327)
                      ·
                        rfl

theorem cell23_7801877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_7801877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801877 prefixEnd_7801877 := by exact prefixLift 7801877
  have htrace : WordTrace (prefixWord ++ tailWord_7801877) baseStart_7801877 baseEnd_7801877 := by
    simpa [prefixWord, tailWord_7801877, baseEnd_7801877] using wordTrace_append hprefix tailTrace_7801877
  have hstable : (prefixWord ++ tailWord_7801877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801877).length < 2 ^ (prefixWord ++ tailWord_7801877).sum := by decide
  have hdescent : baseEnd_7801877 < baseStart_7801877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801887 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 2, 4]
def baseStart_7801887 : Nat := 118140960795 + 7801887 * 2 ^ 59
def prefixEnd_7801887 : Nat := 4983230072969 + 3 ^ 40 * 7801887 * 2
def baseEnd_7801887 : Nat := 1335372681021540604977427

theorem tailTrace_7801887 : CollatzResearch.WordTrace tailWord_7801887 prefixEnd_7801887 1335372681021540604977427 := by
  unfold tailWord_7801887
  simp only [CollatzResearch.WordTrace]
  refine ⟨284558196286103330062451915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189705464190735553374967943 284558196286103330062451915)
  ·
    refine ⟨426837294429154995093677873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284558196286103330062451915 426837294429154995093677873)
    ·
      refine ⟨320127970821866246320258405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426837294429154995093677873 320127970821866246320258405)
      ·
        refine ⟨60023994529099921185048451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320127970821866246320258405 60023994529099921185048451)
        ·
          refine ⟨90035991793649881777572677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60023994529099921185048451 90035991793649881777572677)
          ·
            refine ⟨16881748461309352833294877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90035991793649881777572677 16881748461309352833294877)
            ·
              refine ⟨6330655672991007312485579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16881748461309352833294877 6330655672991007312485579)
              ·
                refine ⟨9495983509486510968728369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330655672991007312485579 9495983509486510968728369)
                ·
                  refine ⟨7121987632114883226546277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9495983509486510968728369 7121987632114883226546277)
                  ·
                    refine ⟨1335372681021540604977427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7121987632114883226546277 1335372681021540604977427)
                    ·
                      rfl

theorem cell23_7801887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 2, 4].length) (baseStart_7801887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801887 prefixEnd_7801887 := by exact prefixLift 7801887
  have htrace : WordTrace (prefixWord ++ tailWord_7801887) baseStart_7801887 baseEnd_7801887 := by
    simpa [prefixWord, tailWord_7801887, baseEnd_7801887] using wordTrace_append hprefix tailTrace_7801887
  have hstable : (prefixWord ++ tailWord_7801887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801887).length < 2 ^ (prefixWord ++ tailWord_7801887).sum := by decide
  have hdescent : baseEnd_7801887 < baseStart_7801887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801890 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_7801890 : Nat := 118140960795 + 7801890 * 2 ^ 59
def prefixEnd_7801890 : Nat := 4983230072969 + 3 ^ 40 * 7801890 * 2
def baseEnd_7801890 : Nat := 4006119583506585303194767

theorem tailTrace_7801890 : CollatzResearch.WordTrace tailWord_7801890 prefixEnd_7801890 4006119583506585303194767 := by
  unfold tailWord_7801890
  simp only [CollatzResearch.WordTrace]
  refine ⟨71139576426273115393702781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189705537136728307716540749 71139576426273115393702781)
  ·
    refine ⟨26677341159852418272638543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71139576426273115393702781 26677341159852418272638543)
    ·
      refine ⟨40016011739778627408957815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26677341159852418272638543 40016011739778627408957815)
      ·
        refine ⟨60024017609667941113436723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40016011739778627408957815 60024017609667941113436723)
        ·
          refine ⟨90036026414501911670155085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60024017609667941113436723 90036026414501911670155085)
          ·
            refine ⟨33763509905438216876308157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90036026414501911670155085 33763509905438216876308157)
            ·
              refine ⟨12661316214539331328615559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33763509905438216876308157 12661316214539331328615559)
              ·
                refine ⟨18991974321808996992923339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12661316214539331328615559 18991974321808996992923339)
                ·
                  refine ⟨28487961482713495489385009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18991974321808996992923339 28487961482713495489385009)
                  ·
                    refine ⟨21365971112035121617038757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28487961482713495489385009 21365971112035121617038757)
                    ·
                      refine ⟨4006119583506585303194767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21365971112035121617038757 4006119583506585303194767)
                      ·
                        rfl

theorem cell23_7801890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_7801890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801890 prefixEnd_7801890 := by exact prefixLift 7801890
  have htrace : WordTrace (prefixWord ++ tailWord_7801890) baseStart_7801890 baseEnd_7801890 := by
    simpa [prefixWord, tailWord_7801890, baseEnd_7801890] using wordTrace_append hprefix tailTrace_7801890
  have hstable : (prefixWord ++ tailWord_7801890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801890).length < 2 ^ (prefixWord ++ tailWord_7801890).sum := by decide
  have hdescent : baseEnd_7801890 < baseStart_7801890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801953 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_7801953 : Nat := 118140960795 + 7801953 * 2 ^ 59
def prefixEnd_7801953 : Nat := 4983230072969 + 3 ^ 40 * 7801953 * 2
def baseEnd_7801953 : Nat := 4006151932787818556706977

theorem tailTrace_7801953 : CollatzResearch.WordTrace tailWord_7801953 prefixEnd_7801953 4006151932787818556706977 := by
  unfold tailWord_7801953
  simp only [CollatzResearch.WordTrace]
  refine ⟨284560603503864223334354513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189707069002576148889569675 284560603503864223334354513)
  ·
    refine ⟨213420452627898167500765885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284560603503864223334354513 213420452627898167500765885)
    ·
      refine ⟨80032669735461812812787207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213420452627898167500765885 80032669735461812812787207)
      ·
        refine ⟨120049004603192719219180811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80032669735461812812787207 120049004603192719219180811)
        ·
          refine ⟨180073506904789078828771217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120049004603192719219180811 180073506904789078828771217)
          ·
            refine ⟨135055130178591809121578413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180073506904789078828771217 135055130178591809121578413)
            ·
              refine ⟨50645673816971928420591905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135055130178591809121578413 50645673816971928420591905)
              ·
                refine ⟨37984255362728946315443929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50645673816971928420591905 37984255362728946315443929)
                ·
                  refine ⟨28488191522046709736582947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37984255362728946315443929 28488191522046709736582947)
                  ·
                    refine ⟨42732287283070064604874421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28488191522046709736582947 42732287283070064604874421)
                    ·
                      refine ⟨4006151932787818556706977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42732287283070064604874421 4006151932787818556706977)
                      ·
                        rfl

theorem cell23_7801953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_7801953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801953 prefixEnd_7801953 := by exact prefixLift 7801953
  have htrace : WordTrace (prefixWord ++ tailWord_7801953) baseStart_7801953 baseEnd_7801953 := by
    simpa [prefixWord, tailWord_7801953, baseEnd_7801953] using wordTrace_append hprefix tailTrace_7801953
  have hstable : (prefixWord ++ tailWord_7801953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801953).length < 2 ^ (prefixWord ++ tailWord_7801953).sum := by decide
  have hdescent : baseEnd_7801953 < baseStart_7801953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801954 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_7801954 : Nat := 118140960795 + 7801954 * 2 ^ 59
def prefixEnd_7801954 : Nat := 4983230072969 + 3 ^ 40 * 7801954 * 2
def baseEnd_7801954 : Nat := 4006152446268473052794473

theorem tailTrace_7801954 : CollatzResearch.WordTrace tailWord_7801954 prefixEnd_7801954 4006152446268473052794473 := by
  unfold tailWord_7801954
  simp only [CollatzResearch.WordTrace]
  refine ⟨71140159994215150126285229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189707093317907067003427277 71140159994215150126285229)
  ·
    refine ⟨26677559997830681297356961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71140159994215150126285229 26677559997830681297356961)
    ·
      refine ⟨20008169998373010973017721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26677559997830681297356961 20008169998373010973017721)
      ·
        refine ⟨15006127498779758229763291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20008169998373010973017721 15006127498779758229763291)
        ·
          refine ⟨22509191248169637344644937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15006127498779758229763291 22509191248169637344644937)
          ·
            refine ⟨16881893436127228008483703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22509191248169637344644937 16881893436127228008483703)
            ·
              refine ⟨25322840154190842012725555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16881893436127228008483703 25322840154190842012725555)
              ·
                refine ⟨37984260231286263019088333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25322840154190842012725555 37984260231286263019088333)
                ·
                  refine ⟨14244097586732348632158125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37984260231286263019088333 14244097586732348632158125)
                  ·
                    refine ⟨5341536595024630737059297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14244097586732348632158125 5341536595024630737059297)
                    ·
                      refine ⟨4006152446268473052794473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341536595024630737059297 4006152446268473052794473)
                      ·
                        rfl

theorem cell23_7801954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_7801954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801954 prefixEnd_7801954 := by exact prefixLift 7801954
  have htrace : WordTrace (prefixWord ++ tailWord_7801954) baseStart_7801954 baseEnd_7801954 := by
    simpa [prefixWord, tailWord_7801954, baseEnd_7801954] using wordTrace_append hprefix tailTrace_7801954
  have hstable : (prefixWord ++ tailWord_7801954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801954).length < 2 ^ (prefixWord ++ tailWord_7801954).sum := by decide
  have hdescent : baseEnd_7801954 < baseStart_7801954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7801983 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 3]
def baseStart_7801983 : Nat := 118140960795 + 7801983 * 2 ^ 59
def prefixEnd_7801983 : Nat := 4983230072969 + 3 ^ 40 * 7801983 * 2
def baseEnd_7801983 : Nat := 4006167337207453439331839

theorem tailTrace_7801983 : CollatzResearch.WordTrace tailWord_7801983 prefixEnd_7801983 4006167337207453439331839 := by
  unfold tailWord_7801983
  simp only [CollatzResearch.WordTrace]
  refine ⟨284561697693755538457946603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189707798462503692305297735 284561697693755538457946603)
  ·
    refine ⟨426842546540633307686919905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284561697693755538457946603 426842546540633307686919905)
    ·
      refine ⟨320131909905474980765189929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426842546540633307686919905 320131909905474980765189929)
      ·
        refine ⟨240098932429106235573892447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320131909905474980765189929 240098932429106235573892447)
        ·
          refine ⟨360148398643659353360838671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240098932429106235573892447 360148398643659353360838671)
          ·
            refine ⟨540222597965489030041258007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360148398643659353360838671 540222597965489030041258007)
            ·
              refine ⟨810333896948233545061887011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540222597965489030041258007 810333896948233545061887011)
              ·
                refine ⟨1215500845422350317592830517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810333896948233545061887011 1215500845422350317592830517)
                ·
                  refine ⟨113953204258345342274327861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1215500845422350317592830517 113953204258345342274327861)
                  ·
                    refine ⟨10683112899219875838218237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113953204258345342274327861 10683112899219875838218237)
                    ·
                      refine ⟨4006167337207453439331839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10683112899219875838218237 4006167337207453439331839)
                      ·
                        rfl

theorem cell23_7801983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_7801983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7801983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7801983 prefixEnd_7801983 := by exact prefixLift 7801983
  have htrace : WordTrace (prefixWord ++ tailWord_7801983) baseStart_7801983 baseEnd_7801983 := by
    simpa [prefixWord, tailWord_7801983, baseEnd_7801983] using wordTrace_append hprefix tailTrace_7801983
  have hstable : (prefixWord ++ tailWord_7801983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7801983).length < 2 ^ (prefixWord ++ tailWord_7801983).sum := by decide
  have hdescent : baseEnd_7801983 < baseStart_7801983 := by decide
  rcases family_descends (prefixWord ++ tailWord_7801983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802003 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 4, 5]
def baseStart_7802003 : Nat := 118140960795 + 7802003 * 2 ^ 59
def prefixEnd_7802003 : Nat := 4983230072969 + 3 ^ 40 * 7802003 * 2
def baseEnd_7802003 : Nat := 1335392535606847787027249

theorem tailTrace_7802003 : CollatzResearch.WordTrace tailWord_7802003 prefixEnd_7802003 1335392535606847787027249 := by
  unfold tailWord_7802003
  simp only [CollatzResearch.WordTrace]
  refine ⟨284562427153683081873674663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189708284769122054582449775 284562427153683081873674663)
  ·
    refine ⟨426843640730524622810511995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284562427153683081873674663 426843640730524622810511995)
    ·
      refine ⟨640265461095786934215767993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426843640730524622810511995 640265461095786934215767993)
      ·
        refine ⟨480199095821840200661825995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640265461095786934215767993 480199095821840200661825995)
        ·
          refine ⟨720298643732760300992738993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480199095821840200661825995 720298643732760300992738993)
          ·
            refine ⟨540223982799570225744554245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720298643732760300992738993 540223982799570225744554245)
            ·
              refine ⟨101291996774919417327103921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540223982799570225744554245 101291996774919417327103921)
              ·
                refine ⟨75968997581189562995327941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101291996774919417327103921 75968997581189562995327941)
                ·
                  refine ⟨14244187046473043061623989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75968997581189562995327941 14244187046473043061623989)
                  ·
                    refine ⟨1335392535606847787027249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14244187046473043061623989 1335392535606847787027249)
                    ·
                      rfl

theorem cell23_7802003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 5].length) (baseStart_7802003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802003 prefixEnd_7802003 := by exact prefixLift 7802003
  have htrace : WordTrace (prefixWord ++ tailWord_7802003) baseStart_7802003 baseEnd_7802003 := by
    simpa [prefixWord, tailWord_7802003, baseEnd_7802003] using wordTrace_append hprefix tailTrace_7802003
  have hstable : (prefixWord ++ tailWord_7802003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802003).length < 2 ^ (prefixWord ++ tailWord_7802003).sum := by decide
  have hdescent : baseEnd_7802003 < baseStart_7802003 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802020 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 1, 7]
def baseStart_7802020 : Nat := 118140960795 + 7802020 * 2 ^ 59
def prefixEnd_7802020 : Nat := 4983230072969 + 3 ^ 40 * 7802020 * 2
def baseEnd_7802020 : Nat := 1335395445330556598189723

theorem tailTrace_7802020 : CollatzResearch.WordTrace tailWord_7802020 prefixEnd_7802020 1335395445330556598189723 := by
  unfold tailWord_7802020
  simp only [CollatzResearch.WordTrace]
  refine ⟨142281523597310746888521757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189708698129747662518029009 142281523597310746888521757)
  ·
    refine ⟨53355571348991530083195659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142281523597310746888521757 53355571348991530083195659)
    ·
      refine ⟨80033357023487295124793489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53355571348991530083195659 80033357023487295124793489)
      ·
        refine ⟨60025017767615471343595117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80033357023487295124793489 60025017767615471343595117)
        ·
          refine ⟨22509381662855801753848169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60025017767615471343595117 22509381662855801753848169)
          ·
            refine ⟨16882036247141851315386127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22509381662855801753848169 16882036247141851315386127)
            ·
              refine ⟨25323054370712776973079191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16882036247141851315386127 25323054370712776973079191)
              ·
                refine ⟨37984581556069165459618787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25323054370712776973079191 37984581556069165459618787)
                ·
                  refine ⟨56976872334103748189428181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37984581556069165459618787 56976872334103748189428181)
                  ·
                    refine ⟨1335395445330556598189723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56976872334103748189428181 1335395445330556598189723)
                    ·
                      rfl

theorem cell23_7802020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_7802020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802020 prefixEnd_7802020 := by exact prefixLift 7802020
  have htrace : WordTrace (prefixWord ++ tailWord_7802020) baseStart_7802020 baseEnd_7802020 := by
    simpa [prefixWord, tailWord_7802020, baseEnd_7802020] using wordTrace_append hprefix tailTrace_7802020
  have hstable : (prefixWord ++ tailWord_7802020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802020).length < 2 ^ (prefixWord ++ tailWord_7802020).sum := by decide
  have hdescent : baseEnd_7802020 < baseStart_7802020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802053 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_7802053 : Nat := 118140960795 + 7802053 * 2 ^ 59
def prefixEnd_7802053 : Nat := 4983230072969 + 3 ^ 40 * 7802053 * 2
def baseEnd_7802053 : Nat := 4006203280853268165456517

theorem tailTrace_7802053 : CollatzResearch.WordTrace tailWord_7802053 prefixEnd_7802053 4006203280853268165456517 := by
  unfold tailWord_7802053
  simp only [CollatzResearch.WordTrace]
  refine ⟨284564250803501940412994813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189709500535667960275329875 284564250803501940412994813)
  ·
    refine ⟨106711594051313227654873055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284564250803501940412994813 106711594051313227654873055)
    ·
      refine ⟨160067391076969841482309583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106711594051313227654873055 160067391076969841482309583)
      ·
        refine ⟨240101086615454762223464375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160067391076969841482309583 240101086615454762223464375)
        ·
          refine ⟨360151629923182143335196563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240101086615454762223464375 360151629923182143335196563)
          ·
            refine ⟨540227444884773215002794845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360151629923182143335196563 540227444884773215002794845)
            ·
              refine ⟨202585291831789955626048067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 540227444884773215002794845 202585291831789955626048067)
              ·
                refine ⟨303877937747684933439072101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202585291831789955626048067 303877937747684933439072101)
                ·
                  refine ⟨56977113327690925019826019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 303877937747684933439072101 56977113327690925019826019)
                  ·
                    refine ⟨85465669991536387529739029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56977113327690925019826019 85465669991536387529739029)
                    ·
                      refine ⟨4006203280853268165456517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85465669991536387529739029 4006203280853268165456517)
                      ·
                        rfl

theorem cell23_7802053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_7802053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802053 prefixEnd_7802053 := by exact prefixLift 7802053
  have htrace : WordTrace (prefixWord ++ tailWord_7802053) baseStart_7802053 baseEnd_7802053 := by
    simpa [prefixWord, tailWord_7802053, baseEnd_7802053] using wordTrace_append hprefix tailTrace_7802053
  have hstable : (prefixWord ++ tailWord_7802053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802053).length < 2 ^ (prefixWord ++ tailWord_7802053).sum := by decide
  have hdescent : baseEnd_7802053 < baseStart_7802053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802084 : List Nat := [2, 3, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_7802084 : Nat := 118140960795 + 7802084 * 2 ^ 59
def prefixEnd_7802084 : Nat := 4983230072969 + 3 ^ 40 * 7802084 * 2
def baseEnd_7802084 : Nat := 1335406399584519181389625

theorem tailTrace_7802084 : CollatzResearch.WordTrace tailWord_7802084 prefixEnd_7802084 1335406399584519181389625 := by
  unfold tailWord_7802084
  simp only [CollatzResearch.WordTrace]
  refine ⟨142282690733194816353686653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189710254310926421804915537 142282690733194816353686653)
  ·
    refine ⟨53356009024948056132632495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142282690733194816353686653 53356009024948056132632495)
    ·
      refine ⟨80034013537422084198948743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53356009024948056132632495 80034013537422084198948743)
      ·
        refine ⟨120051020306133126298423115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80034013537422084198948743 120051020306133126298423115)
        ·
          refine ⟨180076530459199689447634673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120051020306133126298423115 180076530459199689447634673)
          ·
            refine ⟨135057397844399767085726005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180076530459199689447634673 135057397844399767085726005)
            ·
              refine ⟨12661631047912478164286813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135057397844399767085726005 12661631047912478164286813)
              ·
                refine ⟨4748111642967179311607555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12661631047912478164286813 4748111642967179311607555)
                ·
                  refine ⟨7122167464450768967411333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4748111642967179311607555 7122167464450768967411333)
                  ·
                    refine ⟨1335406399584519181389625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7122167464450768967411333 1335406399584519181389625)
                    ·
                      rfl

theorem cell23_7802084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_7802084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802084 prefixEnd_7802084 := by exact prefixLift 7802084
  have htrace : WordTrace (prefixWord ++ tailWord_7802084) baseStart_7802084 baseEnd_7802084 := by
    simpa [prefixWord, tailWord_7802084, baseEnd_7802084] using wordTrace_append hprefix tailTrace_7802084
  have hstable : (prefixWord ++ tailWord_7802084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802084).length < 2 ^ (prefixWord ++ tailWord_7802084).sum := by decide
  have hdescent : baseEnd_7802084 < baseStart_7802084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802114 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 6]
def baseStart_7802114 : Nat := 118140960795 + 7802114 * 2 ^ 59
def prefixEnd_7802114 : Nat := 4983230072969 + 3 ^ 40 * 7802114 * 2
def baseEnd_7802114 : Nat := 445137178130354714088193

theorem tailTrace_7802114 : CollatzResearch.WordTrace tailWord_7802114 prefixEnd_7802114 445137178130354714088193 := by
  unfold tailWord_7802114
  simp only [CollatzResearch.WordTrace]
  refine ⟨71141618914070236957741349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189710983770853965220643597 71141618914070236957741349)
  ·
    refine ⟨13339053546388169429576503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71141618914070236957741349 13339053546388169429576503)
    ·
      refine ⟨20008580319582254144364755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13339053546388169429576503 20008580319582254144364755)
      ·
        refine ⟨30012870479373381216547133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20008580319582254144364755 30012870479373381216547133)
        ·
          refine ⟨11254826429765017956205175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30012870479373381216547133 11254826429765017956205175)
          ·
            refine ⟨16882239644647526934307763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11254826429765017956205175 16882239644647526934307763)
            ·
              refine ⟨25323359466971290401461645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16882239644647526934307763 25323359466971290401461645)
              ·
                refine ⟨9496259800114233900548117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25323359466971290401461645 9496259800114233900548117)
                ·
                  refine ⟨445137178130354714088193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9496259800114233900548117 445137178130354714088193)
                  ·
                    rfl

theorem cell23_7802114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_7802114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802114 prefixEnd_7802114 := by exact prefixLift 7802114
  have htrace : WordTrace (prefixWord ++ tailWord_7802114) baseStart_7802114 baseEnd_7802114 := by
    simpa [prefixWord, tailWord_7802114, baseEnd_7802114] using wordTrace_append hprefix tailTrace_7802114
  have hstable : (prefixWord ++ tailWord_7802114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802114).length < 2 ^ (prefixWord ++ tailWord_7802114).sum := by decide
  have hdescent : baseEnd_7802114 < baseStart_7802114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802117 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 4, 3, 2]
def baseStart_7802117 : Nat := 118140960795 + 7802117 * 2 ^ 59
def prefixEnd_7802117 : Nat := 4983230072969 + 3 ^ 40 * 7802117 * 2
def baseEnd_7802117 : Nat := 4006236143615155915056223

theorem tailTrace_7802117 : CollatzResearch.WordTrace tailWord_7802117 prefixEnd_7802117 4006236143615155915056223 := by
  unfold tailWord_7802117
  simp only [CollatzResearch.WordTrace]
  refine ⟨284566585075270079343324605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189711056716846719562216403 284566585075270079343324605)
  ·
    refine ⟨106712469403226279753746727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284566585075270079343324605 106712469403226279753746727)
    ·
      refine ⟨160068704104839419630620091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106712469403226279753746727 160068704104839419630620091)
      ·
        refine ⟨240103056157259129445930137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160068704104839419630620091 240103056157259129445930137)
        ·
          refine ⟨180077292117944347084447603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240103056157259129445930137 180077292117944347084447603)
          ·
            refine ⟨270115938176916520626671405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180077292117944347084447603 270115938176916520626671405)
            ·
              refine ⟨101293476816343695235001777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270115938176916520626671405 101293476816343695235001777)
              ·
                refine ⟨75970107612257771426251333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101293476816343695235001777 75970107612257771426251333)
                ·
                  refine ⟨14244395177298332142422125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75970107612257771426251333 14244395177298332142422125)
                  ·
                    refine ⟨5341648191486874553408297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14244395177298332142422125 5341648191486874553408297)
                    ·
                      refine ⟨4006236143615155915056223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341648191486874553408297 4006236143615155915056223)
                      ·
                        rfl

theorem cell23_7802117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_7802117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802117 prefixEnd_7802117 := by exact prefixLift 7802117
  have htrace : WordTrace (prefixWord ++ tailWord_7802117) baseStart_7802117 baseEnd_7802117 := by
    simpa [prefixWord, tailWord_7802117, baseEnd_7802117] using wordTrace_append hprefix tailTrace_7802117
  have hstable : (prefixWord ++ tailWord_7802117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802117).length < 2 ^ (prefixWord ++ tailWord_7802117).sum := by decide
  have hdescent : baseEnd_7802117 < baseStart_7802117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802140 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 3, 6]
def baseStart_7802140 : Nat := 118140960795 + 7802140 * 2 ^ 59
def prefixEnd_7802140 : Nat := 4983230072969 + 3 ^ 40 * 7802140 * 2
def baseEnd_7802140 : Nat := 1335415984556736441689539

theorem tailTrace_7802140 : CollatzResearch.WordTrace tailWord_7802140 prefixEnd_7802140 1335415984556736441689539 := by
  unfold tailWord_7802140
  simp only [CollatzResearch.WordTrace]
  refine ⟨142283711977093377135705937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189711615969457836180941249 142283711977093377135705937)
  ·
    refine ⟨106712783982820032851779453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142283711977093377135705937 106712783982820032851779453)
    ·
      refine ⟨40017293993557512319417295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106712783982820032851779453 40017293993557512319417295)
      ·
        refine ⟨60025940990336268479125943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40017293993557512319417295 60025940990336268479125943)
        ·
          refine ⟨90038911485504402718688915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60025940990336268479125943 90038911485504402718688915)
          ·
            refine ⟨135058367228256604078033373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90038911485504402718688915 135058367228256604078033373)
            ·
              refine ⟨50646887710596226529262515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135058367228256604078033373 50646887710596226529262515)
              ·
                refine ⟨75970331565894339793893773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50646887710596226529262515 75970331565894339793893773)
                ·
                  refine ⟨28488874337210377422710165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75970331565894339793893773 28488874337210377422710165)
                  ·
                    refine ⟨1335415984556736441689539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28488874337210377422710165 1335415984556736441689539)
                    ·
                      rfl

theorem cell23_7802140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_7802140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802140 prefixEnd_7802140 := by exact prefixLift 7802140
  have htrace : WordTrace (prefixWord ++ tailWord_7802140) baseStart_7802140 baseEnd_7802140 := by
    simpa [prefixWord, tailWord_7802140, baseEnd_7802140] using wordTrace_append hprefix tailTrace_7802140
  have hstable : (prefixWord ++ tailWord_7802140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802140).length < 2 ^ (prefixWord ++ tailWord_7802140).sum := by decide
  have hdescent : baseEnd_7802140 < baseStart_7802140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802160 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_7802160 : Nat := 118140960795 + 7802160 * 2 ^ 59
def prefixEnd_7802160 : Nat := 4983230072969 + 3 ^ 40 * 7802160 * 2
def baseEnd_7802160 : Nat := 4006258223283299246818525

theorem tailTrace_7802160 : CollatzResearch.WordTrace tailWord_7802160 prefixEnd_7802160 4006258223283299246818525 := by
  unfold tailWord_7802160
  simp only [CollatzResearch.WordTrace]
  refine ⟨142284076707057148843569967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189712102276076198458093289 142284076707057148843569967)
  ·
    refine ⟨213426115060585723265354951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142284076707057148843569967 213426115060585723265354951)
    ·
      refine ⟨320139172590878584898032427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213426115060585723265354951 320139172590878584898032427)
      ·
        refine ⟨480208758886317877347048641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320139172590878584898032427 480208758886317877347048641)
        ·
          refine ⟨360156569164738408010286481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480208758886317877347048641 360156569164738408010286481)
          ·
            refine ⟨270117426873553806007714861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360156569164738408010286481 270117426873553806007714861)
            ·
              refine ⟨101294035077582677252893073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270117426873553806007714861 101294035077582677252893073)
              ·
                refine ⟨75970526308187007939669805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101294035077582677252893073 75970526308187007939669805)
                ·
                  refine ⟨28488947365570127977376177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75970526308187007939669805 28488947365570127977376177)
                  ·
                    refine ⟨21366710524177595983032133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28488947365570127977376177 21366710524177595983032133)
                    ·
                      refine ⟨4006258223283299246818525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21366710524177595983032133 4006258223283299246818525)
                      ·
                        rfl

theorem cell23_7802160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_7802160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802160 prefixEnd_7802160 := by exact prefixLift 7802160
  have htrace : WordTrace (prefixWord ++ tailWord_7802160) baseStart_7802160 baseEnd_7802160 := by
    simpa [prefixWord, tailWord_7802160, baseEnd_7802160] using wordTrace_append hprefix tailTrace_7802160
  have hstable : (prefixWord ++ tailWord_7802160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802160).length < 2 ^ (prefixWord ++ tailWord_7802160).sum := by decide
  have hdescent : baseEnd_7802160 < baseStart_7802160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802174 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_7802174 : Nat := 118140960795 + 7802174 * 2 ^ 59
def prefixEnd_7802174 : Nat := 4983230072969 + 3 ^ 40 * 7802174 * 2
def baseEnd_7802174 : Nat := 1335421804004154064014487

theorem tailTrace_7802174 : CollatzResearch.WordTrace tailWord_7802174 prefixEnd_7802174 1335421804004154064014487 := by
  unfold tailWord_7802174
  simp only [CollatzResearch.WordTrace]
  refine ⟨35571083004507947259768697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189712442690709052052099717 35571083004507947259768697)
  ·
    refine ⟨26678312253380960444826523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35571083004507947259768697 26678312253380960444826523)
    ·
      refine ⟨40017468380071440667239785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26678312253380960444826523 40017468380071440667239785)
      ·
        refine ⟨30013101285053580500429839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40017468380071440667239785 30013101285053580500429839)
        ·
          refine ⟨45019651927580370750644759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30013101285053580500429839 45019651927580370750644759)
          ·
            refine ⟨67529477891370556125967139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45019651927580370750644759 67529477891370556125967139)
            ·
              refine ⟨101294216837055834188950709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67529477891370556125967139 101294216837055834188950709)
              ·
                refine ⟨9496332828473984455214129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101294216837055834188950709 9496332828473984455214129)
                ·
                  refine ⟨7122249621355488341410597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9496332828473984455214129 7122249621355488341410597)
                  ·
                    refine ⟨1335421804004154064014487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7122249621355488341410597 1335421804004154064014487)
                    ·
                      rfl

theorem cell23_7802174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_7802174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802174 prefixEnd_7802174 := by exact prefixLift 7802174
  have htrace : WordTrace (prefixWord ++ tailWord_7802174) baseStart_7802174 baseEnd_7802174 := by
    simpa [prefixWord, tailWord_7802174, baseEnd_7802174] using wordTrace_append hprefix tailTrace_7802174
  have hstable : (prefixWord ++ tailWord_7802174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802174).length < 2 ^ (prefixWord ++ tailWord_7802174).sum := by decide
  have hdescent : baseEnd_7802174 < baseStart_7802174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802231 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 2, 1, 3]
def baseStart_7802231 : Nat := 118140960795 + 7802231 * 2 ^ 59
def prefixEnd_7802231 : Nat := 4983230072969 + 3 ^ 40 * 7802231 * 2
def baseEnd_7802231 : Nat := 4006294680409768469030699

theorem tailTrace_7802231 : CollatzResearch.WordTrace tailWord_7802231 prefixEnd_7802231 4006294680409768469030699 := by
  unfold tailWord_7802231
  simp only [CollatzResearch.WordTrace]
  refine ⟨284570742996857076812974547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189713828664571384541983031 284570742996857076812974547)
  ·
    refine ⟨426856114495285615219461821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284570742996857076812974547 426856114495285615219461821)
    ·
      refine ⟨160071042935732105707298183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426856114495285615219461821 160071042935732105707298183)
      ·
        refine ⟨240106564403598158560947275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160071042935732105707298183 240106564403598158560947275)
        ·
          refine ⟨360159846605397237841420913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240106564403598158560947275 360159846605397237841420913)
          ·
            refine ⟨270119884954047928381065685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360159846605397237841420913 270119884954047928381065685)
            ·
              refine ⟨6330934803610498321431227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 270119884954047928381065685 6330934803610498321431227)
              ·
                refine ⟨9496402205415747482146841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6330934803610498321431227 9496402205415747482146841)
                ·
                  refine ⟨7122301654061810611610131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9496402205415747482146841 7122301654061810611610131)
                  ·
                    refine ⟨10683452481092715917415197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7122301654061810611610131 10683452481092715917415197)
                    ·
                      refine ⟨4006294680409768469030699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10683452481092715917415197 4006294680409768469030699)
                      ·
                        rfl

theorem cell23_7802231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 2, 1, 3].length) (baseStart_7802231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802231 prefixEnd_7802231 := by exact prefixLift 7802231
  have htrace : WordTrace (prefixWord ++ tailWord_7802231) baseStart_7802231 baseEnd_7802231 := by
    simpa [prefixWord, tailWord_7802231, baseEnd_7802231] using wordTrace_append hprefix tailTrace_7802231
  have hstable : (prefixWord ++ tailWord_7802231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802231).length < 2 ^ (prefixWord ++ tailWord_7802231).sum := by decide
  have hdescent : baseEnd_7802231 < baseStart_7802231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802238 : List Nat := [4, 2, 3, 2, 1, 2, 2, 7]
def baseStart_7802238 : Nat := 118140960795 + 7802238 * 2 ^ 59
def prefixEnd_7802238 : Nat := 4983230072969 + 3 ^ 40 * 7802238 * 2
def baseEnd_7802238 : Nat := 148381417584235183023821

theorem tailTrace_7802238 : CollatzResearch.WordTrace tailWord_7802238 prefixEnd_7802238 148381417584235183023821 := by
  unfold tailWord_7802238
  simp only [CollatzResearch.WordTrace]
  refine ⟨35571374788478964626059921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189713998871887811338986245 35571374788478964626059921)
  ·
    refine ⟨26678531091359223469544941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35571374788478964626059921 26678531091359223469544941)
    ·
      refine ⟨10004449159259708801079353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26678531091359223469544941 10004449159259708801079353)
      ·
        refine ⟨7503336869444781600809515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10004449159259708801079353 7503336869444781600809515)
        ·
          refine ⟨11255005304167172401214273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7503336869444781600809515 11255005304167172401214273)
          ·
            refine ⟨8441253978125379300910705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11255005304167172401214273 8441253978125379300910705)
            ·
              refine ⟨6330940483594034475683029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8441253978125379300910705 6330940483594034475683029)
              ·
                refine ⟨148381417584235183023821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6330940483594034475683029 148381417584235183023821)
                ·
                  rfl

theorem cell23_7802238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_7802238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802238 prefixEnd_7802238 := by exact prefixLift 7802238
  have htrace : WordTrace (prefixWord ++ tailWord_7802238) baseStart_7802238 baseEnd_7802238 := by
    simpa [prefixWord, tailWord_7802238, baseEnd_7802238] using wordTrace_append hprefix tailTrace_7802238
  have hstable : (prefixWord ++ tailWord_7802238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802238).length < 2 ^ (prefixWord ++ tailWord_7802238).sum := by decide
  have hdescent : baseEnd_7802238 < baseStart_7802238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802240 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_7802240 : Nat := 118140960795 + 7802240 * 2 ^ 59
def prefixEnd_7802240 : Nat := 4983230072969 + 3 ^ 40 * 7802240 * 2
def baseEnd_7802240 : Nat := 4006299301735658933818157

theorem tailTrace_7802240 : CollatzResearch.WordTrace tailWord_7802240 prefixEnd_7802240 4006299301735658933818157 := by
  unfold tailWord_7802240
  simp only [CollatzResearch.WordTrace]
  refine ⟨142285535626912235675026087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189714047502549647566701449 142285535626912235675026087)
  ·
    refine ⟨213428303440368353512539131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142285535626912235675026087 213428303440368353512539131)
    ·
      refine ⟨320142455160552530268808697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213428303440368353512539131 320142455160552530268808697)
      ·
        refine ⟨240106841370414397701606523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320142455160552530268808697 240106841370414397701606523)
        ·
          refine ⟨360160262055621596552409785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240106841370414397701606523 360160262055621596552409785)
          ·
            refine ⟨270120196541716197414307339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360160262055621596552409785 270120196541716197414307339)
            ·
              refine ⟨405180294812574296121461009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270120196541716197414307339 405180294812574296121461009)
              ·
                refine ⟨303885221109430722091095757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405180294812574296121461009 303885221109430722091095757)
                ·
                  refine ⟨113956957916036520784160909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303885221109430722091095757 113956957916036520784160909)
                  ·
                    refine ⟨42733859218513695294060341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113956957916036520784160909 42733859218513695294060341)
                    ·
                      refine ⟨4006299301735658933818157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42733859218513695294060341 4006299301735658933818157)
                      ·
                        rfl

theorem cell23_7802240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_7802240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802240 prefixEnd_7802240 := by exact prefixLift 7802240
  have htrace : WordTrace (prefixWord ++ tailWord_7802240) baseStart_7802240 baseEnd_7802240 := by
    simpa [prefixWord, tailWord_7802240, baseEnd_7802240] using wordTrace_append hprefix tailTrace_7802240
  have hstable : (prefixWord ++ tailWord_7802240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802240).length < 2 ^ (prefixWord ++ tailWord_7802240).sum := by decide
  have hdescent : baseEnd_7802240 < baseStart_7802240 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802271 : List Nat := [1, 1, 2, 5, 1, 2, 2, 1, 4, 2, 2]
def baseStart_7802271 : Nat := 118140960795 + 7802271 * 2 ^ 59
def prefixEnd_7802271 : Nat := 4983230072969 + 3 ^ 40 * 7802271 * 2
def baseEnd_7802271 : Nat := 4006315219635948312530515

theorem tailTrace_7802271 : CollatzResearch.WordTrace tailWord_7802271 prefixEnd_7802271 4006315219635948312530515 := by
  unfold tailWord_7802271
  simp only [CollatzResearch.WordTrace]
  refine ⟨284572201916712163644430667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189714801277808109096287111 284572201916712163644430667)
  ·
    refine ⟨426858302875068245466646001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284572201916712163644430667 426858302875068245466646001)
    ·
      refine ⟨320143727156301184099984501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426858302875068245466646001 320143727156301184099984501)
      ·
        refine ⟨30013474420903236009373547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320143727156301184099984501 30013474420903236009373547)
        ·
          refine ⟨45020211631354854014060321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30013474420903236009373547 45020211631354854014060321)
          ·
            refine ⟨33765158723516140510545241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45020211631354854014060321 33765158723516140510545241)
            ·
              refine ⟨25323869042637105382908931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33765158723516140510545241 25323869042637105382908931)
              ·
                refine ⟨37985803563955658074363397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25323869042637105382908931 37985803563955658074363397)
                ·
                  refine ⟨7122338168241685888943137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37985803563955658074363397 7122338168241685888943137)
                  ·
                    refine ⟨5341753626181264416707353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7122338168241685888943137 5341753626181264416707353)
                    ·
                      refine ⟨4006315219635948312530515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341753626181264416707353 4006315219635948312530515)
                      ·
                        rfl

theorem cell23_7802271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_7802271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802271 prefixEnd_7802271 := by exact prefixLift 7802271
  have htrace : WordTrace (prefixWord ++ tailWord_7802271) baseStart_7802271 baseEnd_7802271 := by
    simpa [prefixWord, tailWord_7802271, baseEnd_7802271] using wordTrace_append hprefix tailTrace_7802271
  have hstable : (prefixWord ++ tailWord_7802271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802271).length < 2 ^ (prefixWord ++ tailWord_7802271).sum := by decide
  have hdescent : baseEnd_7802271 < baseStart_7802271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802287 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 3]
def baseStart_7802287 : Nat := 118140960795 + 7802287 * 2 ^ 59
def prefixEnd_7802287 : Nat := 4983230072969 + 3 ^ 40 * 7802287 * 2
def baseEnd_7802287 : Nat := 4006323435326420249930441

theorem tailTrace_7802287 : CollatzResearch.WordTrace tailWord_7802287 prefixEnd_7802287 4006323435326420249930441 := by
  unfold tailWord_7802287
  simp only [CollatzResearch.WordTrace]
  refine ⟨284572785484654198377013115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189715190323102798918008743 284572785484654198377013115)
  ·
    refine ⟨426859178226981297565519673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284572785484654198377013115 426859178226981297565519673)
    ·
      refine ⟨320144383670235973174139755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426859178226981297565519673 320144383670235973174139755)
      ·
        refine ⟨480216575505353959761209633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320144383670235973174139755 480216575505353959761209633)
        ·
          refine ⟨360162431629015469820907225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480216575505353959761209633 360162431629015469820907225)
          ·
            refine ⟨270121823721761602365680419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360162431629015469820907225 270121823721761602365680419)
            ·
              refine ⟨405182735582642403548520629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270121823721761602365680419 405182735582642403548520629)
              ·
                refine ⟨37985881460872725332673809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405182735582642403548520629 37985881460872725332673809)
                ·
                  refine ⟨28489411095654543999505357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37985881460872725332673809 28489411095654543999505357)
                  ·
                    refine ⟨10683529160870453999814509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28489411095654543999505357 10683529160870453999814509)
                    ·
                      refine ⟨4006323435326420249930441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10683529160870453999814509 4006323435326420249930441)
                      ·
                        rfl

theorem cell23_7802287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 3].length) (baseStart_7802287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802287 prefixEnd_7802287 := by exact prefixLift 7802287
  have htrace : WordTrace (prefixWord ++ tailWord_7802287) baseStart_7802287 baseEnd_7802287 := by
    simpa [prefixWord, tailWord_7802287, baseEnd_7802287] using wordTrace_append hprefix tailTrace_7802287
  have hstable : (prefixWord ++ tailWord_7802287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802287).length < 2 ^ (prefixWord ++ tailWord_7802287).sum := by decide
  have hdescent : baseEnd_7802287 < baseStart_7802287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802307 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 2, 5]
def baseStart_7802307 : Nat := 118140960795 + 7802307 * 2 ^ 59
def prefixEnd_7802307 : Nat := 4983230072969 + 3 ^ 40 * 7802307 * 2
def baseEnd_7802307 : Nat := 1335444568313170057226783

theorem tailTrace_7802307 : CollatzResearch.WordTrace tailWord_7802307 prefixEnd_7802307 1335444568313170057226783 := by
  unfold tailWord_7802307
  simp only [CollatzResearch.WordTrace]
  refine ⟨284573514944581741792741175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189715676629721161195160783 284573514944581741792741175)
  ·
    refine ⟨426860272416872612689111763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284573514944581741792741175 426860272416872612689111763)
    ·
      refine ⟨640290408625308919033667645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426860272416872612689111763 640290408625308919033667645)
      ·
        refine ⟨240108903234490844637625367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640290408625308919033667645 240108903234490844637625367)
        ·
          refine ⟨360163354851736266956438051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240108903234490844637625367 360163354851736266956438051)
          ·
            refine ⟨540245032277604400434657077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360163354851736266956438051 540245032277604400434657077)
            ·
              refine ⟨50647971776025412540749101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 540245032277604400434657077 50647971776025412540749101)
              ·
                refine ⟨18992989416009529702780913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50647971776025412540749101 18992989416009529702780913)
                ·
                  refine ⟨14244742062007147277085685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18992989416009529702780913 14244742062007147277085685)
                  ·
                    refine ⟨1335444568313170057226783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14244742062007147277085685 1335444568313170057226783)
                    ·
                      rfl

theorem cell23_7802307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 5].length) (baseStart_7802307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802307 prefixEnd_7802307 := by exact prefixLift 7802307
  have htrace : WordTrace (prefixWord ++ tailWord_7802307) baseStart_7802307 baseEnd_7802307 := by
    simpa [prefixWord, tailWord_7802307, baseEnd_7802307] using wordTrace_append hprefix tailTrace_7802307
  have hstable : (prefixWord ++ tailWord_7802307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802307).length < 2 ^ (prefixWord ++ tailWord_7802307).sum := by decide
  have hdescent : baseEnd_7802307 < baseStart_7802307 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802387 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 6]
def baseStart_7802387 : Nat := 118140960795 + 7802387 * 2 ^ 59
def prefixEnd_7802387 : Nat := 4983230072969 + 3 ^ 40 * 7802387 * 2
def baseEnd_7802387 : Nat := 4006374783391869858679981

theorem tailTrace_7802387 : CollatzResearch.WordTrace tailWord_7802387 prefixEnd_7802387 4006374783391869858679981 := by
  unfold tailWord_7802387
  simp only [CollatzResearch.WordTrace]
  refine ⟨284576432784291915455653415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189717621856194610303768943 284576432784291915455653415)
  ·
    refine ⟨426864649176437873183480123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284576432784291915455653415 426864649176437873183480123)
    ·
      refine ⟨640296973764656809775220185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426864649176437873183480123 640296973764656809775220185)
      ·
        refine ⟨480222730323492607331415139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640296973764656809775220185 480222730323492607331415139)
        ·
          refine ⟨720334095485238910997122709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480222730323492607331415139 720334095485238910997122709)
          ·
            refine ⟨33765660725870573952990127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 720334095485238910997122709 33765660725870573952990127)
            ·
              refine ⟨50648491088805860929485191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33765660725870573952990127 50648491088805860929485191)
              ·
                refine ⟨75972736633208791394227787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50648491088805860929485191 75972736633208791394227787)
                ·
                  refine ⟨113959104949813187091341681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75972736633208791394227787 113959104949813187091341681)
                  ·
                    refine ⟨85469328712359890318506261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113959104949813187091341681 85469328712359890318506261)
                    ·
                      refine ⟨4006374783391869858679981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85469328712359890318506261 4006374783391869858679981)
                      ·
                        rfl

theorem cell23_7802387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 6].length) (baseStart_7802387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802387 prefixEnd_7802387 := by exact prefixLift 7802387
  have htrace : WordTrace (prefixWord ++ tailWord_7802387) baseStart_7802387 baseEnd_7802387 := by
    simpa [prefixWord, tailWord_7802387, baseEnd_7802387] using wordTrace_append hprefix tailTrace_7802387
  have hstable : (prefixWord ++ tailWord_7802387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802387).length < 2 ^ (prefixWord ++ tailWord_7802387).sum := by decide
  have hdescent : baseEnd_7802387 < baseStart_7802387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802401 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 6]
def baseStart_7802401 : Nat := 118140960795 + 7802401 * 2 ^ 59
def prefixEnd_7802401 : Nat := 4983230072969 + 3 ^ 40 * 7802401 * 2
def baseEnd_7802401 : Nat := 445153552457892533767213

theorem tailTrace_7802401 : CollatzResearch.WordTrace tailWord_7802401 prefixEnd_7802401 445153552457892533767213 := by
  unfold tailWord_7802401
  simp only [CollatzResearch.WordTrace]
  refine ⟨284576943406241195846663057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189717962270827463897775371 284576943406241195846663057)
  ·
    refine ⟨213432707554680896884997293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284576943406241195846663057 213432707554680896884997293)
    ·
      refine ⟨80037265333005336331873985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213432707554680896884997293 80037265333005336331873985)
      ·
        refine ⟨60027948999754002248905489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80037265333005336331873985 60027948999754002248905489)
        ·
          refine ⟨45020961749815501686679117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60027948999754002248905489 45020961749815501686679117)
          ·
            refine ⟨16882860656180813132504669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45020961749815501686679117 16882860656180813132504669)
            ·
              refine ⟨6331072746067804924689251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16882860656180813132504669 6331072746067804924689251)
              ·
                refine ⟨9496609119101707387033877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6331072746067804924689251 9496609119101707387033877)
                ·
                  refine ⟨445153552457892533767213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9496609119101707387033877 445153552457892533767213)
                  ·
                    rfl

theorem cell23_7802401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 6].length) (baseStart_7802401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802401 prefixEnd_7802401 := by exact prefixLift 7802401
  have htrace : WordTrace (prefixWord ++ tailWord_7802401) baseStart_7802401 baseEnd_7802401 := by
    simpa [prefixWord, tailWord_7802401, baseEnd_7802401] using wordTrace_append hprefix tailTrace_7802401
  have hstable : (prefixWord ++ tailWord_7802401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802401).length < 2 ^ (prefixWord ++ tailWord_7802401).sum := by decide
  have hdescent : baseEnd_7802401 < baseStart_7802401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802421 : List Nat := [1, 3, 3, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_7802421 : Nat := 118140960795 + 7802421 * 2 ^ 59
def prefixEnd_7802421 : Nat := 4983230072969 + 3 ^ 40 * 7802421 * 2
def baseEnd_7802421 : Nat := 4006392241734122725654825

theorem tailTrace_7802421 : CollatzResearch.WordTrace tailWord_7802421 prefixEnd_7802421 4006392241734122725654825 := by
  unfold tailWord_7802421
  simp only [CollatzResearch.WordTrace]
  refine ⟨284577672866168739262391117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189718448577445826174927411 284577672866168739262391117)
  ·
    refine ⟨106716627324813277223396669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284577672866168739262391117 106716627324813277223396669)
    ·
      refine ⟨40018735246804978958773751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106716627324813277223396669 40018735246804978958773751)
      ·
        refine ⟨60028102870207468438160627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40018735246804978958773751 60028102870207468438160627)
        ·
          refine ⟨90042154305311202657240941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60028102870207468438160627 90042154305311202657240941)
          ·
            refine ⟨33765807864491700996465353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90042154305311202657240941 33765807864491700996465353)
            ·
              refine ⟨25324355898368775747349015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33765807864491700996465353 25324355898368775747349015)
              ·
                refine ⟨37986533847553163621023523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25324355898368775747349015 37986533847553163621023523)
                ·
                  refine ⟨56979800771329745431535285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37986533847553163621023523 56979800771329745431535285)
                  ·
                    refine ⟨5341856322312163634206433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56979800771329745431535285 5341856322312163634206433)
                    ·
                      refine ⟨4006392241734122725654825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341856322312163634206433 4006392241734122725654825)
                      ·
                        rfl

theorem cell23_7802421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_7802421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802421 prefixEnd_7802421 := by exact prefixLift 7802421
  have htrace : WordTrace (prefixWord ++ tailWord_7802421) baseStart_7802421 baseEnd_7802421 := by
    simpa [prefixWord, tailWord_7802421, baseEnd_7802421] using wordTrace_append hprefix tailTrace_7802421
  have hstable : (prefixWord ++ tailWord_7802421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802421).length < 2 ^ (prefixWord ++ tailWord_7802421).sum := by decide
  have hdescent : baseEnd_7802421 < baseStart_7802421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802422 : List Nat := [5, 1, 2, 1, 3, 2, 1, 3, 1, 4]
def baseStart_7802422 : Nat := 118140960795 + 7802422 * 2 ^ 59
def prefixEnd_7802422 : Nat := 4983230072969 + 3 ^ 40 * 7802422 * 2
def baseEnd_7802422 : Nat := 1335464251738259073914107

theorem tailTrace_7802422 : CollatzResearch.WordTrace tailWord_7802422 prefixEnd_7802422 1335464251738259073914107 := by
  unfold tailWord_7802422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17786106833697819777073595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189718472892776744288785013 17786106833697819777073595)
  ·
    refine ⟨26679160250546729665610393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17786106833697819777073595 26679160250546729665610393)
    ·
      refine ⟨20009370187910047249207795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26679160250546729665610393 20009370187910047249207795)
      ·
        refine ⟨30014055281865070873811693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20009370187910047249207795 30014055281865070873811693)
        ·
          refine ⟨11255270730699401577679385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30014055281865070873811693 11255270730699401577679385)
          ·
            refine ⟨8441453048024551183259539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11255270730699401577679385 8441453048024551183259539)
            ·
              refine ⟨12662179572036826774889309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8441453048024551183259539 12662179572036826774889309)
              ·
                refine ⟨4748317339513810040583491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12662179572036826774889309 4748317339513810040583491)
                ·
                  refine ⟨7122476009270715060875237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4748317339513810040583491 7122476009270715060875237)
                  ·
                    refine ⟨1335464251738259073914107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7122476009270715060875237 1335464251738259073914107)
                    ·
                      rfl

theorem cell23_7802422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_7802422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802422 prefixEnd_7802422 := by exact prefixLift 7802422
  have htrace : WordTrace (prefixWord ++ tailWord_7802422) baseStart_7802422 baseEnd_7802422 := by
    simpa [prefixWord, tailWord_7802422, baseEnd_7802422] using wordTrace_append hprefix tailTrace_7802422
  have hstable : (prefixWord ++ tailWord_7802422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802422).length < 2 ^ (prefixWord ++ tailWord_7802422).sum := by decide
  have hdescent : baseEnd_7802422 < baseStart_7802422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802451 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 9, 2, 2]
def baseStart_7802451 : Nat := 118140960795 + 7802451 * 2 ^ 59
def prefixEnd_7802451 : Nat := 4983230072969 + 3 ^ 40 * 7802451 * 2
def baseEnd_7802451 : Nat := 4006407646153757608279687

theorem tailTrace_7802451 : CollatzResearch.WordTrace tailWord_7802451 prefixEnd_7802451 4006407646153757608279687 := by
  unfold tailWord_7802451
  simp only [CollatzResearch.WordTrace]
  refine ⟨284578767056060054385983207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189719178037373369590655471 284578767056060054385983207)
  ·
    refine ⟨426868150584090081578974811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284578767056060054385983207 426868150584090081578974811)
    ·
      refine ⟨640302225876135122368462217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426868150584090081578974811 640302225876135122368462217)
      ·
        refine ⟨480226669407101341776346663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640302225876135122368462217 480226669407101341776346663)
        ·
          refine ⟨720340004110652012664519995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480226669407101341776346663 720340004110652012664519995)
          ·
            refine ⟨1080510006165978018996779993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720340004110652012664519995 1080510006165978018996779993)
            ·
              refine ⟨810382504624483514247584995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1080510006165978018996779993 810382504624483514247584995)
              ·
                refine ⟨1215573756936725271371377493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810382504624483514247584995 1215573756936725271371377493)
                ·
                  refine ⟨7122502482051124636941665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1215573756936725271371377493 7122502482051124636941665)
                  ·
                    refine ⟨5341876861538343477706249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7122502482051124636941665 5341876861538343477706249)
                    ·
                      refine ⟨4006407646153757608279687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341876861538343477706249 4006407646153757608279687)
                      ·
                        rfl

theorem cell23_7802451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 2, 2].length) (baseStart_7802451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802451 prefixEnd_7802451 := by exact prefixLift 7802451
  have htrace : WordTrace (prefixWord ++ tailWord_7802451) baseStart_7802451 baseEnd_7802451 := by
    simpa [prefixWord, tailWord_7802451, baseEnd_7802451] using wordTrace_append hprefix tailTrace_7802451
  have hstable : (prefixWord ++ tailWord_7802451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802451).length < 2 ^ (prefixWord ++ tailWord_7802451).sum := by decide
  have hdescent : baseEnd_7802451 < baseStart_7802451 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802464 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 4]
def baseStart_7802464 : Nat := 118140960795 + 7802464 * 2 ^ 59
def prefixEnd_7802464 : Nat := 4983230072969 + 3 ^ 40 * 7802464 * 2
def baseEnd_7802464 : Nat := 4006414321402266057417127

theorem tailTrace_7802464 : CollatzResearch.WordTrace tailWord_7802464 prefixEnd_7802464 4006414321402266057417127 := by
  unfold tailWord_7802464
  simp only [CollatzResearch.WordTrace]
  refine ⟨142289620602506478803103223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189719494136675305070804297 142289620602506478803103223)
  ·
    refine ⟨213434430903759718204654835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142289620602506478803103223 213434430903759718204654835)
    ·
      refine ⟨320151646355639577306982253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213434430903759718204654835 320151646355639577306982253)
      ·
        refine ⟨120056867383364841490118345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320151646355639577306982253 120056867383364841490118345)
        ·
          refine ⟨90042650537523631117588759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120056867383364841490118345 90042650537523631117588759)
          ·
            refine ⟨135063975806285446676383139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90042650537523631117588759 135063975806285446676383139)
            ·
              refine ⟨202595963709428170014574709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135063975806285446676383139 202595963709428170014574709)
              ·
                refine ⟨18993371597758890938866379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202595963709428170014574709 18993371597758890938866379)
                ·
                  refine ⟨28490057396638336408299569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18993371597758890938866379 28490057396638336408299569)
                  ·
                    refine ⟨21367543047478752306224677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28490057396638336408299569 21367543047478752306224677)
                    ·
                      refine ⟨4006414321402266057417127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21367543047478752306224677 4006414321402266057417127)
                      ·
                        rfl

theorem cell23_7802464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_7802464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802464 prefixEnd_7802464 := by exact prefixLift 7802464
  have htrace : WordTrace (prefixWord ++ tailWord_7802464) baseStart_7802464 baseEnd_7802464 := by
    simpa [prefixWord, tailWord_7802464, baseEnd_7802464] using wordTrace_append hprefix tailTrace_7802464
  have hstable : (prefixWord ++ tailWord_7802464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802464).length < 2 ^ (prefixWord ++ tailWord_7802464).sum := by decide
  have hdescent : baseEnd_7802464 < baseStart_7802464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802468 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 1, 1, 4]
def baseStart_7802468 : Nat := 118140960795 + 7802468 * 2 ^ 59
def prefixEnd_7802468 : Nat := 4983230072969 + 3 ^ 40 * 7802468 * 2
def baseEnd_7802468 : Nat := 4006416375324884041767109

theorem tailTrace_7802468 : CollatzResearch.WordTrace tailWord_7802468 prefixEnd_7802468 4006416375324884041767109 := by
  unfold tailWord_7802468
  simp only [CollatzResearch.WordTrace]
  refine ⟨142289693548499233144676029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189719591397998977526234705 142289693548499233144676029)
  ·
    refine ⟨53358635080687212429253511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142289693548499233144676029 53358635080687212429253511)
    ·
      refine ⟨80037952621030818643880267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53358635080687212429253511 80037952621030818643880267)
      ·
        refine ⟨120056928931546227965820401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80037952621030818643880267 120056928931546227965820401)
        ·
          refine ⟨90042696698659670974365301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120056928931546227965820401 90042696698659670974365301)
          ·
            refine ⟨8441502815499344153846747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90042696698659670974365301 8441502815499344153846747)
            ·
              refine ⟨12662254223249016230770121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8441502815499344153846747 12662254223249016230770121)
              ·
                refine ⟨9496690667436762173077591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12662254223249016230770121 9496690667436762173077591)
                ·
                  refine ⟨14245036001155143259616387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9496690667436762173077591 14245036001155143259616387)
                  ·
                    refine ⟨21367554001732714889424581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14245036001155143259616387 21367554001732714889424581)
                    ·
                      refine ⟨4006416375324884041767109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21367554001732714889424581 4006416375324884041767109)
                      ·
                        rfl

theorem cell23_7802468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_7802468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802468 prefixEnd_7802468 := by exact prefixLift 7802468
  have htrace : WordTrace (prefixWord ++ tailWord_7802468) baseStart_7802468 baseEnd_7802468 := by
    simpa [prefixWord, tailWord_7802468, baseEnd_7802468] using wordTrace_append hprefix tailTrace_7802468
  have hstable : (prefixWord ++ tailWord_7802468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802468).length < 2 ^ (prefixWord ++ tailWord_7802468).sum := by decide
  have hdescent : baseEnd_7802468 < baseStart_7802468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802474 : List Nat := [3, 1, 3, 2, 1, 2, 2, 9]
def baseStart_7802474 : Nat := 118140960795 + 7802474 * 2 ^ 59
def prefixEnd_7802474 : Nat := 4983230072969 + 3 ^ 40 * 7802474 * 2
def baseEnd_7802474 : Nat := 148385905785511519196003

theorem tailTrace_7802474 : CollatzResearch.WordTrace tailWord_7802474 prefixEnd_7802474 148385905785511519196003 := by
  unfold tailWord_7802474
  simp only [CollatzResearch.WordTrace]
  refine ⟨71144901483744182328517619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189719737289984486209380317 71144901483744182328517619)
  ·
    refine ⟨106717352225616273492776429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71144901483744182328517619 106717352225616273492776429)
    ·
      refine ⟨40019007084606102559791161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106717352225616273492776429 40019007084606102559791161)
      ·
        refine ⟨30014255313454576919843371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40019007084606102559791161 30014255313454576919843371)
        ·
          refine ⟨45021382970181865379765057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30014255313454576919843371 45021382970181865379765057)
          ·
            refine ⟨33766037227636399034823793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45021382970181865379765057 33766037227636399034823793)
            ·
              refine ⟨25324527920727299276117845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33766037227636399034823793 25324527920727299276117845)
              ·
                refine ⟨148385905785511519196003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25324527920727299276117845 148385905785511519196003)
                ·
                  rfl

theorem cell23_7802474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 9].length) (baseStart_7802474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802474 prefixEnd_7802474 := by exact prefixLift 7802474
  have htrace : WordTrace (prefixWord ++ tailWord_7802474) baseStart_7802474 baseEnd_7802474 := by
    simpa [prefixWord, tailWord_7802474, baseEnd_7802474] using wordTrace_append hprefix tailTrace_7802474
  have hstable : (prefixWord ++ tailWord_7802474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802474).length < 2 ^ (prefixWord ++ tailWord_7802474).sum := by decide
  have hdescent : baseEnd_7802474 < baseStart_7802474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802485 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_7802485 : Nat := 118140960795 + 7802485 * 2 ^ 59
def prefixEnd_7802485 : Nat := 4983230072969 + 3 ^ 40 * 7802485 * 2
def baseEnd_7802485 : Nat := 4006425104496010475254531

theorem tailTrace_7802485 : CollatzResearch.WordTrace tailWord_7802485 prefixEnd_7802485 4006425104496010475254531 := by
  unfold tailWord_7802485
  simp only [CollatzResearch.WordTrace]
  refine ⟨284580007137936878192720909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189720004758624585461813939 284580007137936878192720909)
  ·
    refine ⟨106717502676726329322270341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284580007137936878192720909 106717502676726329322270341)
    ·
      refine ⟨20009531751886186747925689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106717502676726329322270341 20009531751886186747925689)
      ·
        refine ⟨15007148813914640060944267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20009531751886186747925689 15007148813914640060944267)
        ·
          refine ⟨22510723220871960091416401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15007148813914640060944267 22510723220871960091416401)
          ·
            refine ⟨16883042415653970068562301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22510723220871960091416401 16883042415653970068562301)
            ·
              refine ⟨6331140905870238775710863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16883042415653970068562301 6331140905870238775710863)
              ·
                refine ⟨9496711358805358163566295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6331140905870238775710863 9496711358805358163566295)
                ·
                  refine ⟨14245067038208037245349443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9496711358805358163566295 14245067038208037245349443)
                  ·
                    refine ⟨21367600557312055868024165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14245067038208037245349443 21367600557312055868024165)
                    ·
                      refine ⟨4006425104496010475254531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21367600557312055868024165 4006425104496010475254531)
                      ·
                        rfl

theorem cell23_7802485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_7802485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802485 prefixEnd_7802485 := by exact prefixLift 7802485
  have htrace : WordTrace (prefixWord ++ tailWord_7802485) baseStart_7802485 baseEnd_7802485 := by
    simpa [prefixWord, tailWord_7802485, baseEnd_7802485] using wordTrace_append hprefix tailTrace_7802485
  have hstable : (prefixWord ++ tailWord_7802485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802485).length < 2 ^ (prefixWord ++ tailWord_7802485).sum := by decide
  have hdescent : baseEnd_7802485 < baseStart_7802485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802528 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 3, 3, 2]
def baseStart_7802528 : Nat := 118140960795 + 7802528 * 2 ^ 59
def prefixEnd_7802528 : Nat := 4983230072969 + 3 ^ 40 * 7802528 * 2
def baseEnd_7802528 : Nat := 4006447184164153807016833

theorem tailTrace_7802528 : CollatzResearch.WordTrace tailWord_7802528 prefixEnd_7802528 4006447184164153807016833 := by
  unfold tailWord_7802528
  simp only [CollatzResearch.WordTrace]
  refine ⟨142290787738390548268268119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189721050317854064357690825 142290787738390548268268119)
  ·
    refine ⟨213436181607585822402402179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142290787738390548268268119 213436181607585822402402179)
    ·
      refine ⟨320154272411378733603603269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213436181607585822402402179 320154272411378733603603269)
      ·
        refine ⟨60028926077133512550675613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320154272411378733603603269 60028926077133512550675613)
        ·
          refine ⟨22510847278925067206503355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60028926077133512550675613 22510847278925067206503355)
          ·
            refine ⟨33766270918387600809755033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22510847278925067206503355 33766270918387600809755033)
            ·
              refine ⟨25324703188790700607316275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33766270918387600809755033 25324703188790700607316275)
              ·
                refine ⟨37987054783186050910974413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25324703188790700607316275 37987054783186050910974413)
                ·
                  refine ⟨14245145543694769091615405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37987054783186050910974413 14245145543694769091615405)
                  ·
                    refine ⟨5341929578885538409355777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14245145543694769091615405 5341929578885538409355777)
                    ·
                      refine ⟨4006447184164153807016833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341929578885538409355777 4006447184164153807016833)
                      ·
                        rfl

theorem cell23_7802528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_7802528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802528 prefixEnd_7802528 := by exact prefixLift 7802528
  have htrace : WordTrace (prefixWord ++ tailWord_7802528) baseStart_7802528 baseEnd_7802528 := by
    simpa [prefixWord, tailWord_7802528, baseEnd_7802528] using wordTrace_append hprefix tailTrace_7802528
  have hstable : (prefixWord ++ tailWord_7802528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802528).length < 2 ^ (prefixWord ++ tailWord_7802528).sum := by decide
  have hdescent : baseEnd_7802528 < baseStart_7802528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802536 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7802536 : Nat := 118140960795 + 7802536 * 2 ^ 59
def prefixEnd_7802536 : Nat := 4983230072969 + 3 ^ 40 * 7802536 * 2
def baseEnd_7802536 : Nat := 4006451292009389775716797

theorem tailTrace_7802536 : CollatzResearch.WordTrace tailWord_7802536 prefixEnd_7802536 4006451292009389775716797 := by
  unfold tailWord_7802536
  simp only [CollatzResearch.WordTrace]
  refine ⟨142290933630376056951413731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189721244840501409268551641 142290933630376056951413731)
  ·
    refine ⟨213436400445564085427120597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142290933630376056951413731 213436400445564085427120597)
    ·
      refine ⟨5002415635442908252198139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 213436400445564085427120597 5002415635442908252198139)
      ·
        refine ⟨7503623453164362378297209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002415635442908252198139 7503623453164362378297209)
        ·
          refine ⟨5627717589873271783722907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7503623453164362378297209 5627717589873271783722907)
          ·
            refine ⟨8441576384809907675584361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5627717589873271783722907 8441576384809907675584361)
            ·
              refine ⟨6331182288607430756688271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8441576384809907675584361 6331182288607430756688271)
              ·
                refine ⟨9496773432911146135032407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6331182288607430756688271 9496773432911146135032407)
                ·
                  refine ⟨14245160149366719202548611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9496773432911146135032407 14245160149366719202548611)
                  ·
                    refine ⟨21367740224050078803822917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14245160149366719202548611 21367740224050078803822917)
                    ·
                      refine ⟨4006451292009389775716797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21367740224050078803822917 4006451292009389775716797)
                      ·
                        rfl

theorem cell23_7802536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7802536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802536 prefixEnd_7802536 := by exact prefixLift 7802536
  have htrace : WordTrace (prefixWord ++ tailWord_7802536) baseStart_7802536 baseEnd_7802536 := by
    simpa [prefixWord, tailWord_7802536, baseEnd_7802536] using wordTrace_append hprefix tailTrace_7802536
  have hstable : (prefixWord ++ tailWord_7802536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802536).length < 2 ^ (prefixWord ++ tailWord_7802536).sum := by decide
  have hdescent : baseEnd_7802536 < baseStart_7802536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802544 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_7802544 : Nat := 118140960795 + 7802544 * 2 ^ 59
def prefixEnd_7802544 : Nat := 4983230072969 + 3 ^ 40 * 7802544 * 2
def baseEnd_7802544 : Nat := 4006455399854625744416759

theorem tailTrace_7802544 : CollatzResearch.WordTrace tailWord_7802544 prefixEnd_7802544 4006455399854625744416759 := by
  unfold tailWord_7802544
  simp only [CollatzResearch.WordTrace]
  refine ⟨142291079522361565634559343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189721439363148754179412457 142291079522361565634559343)
  ·
    refine ⟨213436619283542348451839015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142291079522361565634559343 213436619283542348451839015)
    ·
      refine ⟨320154928925313522677758523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213436619283542348451839015 320154928925313522677758523)
      ·
        refine ⟨480232393387970284016637785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320154928925313522677758523 480232393387970284016637785)
        ·
          refine ⟨360174295040977713012478339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480232393387970284016637785 360174295040977713012478339)
          ·
            refine ⟨540261442561466569518717509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360174295040977713012478339 540261442561466569518717509)
            ·
              refine ⟨101299020480274981784759533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540261442561466569518717509 101299020480274981784759533)
              ·
                refine ⟨37987132680103118169284825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101299020480274981784759533 37987132680103118169284825)
                ·
                  refine ⟨28490349510077338626963619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37987132680103118169284825 28490349510077338626963619)
                  ·
                    refine ⟨42735524265116007940445429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28490349510077338626963619 42735524265116007940445429)
                    ·
                      refine ⟨4006455399854625744416759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42735524265116007940445429 4006455399854625744416759)
                      ·
                        rfl

theorem cell23_7802544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_7802544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802544 prefixEnd_7802544 := by exact prefixLift 7802544
  have htrace : WordTrace (prefixWord ++ tailWord_7802544) baseStart_7802544 baseEnd_7802544 := by
    simpa [prefixWord, tailWord_7802544, baseEnd_7802544] using wordTrace_append hprefix tailTrace_7802544
  have hstable : (prefixWord ++ tailWord_7802544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802544).length < 2 ^ (prefixWord ++ tailWord_7802544).sum := by decide
  have hdescent : baseEnd_7802544 < baseStart_7802544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802601 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 1, 7, 2]
def baseStart_7802601 : Nat := 118140960795 + 7802601 * 2 ^ 59
def prefixEnd_7802601 : Nat := 4983230072969 + 3 ^ 40 * 7802601 * 2
def baseEnd_7802601 : Nat := 4006484668251932021403997

theorem tailTrace_7802601 : CollatzResearch.WordTrace tailWord_7802601 prefixEnd_7802601 4006484668251932021403997 := by
  unfold tailWord_7802601
  simp only [CollatzResearch.WordTrace]
  refine ⟨284584238005516630003943657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189722825337011086669295771 284584238005516630003943657)
  ·
    refine ⟨213438178504137472502957743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284584238005516630003943657 213438178504137472502957743)
    ·
      refine ⟨320157267756206208754436615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213438178504137472502957743 320157267756206208754436615)
      ·
        refine ⟨480235901634309313131654923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320157267756206208754436615 480235901634309313131654923)
        ·
          refine ⟨720353852451463969697482385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480235901634309313131654923 720353852451463969697482385)
          ·
            refine ⟨540265389338597977273111789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720353852451463969697482385 540265389338597977273111789)
            ·
              refine ⟨202599521001974241477416921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 540265389338597977273111789 202599521001974241477416921)
              ·
                refine ⟨151949640751480681108062691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202599521001974241477416921 151949640751480681108062691)
                ·
                  refine ⟨227924461127221021662094037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151949640751480681108062691 227924461127221021662094037)
                  ·
                    refine ⟨5341979557669242695205329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 227924461127221021662094037 5341979557669242695205329)
                    ·
                      refine ⟨4006484668251932021403997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341979557669242695205329 4006484668251932021403997)
                      ·
                        rfl

theorem cell23_7802601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 7, 2].length) (baseStart_7802601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802601 prefixEnd_7802601 := by exact prefixLift 7802601
  have htrace : WordTrace (prefixWord ++ tailWord_7802601) baseStart_7802601 baseEnd_7802601 := by
    simpa [prefixWord, tailWord_7802601, baseEnd_7802601] using wordTrace_append hprefix tailTrace_7802601
  have hstable : (prefixWord ++ tailWord_7802601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802601).length < 2 ^ (prefixWord ++ tailWord_7802601).sum := by decide
  have hdescent : baseEnd_7802601 < baseStart_7802601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802630 : List Nat := [6, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7802630 : Nat := 118140960795 + 7802630 * 2 ^ 59
def prefixEnd_7802630 : Nat := 4983230072969 + 3 ^ 40 * 7802630 * 2
def baseEnd_7802630 : Nat := 4006499559190912407941365

theorem tailTrace_7802630 : CollatzResearch.WordTrace tailWord_7802630 prefixEnd_7802630 4006499559190912407941365 := by
  unfold tailWord_7802630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8893290491325361498648417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 189723530481607711971166229 8893290491325361498648417)
  ·
    refine ⟨6669967868494021123986313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8893290491325361498648417 6669967868494021123986313)
    ·
      refine ⟨5002475901370515842989735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6669967868494021123986313 5002475901370515842989735)
      ·
        refine ⟨7503713852055773764484603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002475901370515842989735 7503713852055773764484603)
        ·
          refine ⟨11255570778083660646726905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7503713852055773764484603 11255570778083660646726905)
          ·
            refine ⟨8441678083562745485045179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11255570778083660646726905 8441678083562745485045179)
            ·
              refine ⟨12662517125344118227567769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8441678083562745485045179 12662517125344118227567769)
              ·
                refine ⟨9496887844008088670675827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12662517125344118227567769 9496887844008088670675827)
                ·
                  refine ⟨14245331766012133006013741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9496887844008088670675827 14245331766012133006013741)
                  ·
                    refine ⟨5341999412254549877255153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14245331766012133006013741 5341999412254549877255153)
                    ·
                      refine ⟨4006499559190912407941365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5341999412254549877255153 4006499559190912407941365)
                      ·
                        rfl

theorem cell23_7802630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7802630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802630 prefixEnd_7802630 := by exact prefixLift 7802630
  have htrace : WordTrace (prefixWord ++ tailWord_7802630) baseStart_7802630 baseEnd_7802630 := by
    simpa [prefixWord, tailWord_7802630, baseEnd_7802630] using wordTrace_append hprefix tailTrace_7802630
  have hstable : (prefixWord ++ tailWord_7802630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802630).length < 2 ^ (prefixWord ++ tailWord_7802630).sum := by decide
  have hdescent : baseEnd_7802630 < baseStart_7802630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802641 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 5, 4]
def baseStart_7802641 : Nat := 118140960795 + 7802641 * 2 ^ 59
def prefixEnd_7802641 : Nat := 4983230072969 + 3 ^ 40 * 7802641 * 2
def baseEnd_7802641 : Nat := 1335501735826037288301271

theorem tailTrace_7802641 : CollatzResearch.WordTrace tailWord_7802641 prefixEnd_7802641 1335501735826037288301271 := by
  unfold tailWord_7802641
  simp only [CollatzResearch.WordTrace]
  refine ⟨284585696925371716835399777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189723797950247811223599851 284585696925371716835399777)
  ·
    refine ⟨213439272694028787626549833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284585696925371716835399777 213439272694028787626549833)
    ·
      refine ⟨160079454520521590719912375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213439272694028787626549833 160079454520521590719912375)
      ·
        refine ⟨240119181780782386079868563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160079454520521590719912375 240119181780782386079868563)
        ·
          refine ⟨360178772671173579119802845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240119181780782386079868563 360178772671173579119802845)
          ·
            refine ⟨135067039751690092169926067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360178772671173579119802845 135067039751690092169926067)
            ·
              refine ⟨202600559627535138254889101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135067039751690092169926067 202600559627535138254889101)
              ·
                refine ⟨75975209860325676845583413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202600559627535138254889101 75975209860325676845583413)
                ·
                  refine ⟨7122675924405532204273445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75975209860325676845583413 7122675924405532204273445)
                  ·
                    refine ⟨1335501735826037288301271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7122675924405532204273445 1335501735826037288301271)
                    ·
                      rfl

theorem cell23_7802641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 4].length) (baseStart_7802641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802641 prefixEnd_7802641 := by exact prefixLift 7802641
  have htrace : WordTrace (prefixWord ++ tailWord_7802641) baseStart_7802641 baseEnd_7802641 := by
    simpa [prefixWord, tailWord_7802641, baseEnd_7802641] using wordTrace_append hprefix tailTrace_7802641
  have hstable : (prefixWord ++ tailWord_7802641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802641).length < 2 ^ (prefixWord ++ tailWord_7802641).sum := by decide
  have hdescent : baseEnd_7802641 < baseStart_7802641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802651 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 3]
def baseStart_7802651 : Nat := 118140960795 + 7802651 * 2 ^ 59
def prefixEnd_7802651 : Nat := 4983230072969 + 3 ^ 40 * 7802651 * 2
def baseEnd_7802651 : Nat := 4006510342284656825778767

theorem tailTrace_7802651 : CollatzResearch.WordTrace tailWord_7802651 prefixEnd_7802651 4006510342284656825778767 := by
  unfold tailWord_7802651
  simp only [CollatzResearch.WordTrace]
  refine ⟨284586061655335488543263807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189724041103556992362175871 284586061655335488543263807)
  ·
    refine ⟨426879092483003232814895711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284586061655335488543263807 426879092483003232814895711)
    ·
      refine ⟨640318638724504849222343567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426879092483003232814895711 640318638724504849222343567)
      ·
        refine ⟨960477958086757273833515351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640318638724504849222343567 960477958086757273833515351)
        ·
          refine ⟨1440716937130135910750273027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960477958086757273833515351 1440716937130135910750273027)
          ·
            refine ⟨2161075405695203866125409541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1440716937130135910750273027 2161075405695203866125409541)
            ·
              refine ⟨405201638567850724898514289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2161075405695203866125409541 405201638567850724898514289)
              ·
                refine ⟨303901228925888043673885717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405201638567850724898514289 303901228925888043673885717)
                ·
                  refine ⟨14245370105901002047213393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 303901228925888043673885717 14245370105901002047213393)
                  ·
                    refine ⟨10684027579425751535410045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14245370105901002047213393 10684027579425751535410045)
                    ·
                      refine ⟨4006510342284656825778767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10684027579425751535410045 4006510342284656825778767)
                      ·
                        rfl

theorem cell23_7802651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 3].length) (baseStart_7802651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802651 prefixEnd_7802651 := by exact prefixLift 7802651
  have htrace : WordTrace (prefixWord ++ tailWord_7802651) baseStart_7802651 baseEnd_7802651 := by
    simpa [prefixWord, tailWord_7802651, baseEnd_7802651] using wordTrace_append hprefix tailTrace_7802651
  have hstable : (prefixWord ++ tailWord_7802651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802651).length < 2 ^ (prefixWord ++ tailWord_7802651).sum := by decide
  have hdescent : baseEnd_7802651 < baseStart_7802651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802668 : List Nat := [2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 3]
def baseStart_7802668 : Nat := 118140960795 + 7802668 * 2 ^ 59
def prefixEnd_7802668 : Nat := 4983230072969 + 3 ^ 40 * 7802668 * 2
def baseEnd_7802668 : Nat := 4006519071455783259266189

theorem tailTrace_7802668 : CollatzResearch.WordTrace tailWord_7802668 prefixEnd_7802668 4006519071455783259266189 := by
  unfold tailWord_7802668
  simp only [CollatzResearch.WordTrace]
  refine ⟨142293340848136950223316329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189724454464182600297755105 142293340848136950223316329)
  ·
    refine ⟨106720005636102712667487247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142293340848136950223316329 106720005636102712667487247)
    ·
      refine ⟨160080008454154069001230871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106720005636102712667487247 160080008454154069001230871)
      ·
        refine ⟨240120012681231103501846307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160080008454154069001230871 240120012681231103501846307)
        ·
          refine ⟨360180019021846655252769461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240120012681231103501846307 360180019021846655252769461)
          ·
            refine ⟨33766876783298123929947137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 360180019021846655252769461 33766876783298123929947137)
            ·
              refine ⟨25325157587473592947460353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33766876783298123929947137 25325157587473592947460353)
              ·
                refine ⟨18993868190605194710595265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25325157587473592947460353 18993868190605194710595265)
                ·
                  refine ⟨14245401142953896032946449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18993868190605194710595265 14245401142953896032946449)
                  ·
                    refine ⟨10684050857215422024709837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14245401142953896032946449 10684050857215422024709837)
                    ·
                      refine ⟨4006519071455783259266189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10684050857215422024709837 4006519071455783259266189)
                      ·
                        rfl

theorem cell23_7802668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_7802668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802668 prefixEnd_7802668 := by exact prefixLift 7802668
  have htrace : WordTrace (prefixWord ++ tailWord_7802668) baseStart_7802668 baseEnd_7802668 := by
    simpa [prefixWord, tailWord_7802668, baseEnd_7802668] using wordTrace_append hprefix tailTrace_7802668
  have hstable : (prefixWord ++ tailWord_7802668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802668).length < 2 ^ (prefixWord ++ tailWord_7802668).sum := by decide
  have hdescent : baseEnd_7802668 < baseStart_7802668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802732 : List Nat := [2, 2, 1, 1, 4, 2, 2, 4, 1, 1, 3]
def baseStart_7802732 : Nat := 118140960795 + 7802732 * 2 ^ 59
def prefixEnd_7802732 : Nat := 4983230072969 + 3 ^ 40 * 7802732 * 2
def baseEnd_7802732 : Nat := 4006551934217671008865895

theorem tailTrace_7802732 : CollatzResearch.WordTrace tailWord_7802732 prefixEnd_7802732 4006551934217671008865895 := by
  unfold tailWord_7802732
  simp only [CollatzResearch.WordTrace]
  refine ⟨142294507984021019688481225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189726010645361359584641633 142294507984021019688481225)
  ·
    refine ⟨106720880988015764766360919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142294507984021019688481225 106720880988015764766360919)
    ·
      refine ⟨160081321482023647149541379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106720880988015764766360919 160081321482023647149541379)
      ·
        refine ⟨240121982223035470724312069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160081321482023647149541379 240121982223035470724312069)
        ·
          refine ⟨45022871666819150760808513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240121982223035470724312069 45022871666819150760808513)
          ·
            refine ⟨33767153750114363070606385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45022871666819150760808513 33767153750114363070606385)
            ·
              refine ⟨25325365312585772302954789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33767153750114363070606385 25325365312585772302954789)
              ·
                refine ⟨4748505996109832306804023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25325365312585772302954789 4748505996109832306804023)
                ·
                  refine ⟨7122758994164748460206035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4748505996109832306804023 7122758994164748460206035)
                  ·
                    refine ⟨10684138491247122690309053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7122758994164748460206035 10684138491247122690309053)
                    ·
                      refine ⟨4006551934217671008865895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10684138491247122690309053 4006551934217671008865895)
                      ·
                        rfl

theorem cell23_7802732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 4, 1, 1, 3].length) (baseStart_7802732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802732 prefixEnd_7802732 := by exact prefixLift 7802732
  have htrace : WordTrace (prefixWord ++ tailWord_7802732) baseStart_7802732 baseEnd_7802732 := by
    simpa [prefixWord, tailWord_7802732, baseEnd_7802732] using wordTrace_append hprefix tailTrace_7802732
  have hstable : (prefixWord ++ tailWord_7802732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802732).length < 2 ^ (prefixWord ++ tailWord_7802732).sum := by decide
  have hdescent : baseEnd_7802732 < baseStart_7802732 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802755 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 4]
def baseStart_7802755 : Nat := 118140960795 + 7802755 * 2 ^ 59
def prefixEnd_7802755 : Nat := 4983230072969 + 3 ^ 40 * 7802755 * 2
def baseEnd_7802755 : Nat := 4006563744272724418878289

theorem tailTrace_7802755 : CollatzResearch.WordTrace tailWord_7802755 prefixEnd_7802755 4006563744272724418878289 := by
  unfold tailWord_7802755
  simp only [CollatzResearch.WordTrace]
  refine ⟨284589854846958714305049719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189726569897972476203366479 284589854846958714305049719)
  ·
    refine ⟨426884782270438071457574579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284589854846958714305049719 426884782270438071457574579)
    ·
      refine ⟨640327173405657107186361869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426884782270438071457574579 640327173405657107186361869)
      ·
        refine ⟨240122690027121415194885701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640327173405657107186361869 240122690027121415194885701)
        ·
          refine ⟨45023004380085265349041069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240122690027121415194885701 45023004380085265349041069)
          ·
            refine ⟨16883626642531974505890401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45023004380085265349041069 16883626642531974505890401)
            ·
              refine ⟨12662719981898980879417801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16883626642531974505890401 12662719981898980879417801)
              ·
                refine ⟨9497039986424235659563351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12662719981898980879417801 9497039986424235659563351)
                ·
                  refine ⟨14245559979636353489345027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9497039986424235659563351 14245559979636353489345027)
                  ·
                    refine ⟨21368339969454530234017541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14245559979636353489345027 21368339969454530234017541)
                    ·
                      refine ⟨4006563744272724418878289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21368339969454530234017541 4006563744272724418878289)
                      ·
                        rfl

theorem cell23_7802755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_7802755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802755 prefixEnd_7802755 := by exact prefixLift 7802755
  have htrace : WordTrace (prefixWord ++ tailWord_7802755) baseStart_7802755 baseEnd_7802755 := by
    simpa [prefixWord, tailWord_7802755, baseEnd_7802755] using wordTrace_append hprefix tailTrace_7802755
  have hstable : (prefixWord ++ tailWord_7802755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802755).length < 2 ^ (prefixWord ++ tailWord_7802755).sum := by decide
  have hdescent : baseEnd_7802755 < baseStart_7802755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802761 : List Nat := [1, 2, 1, 1, 5, 1, 3, 9]
def baseStart_7802761 : Nat := 118140960795 + 7802761 * 2 ^ 59
def prefixEnd_7802761 : Nat := 4983230072969 + 3 ^ 40 * 7802761 * 2
def baseEnd_7802761 : Nat := 148391363894690792422343

theorem tailTrace_7802761 : CollatzResearch.WordTrace tailWord_7802761 prefixEnd_7802761 148391363894690792422343 := by
  unfold tailWord_7802761
  simp only [CollatzResearch.WordTrace]
  refine ⟨284590073684936977329768137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189726715789957984886512091 284590073684936977329768137)
  ·
    refine ⟨213442555263702732997326103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284590073684936977329768137 213442555263702732997326103)
    ·
      refine ⟨320163832895554099495989155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213442555263702732997326103 320163832895554099495989155)
      ·
        refine ⟨480245749343331149243983733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320163832895554099495989155 480245749343331149243983733)
        ·
          refine ⟨45023039000937295241623475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 480245749343331149243983733 45023039000937295241623475)
          ·
            refine ⟨67534558501405942862435213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45023039000937295241623475 67534558501405942862435213)
            ·
              refine ⟨25325459438027228573413205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67534558501405942862435213 25325459438027228573413205)
              ·
                refine ⟨148391363894690792422343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25325459438027228573413205 148391363894690792422343)
                ·
                  rfl

theorem cell23_7802761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 9].length) (baseStart_7802761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802761 prefixEnd_7802761 := by exact prefixLift 7802761
  have htrace : WordTrace (prefixWord ++ tailWord_7802761) baseStart_7802761 baseEnd_7802761 := by
    simpa [prefixWord, tailWord_7802761, baseEnd_7802761] using wordTrace_append hprefix tailTrace_7802761
  have hstable : (prefixWord ++ tailWord_7802761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802761).length < 2 ^ (prefixWord ++ tailWord_7802761).sum := by decide
  have hdescent : baseEnd_7802761 < baseStart_7802761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802775 : List Nat := [1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 3]
def baseStart_7802775 : Nat := 118140960795 + 7802775 * 2 ^ 59
def prefixEnd_7802775 : Nat := 4983230072969 + 3 ^ 40 * 7802775 * 2
def baseEnd_7802775 : Nat := 4006574013885814340628197

theorem tailTrace_7802775 : CollatzResearch.WordTrace tailWord_7802775 prefixEnd_7802775 4006574013885814340628197 := by
  unfold tailWord_7802775
  simp only [CollatzResearch.WordTrace]
  refine ⟨284590584306886257720777779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189727056204590838480518519 284590584306886257720777779)
  ·
    refine ⟨426885876460329386581166669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284590584306886257720777779 426885876460329386581166669)
    ·
      refine ⟨160082203672623519967937501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426885876460329386581166669 160082203672623519967937501)
      ·
        refine ⟨60030826377233819987976563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160082203672623519967937501 60030826377233819987976563)
        ·
          refine ⟨90046239565850729981964845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60030826377233819987976563 90046239565850729981964845)
          ·
            refine ⟨33767339837194023743236817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90046239565850729981964845 33767339837194023743236817)
            ·
              refine ⟨25325504877895517807427613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33767339837194023743236817 25325504877895517807427613)
              ·
                refine ⟨9497064329210819177785355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25325504877895517807427613 9497064329210819177785355)
                ·
                  refine ⟨14245596493816228766678033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9497064329210819177785355 14245596493816228766678033)
                  ·
                    refine ⟨10684197370362171575008525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14245596493816228766678033 10684197370362171575008525)
                    ·
                      refine ⟨4006574013885814340628197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10684197370362171575008525 4006574013885814340628197)
                      ·
                        rfl

theorem cell23_7802775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_7802775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802775 prefixEnd_7802775 := by exact prefixLift 7802775
  have htrace : WordTrace (prefixWord ++ tailWord_7802775) baseStart_7802775 baseEnd_7802775 := by
    simpa [prefixWord, tailWord_7802775, baseEnd_7802775] using wordTrace_append hprefix tailTrace_7802775
  have hstable : (prefixWord ++ tailWord_7802775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802775).length < 2 ^ (prefixWord ++ tailWord_7802775).sum := by decide
  have hdescent : baseEnd_7802775 < baseStart_7802775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802778 : List Nat := [3, 1, 1, 4, 2, 3, 9]
def baseStart_7802778 : Nat := 118140960795 + 7802778 * 2 ^ 59
def prefixEnd_7802778 : Nat := 4983230072969 + 3 ^ 40 * 7802778 * 2
def baseEnd_7802778 : Nat := 49463895732441701591243

theorem tailTrace_7802778 : CollatzResearch.WordTrace tailWord_7802778 prefixEnd_7802778 49463895732441701591243 := by
  unfold tailWord_7802778
  simp only [CollatzResearch.WordTrace]
  refine ⟨71147673431468847308284247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189727129150583592822091325 71147673431468847308284247)
  ·
    refine ⟨106721510147203270962426371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71147673431468847308284247 106721510147203270962426371)
    ·
      refine ⟨160082265220804906443639557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106721510147203270962426371 160082265220804906443639557)
      ·
        refine ⟨30015424728900919958182417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160082265220804906443639557 30015424728900919958182417)
        ·
          refine ⟨22511568546675689968636813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30015424728900919958182417 22511568546675689968636813)
          ·
            refine ⟨8441838205003383738238805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22511568546675689968636813 8441838205003383738238805)
            ·
              refine ⟨49463895732441701591243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8441838205003383738238805 49463895732441701591243)
              ·
                rfl

theorem cell23_7802778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 9].length) (baseStart_7802778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802778 prefixEnd_7802778 := by exact prefixLift 7802778
  have htrace : WordTrace (prefixWord ++ tailWord_7802778) baseStart_7802778 baseEnd_7802778 := by
    simpa [prefixWord, tailWord_7802778, baseEnd_7802778] using wordTrace_append hprefix tailTrace_7802778
  have hstable : (prefixWord ++ tailWord_7802778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802778).length < 2 ^ (prefixWord ++ tailWord_7802778).sum := by decide
  have hdescent : baseEnd_7802778 < baseStart_7802778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802815 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 3, 3, 2]
def baseStart_7802815 : Nat := 118140960795 + 7802815 * 2 ^ 59
def prefixEnd_7802815 : Nat := 4983230072969 + 3 ^ 40 * 7802815 * 2
def baseEnd_7802815 : Nat := 4006594553111994184128013

theorem tailTrace_7802815 : CollatzResearch.WordTrace tailWord_7802815 prefixEnd_7802815 4006594553111994184128013 := by
  unfold tailWord_7802815
  simp only [CollatzResearch.WordTrace]
  refine ⟨284592043226741344552233899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189728028817827563034822599 284592043226741344552233899)
  ·
    refine ⟨426888064840112016828350849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284592043226741344552233899 426888064840112016828350849)
    ·
      refine ⟨320166048630084012621263137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426888064840112016828350849 320166048630084012621263137)
      ·
        refine ⟨240124536472563009465947353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320166048630084012621263137 240124536472563009465947353)
        ·
          refine ⟨180093402354422257099460515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240124536472563009465947353 180093402354422257099460515)
          ·
            refine ⟨270140103531633385649190773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180093402354422257099460515 270140103531633385649190773)
            ·
              refine ⟨25325634706090629904611635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270140103531633385649190773 25325634706090629904611635)
              ·
                refine ⟨37988452059135944856917453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25325634706090629904611635 37988452059135944856917453)
                ·
                  refine ⟨14245669522175979321344045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37988452059135944856917453 14245669522175979321344045)
                  ·
                    refine ⟨5342126070815992245504017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14245669522175979321344045 5342126070815992245504017)
                    ·
                      refine ⟨4006594553111994184128013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5342126070815992245504017 4006594553111994184128013)
                      ·
                        rfl

theorem cell23_7802815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_7802815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802815 prefixEnd_7802815 := by exact prefixLift 7802815
  have htrace : WordTrace (prefixWord ++ tailWord_7802815) baseStart_7802815 baseEnd_7802815 := by
    simpa [prefixWord, tailWord_7802815, baseEnd_7802815] using wordTrace_append hprefix tailTrace_7802815
  have hstable : (prefixWord ++ tailWord_7802815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802815).length < 2 ^ (prefixWord ++ tailWord_7802815).sum := by decide
  have hdescent : baseEnd_7802815 < baseStart_7802815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802821 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 3, 8]
def baseStart_7802821 : Nat := 118140960795 + 7802821 * 2 ^ 59
def prefixEnd_7802821 : Nat := 4983230072969 + 3 ^ 40 * 7802821 * 2
def baseEnd_7802821 : Nat := 1335532544665307053550995

theorem tailTrace_7802821 : CollatzResearch.WordTrace tailWord_7802821 prefixEnd_7802821 1335532544665307053550995 := by
  unfold tailWord_7802821
  simp only [CollatzResearch.WordTrace]
  refine ⟨284592262064719607576952317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189728174709813071717968211 284592262064719607576952317)
  ·
    refine ⟨106722098274269852841357119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284592262064719607576952317 106722098274269852841357119)
    ·
      refine ⟨160083147411404779262035679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106722098274269852841357119 160083147411404779262035679)
      ·
        refine ⟨240124721117107168893053519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160083147411404779262035679 240124721117107168893053519)
        ·
          refine ⟨360187081675660753339580279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240124721117107168893053519 360187081675660753339580279)
          ·
            refine ⟨540280622513491130009370419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360187081675660753339580279 540280622513491130009370419)
            ·
              refine ⟨810420933770236695014055629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540280622513491130009370419 810420933770236695014055629)
              ·
                refine ⟨303907850163838760630270861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 810420933770236695014055629 303907850163838760630270861)
                ·
                  refine ⟨113965443811439535236351573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303907850163838760630270861 113965443811439535236351573)
                  ·
                    refine ⟨1335532544665307053550995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113965443811439535236351573 1335532544665307053550995)
                    ·
                      rfl

theorem cell23_7802821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_7802821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802821 prefixEnd_7802821 := by exact prefixLift 7802821
  have htrace : WordTrace (prefixWord ++ tailWord_7802821) baseStart_7802821 baseEnd_7802821 := by
    simpa [prefixWord, tailWord_7802821, baseEnd_7802821] using wordTrace_append hprefix tailTrace_7802821
  have hstable : (prefixWord ++ tailWord_7802821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802821).length < 2 ^ (prefixWord ++ tailWord_7802821).sum := by decide
  have hdescent : baseEnd_7802821 < baseStart_7802821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802855 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 2, 6]
def baseStart_7802855 : Nat := 118140960795 + 7802855 * 2 ^ 59
def prefixEnd_7802855 : Nat := 4983230072969 + 3 ^ 40 * 7802855 * 2
def baseEnd_7802855 : Nat := 1335538364112724675875943

theorem tailTrace_7802855 : CollatzResearch.WordTrace tailWord_7802855 prefixEnd_7802855 1335538364112724675875943 := by
  unfold tailWord_7802855
  simp only [CollatzResearch.WordTrace]
  refine ⟨284593502146596431383690019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189729001431064287589126679 284593502146596431383690019)
  ·
    refine ⟨426890253219894647075535029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284593502146596431383690019 426890253219894647075535029)
    ·
      refine ⟨40020961239365123163331409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 426890253219894647075535029 40020961239365123163331409)
      ·
        refine ⟨30015720929523842372498557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40020961239365123163331409 30015720929523842372498557)
        ·
          refine ⟨11255895348571440889686959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30015720929523842372498557 11255895348571440889686959)
          ·
            refine ⟨16883843022857161334530439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11255895348571440889686959 16883843022857161334530439)
            ·
              refine ⟨25325764534285742001795659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16883843022857161334530439 25325764534285742001795659)
              ·
                refine ⟨37988646801428613002693489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25325764534285742001795659 37988646801428613002693489)
                ·
                  refine ⟨28491485101071459752020117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37988646801428613002693489 28491485101071459752020117)
                  ·
                    refine ⟨1335538364112724675875943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28491485101071459752020117 1335538364112724675875943)
                    ·
                      rfl

theorem cell23_7802855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_7802855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802855 prefixEnd_7802855 := by exact prefixLift 7802855
  have htrace : WordTrace (prefixWord ++ tailWord_7802855) baseStart_7802855 baseEnd_7802855 := by
    simpa [prefixWord, tailWord_7802855, baseEnd_7802855] using wordTrace_append hprefix tailTrace_7802855
  have hstable : (prefixWord ++ tailWord_7802855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802855).length < 2 ^ (prefixWord ++ tailWord_7802855).sum := by decide
  have hdescent : baseEnd_7802855 < baseStart_7802855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802862 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_7802862 : Nat := 118140960795 + 7802862 * 2 ^ 59
def prefixEnd_7802862 : Nat := 4983230072969 + 3 ^ 40 * 7802862 * 2
def baseEnd_7802862 : Nat := 4006618686702755500240297

theorem tailTrace_7802862 : CollatzResearch.WordTrace tailWord_7802862 prefixEnd_7802862 4006618686702755500240297 := by
  unfold tailWord_7802862
  simp only [CollatzResearch.WordTrace]
  refine ⟨35574219682196383947399355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189729171638380714386129893 35574219682196383947399355)
  ·
    refine ⟨53361329523294575921099033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35574219682196383947399355 53361329523294575921099033)
    ·
      refine ⟨40020997142470931940824275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53361329523294575921099033 40020997142470931940824275)
      ·
        refine ⟨60031495713706397911236413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40020997142470931940824275 60031495713706397911236413)
        ·
          refine ⟨22511810892639899216713655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60031495713706397911236413 22511810892639899216713655)
          ·
            refine ⟨33767716338959848825070483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22511810892639899216713655 33767716338959848825070483)
            ·
              refine ⟨50651574508439773237605725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33767716338959848825070483 50651574508439773237605725)
              ·
                refine ⟨18994340440664914964102147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50651574508439773237605725 18994340440664914964102147)
                ·
                  refine ⟨28491510660997372446153221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18994340440664914964102147 28491510660997372446153221)
                  ·
                    refine ⟨5342158248937007333653729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28491510660997372446153221 5342158248937007333653729)
                    ·
                      refine ⟨4006618686702755500240297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5342158248937007333653729 4006618686702755500240297)
                      ·
                        rfl

theorem cell23_7802862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_7802862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802862 prefixEnd_7802862 := by exact prefixLift 7802862
  have htrace : WordTrace (prefixWord ++ tailWord_7802862) baseStart_7802862 baseEnd_7802862 := by
    simpa [prefixWord, tailWord_7802862, baseEnd_7802862] using wordTrace_append hprefix tailTrace_7802862
  have hstable : (prefixWord ++ tailWord_7802862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802862).length < 2 ^ (prefixWord ++ tailWord_7802862).sum := by decide
  have hdescent : baseEnd_7802862 < baseStart_7802862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802885 : List Nat := [1, 3, 1, 1, 2, 4, 1, 5, 5]
def baseStart_7802885 : Nat := 118140960795 + 7802885 * 2 ^ 59
def prefixEnd_7802885 : Nat := 4983230072969 + 3 ^ 40 * 7802885 * 2
def baseEnd_7802885 : Nat := 445181166306423212250299

theorem tailTrace_7802885 : CollatzResearch.WordTrace tailWord_7802885 prefixEnd_7802885 445181166306423212250299 := by
  unfold tailWord_7802885
  simp only [CollatzResearch.WordTrace]
  refine ⟨284594596336487746507282109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189729730890991831004854739 284594596336487746507282109)
  ·
    refine ⟨106722973626182904940230791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284594596336487746507282109 106722973626182904940230791)
    ·
      refine ⟨160084460439274357410346187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106722973626182904940230791 160084460439274357410346187)
      ·
        refine ⟨240126690658911536115519281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160084460439274357410346187 240126690658911536115519281)
        ·
          refine ⟨180095017994183652086639461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240126690658911536115519281 180095017994183652086639461)
          ·
            refine ⟨33767815873909434766244899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180095017994183652086639461 33767815873909434766244899)
            ·
              refine ⟨50651723810864152149367349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33767815873909434766244899 50651723810864152149367349)
              ·
                refine ⟨4748599107268514264003189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50651723810864152149367349 4748599107268514264003189)
                ·
                  refine ⟨445181166306423212250299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4748599107268514264003189 445181166306423212250299)
                  ·
                    rfl

theorem cell23_7802885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_7802885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802885 prefixEnd_7802885 := by exact prefixLift 7802885
  have htrace : WordTrace (prefixWord ++ tailWord_7802885) baseStart_7802885 baseEnd_7802885 := by
    simpa [prefixWord, tailWord_7802885, baseEnd_7802885] using wordTrace_append hprefix tailTrace_7802885
  have hstable : (prefixWord ++ tailWord_7802885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802885).length < 2 ^ (prefixWord ++ tailWord_7802885).sum := by decide
  have hdescent : baseEnd_7802885 < baseStart_7802885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802935 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 1, 6, 2]
def baseStart_7802935 : Nat := 118140960795 + 7802935 * 2 ^ 59
def prefixEnd_7802935 : Nat := 4983230072969 + 3 ^ 40 * 7802935 * 2
def baseEnd_7802935 : Nat := 4006656170790533714627461

theorem tailTrace_7802935 : CollatzResearch.WordTrace tailWord_7802935 prefixEnd_7802935 4006656170790533714627461 := by
  unfold tailWord_7802935
  simp only [CollatzResearch.WordTrace]
  refine ⟨284596419986306605046602259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189730946657537736697734839 284596419986306605046602259)
  ·
    refine ⟨426894629979459907569903389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284596419986306605046602259 426894629979459907569903389)
    ·
      refine ⟨160085486242297465338713771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426894629979459907569903389 160085486242297465338713771)
      ·
        refine ⟨240128229363446198008070657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160085486242297465338713771 240128229363446198008070657)
        ·
          refine ⟨180096172022584648506052993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240128229363446198008070657 180096172022584648506052993)
          ·
            refine ⟨135072129016938486379539745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180096172022584648506052993 135072129016938486379539745)
            ·
              refine ⟨101304096762703864784654809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135072129016938486379539745 101304096762703864784654809)
              ·
                refine ⟨75978072572027898588491107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101304096762703864784654809 75978072572027898588491107)
                ·
                  refine ⟨113967108858041847882736661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75978072572027898588491107 113967108858041847882736661)
                  ·
                    refine ⟨5342208227720711619503281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113967108858041847882736661 5342208227720711619503281)
                    ·
                      refine ⟨4006656170790533714627461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5342208227720711619503281 4006656170790533714627461)
                      ·
                        rfl

theorem cell23_7802935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 6, 2].length) (baseStart_7802935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802935 prefixEnd_7802935 := by exact prefixLift 7802935
  have htrace : WordTrace (prefixWord ++ tailWord_7802935) baseStart_7802935 baseEnd_7802935 := by
    simpa [prefixWord, tailWord_7802935, baseEnd_7802935] using wordTrace_append hprefix tailTrace_7802935
  have hstable : (prefixWord ++ tailWord_7802935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802935).length < 2 ^ (prefixWord ++ tailWord_7802935).sum := by decide
  have hdescent : baseEnd_7802935 < baseStart_7802935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802938 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_7802938 : Nat := 118140960795 + 7802938 * 2 ^ 59
def prefixEnd_7802938 : Nat := 4983230072969 + 3 ^ 40 * 7802938 * 2
def baseEnd_7802938 : Nat := 4006657711232497202889947

theorem tailTrace_7802938 : CollatzResearch.WordTrace tailWord_7802938 prefixEnd_7802938 4006657711232497202889947 := by
  unfold tailWord_7802938
  simp only [CollatzResearch.WordTrace]
  refine ⟨71149132351323934139740367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189731019603530491039307645 71149132351323934139740367)
  ·
    refine ⟨106723698526985901209610551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71149132351323934139740367 106723698526985901209610551)
    ·
      refine ⟨160085547790478851814415827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106723698526985901209610551 160085547790478851814415827)
      ·
        refine ⟨240128321685718277721623741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160085547790478851814415827 240128321685718277721623741)
        ·
          refine ⟨90048120632144354145608903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240128321685718277721623741 90048120632144354145608903)
          ·
            refine ⟨135072180948216531218413355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90048120632144354145608903 135072180948216531218413355)
            ·
              refine ⟨202608271422324796827620033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135072180948216531218413355 202608271422324796827620033)
              ·
                refine ⟨151956203566743597620715025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202608271422324796827620033 151956203566743597620715025)
                ·
                  refine ⟨113967152675057698215536269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 151956203566743597620715025 113967152675057698215536269)
                  ·
                    refine ⟨42737682253146636830826101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113967152675057698215536269 42737682253146636830826101)
                    ·
                      refine ⟨4006657711232497202889947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42737682253146636830826101 4006657711232497202889947)
                      ·
                        rfl

theorem cell23_7802938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_7802938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802938 prefixEnd_7802938 := by exact prefixLift 7802938
  have htrace : WordTrace (prefixWord ++ tailWord_7802938) baseStart_7802938 baseEnd_7802938 := by
    simpa [prefixWord, tailWord_7802938, baseEnd_7802938] using wordTrace_append hprefix tailTrace_7802938
  have hstable : (prefixWord ++ tailWord_7802938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802938).length < 2 ^ (prefixWord ++ tailWord_7802938).sum := by decide
  have hdescent : baseEnd_7802938 < baseStart_7802938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7802955 : List Nat := [1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 3]
def baseStart_7802955 : Nat := 118140960795 + 7802955 * 2 ^ 59
def prefixEnd_7802955 : Nat := 4983230072969 + 3 ^ 40 * 7802955 * 2
def baseEnd_7802955 : Nat := 4006666440403623636377369

theorem tailTrace_7802955 : CollatzResearch.WordTrace tailWord_7802955 prefixEnd_7802955 4006666440403623636377369 := by
  unfold tailWord_7802955
  simp only [CollatzResearch.WordTrace]
  refine ⟨284597149446234148462330319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189731432964156098974886879 284597149446234148462330319)
  ·
    refine ⟨426895724169351222693495479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284597149446234148462330319 426895724169351222693495479)
    ·
      refine ⟨640343586254026834040243219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426895724169351222693495479 640343586254026834040243219)
      ·
        refine ⟨960515379381040251060364829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640343586254026834040243219 960515379381040251060364829)
        ·
          refine ⟨360193267267890094147636811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 960515379381040251060364829 360193267267890094147636811)
          ·
            refine ⟨540289900901835141221455217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360193267267890094147636811 540289900901835141221455217)
            ·
              refine ⟨405217425676376355916091413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540289900901835141221455217 405217425676376355916091413)
              ·
                refine ⟨18994566828580141683566785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 405217425676376355916091413 18994566828580141683566785)
                ·
                  refine ⟨14245925121435106262675089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18994566828580141683566785 14245925121435106262675089)
                  ·
                    refine ⟨10684443841076329697006317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14245925121435106262675089 10684443841076329697006317)
                    ·
                      refine ⟨4006666440403623636377369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10684443841076329697006317 4006666440403623636377369)
                      ·
                        rfl

theorem cell23_7802955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 3].length) (baseStart_7802955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7802955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7802955 prefixEnd_7802955 := by exact prefixLift 7802955
  have htrace : WordTrace (prefixWord ++ tailWord_7802955) baseStart_7802955 baseEnd_7802955 := by
    simpa [prefixWord, tailWord_7802955, baseEnd_7802955] using wordTrace_append hprefix tailTrace_7802955
  have hstable : (prefixWord ++ tailWord_7802955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7802955).length < 2 ^ (prefixWord ++ tailWord_7802955).sum := by decide
  have hdescent : baseEnd_7802955 < baseStart_7802955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7802955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803030 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7803030 : Nat := 118140960795 + 7803030 * 2 ^ 59
def prefixEnd_7803030 : Nat := 4983230072969 + 3 ^ 40 * 7803030 * 2
def baseEnd_7803030 : Nat := 1335568317150903614313175

theorem tailTrace_7803030 : CollatzResearch.WordTrace tailWord_7803030 prefixEnd_7803030 1335568317150903614313175 := by
  unfold tailWord_7803030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17787492807560152266956909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189733256613974957514207029 17787492807560152266956909)
  ·
    refine ⟨6670309802835057100108841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17787492807560152266956909 6670309802835057100108841)
    ·
      refine ⟨5002732352126292825081631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6670309802835057100108841 5002732352126292825081631)
      ·
        refine ⟨7504098528189439237622447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002732352126292825081631 7504098528189439237622447)
        ·
          refine ⟨11256147792284158856433671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7504098528189439237622447 11256147792284158856433671)
          ·
            refine ⟨16884221688426238284650507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11256147792284158856433671 16884221688426238284650507)
            ·
              refine ⟨25326332532639357426975761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16884221688426238284650507 25326332532639357426975761)
              ·
                refine ⟨18994749399479518070231821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25326332532639357426975761 18994749399479518070231821)
                ·
                  refine ⟨7123031024804819276336933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18994749399479518070231821 7123031024804819276336933)
                  ·
                    refine ⟨1335568317150903614313175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7123031024804819276336933 1335568317150903614313175)
                    ·
                      rfl

theorem cell23_7803030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7803030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803030 prefixEnd_7803030 := by exact prefixLift 7803030
  have htrace : WordTrace (prefixWord ++ tailWord_7803030) baseStart_7803030 baseEnd_7803030 := by
    simpa [prefixWord, tailWord_7803030, baseEnd_7803030] using wordTrace_append hprefix tailTrace_7803030
  have hstable : (prefixWord ++ tailWord_7803030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803030).length < 2 ^ (prefixWord ++ tailWord_7803030).sum := by decide
  have hdescent : baseEnd_7803030 < baseStart_7803030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803053 : List Nat := [1, 5, 2, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_7803053 : Nat := 118140960795 + 7803053 * 2 ^ 59
def prefixEnd_7803053 : Nat := 4983230072969 + 3 ^ 40 * 7803053 * 2
def baseEnd_7803053 : Nat := 4006716761507764252951919

theorem tailTrace_7803053 : CollatzResearch.WordTrace tailWord_7803053 prefixEnd_7803053 4006716761507764252951919 := by
  unfold tailWord_7803053
  simp only [CollatzResearch.WordTrace]
  refine ⟨284600723799879111199397813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189733815866586074132931875 284600723799879111199397813)
  ·
    refine ⟨26681317856238666674943545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284600723799879111199397813 26681317856238666674943545)
    ·
      refine ⟨20010988392179000006207659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26681317856238666674943545 20010988392179000006207659)
      ·
        refine ⟨30016482588268500009311489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20010988392179000006207659 30016482588268500009311489)
        ·
          refine ⟨22512361941201375006983617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30016482588268500009311489 22512361941201375006983617)
          ·
            refine ⟨16884271455901031255237713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22512361941201375006983617 16884271455901031255237713)
            ·
              refine ⟨12663203591925773441428285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16884271455901031255237713 12663203591925773441428285)
              ·
                refine ⟨4748701346972165040535607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12663203591925773441428285 4748701346972165040535607)
                ·
                  refine ⟨7123052020458247560803411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4748701346972165040535607 7123052020458247560803411)
                  ·
                    refine ⟨10684578030687371341205117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7123052020458247560803411 10684578030687371341205117)
                    ·
                      refine ⟨4006716761507764252951919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10684578030687371341205117 4006716761507764252951919)
                      ·
                        rfl

theorem cell23_7803053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_7803053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803053 prefixEnd_7803053 := by exact prefixLift 7803053
  have htrace : WordTrace (prefixWord ++ tailWord_7803053) baseStart_7803053 baseEnd_7803053 := by
    simpa [prefixWord, tailWord_7803053, baseEnd_7803053] using wordTrace_append hprefix tailTrace_7803053
  have hstable : (prefixWord ++ tailWord_7803053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803053).length < 2 ^ (prefixWord ++ tailWord_7803053).sum := by decide
  have hdescent : baseEnd_7803053 < baseStart_7803053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803060 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 6]
def baseStart_7803060 : Nat := 118140960795 + 7803060 * 2 ^ 59
def prefixEnd_7803060 : Nat := 4983230072969 + 3 ^ 40 * 7803060 * 2
def baseEnd_7803060 : Nat := 445191150652482858396043

theorem tailTrace_7803060 : CollatzResearch.WordTrace tailWord_7803060 prefixEnd_7803060 445191150652482858396043 := by
  unfold tailWord_7803060
  simp only [CollatzResearch.WordTrace]
  refine ⟨142300489555426875697451317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189733986073902500929935089 142300489555426875697451317)
  ·
    refine ⟨13340670895821269596636061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142300489555426875697451317 13340670895821269596636061)
    ·
      refine ⟨5002751585932976098738523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13340670895821269596636061 5002751585932976098738523)
      ·
        refine ⟨7504127378899464148107785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002751585932976098738523 7504127378899464148107785)
        ·
          refine ⟨5628095534174598111080839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7504127378899464148107785 5628095534174598111080839)
          ·
            refine ⟨8442143301261897166621259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5628095534174598111080839 8442143301261897166621259)
            ·
              refine ⟨12663214951892845749931889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8442143301261897166621259 12663214951892845749931889)
              ·
                refine ⟨9497411213919634312448917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12663214951892845749931889 9497411213919634312448917)
                ·
                  refine ⟨445191150652482858396043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9497411213919634312448917 445191150652482858396043)
                  ·
                    rfl

theorem cell23_7803060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_7803060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803060 prefixEnd_7803060 := by exact prefixLift 7803060
  have htrace : WordTrace (prefixWord ++ tailWord_7803060) baseStart_7803060 baseEnd_7803060 := by
    simpa [prefixWord, tailWord_7803060, baseEnd_7803060] using wordTrace_append hprefix tailTrace_7803060
  have hstable : (prefixWord ++ tailWord_7803060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803060).length < 2 ^ (prefixWord ++ tailWord_7803060).sum := by decide
  have hdescent : baseEnd_7803060 < baseStart_7803060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803076 : List Nat := [2, 3, 3, 1, 2, 1, 1, 3, 3, 2, 2]
def baseStart_7803076 : Nat := 118140960795 + 7803076 * 2 ^ 59
def prefixEnd_7803076 : Nat := 4983230072969 + 3 ^ 40 * 7803076 * 2
def baseEnd_7803076 : Nat := 4006728571562817662964313

theorem tailTrace_7803076 : CollatzResearch.WordTrace tailWord_7803076 prefixEnd_7803076 4006728571562817662964313 := by
  unfold tailWord_7803076
  simp only [CollatzResearch.WordTrace]
  refine ⟨142300781339397893063742541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189734375119197190751656721 142300781339397893063742541)
  ·
    refine ⟨53362793002274209898903453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142300781339397893063742541 53362793002274209898903453)
    ·
      refine ⟨20011047375852828712088795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53362793002274209898903453 20011047375852828712088795)
      ·
        refine ⟨30016571063779243068133193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20011047375852828712088795 30016571063779243068133193)
        ·
          refine ⟨22512428297834432301099895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30016571063779243068133193 22512428297834432301099895)
          ·
            refine ⟨33768642446751648451649843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22512428297834432301099895 33768642446751648451649843)
            ·
              refine ⟨50652963670127472677474765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33768642446751648451649843 50652963670127472677474765)
              ·
                refine ⟨18994861376297802254053037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50652963670127472677474765 18994861376297802254053037)
                ·
                  refine ⟨7123073016111675845269889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18994861376297802254053037 7123073016111675845269889)
                  ·
                    refine ⟨5342304762083756883952417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7123073016111675845269889 5342304762083756883952417)
                    ·
                      refine ⟨4006728571562817662964313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5342304762083756883952417 4006728571562817662964313)
                      ·
                        rfl

theorem cell23_7803076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_7803076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803076 prefixEnd_7803076 := by exact prefixLift 7803076
  have htrace : WordTrace (prefixWord ++ tailWord_7803076) baseStart_7803076 baseEnd_7803076 := by
    simpa [prefixWord, tailWord_7803076, baseEnd_7803076] using wordTrace_append hprefix tailTrace_7803076
  have hstable : (prefixWord ++ tailWord_7803076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803076).length < 2 ^ (prefixWord ++ tailWord_7803076).sum := by decide
  have hdescent : baseEnd_7803076 < baseStart_7803076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803086 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_7803086 : Nat := 118140960795 + 7803086 * 2 ^ 59
def prefixEnd_7803086 : Nat := 4983230072969 + 3 ^ 40 * 7803086 * 2
def baseEnd_7803086 : Nat := 1335577902123120874613089

theorem tailTrace_7803086 : CollatzResearch.WordTrace tailWord_7803086 prefixEnd_7803086 1335577902123120874613089 := by
  unfold tailWord_7803086
  simp only [CollatzResearch.WordTrace]
  refine ⟨35575240926094944729418639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189734618272506371890232741 35575240926094944729418639)
  ·
    refine ⟨53362861389142417094127959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35575240926094944729418639 53362861389142417094127959)
    ·
      refine ⟨80044292083713625641191939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53362861389142417094127959 80044292083713625641191939)
      ·
        refine ⟨120066438125570438461787909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80044292083713625641191939 120066438125570438461787909)
        ·
          refine ⟨22512457148544457211585233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120066438125570438461787909 22512457148544457211585233)
          ·
            refine ⟨16884342861408342908688925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22512457148544457211585233 16884342861408342908688925)
            ·
              refine ⟨6331628573028128590758347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16884342861408342908688925 6331628573028128590758347)
              ·
                refine ⟨9497442859542192886137521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6331628573028128590758347 9497442859542192886137521)
                ·
                  refine ⟨7123082144656644664603141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9497442859542192886137521 7123082144656644664603141)
                  ·
                    refine ⟨1335577902123120874613089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7123082144656644664603141 1335577902123120874613089)
                    ·
                      rfl

theorem cell23_7803086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_7803086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803086 prefixEnd_7803086 := by exact prefixLift 7803086
  have htrace : WordTrace (prefixWord ++ tailWord_7803086) baseStart_7803086 baseEnd_7803086 := by
    simpa [prefixWord, tailWord_7803086, baseEnd_7803086] using wordTrace_append hprefix tailTrace_7803086
  have hstable : (prefixWord ++ tailWord_7803086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803086).length < 2 ^ (prefixWord ++ tailWord_7803086).sum := by decide
  have hdescent : baseEnd_7803086 < baseStart_7803086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803105 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_7803105 : Nat := 118140960795 + 7803105 * 2 ^ 59
def prefixEnd_7803105 : Nat := 4983230072969 + 3 ^ 40 * 7803105 * 2
def baseEnd_7803105 : Nat := 4006743462501798049501679

theorem tailTrace_7803105 : CollatzResearch.WordTrace tailWord_7803105 prefixEnd_7803105 4006743462501798049501679 := by
  unfold tailWord_7803105
  simp only [CollatzResearch.WordTrace]
  refine ⟨284602620395690724080290769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189735080263793816053527179 284602620395690724080290769)
  ·
    refine ⟨213451965296768043060218077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284602620395690724080290769 213451965296768043060218077)
    ·
      refine ⟨80044486986288016147581779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213451965296768043060218077 80044486986288016147581779)
      ·
        refine ⟨120066730479432024221372669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80044486986288016147581779 120066730479432024221372669)
        ·
          refine ⟨45025023929787009083014751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120066730479432024221372669 45025023929787009083014751)
          ·
            refine ⟨67537535894680513624522127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45025023929787009083014751 67537535894680513624522127)
            ·
              refine ⟨101306303842020770436783191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67537535894680513624522127 101306303842020770436783191)
              ·
                refine ⟨151959455763031155655174787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101306303842020770436783191 151959455763031155655174787)
                ·
                  refine ⟨227939183644546733482762181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151959455763031155655174787 227939183644546733482762181)
                  ·
                    refine ⟨42738596933352512528017909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227939183644546733482762181 42738596933352512528017909)
                    ·
                      refine ⟨4006743462501798049501679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42738596933352512528017909 4006743462501798049501679)
                      ·
                        rfl

theorem cell23_7803105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_7803105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803105 prefixEnd_7803105 := by exact prefixLift 7803105
  have htrace : WordTrace (prefixWord ++ tailWord_7803105) baseStart_7803105 baseEnd_7803105 := by
    simpa [prefixWord, tailWord_7803105, baseEnd_7803105] using wordTrace_append hprefix tailTrace_7803105
  have hstable : (prefixWord ++ tailWord_7803105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803105).length < 2 ^ (prefixWord ++ tailWord_7803105).sum := by decide
  have hdescent : baseEnd_7803105 < baseStart_7803105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803109 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 4, 1, 3]
def baseStart_7803109 : Nat := 118140960795 + 7803109 * 2 ^ 59
def prefixEnd_7803109 : Nat := 4983230072969 + 3 ^ 40 * 7803109 * 2
def baseEnd_7803109 : Nat := 4006745516424416033851661

theorem tailTrace_7803109 : CollatzResearch.WordTrace tailWord_7803109 prefixEnd_7803109 4006745516424416033851661 := by
  unfold tailWord_7803109
  simp only [CollatzResearch.WordTrace]
  refine ⟨284602766287676232763436381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189735177525117488508957587 284602766287676232763436381)
  ·
    refine ⟨106726037357878587286288643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284602766287676232763436381 106726037357878587286288643)
    ·
      refine ⟨160089056036817880929432965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106726037357878587286288643 160089056036817880929432965)
      ·
        refine ⟨30016698006903352674268681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160089056036817880929432965 30016698006903352674268681)
        ·
          refine ⟨22512523505177514505701511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30016698006903352674268681 22512523505177514505701511)
          ·
            refine ⟨33768785257766271758552267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22512523505177514505701511 33768785257766271758552267)
            ·
              refine ⟨50653177886649407637828401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33768785257766271758552267 50653177886649407637828401)
              ·
                refine ⟨37989883414987055728371301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50653177886649407637828401 37989883414987055728371301)
                ·
                  refine ⟨7123103140310072949069619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37989883414987055728371301 7123103140310072949069619)
                  ·
                    refine ⟨10684654710465109423604429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7123103140310072949069619 10684654710465109423604429)
                    ·
                      refine ⟨4006745516424416033851661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10684654710465109423604429 4006745516424416033851661)
                      ·
                        rfl

theorem cell23_7803109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_7803109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803109 prefixEnd_7803109 := by exact prefixLift 7803109
  have htrace : WordTrace (prefixWord ++ tailWord_7803109) baseStart_7803109 baseEnd_7803109 := by
    simpa [prefixWord, tailWord_7803109, baseEnd_7803109] using wordTrace_append hprefix tailTrace_7803109
  have hstable : (prefixWord ++ tailWord_7803109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803109).length < 2 ^ (prefixWord ++ tailWord_7803109).sum := by decide
  have hdescent : baseEnd_7803109 < baseStart_7803109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803135 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 5]
def baseStart_7803135 : Nat := 118140960795 + 7803135 * 2 ^ 59
def prefixEnd_7803135 : Nat := 4983230072969 + 3 ^ 40 * 7803135 * 2
def baseEnd_7803135 : Nat := 4006758866921432932126541

theorem tailTrace_7803135 : CollatzResearch.WordTrace tailWord_7803135 prefixEnd_7803135 4006758866921432932126541 := by
  unfold tailWord_7803135
  simp only [CollatzResearch.WordTrace]
  refine ⟨284603714585582039203882859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189735809723721359469255239 284603714585582039203882859)
  ·
    refine ⟨426905571878373058805824289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284603714585582039203882859 426905571878373058805824289)
    ·
      refine ⟨320179178908779794104368217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426905571878373058805824289 320179178908779794104368217)
      ·
        refine ⟨240134384181584845578276163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320179178908779794104368217 240134384181584845578276163)
        ·
          refine ⟨360201576272377268367414245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240134384181584845578276163 360201576272377268367414245)
          ·
            refine ⟨67537795551070737818890171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360201576272377268367414245 67537795551070737818890171)
            ·
              refine ⟨101306693326606106728335257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67537795551070737818890171 101306693326606106728335257)
              ·
                refine ⟨75980019994954580046251443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101306693326606106728335257 75980019994954580046251443)
                ·
                  refine ⟨113970029992431870069377165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75980019994954580046251443 113970029992431870069377165)
                  ·
                    refine ⟨42738761247161951276016437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113970029992431870069377165 42738761247161951276016437)
                    ·
                      refine ⟨4006758866921432932126541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42738761247161951276016437 4006758866921432932126541)
                      ·
                        rfl

theorem cell23_7803135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_7803135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803135 prefixEnd_7803135 := by exact prefixLift 7803135
  have htrace : WordTrace (prefixWord ++ tailWord_7803135) baseStart_7803135 baseEnd_7803135 := by
    simpa [prefixWord, tailWord_7803135, baseEnd_7803135] using wordTrace_append hprefix tailTrace_7803135
  have hstable : (prefixWord ++ tailWord_7803135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803135).length < 2 ^ (prefixWord ++ tailWord_7803135).sum := by decide
  have hdescent : baseEnd_7803135 < baseStart_7803135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803143 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_7803143 : Nat := 118140960795 + 7803143 * 2 ^ 59
def prefixEnd_7803143 : Nat := 4983230072969 + 3 ^ 40 * 7803143 * 2
def baseEnd_7803143 : Nat := 4006762974766668900826505

theorem tailTrace_7803143 : CollatzResearch.WordTrace tailWord_7803143 prefixEnd_7803143 4006762974766668900826505 := by
  unfold tailWord_7803143
  simp only [CollatzResearch.WordTrace]
  refine ⟨284604006369553056570174083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189736004246368704380116055 284604006369553056570174083)
  ·
    refine ⟨426906009554329584855261125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284604006369553056570174083 426906009554329584855261125)
    ·
      refine ⟨80044876791436797160361461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 426906009554329584855261125 80044876791436797160361461)
      ·
        refine ⟨7504207199197199733783887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80044876791436797160361461 7504207199197199733783887)
        ·
          refine ⟨11256310798795799600675831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7504207199197199733783887 11256310798795799600675831)
          ·
            refine ⟨16884466198193699401013747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11256310798795799600675831 16884466198193699401013747)
            ·
              refine ⟨25326699297290549101520621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16884466198193699401013747 25326699297290549101520621)
              ·
                refine ⟨9497512236483955913070233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25326699297290549101520621 9497512236483955913070233)
                ·
                  refine ⟨7123134177362966934802675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9497512236483955913070233 7123134177362966934802675)
                  ·
                    refine ⟨10684701266044450402204013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7123134177362966934802675 10684701266044450402204013)
                    ·
                      refine ⟨4006762974766668900826505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10684701266044450402204013 4006762974766668900826505)
                      ·
                        rfl

theorem cell23_7803143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_7803143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803143 prefixEnd_7803143 := by exact prefixLift 7803143
  have htrace : WordTrace (prefixWord ++ tailWord_7803143) baseStart_7803143 baseEnd_7803143 := by
    simpa [prefixWord, tailWord_7803143, baseEnd_7803143] using wordTrace_append hprefix tailTrace_7803143
  have hstable : (prefixWord ++ tailWord_7803143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803143).length < 2 ^ (prefixWord ++ tailWord_7803143).sum := by decide
  have hdescent : baseEnd_7803143 < baseStart_7803143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803155 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 7]
def baseStart_7803155 : Nat := 118140960795 + 7803155 * 2 ^ 59
def prefixEnd_7803155 : Nat := 4983230072969 + 3 ^ 40 * 7803155 * 2
def baseEnd_7803155 : Nat := 445196570726058094875161

theorem tailTrace_7803155 : CollatzResearch.WordTrace tailWord_7803155 prefixEnd_7803155 445196570726058094875161 := by
  unfold tailWord_7803155
  simp only [CollatzResearch.WordTrace]
  refine ⟨284604444045509582619610919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189736296030339721746407279 284604444045509582619610919)
  ·
    refine ⟨426906666068264373929416379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284604444045509582619610919 426906666068264373929416379)
    ·
      refine ⟨640359999102396560894124569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426906666068264373929416379 640359999102396560894124569)
      ·
        refine ⟨480269999326797420670593427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640359999102396560894124569 480269999326797420670593427)
        ·
          refine ⟨720404998990196131005890141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480269999326797420670593427 720404998990196131005890141)
          ·
            refine ⟨270151874621323549127208803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 720404998990196131005890141 270151874621323549127208803)
            ·
              refine ⟨405227811931985323690813205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270151874621323549127208803 405227811931985323690813205)
              ·
                refine ⟨18995053684311812048006869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 405227811931985323690813205 18995053684311812048006869)
                ·
                  refine ⟨445196570726058094875161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18995053684311812048006869 445196570726058094875161)
                  ·
                    rfl

theorem cell23_7803155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 7].length) (baseStart_7803155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803155 prefixEnd_7803155 := by exact prefixLift 7803155
  have htrace : WordTrace (prefixWord ++ tailWord_7803155) baseStart_7803155 baseEnd_7803155 := by
    simpa [prefixWord, tailWord_7803155, baseEnd_7803155] using wordTrace_append hprefix tailTrace_7803155
  have hstable : (prefixWord ++ tailWord_7803155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803155).length < 2 ^ (prefixWord ++ tailWord_7803155).sum := by decide
  have hdescent : baseEnd_7803155 < baseStart_7803155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803189 : List Nat := [1, 3, 3, 1, 2, 1, 3, 4, 5]
def baseStart_7803189 : Nat := 118140960795 + 7803189 * 2 ^ 59
def prefixEnd_7803189 : Nat := 4983230072969 + 3 ^ 40 * 7803189 * 2
def baseEnd_7803189 : Nat := 445198510541863968983477

theorem tailTrace_7803189 : CollatzResearch.WordTrace tailWord_7803189 prefixEnd_7803189 445198510541863968983477 := by
  unfold tailWord_7803189
  simp only [CollatzResearch.WordTrace]
  refine ⟨284605684127386406426348621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189737122751590937617565747 284605684127386406426348621)
  ·
    refine ⟨106727131547769902409880733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284605684127386406426348621 106727131547769902409880733)
    ·
      refine ⟨40022674330413713403705275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106727131547769902409880733 40022674330413713403705275)
      ·
        refine ⟨60034011495620570105557913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40022674330413713403705275 60034011495620570105557913)
        ·
          refine ⟨45025508621715427579168435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60034011495620570105557913 45025508621715427579168435)
          ·
            refine ⟨67538262932573141368752653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45025508621715427579168435 67538262932573141368752653)
            ·
              refine ⟨25326848599714928013282245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67538262932573141368752653 25326848599714928013282245)
              ·
                refine ⟨4748784112446549002490421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25326848599714928013282245 4748784112446549002490421)
                ·
                  refine ⟨445198510541863968983477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4748784112446549002490421 445198510541863968983477)
                  ·
                    rfl

theorem cell23_7803189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 5].length) (baseStart_7803189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803189 prefixEnd_7803189 := by exact prefixLift 7803189
  have htrace : WordTrace (prefixWord ++ tailWord_7803189) baseStart_7803189 baseEnd_7803189 := by
    simpa [prefixWord, tailWord_7803189, baseEnd_7803189] using wordTrace_append hprefix tailTrace_7803189
  have hstable : (prefixWord ++ tailWord_7803189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803189).length < 2 ^ (prefixWord ++ tailWord_7803189).sum := by decide
  have hdescent : baseEnd_7803189 < baseStart_7803189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803215 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 1, 10]
def baseStart_7803215 : Nat := 118140960795 + 7803215 * 2 ^ 59
def prefixEnd_7803215 : Nat := 4983230072969 + 3 ^ 40 * 7803215 * 2
def baseEnd_7803215 : Nat := 1335599981791264206375391

theorem tailTrace_7803215 : CollatzResearch.WordTrace tailWord_7803215 prefixEnd_7803215 1335599981791264206375391 := by
  unfold tailWord_7803215
  simp only [CollatzResearch.WordTrace]
  refine ⟨284606632425292212866795099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189737754950194808577863399 284606632425292212866795099)
  ·
    refine ⟨426909948637938319300192649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284606632425292212866795099 426909948637938319300192649)
    ·
      refine ⟨320182461478453739475144487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426909948637938319300192649 320182461478453739475144487)
      ·
        refine ⟨480273692217680609212716731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320182461478453739475144487 480273692217680609212716731)
        ·
          refine ⟨720410538326520913819075097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480273692217680609212716731 720410538326520913819075097)
          ·
            refine ⟨540307903744890685364306323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720410538326520913819075097 540307903744890685364306323)
            ·
              refine ⟨810461855617336028046459485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540307903744890685364306323 810461855617336028046459485)
              ·
                refine ⟨303923195856501010517422307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 810461855617336028046459485 303923195856501010517422307)
                ·
                  refine ⟨455884793784751515776133461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303923195856501010517422307 455884793784751515776133461)
                  ·
                    refine ⟨1335599981791264206375391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 455884793784751515776133461 1335599981791264206375391)
                    ·
                      rfl

theorem cell23_7803215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_7803215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803215 prefixEnd_7803215 := by exact prefixLift 7803215
  have htrace : WordTrace (prefixWord ++ tailWord_7803215) baseStart_7803215 baseEnd_7803215 := by
    simpa [prefixWord, tailWord_7803215, baseEnd_7803215] using wordTrace_append hprefix tailTrace_7803215
  have hstable : (prefixWord ++ tailWord_7803215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803215).length < 2 ^ (prefixWord ++ tailWord_7803215).sum := by decide
  have hdescent : baseEnd_7803215 < baseStart_7803215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803322 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 5, 6]
def baseStart_7803322 : Nat := 118140960795 + 7803322 * 2 ^ 59
def prefixEnd_7803322 : Nat := 4983230072969 + 3 ^ 40 * 7803322 * 2
def baseEnd_7803322 : Nat := 1335618295934607900162727

theorem tailTrace_7803322 : CollatzResearch.WordTrace tailWord_7803322 prefixEnd_7803322 1335618295934607900162727 := by
  unfold tailWord_7803322
  simp only [CollatzResearch.WordTrace]
  refine ⟨71152633758976142535235055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189740356690603046760626813 71152633758976142535235055)
  ·
    refine ⟨106728950638464213802852583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71152633758976142535235055 106728950638464213802852583)
    ·
      refine ⟨160093425957696320704278875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106728950638464213802852583 160093425957696320704278875)
      ·
        refine ⟨240140138936544481056418313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160093425957696320704278875 240140138936544481056418313)
        ·
          refine ⟨180105104202408360792313735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240140138936544481056418313 180105104202408360792313735)
          ·
            refine ⟨270157656303612541188470603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180105104202408360792313735 270157656303612541188470603)
            ·
              refine ⟨405236484455418811782705905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270157656303612541188470603 405236484455418811782705905)
              ·
                refine ⟨303927363341564108837029429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405236484455418811782705905 303927363341564108837029429)
                ·
                  refine ⟨28493190313271635203471509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 303927363341564108837029429 28493190313271635203471509)
                  ·
                    refine ⟨1335618295934607900162727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28493190313271635203471509 1335618295934607900162727)
                    ·
                      rfl

theorem cell23_7803322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_7803322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803322 prefixEnd_7803322 := by exact prefixLift 7803322
  have htrace : WordTrace (prefixWord ++ tailWord_7803322) baseStart_7803322 baseEnd_7803322 := by
    simpa [prefixWord, tailWord_7803322, baseEnd_7803322] using wordTrace_append hprefix tailTrace_7803322
  have hstable : (prefixWord ++ tailWord_7803322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803322).length < 2 ^ (prefixWord ++ tailWord_7803322).sum := by decide
  have hdescent : baseEnd_7803322 < baseStart_7803322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803326 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_7803326 : Nat := 118140960795 + 7803326 * 2 ^ 59
def prefixEnd_7803326 : Nat := 4983230072969 + 3 ^ 40 * 7803326 * 2
def baseEnd_7803326 : Nat := 1335618980575480561612721

theorem tailTrace_7803326 : CollatzResearch.WordTrace tailWord_7803326 prefixEnd_7803326 1335618980575480561612721 := by
  unfold tailWord_7803326
  simp only [CollatzResearch.WordTrace]
  refine ⟨35576335115986259853010729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189740453951926719216057221 35576335115986259853010729)
  ·
    refine ⟨26682251336989694889758047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35576335115986259853010729 26682251336989694889758047)
    ·
      refine ⟨40023377005484542334637071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26682251336989694889758047 40023377005484542334637071)
      ·
        refine ⟨60035065508226813501955607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40023377005484542334637071 60035065508226813501955607)
        ·
          refine ⟨90052598262340220252933411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60035065508226813501955607 90052598262340220252933411)
          ·
            refine ⟨135078897393510330379400117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90052598262340220252933411 135078897393510330379400117)
            ·
              refine ⟨12663646630641593473068761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135078897393510330379400117 12663646630641593473068761)
              ·
                refine ⟨9497734972981195104801571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12663646630641593473068761 9497734972981195104801571)
                ·
                  refine ⟨14246602459471792657202357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9497734972981195104801571 14246602459471792657202357)
                  ·
                    refine ⟨1335618980575480561612721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14246602459471792657202357 1335618980575480561612721)
                    ·
                      rfl

theorem cell23_7803326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_7803326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803326 prefixEnd_7803326 := by exact prefixLift 7803326
  have htrace : WordTrace (prefixWord ++ tailWord_7803326) baseStart_7803326 baseEnd_7803326 := by
    simpa [prefixWord, tailWord_7803326, baseEnd_7803326] using wordTrace_append hprefix tailTrace_7803326
  have hstable : (prefixWord ++ tailWord_7803326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803326).length < 2 ^ (prefixWord ++ tailWord_7803326).sum := by decide
  have hdescent : baseEnd_7803326 < baseStart_7803326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803373 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_7803373 : Nat := 118140960795 + 7803373 * 2 ^ 59
def prefixEnd_7803373 : Nat := 4983230072969 + 3 ^ 40 * 7803373 * 2
def baseEnd_7803373 : Nat := 1335627025105734333650149

theorem tailTrace_7803373 : CollatzResearch.WordTrace tailWord_7803373 prefixEnd_7803373 1335627025105734333650149 := by
  unfold tailWord_7803373
  simp only [CollatzResearch.WordTrace]
  refine ⟨284612395158719805851046773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189741596772479870567364515 284612395158719805851046773)
  ·
    refine ⟨26682412046129981798535635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284612395158719805851046773 26682412046129981798535635)
    ·
      refine ⟨40023618069194972697803453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26682412046129981798535635 40023618069194972697803453)
      ·
        refine ⟨15008856775948114761676295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40023618069194972697803453 15008856775948114761676295)
        ·
          refine ⟨22513285163922172142514443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15008856775948114761676295 22513285163922172142514443)
          ·
            refine ⟨33769927745883258213771665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22513285163922172142514443 33769927745883258213771665)
            ·
              refine ⟨25327445809412443660328749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33769927745883258213771665 25327445809412443660328749)
              ·
                refine ⟨9497792178529666372623281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25327445809412443660328749 9497792178529666372623281)
                ·
                  refine ⟨7123344133897249779467461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9497792178529666372623281 7123344133897249779467461)
                  ·
                    refine ⟨1335627025105734333650149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7123344133897249779467461 1335627025105734333650149)
                    ·
                      rfl

theorem cell23_7803373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_7803373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803373 prefixEnd_7803373 := by exact prefixLift 7803373
  have htrace : WordTrace (prefixWord ++ tailWord_7803373) baseStart_7803373 baseEnd_7803373 := by
    simpa [prefixWord, tailWord_7803373, baseEnd_7803373] using wordTrace_append hprefix tailTrace_7803373
  have hstable : (prefixWord ++ tailWord_7803373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803373).length < 2 ^ (prefixWord ++ tailWord_7803373).sum := by decide
  have hdescent : baseEnd_7803373 < baseStart_7803373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803429 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 2, 6]
def baseStart_7803429 : Nat := 118140960795 + 7803429 * 2 ^ 59
def prefixEnd_7803429 : Nat := 4983230072969 + 3 ^ 40 * 7803429 * 2
def baseEnd_7803429 : Nat := 1335636610077951593950063

theorem tailTrace_7803429 : CollatzResearch.WordTrace tailWord_7803429 prefixEnd_7803429 1335636610077951593950063 := by
  unfold tailWord_7803429
  simp only [CollatzResearch.WordTrace]
  refine ⟨284614437646516927415085341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189742958431011284943390227 284614437646516927415085341)
  ·
    refine ⟨106730414117443847780657003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284614437646516927415085341 106730414117443847780657003)
    ·
      refine ⟨160095621176165771670985505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106730414117443847780657003 160095621176165771670985505)
      ·
        refine ⟨120071715882124328753239129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160095621176165771670985505 120071715882124328753239129)
        ·
          refine ⟨90053786911593246564929347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120071715882124328753239129 90053786911593246564929347)
          ·
            refine ⟨135080680367389869847394021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90053786911593246564929347 135080680367389869847394021)
            ·
              refine ⟨25327627568885600596386379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135080680367389869847394021 25327627568885600596386379)
              ·
                refine ⟨37991441353328400894579569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25327627568885600596386379 37991441353328400894579569)
                ·
                  refine ⟨28493581014996300670934677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37991441353328400894579569 28493581014996300670934677)
                  ·
                    refine ⟨1335636610077951593950063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28493581014996300670934677 1335636610077951593950063)
                    ·
                      rfl

theorem cell23_7803429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_7803429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803429 prefixEnd_7803429 := by exact prefixLift 7803429
  have htrace : WordTrace (prefixWord ++ tailWord_7803429) baseStart_7803429 baseEnd_7803429 := by
    simpa [prefixWord, tailWord_7803429, baseEnd_7803429] using wordTrace_append hprefix tailTrace_7803429
  have hstable : (prefixWord ++ tailWord_7803429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803429).length < 2 ^ (prefixWord ++ tailWord_7803429).sum := by decide
  have hdescent : baseEnd_7803429 < baseStart_7803429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803437 : List Nat := [1, 5, 4, 1, 1, 2, 2, 7]
def baseStart_7803437 : Nat := 118140960795 + 7803437 * 2 ^ 59
def prefixEnd_7803437 : Nat := 4983230072969 + 3 ^ 40 * 7803437 * 2
def baseEnd_7803437 : Nat := 148404219928855212983339

theorem tailTrace_7803437 : CollatzResearch.WordTrace tailWord_7803437 prefixEnd_7803437 148404219928855212983339 := by
  unfold tailWord_7803437
  simp only [CollatzResearch.WordTrace]
  refine ⟨284614729430487944781376565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189743152953658629854251043 284614729430487944781376565)
  ·
    refine ⟨26682630884108244823254053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 284614729430487944781376565 26682630884108244823254053)
    ·
      refine ⟨5002993290770295904360135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26682630884108244823254053 5002993290770295904360135)
      ·
        refine ⟨7504489936155443856540203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5002993290770295904360135 7504489936155443856540203)
        ·
          refine ⟨11256734904233165784810305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7504489936155443856540203 11256734904233165784810305)
          ·
            refine ⟨8442551178174874338607729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11256734904233165784810305 8442551178174874338607729)
            ·
              refine ⟨6331913383631155753955797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8442551178174874338607729 6331913383631155753955797)
              ·
                refine ⟨148404219928855212983339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6331913383631155753955797 148404219928855212983339)
                ·
                  rfl

theorem cell23_7803437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 7].length) (baseStart_7803437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803437 prefixEnd_7803437 := by exact prefixLift 7803437
  have htrace : WordTrace (prefixWord ++ tailWord_7803437) baseStart_7803437 baseEnd_7803437 := by
    simpa [prefixWord, tailWord_7803437, baseEnd_7803437] using wordTrace_append hprefix tailTrace_7803437
  have hstable : (prefixWord ++ tailWord_7803437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803437).length < 2 ^ (prefixWord ++ tailWord_7803437).sum := by decide
  have hdescent : baseEnd_7803437 < baseStart_7803437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803476 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 7]
def baseStart_7803476 : Nat := 118140960795 + 7803476 * 2 ^ 59
def prefixEnd_7803476 : Nat := 4983230072969 + 3 ^ 40 * 7803476 * 2
def baseEnd_7803476 : Nat := 445214884869401788662497

theorem tailTrace_7803476 : CollatzResearch.WordTrace tailWord_7803476 prefixEnd_7803476 445214884869401788662497 := by
  unfold tailWord_7803476
  simp only [CollatzResearch.WordTrace]
  refine ⟨142308075938673327221023141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189744101251564436294697521 142308075938673327221023141)
  ·
    refine ⟨26682764238501248853941839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142308075938673327221023141 26682764238501248853941839)
    ·
      refine ⟨40024146357751873280912759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26682764238501248853941839 40024146357751873280912759)
      ·
        refine ⟨60036219536627809921369139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40024146357751873280912759 60036219536627809921369139)
        ·
          refine ⟨90054329304941714882053709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60036219536627809921369139 90054329304941714882053709)
          ·
            refine ⟨33770373489353143080770141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90054329304941714882053709 33770373489353143080770141)
            ·
              refine ⟨12663890058507428655288803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33770373489353143080770141 12663890058507428655288803)
              ·
                refine ⟨18995835087761142982933205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12663890058507428655288803 18995835087761142982933205)
                ·
                  refine ⟨445214884869401788662497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18995835087761142982933205 445214884869401788662497)
                  ·
                    rfl

theorem cell23_7803476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_7803476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803476 prefixEnd_7803476 := by exact prefixLift 7803476
  have htrace : WordTrace (prefixWord ++ tailWord_7803476) baseStart_7803476 baseEnd_7803476 := by
    simpa [prefixWord, tailWord_7803476, baseEnd_7803476] using wordTrace_append hprefix tailTrace_7803476
  have hstable : (prefixWord ++ tailWord_7803476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803476).length < 2 ^ (prefixWord ++ tailWord_7803476).sum := by decide
  have hdescent : baseEnd_7803476 < baseStart_7803476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803529 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_7803529 : Nat := 118140960795 + 7803529 * 2 ^ 59
def prefixEnd_7803529 : Nat := 4983230072969 + 3 ^ 40 * 7803529 * 2
def baseEnd_7803529 : Nat := 4006961178299304390599729

theorem tailTrace_7803529 : CollatzResearch.WordTrace tailWord_7803529 prefixEnd_7803529 4006961178299304390599729 := by
  unfold tailWord_7803529
  simp only [CollatzResearch.WordTrace]
  refine ⟨284618084946154644493725641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189745389964103096329150427 284618084946154644493725641)
  ·
    refine ⟨213463563709615983370294231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284618084946154644493725641 213463563709615983370294231)
    ·
      refine ⟨320195345564423975055441347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213463563709615983370294231 320195345564423975055441347)
      ·
        refine ⟨480293018346635962583162021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320195345564423975055441347 480293018346635962583162021)
        ·
          refine ⟨90054940939994242984342879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 480293018346635962583162021 90054940939994242984342879)
          ·
            refine ⟨135082411409991364476514319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90054940939994242984342879 135082411409991364476514319)
            ·
              refine ⟨202623617114987046714771479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135082411409991364476514319 202623617114987046714771479)
              ·
                refine ⟨303935425672480570072157219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202623617114987046714771479 303935425672480570072157219)
                ·
                  refine ⟨455903138508720855108235829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303935425672480570072157219 455903138508720855108235829)
                  ·
                    refine ⟨42740919235192580166397109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 455903138508720855108235829 42740919235192580166397109)
                    ·
                      refine ⟨4006961178299304390599729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42740919235192580166397109 4006961178299304390599729)
                      ·
                        rfl

theorem cell23_7803529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_7803529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803529 prefixEnd_7803529 := by exact prefixLift 7803529
  have htrace : WordTrace (prefixWord ++ tailWord_7803529) baseStart_7803529 baseEnd_7803529 := by
    simpa [prefixWord, tailWord_7803529, baseEnd_7803529] using wordTrace_append hprefix tailTrace_7803529
  have hstable : (prefixWord ++ tailWord_7803529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803529).length < 2 ^ (prefixWord ++ tailWord_7803529).sum := by decide
  have hdescent : baseEnd_7803529 < baseStart_7803529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803539 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 6]
def baseStart_7803539 : Nat := 118140960795 + 7803539 * 2 ^ 59
def prefixEnd_7803539 : Nat := 4983230072969 + 3 ^ 40 * 7803539 * 2
def baseEnd_7803539 : Nat := 4006966313105849351474683

theorem tailTrace_7803539 : CollatzResearch.WordTrace tailWord_7803539 prefixEnd_7803539 4006966313105849351474683 := by
  unfold tailWord_7803539
  simp only [CollatzResearch.WordTrace]
  refine ⟨284618449676118416201589671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189745633117412277467726447 284618449676118416201589671)
  ·
    refine ⟨426927674514177624302384507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284618449676118416201589671 426927674514177624302384507)
    ·
      refine ⟨640391511771266436453576761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426927674514177624302384507 640391511771266436453576761)
      ·
        refine ⟨480293633828449827340182571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640391511771266436453576761 480293633828449827340182571)
        ·
          refine ⟨720440450742674741010273857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480293633828449827340182571 720440450742674741010273857)
          ·
            refine ⟨540330338057006055757705393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720440450742674741010273857 540330338057006055757705393)
            ·
              refine ⟨405247753542754541818279045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540330338057006055757705393 405247753542754541818279045)
              ·
                refine ⟨75983953789266476590927321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405247753542754541818279045 75983953789266476590927321)
                ·
                  refine ⟨56987965341949857443195491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75983953789266476590927321 56987965341949857443195491)
                  ·
                    refine ⟨85481948012924786164793237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56987965341949857443195491 85481948012924786164793237)
                    ·
                      refine ⟨4006966313105849351474683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85481948012924786164793237 4006966313105849351474683)
                      ·
                        rfl

theorem cell23_7803539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_7803539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803539 prefixEnd_7803539 := by exact prefixLift 7803539
  have htrace : WordTrace (prefixWord ++ tailWord_7803539) baseStart_7803539 baseEnd_7803539 := by
    simpa [prefixWord, tailWord_7803539, baseEnd_7803539] using wordTrace_append hprefix tailTrace_7803539
  have hstable : (prefixWord ++ tailWord_7803539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803539).length < 2 ^ (prefixWord ++ tailWord_7803539).sum := by decide
  have hdescent : baseEnd_7803539 < baseStart_7803539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803543 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 2, 4, 2]
def baseStart_7803543 : Nat := 118140960795 + 7803543 * 2 ^ 59
def prefixEnd_7803543 : Nat := 4983230072969 + 3 ^ 40 * 7803543 * 2
def baseEnd_7803543 : Nat := 4006968367028467335824665

theorem tailTrace_7803543 : CollatzResearch.WordTrace tailWord_7803543 prefixEnd_7803543 4006968367028467335824665 := by
  unfold tailWord_7803543
  simp only [CollatzResearch.WordTrace]
  refine ⟨284618595568103924884735283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189745730378735949923156855 284618595568103924884735283)
  ·
    refine ⟨426927893352155887327102925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284618595568103924884735283 426927893352155887327102925)
    ·
      refine ⟨160097960007058457747663597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426927893352155887327102925 160097960007058457747663597)
      ·
        refine ⟨60036735002646921655373849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160097960007058457747663597 60036735002646921655373849)
        ·
          refine ⟨45027551251985191241530387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60036735002646921655373849 45027551251985191241530387)
          ·
            refine ⟨67541326877977786862295581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45027551251985191241530387 67541326877977786862295581)
            ·
              refine ⟨25327997579241670073360843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67541326877977786862295581 25327997579241670073360843)
              ·
                refine ⟨37991996368862505110041265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25327997579241670073360843 37991996368862505110041265)
                ·
                  refine ⟨28493997276646878832530949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37991996368862505110041265 28493997276646878832530949)
                  ·
                    refine ⟨5342624489371289781099553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28493997276646878832530949 5342624489371289781099553)
                    ·
                      refine ⟨4006968367028467335824665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5342624489371289781099553 4006968367028467335824665)
                      ·
                        rfl

theorem cell23_7803543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_7803543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803543 prefixEnd_7803543 := by exact prefixLift 7803543
  have htrace : WordTrace (prefixWord ++ tailWord_7803543) baseStart_7803543 baseEnd_7803543 := by
    simpa [prefixWord, tailWord_7803543, baseEnd_7803543] using wordTrace_append hprefix tailTrace_7803543
  have hstable : (prefixWord ++ tailWord_7803543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803543).length < 2 ^ (prefixWord ++ tailWord_7803543).sum := by decide
  have hdescent : baseEnd_7803543 < baseStart_7803543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803583 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 6]
def baseStart_7803583 : Nat := 118140960795 + 7803583 * 2 ^ 59
def prefixEnd_7803583 : Nat := 4983230072969 + 3 ^ 40 * 7803583 * 2
def baseEnd_7803583 : Nat := 445220989583849686591609

theorem tailTrace_7803583 : CollatzResearch.WordTrace tailWord_7803583 prefixEnd_7803583 445220989583849686591609 := by
  unfold tailWord_7803583
  simp only [CollatzResearch.WordTrace]
  refine ⟨284620054487959011716191403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189746702991972674477460935 284620054487959011716191403)
  ·
    refine ⟨426930081731938517574287105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284620054487959011716191403 426930081731938517574287105)
    ·
      refine ⟨320197561298953888180715329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426930081731938517574287105 320197561298953888180715329)
      ·
        refine ⟨240148170974215416135536497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320197561298953888180715329 240148170974215416135536497)
        ·
          refine ⟨180111128230661562101652373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240148170974215416135536497 180111128230661562101652373)
          ·
            refine ⟨8442709135812260723514955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180111128230661562101652373 8442709135812260723514955)
            ·
              refine ⟨12664063703718391085272433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8442709135812260723514955 12664063703718391085272433)
              ·
                refine ⟨9498047777788793313954325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12664063703718391085272433 9498047777788793313954325)
                ·
                  refine ⟨445220989583849686591609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9498047777788793313954325 445220989583849686591609)
                  ·
                    rfl

theorem cell23_7803583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 6].length) (baseStart_7803583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803583 prefixEnd_7803583 := by exact prefixLift 7803583
  have htrace : WordTrace (prefixWord ++ tailWord_7803583) baseStart_7803583 baseEnd_7803583 := by
    simpa [prefixWord, tailWord_7803583, baseEnd_7803583] using wordTrace_append hprefix tailTrace_7803583
  have hstable : (prefixWord ++ tailWord_7803583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803583).length < 2 ^ (prefixWord ++ tailWord_7803583).sum := by decide
  have hdescent : baseEnd_7803583 < baseStart_7803583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803626 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 3, 6]
def baseStart_7803626 : Nat := 118140960795 + 7803626 * 2 ^ 59
def prefixEnd_7803626 : Nat := 4983230072969 + 3 ^ 40 * 7803626 * 2
def baseEnd_7803626 : Nat := 1335670328640930170362261

theorem tailTrace_7803626 : CollatzResearch.WordTrace tailWord_7803626 prefixEnd_7803626 1335670328640930170362261 := by
  unfold tailWord_7803626
  simp only [CollatzResearch.WordTrace]
  refine ⟨71155405706700807515001683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189747748551202153373337821 71155405706700807515001683)
  ·
    refine ⟨106733108560051211272502525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71155405706700807515001683 106733108560051211272502525)
    ·
      refine ⟨40024915710019204227188447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106733108560051211272502525 40024915710019204227188447)
      ·
        refine ⟨60037373565028806340782671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40024915710019204227188447 60037373565028806340782671)
        ·
          refine ⟨90056060347543209511174007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60037373565028806340782671 90056060347543209511174007)
          ·
            refine ⟨135084090521314814266761011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90056060347543209511174007 135084090521314814266761011)
            ·
              refine ⟨202626135781972221400141517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135084090521314814266761011 202626135781972221400141517)
              ·
                refine ⟨75984800918239583025053069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202626135781972221400141517 75984800918239583025053069)
                ·
                  refine ⟨28494300344339843634394901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75984800918239583025053069 28494300344339843634394901)
                  ·
                    refine ⟨1335670328640930170362261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28494300344339843634394901 1335670328640930170362261)
                    ·
                      rfl

theorem cell23_7803626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_7803626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803626 prefixEnd_7803626 := by exact prefixLift 7803626
  have htrace : WordTrace (prefixWord ++ tailWord_7803626) baseStart_7803626 baseEnd_7803626 := by
    simpa [prefixWord, tailWord_7803626, baseEnd_7803626] using wordTrace_append hprefix tailTrace_7803626
  have hstable : (prefixWord ++ tailWord_7803626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803626).length < 2 ^ (prefixWord ++ tailWord_7803626).sum := by decide
  have hdescent : baseEnd_7803626 < baseStart_7803626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803633 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 4]
def baseStart_7803633 : Nat := 118140960795 + 7803633 * 2 ^ 59
def prefixEnd_7803633 : Nat := 4983230072969 + 3 ^ 40 * 7803633 * 2
def baseEnd_7803633 : Nat := 4007014580287371983699251

theorem tailTrace_7803633 : CollatzResearch.WordTrace tailWord_7803633 prefixEnd_7803633 4007014580287371983699251 := by
  unfold tailWord_7803633
  simp only [CollatzResearch.WordTrace]
  refine ⟨284621878137777870255511553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189747918758518580170341035 284621878137777870255511553)
  ·
    refine ⟨213466408603333402691633665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284621878137777870255511553 213466408603333402691633665)
    ·
      refine ⟨160099806452500052018725249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213466408603333402691633665 160099806452500052018725249)
      ·
        refine ⟨120074854839375039014043937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160099806452500052018725249 120074854839375039014043937)
        ·
          refine ⟨90056141129531279260532953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120074854839375039014043937 90056141129531279260532953)
          ·
            refine ⟨67542105847148459445399715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90056141129531279260532953 67542105847148459445399715)
            ·
              refine ⟨101313158770722689168099573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67542105847148459445399715 101313158770722689168099573)
              ·
                refine ⟨9498108634755252109509335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101313158770722689168099573 9498108634755252109509335)
                ·
                  refine ⟨14247162952132878164264003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9498108634755252109509335 14247162952132878164264003)
                  ·
                    refine ⟨21370744428199317246396005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14247162952132878164264003 21370744428199317246396005)
                    ·
                      refine ⟨4007014580287371983699251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21370744428199317246396005 4007014580287371983699251)
                      ·
                        rfl

theorem cell23_7803633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_7803633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803633 prefixEnd_7803633 := by exact prefixLift 7803633
  have htrace : WordTrace (prefixWord ++ tailWord_7803633) baseStart_7803633 baseEnd_7803633 := by
    simpa [prefixWord, tailWord_7803633, baseEnd_7803633] using wordTrace_append hprefix tailTrace_7803633
  have hstable : (prefixWord ++ tailWord_7803633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803633).length < 2 ^ (prefixWord ++ tailWord_7803633).sum := by decide
  have hdescent : baseEnd_7803633 < baseStart_7803633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803644 : List Nat := [2, 2, 2, 1, 3, 3, 3, 2, 1, 1, 3]
def baseStart_7803644 : Nat := 118140960795 + 7803644 * 2 ^ 59
def prefixEnd_7803644 : Nat := 4983230072969 + 3 ^ 40 * 7803644 * 2
def baseEnd_7803644 : Nat := 4007020228574571440661701

theorem tailTrace_7803644 : CollatzResearch.WordTrace tailWord_7803644 prefixEnd_7803644 4007020228574571440661701 := by
  unfold tailWord_7803644
  simp only [CollatzResearch.WordTrace]
  refine ⟨142311139670369009567080993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189748186227158679422774657 142311139670369009567080993)
  ·
    refine ⟨106733354752776757175310745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142311139670369009567080993 106733354752776757175310745)
    ·
      refine ⟨80050016064582567881483059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106733354752776757175310745 80050016064582567881483059)
      ·
        refine ⟨120075024096873851822224589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80050016064582567881483059 120075024096873851822224589)
        ·
          refine ⟨45028134036327694433334221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120075024096873851822224589 45028134036327694433334221)
          ·
            refine ⟨16885550263622885412500333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45028134036327694433334221 16885550263622885412500333)
            ·
              refine ⟨6332081348858582029687625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16885550263622885412500333 6332081348858582029687625)
              ·
                refine ⟨4749061011643936522265719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6332081348858582029687625 4749061011643936522265719)
                ·
                  refine ⟨7123591517465904783398579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749061011643936522265719 7123591517465904783398579)
                  ·
                    refine ⟨10685387276198857175097869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7123591517465904783398579 10685387276198857175097869)
                    ·
                      refine ⟨4007020228574571440661701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10685387276198857175097869 4007020228574571440661701)
                      ·
                        rfl

theorem cell23_7803644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_7803644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803644 prefixEnd_7803644 := by exact prefixLift 7803644
  have htrace : WordTrace (prefixWord ++ tailWord_7803644) baseStart_7803644 baseEnd_7803644 := by
    simpa [prefixWord, tailWord_7803644, baseEnd_7803644] using wordTrace_append hprefix tailTrace_7803644
  have hstable : (prefixWord ++ tailWord_7803644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803644).length < 2 ^ (prefixWord ++ tailWord_7803644).sum := by decide
  have hdescent : baseEnd_7803644 < baseStart_7803644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803656 : List Nat := [2, 1, 3, 2, 2, 2, 1, 10]
def baseStart_7803656 : Nat := 118140960795 + 7803656 * 2 ^ 59
def prefixEnd_7803656 : Nat := 4983230072969 + 3 ^ 40 * 7803656 * 2
def baseEnd_7803656 : Nat := 148408384827497236804135

theorem tailTrace_7803656 : CollatzResearch.WordTrace tailWord_7803656 prefixEnd_7803656 148408384827497236804135 := by
  unfold tailWord_7803656
  simp only [CollatzResearch.WordTrace]
  refine ⟨142311358508347272591799411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189748478011129696789065881 142311358508347272591799411)
  ·
    refine ⟨213467037762520908887699117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142311358508347272591799411 213467037762520908887699117)
    ·
      refine ⟨80050139160945340832887169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213467037762520908887699117 80050139160945340832887169)
      ·
        refine ⟨60037604370709005624665377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80050139160945340832887169 60037604370709005624665377)
        ·
          refine ⟨45028203278031754218499033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60037604370709005624665377 45028203278031754218499033)
          ·
            refine ⟨33771152458523815663874275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45028203278031754218499033 33771152458523815663874275)
            ·
              refine ⟨50656728687785723495811413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33771152458523815663874275 50656728687785723495811413)
              ·
                refine ⟨148408384827497236804135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50656728687785723495811413 148408384827497236804135)
                ·
                  rfl

theorem cell23_7803656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 10].length) (baseStart_7803656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803656 prefixEnd_7803656 := by exact prefixLift 7803656
  have htrace : WordTrace (prefixWord ++ tailWord_7803656) baseStart_7803656 baseEnd_7803656 := by
    simpa [prefixWord, tailWord_7803656, baseEnd_7803656] using wordTrace_append hprefix tailTrace_7803656
  have hstable : (prefixWord ++ tailWord_7803656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803656).length < 2 ^ (prefixWord ++ tailWord_7803656).sum := by decide
  have hdescent : baseEnd_7803656 < baseStart_7803656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803690 : List Nat := [3, 1, 4, 3, 2, 10]
def baseStart_7803690 : Nat := 118140960795 + 7803690 * 2 ^ 59
def prefixEnd_7803690 : Nat := 4983230072969 + 3 ^ 40 * 7803690 * 2
def baseEnd_7803690 : Nat := 16489892381418429056323

theorem tailTrace_7803690 : CollatzResearch.WordTrace tailWord_7803690 prefixEnd_7803690 16489892381418429056323 := by
  unfold tailWord_7803690
  simp only [CollatzResearch.WordTrace]
  refine ⟨71155989274642842247584131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189749304732380912660224349 71155989274642842247584131)
  ·
    refine ⟨106733983911964263371376197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71155989274642842247584131 106733983911964263371376197)
    ·
      refine ⟨20012621983493299382133037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106733983911964263371376197 20012621983493299382133037)
      ·
        refine ⟨7504733243809987268299889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20012621983493299382133037 7504733243809987268299889)
        ·
          refine ⟨5628549932857490451224917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7504733243809987268299889 5628549932857490451224917)
          ·
            refine ⟨16489892381418429056323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5628549932857490451224917 16489892381418429056323)
            ·
              rfl

theorem cell23_7803690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 10].length) (baseStart_7803690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803690 prefixEnd_7803690 := by exact prefixLift 7803690
  have htrace : WordTrace (prefixWord ++ tailWord_7803690) baseStart_7803690 baseEnd_7803690 := by
    simpa [prefixWord, tailWord_7803690, baseEnd_7803690] using wordTrace_append hprefix tailTrace_7803690
  have hstable : (prefixWord ++ tailWord_7803690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803690).length < 2 ^ (prefixWord ++ tailWord_7803690).sum := by decide
  have hdescent : baseEnd_7803690 < baseStart_7803690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803696 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_7803696 : Nat := 118140960795 + 7803696 * 2 ^ 59
def prefixEnd_7803696 : Nat := 4983230072969 + 3 ^ 40 * 7803696 * 2
def baseEnd_7803696 : Nat := 4007046929568605237211461

theorem tailTrace_7803696 : CollatzResearch.WordTrace tailWord_7803696 prefixEnd_7803696 4007046929568605237211461 := by
  unfold tailWord_7803696
  simp only [CollatzResearch.WordTrace]
  refine ⟨142312087968274816007527471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189749450624366421343369961 142312087968274816007527471)
  ·
    refine ⟨213468131952412224011291207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142312087968274816007527471 213468131952412224011291207)
    ·
      refine ⟨320202197928618336016936811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213468131952412224011291207 320202197928618336016936811)
      ·
        refine ⟨480303296892927504025405217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320202197928618336016936811 480303296892927504025405217)
        ·
          refine ⟨360227472669695628019053913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480303296892927504025405217 360227472669695628019053913)
          ·
            refine ⟨270170604502271721014290435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360227472669695628019053913 270170604502271721014290435)
            ·
              refine ⟨405255906753407581521435653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270170604502271721014290435 405255906753407581521435653)
              ·
                refine ⟨75985482516263921535269185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 405255906753407581521435653 75985482516263921535269185)
                ·
                  refine ⟨56989111887197941151451889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75985482516263921535269185 56989111887197941151451889)
                  ·
                    refine ⟨42741833915398455863588917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56989111887197941151451889 42741833915398455863588917)
                    ·
                      refine ⟨4007046929568605237211461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42741833915398455863588917 4007046929568605237211461)
                      ·
                        rfl

theorem cell23_7803696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_7803696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803696 prefixEnd_7803696 := by exact prefixLift 7803696
  have htrace : WordTrace (prefixWord ++ tailWord_7803696) baseStart_7803696 baseEnd_7803696 := by
    simpa [prefixWord, tailWord_7803696, baseEnd_7803696] using wordTrace_append hprefix tailTrace_7803696
  have hstable : (prefixWord ++ tailWord_7803696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803696).length < 2 ^ (prefixWord ++ tailWord_7803696).sum := by decide
  have hdescent : baseEnd_7803696 < baseStart_7803696 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803701 : List Nat := [1, 3, 3, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_7803701 : Nat := 118140960795 + 7803701 * 2 ^ 59
def prefixEnd_7803701 : Nat := 4983230072969 + 3 ^ 40 * 7803701 * 2
def baseEnd_7803701 : Nat := 4007049496971877717648939

theorem tailTrace_7803701 : CollatzResearch.WordTrace tailWord_7803701 prefixEnd_7803701 4007049496971877717648939 := by
  unfold tailWord_7803701
  simp only [CollatzResearch.WordTrace]
  refine ⟨284624358301531517868986957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189749572201021011912657971 284624358301531517868986957)
  ·
    refine ⟨106734134363074319200870109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284624358301531517868986957 106734134363074319200870109)
    ·
      refine ⟨40025300386152869700326291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106734134363074319200870109 40025300386152869700326291)
      ·
        refine ⟨60037950579229304550489437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40025300386152869700326291 60037950579229304550489437)
        ·
          refine ⟨22514231467210989206433539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60037950579229304550489437 22514231467210989206433539)
          ·
            refine ⟨33771347200816483809650309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22514231467210989206433539 33771347200816483809650309)
            ·
              refine ⟨6332127600153090714309433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33771347200816483809650309 6332127600153090714309433)
              ·
                refine ⟨4749095700114818035732075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6332127600153090714309433 4749095700114818035732075)
                ·
                  refine ⟨7123643550172227053598113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749095700114818035732075 7123643550172227053598113)
                  ·
                    refine ⟨5342732662629170290198585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7123643550172227053598113 5342732662629170290198585)
                    ·
                      refine ⟨4007049496971877717648939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5342732662629170290198585 4007049496971877717648939)
                      ·
                        rfl

theorem cell23_7803701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_7803701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803701 prefixEnd_7803701 := by exact prefixLift 7803701
  have htrace : WordTrace (prefixWord ++ tailWord_7803701) baseStart_7803701 baseEnd_7803701 := by
    simpa [prefixWord, tailWord_7803701, baseEnd_7803701] using wordTrace_append hprefix tailTrace_7803701
  have hstable : (prefixWord ++ tailWord_7803701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803701).length < 2 ^ (prefixWord ++ tailWord_7803701).sum := by decide
  have hdescent : baseEnd_7803701 < baseStart_7803701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803778 : List Nat := [3, 4, 2, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_7803778 : Nat := 118140960795 + 7803778 * 2 ^ 59
def prefixEnd_7803778 : Nat := 4983230072969 + 3 ^ 40 * 7803778 * 2
def baseEnd_7803778 : Nat := 4007089034982273916386085

theorem tailTrace_7803778 : CollatzResearch.WordTrace tailWord_7803778 prefixEnd_7803778 4007089034982273916386085 := by
  unfold tailWord_7803778
  simp only [CollatzResearch.WordTrace]
  refine ⟨71156791680563140004884997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189751444481501706679693325 71156791680563140004884997)
  ·
    refine ⟨13341898440105588750915937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71156791680563140004884997 13341898440105588750915937)
    ·
      refine ⟨10006423830079191563186953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13341898440105588750915937 10006423830079191563186953)
      ·
        refine ⟨7504817872559393672390215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10006423830079191563186953 7504817872559393672390215)
        ·
          refine ⟨11257226808839090508585323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7504817872559393672390215 11257226808839090508585323)
          ·
            refine ⟨16885840213258635762877985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11257226808839090508585323 16885840213258635762877985)
            ·
              refine ⟨12664380159943976822158489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16885840213258635762877985 12664380159943976822158489)
              ·
                refine ⟨9498285119957982616618867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12664380159943976822158489 9498285119957982616618867)
                ·
                  refine ⟨14247427679936973924928301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9498285119957982616618867 14247427679936973924928301)
                  ·
                    refine ⟨5342785379976365221848113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14247427679936973924928301 5342785379976365221848113)
                    ·
                      refine ⟨4007089034982273916386085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5342785379976365221848113 4007089034982273916386085)
                      ·
                        rfl

theorem cell23_7803778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_7803778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803778 prefixEnd_7803778 := by exact prefixLift 7803778
  have htrace : WordTrace (prefixWord ++ tailWord_7803778) baseStart_7803778 baseEnd_7803778 := by
    simpa [prefixWord, tailWord_7803778, baseEnd_7803778] using wordTrace_append hprefix tailTrace_7803778
  have hstable : (prefixWord ++ tailWord_7803778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803778).length < 2 ^ (prefixWord ++ tailWord_7803778).sum := by decide
  have hdescent : baseEnd_7803778 < baseStart_7803778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803793 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 2, 5]
def baseStart_7803793 : Nat := 118140960795 + 7803793 * 2 ^ 59
def prefixEnd_7803793 : Nat := 4983230072969 + 3 ^ 40 * 7803793 * 2
def baseEnd_7803793 : Nat := 1335698912397363785899505

theorem tailTrace_7803793 : CollatzResearch.WordTrace tailWord_7803793 prefixEnd_7803793 1335698912397363785899505 := by
  unfold tailWord_7803793
  simp only [CollatzResearch.WordTrace]
  refine ⟨284627713817198217581336033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189751809211465478387557355 284627713817198217581336033)
  ·
    refine ⟨213470785362898663186002025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284627713817198217581336033 213470785362898663186002025)
    ·
      refine ⟨160103089022173997389501519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213470785362898663186002025 160103089022173997389501519)
      ·
        refine ⟨240154633533260996084252279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160103089022173997389501519 240154633533260996084252279)
        ·
          refine ⟨360231950299891494126378419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240154633533260996084252279 360231950299891494126378419)
          ·
            refine ⟨540347925449837241189567629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360231950299891494126378419 540347925449837241189567629)
            ·
              refine ⟨202630472043688965446087861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 540347925449837241189567629 202630472043688965446087861)
              ·
                refine ⟨18996606754095840510570737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202630472043688965446087861 18996606754095840510570737)
                ·
                  refine ⟨14247455065571880382928053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18996606754095840510570737 14247455065571880382928053)
                  ·
                    refine ⟨1335698912397363785899505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14247455065571880382928053 1335698912397363785899505)
                    ·
                      rfl

theorem cell23_7803793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_7803793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803793 prefixEnd_7803793 := by exact prefixLift 7803793
  have htrace : WordTrace (prefixWord ++ tailWord_7803793) baseStart_7803793 baseEnd_7803793 := by
    simpa [prefixWord, tailWord_7803793, baseEnd_7803793] using wordTrace_append hprefix tailTrace_7803793
  have hstable : (prefixWord ++ tailWord_7803793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803793).length < 2 ^ (prefixWord ++ tailWord_7803793).sum := by decide
  have hdescent : baseEnd_7803793 < baseStart_7803793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803797 : List Nat := [1, 3, 2, 1, 1, 6, 1, 3, 5]
def baseStart_7803797 : Nat := 118140960795 + 7803797 * 2 ^ 59
def prefixEnd_7803797 : Nat := 4983230072969 + 3 ^ 40 * 7803797 * 2
def baseEnd_7803797 : Nat := 445233199012745482449833

theorem tailTrace_7803797 : CollatzResearch.WordTrace tailWord_7803797 prefixEnd_7803797 445233199012745482449833 := by
  unfold tailWord_7803797
  simp only [CollatzResearch.WordTrace]
  refine ⟨284627859709183726264481645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189751906472789150842987763 284627859709183726264481645)
  ·
    refine ⟨106735447390943897349180617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284627859709183726264481645 106735447390943897349180617)
    ·
      refine ⟨80051585543207923011885463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106735447390943897349180617 80051585543207923011885463)
      ·
        refine ⟨120077378314811884517828195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80051585543207923011885463 120077378314811884517828195)
        ·
          refine ⟨180116067472217826776742293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120077378314811884517828195 180116067472217826776742293)
          ·
            refine ⟨8442940662760210630159795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 180116067472217826776742293 8442940662760210630159795)
            ·
              refine ⟨12664410994140315945239693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8442940662760210630159795 12664410994140315945239693)
              ·
                refine ⟨4749154122802618479464885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12664410994140315945239693 4749154122802618479464885)
                ·
                  refine ⟨445233199012745482449833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4749154122802618479464885 445233199012745482449833)
                  ·
                    rfl

theorem cell23_7803797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_7803797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803797 prefixEnd_7803797 := by exact prefixLift 7803797
  have htrace : WordTrace (prefixWord ++ tailWord_7803797) baseStart_7803797 baseEnd_7803797 := by
    simpa [prefixWord, tailWord_7803797, baseEnd_7803797] using wordTrace_append hprefix tailTrace_7803797
  have hstable : (prefixWord ++ tailWord_7803797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803797).length < 2 ^ (prefixWord ++ tailWord_7803797).sum := by decide
  have hdescent : baseEnd_7803797 < baseStart_7803797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803810 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_7803810 : Nat := 118140960795 + 7803810 * 2 ^ 59
def prefixEnd_7803810 : Nat := 4983230072969 + 3 ^ 40 * 7803810 * 2
def baseEnd_7803810 : Nat := 1335701822121072597061979

theorem tailTrace_7803810 : CollatzResearch.WordTrace tailWord_7803810 prefixEnd_7803810 1335701822121072597061979 := by
  unfold tailWord_7803810
  simp only [CollatzResearch.WordTrace]
  refine ⟨71157083464534157371176221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189752222572091086323136589 71157083464534157371176221)
  ·
    refine ⟨26683906299200309014191083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71157083464534157371176221 26683906299200309014191083)
    ·
      refine ⟨40025859448800463521286625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26683906299200309014191083 40025859448800463521286625)
      ·
        refine ⟨30019394586600347640964969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40025859448800463521286625 30019394586600347640964969)
        ·
          refine ⟨22514545939950260730723727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30019394586600347640964969 22514545939950260730723727)
          ·
            refine ⟨33771818909925391096085591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22514545939950260730723727 33771818909925391096085591)
            ·
              refine ⟨50657728364888086644128387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33771818909925391096085591 50657728364888086644128387)
              ·
                refine ⟨75986592547332129966192581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50657728364888086644128387 75986592547332129966192581)
                ·
                  refine ⟨14247486102624774368661109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75986592547332129966192581 14247486102624774368661109)
                  ·
                    refine ⟨1335701822121072597061979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14247486102624774368661109 1335701822121072597061979)
                    ·
                      rfl

theorem cell23_7803810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_7803810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803810 prefixEnd_7803810 := by exact prefixLift 7803810
  have htrace : WordTrace (prefixWord ++ tailWord_7803810) baseStart_7803810 baseEnd_7803810 := by
    simpa [prefixWord, tailWord_7803810, baseEnd_7803810] using wordTrace_append hprefix tailTrace_7803810
  have hstable : (prefixWord ++ tailWord_7803810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803810).length < 2 ^ (prefixWord ++ tailWord_7803810).sum := by decide
  have hdescent : baseEnd_7803810 < baseStart_7803810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803844 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 2, 5]
def baseStart_7803844 : Nat := 118140960795 + 7803844 * 2 ^ 59
def prefixEnd_7803844 : Nat := 4983230072969 + 3 ^ 40 * 7803844 * 2
def baseEnd_7803844 : Nat := 1335707641568490219386927

theorem tailTrace_7803844 : CollatzResearch.WordTrace tailWord_7803844 prefixEnd_7803844 1335707641568490219386927 := by
  unfold tailWord_7803844
  simp only [CollatzResearch.WordTrace]
  refine ⟨142314786970006726645721293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189753049293342302194295057 142314786970006726645721293)
  ·
    refine ⟨53368045113752522492145485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142314786970006726645721293 53368045113752522492145485)
    ·
      refine ⟨20013016917657195934554557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53368045113752522492145485 20013016917657195934554557)
      ·
        refine ⟨7504881344121448475457959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20013016917657195934554557 7504881344121448475457959)
        ·
          refine ⟨11257322016182172713186939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7504881344121448475457959 11257322016182172713186939)
          ·
            refine ⟨16885983024273259069780409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11257322016182172713186939 16885983024273259069780409)
            ·
              refine ⟨12664487268204944302335307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16885983024273259069780409 12664487268204944302335307)
              ·
                refine ⟨18996730902307416453502961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12664487268204944302335307 18996730902307416453502961)
                ·
                  refine ⟨14247548176730562340127221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18996730902307416453502961 14247548176730562340127221)
                  ·
                    refine ⟨1335707641568490219386927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14247548176730562340127221 1335707641568490219386927)
                    ·
                      rfl

theorem cell23_7803844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_7803844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803844 prefixEnd_7803844 := by exact prefixLift 7803844
  have htrace : WordTrace (prefixWord ++ tailWord_7803844) baseStart_7803844 baseEnd_7803844 := by
    simpa [prefixWord, tailWord_7803844, baseEnd_7803844] using wordTrace_append hprefix tailTrace_7803844
  have hstable : (prefixWord ++ tailWord_7803844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803844).length < 2 ^ (prefixWord ++ tailWord_7803844).sum := by decide
  have hdescent : baseEnd_7803844 < baseStart_7803844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803857 : List Nat := [1, 2, 2, 1, 2, 1, 4, 5, 1, 4]
def baseStart_7803857 : Nat := 118140960795 + 7803857 * 2 ^ 59
def prefixEnd_7803857 : Nat := 4983230072969 + 3 ^ 40 * 7803857 * 2
def baseEnd_7803857 : Nat := 1335709866651326369099407

theorem tailTrace_7803857 : CollatzResearch.WordTrace tailWord_7803857 prefixEnd_7803857 1335709866651326369099407 := by
  unfold tailWord_7803857
  simp only [CollatzResearch.WordTrace]
  refine ⟨284630048088966356511665825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189753365392644237674443883 284630048088966356511665825)
  ·
    refine ⟨213472536066724767383749369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284630048088966356511665825 213472536066724767383749369)
    ·
      refine ⟨160104402050043575537812027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213472536066724767383749369 160104402050043575537812027)
      ·
        refine ⟨240156603075065363306718041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160104402050043575537812027 240156603075065363306718041)
        ·
          refine ⟨180117452306299022480038531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240156603075065363306718041 180117452306299022480038531)
          ·
            refine ⟨270176178459448533720057797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180117452306299022480038531 270176178459448533720057797)
            ·
              refine ⟨50658033461146600072510837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270176178459448533720057797 50658033461146600072510837)
              ·
                refine ⟨4749190636982493756797891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50658033461146600072510837 4749190636982493756797891)
                ·
                  refine ⟨7123785955473740635196837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749190636982493756797891 7123785955473740635196837)
                  ·
                    refine ⟨1335709866651326369099407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7123785955473740635196837 1335709866651326369099407)
                    ·
                      rfl

theorem cell23_7803857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_7803857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803857 prefixEnd_7803857 := by exact prefixLift 7803857
  have htrace : WordTrace (prefixWord ++ tailWord_7803857) baseStart_7803857 baseEnd_7803857 := by
    simpa [prefixWord, tailWord_7803857, baseEnd_7803857] using wordTrace_append hprefix tailTrace_7803857
  have hstable : (prefixWord ++ tailWord_7803857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803857).length < 2 ^ (prefixWord ++ tailWord_7803857).sum := by decide
  have hdescent : baseEnd_7803857 < baseStart_7803857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803873 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_7803873 : Nat := 118140960795 + 7803873 * 2 ^ 59
def prefixEnd_7803873 : Nat := 4983230072969 + 3 ^ 40 * 7803873 * 2
def baseEnd_7803873 : Nat := 4007137815644451044698147

theorem tailTrace_7803873 : CollatzResearch.WordTrace tailWord_7803873 prefixEnd_7803873 4007137815644451044698147 := by
  unfold tailWord_7803873
  simp only [CollatzResearch.WordTrace]
  refine ⟨284630631656908391244248273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189753754437938927496165515 284630631656908391244248273)
  ·
    refine ⟨213472973742681293433186205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284630631656908391244248273 213472973742681293433186205)
    ·
      refine ⟨80052365153505485037444827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213472973742681293433186205 80052365153505485037444827)
      ·
        refine ⟨120078547730258227556167241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80052365153505485037444827 120078547730258227556167241)
        ·
          refine ⟨90058910797693670667125431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120078547730258227556167241 90058910797693670667125431)
          ·
            refine ⟨135088366196540506000688147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90058910797693670667125431 135088366196540506000688147)
            ·
              refine ⟨202632549294810759001032221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135088366196540506000688147 202632549294810759001032221)
              ·
                refine ⟨75987205985554034625387083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202632549294810759001032221 75987205985554034625387083)
                ·
                  refine ⟨113980808978331051938080625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75987205985554034625387083 113980808978331051938080625)
                  ·
                    refine ⟨85485606733748288953560469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113980808978331051938080625 85485606733748288953560469)
                    ·
                      refine ⟨4007137815644451044698147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85485606733748288953560469 4007137815644451044698147)
                      ·
                        rfl

theorem cell23_7803873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_7803873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803873 prefixEnd_7803873 := by exact prefixLift 7803873
  have htrace : WordTrace (prefixWord ++ tailWord_7803873) baseStart_7803873 baseEnd_7803873 := by
    simpa [prefixWord, tailWord_7803873, baseEnd_7803873] using wordTrace_append hprefix tailTrace_7803873
  have hstable : (prefixWord ++ tailWord_7803873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803873).length < 2 ^ (prefixWord ++ tailWord_7803873).sum := by decide
  have hdescent : baseEnd_7803873 < baseStart_7803873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803897 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 3, 1, 3]
def baseStart_7803897 : Nat := 118140960795 + 7803897 * 2 ^ 59
def prefixEnd_7803897 : Nat := 4983230072969 + 3 ^ 40 * 7803897 * 2
def baseEnd_7803897 : Nat := 4007150139180158950798037

theorem tailTrace_7803897 : CollatzResearch.WordTrace tailWord_7803897 prefixEnd_7803897 4007150139180158950798037 := by
  unfold tailWord_7803897
  simp only [CollatzResearch.WordTrace]
  refine ⟨284631507008821443343121945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189754338005880962228747963 284631507008821443343121945)
  ·
    refine ⟨213473630256616082507341459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284631507008821443343121945 213473630256616082507341459)
    ·
      refine ⟨320210445384924123761012189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213473630256616082507341459 320210445384924123761012189)
      ·
        refine ⟨120078917019346546410379571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320210445384924123761012189 120078917019346546410379571)
        ·
          refine ⟨180118375529019819615569357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120078917019346546410379571 180118375529019819615569357)
          ·
            refine ⟨67544390823382432355838509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180118375529019819615569357 67544390823382432355838509)
            ·
              refine ⟨25329146558768412133439441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67544390823382432355838509 25329146558768412133439441)
              ·
                refine ⟨18996859919076309100079581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25329146558768412133439441 18996859919076309100079581)
                ·
                  refine ⟨7123822469653615912529843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18996859919076309100079581 7123822469653615912529843)
                  ·
                    refine ⟨10685733704480423868794765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7123822469653615912529843 10685733704480423868794765)
                    ·
                      refine ⟨4007150139180158950798037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10685733704480423868794765 4007150139180158950798037)
                      ·
                        rfl

theorem cell23_7803897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_7803897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803897 prefixEnd_7803897 := by exact prefixLift 7803897
  have htrace : WordTrace (prefixWord ++ tailWord_7803897) baseStart_7803897 baseEnd_7803897 := by
    simpa [prefixWord, tailWord_7803897, baseEnd_7803897] using wordTrace_append hprefix tailTrace_7803897
  have hstable : (prefixWord ++ tailWord_7803897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803897).length < 2 ^ (prefixWord ++ tailWord_7803897).sum := by decide
  have hdescent : baseEnd_7803897 < baseStart_7803897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803900 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 3, 5]
def baseStart_7803900 : Nat := 118140960795 + 7803900 * 2 ^ 59
def prefixEnd_7803900 : Nat := 4983230072969 + 3 ^ 40 * 7803900 * 2
def baseEnd_7803900 : Nat := 1335717226540707479686841

theorem tailTrace_7803900 : CollatzResearch.WordTrace tailWord_7803900 prefixEnd_7803900 1335717226540707479686841 := by
  unfold tailWord_7803900
  simp only [CollatzResearch.WordTrace]
  refine ⟨142315808213905287427740577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189754410951873716570320769 142315808213905287427740577)
  ·
    refine ⟨106736856160428965570805433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142315808213905287427740577 106736856160428965570805433)
    ·
      refine ⟨80052642120321724178104075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106736856160428965570805433 80052642120321724178104075)
      ·
        refine ⟨120078963180482586267156113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80052642120321724178104075 120078963180482586267156113)
        ·
          refine ⟨90059222385361939700367085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120078963180482586267156113 90059222385361939700367085)
          ·
            refine ⟨33772208394510727387637657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90059222385361939700367085 33772208394510727387637657)
            ·
              refine ⟨25329156295883045540728243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33772208394510727387637657 25329156295883045540728243)
              ·
                refine ⟨37993734443824568311092365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25329156295883045540728243 37993734443824568311092365)
                ·
                  refine ⟨14247650416434213116659637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37993734443824568311092365 14247650416434213116659637)
                  ·
                    refine ⟨1335717226540707479686841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14247650416434213116659637 1335717226540707479686841)
                    ·
                      rfl

theorem cell23_7803900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_7803900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803900 prefixEnd_7803900 := by exact prefixLift 7803900
  have htrace : WordTrace (prefixWord ++ tailWord_7803900) baseStart_7803900 baseEnd_7803900 := by
    simpa [prefixWord, tailWord_7803900, baseEnd_7803900] using wordTrace_append hprefix tailTrace_7803900
  have hstable : (prefixWord ++ tailWord_7803900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803900).length < 2 ^ (prefixWord ++ tailWord_7803900).sum := by decide
  have hdescent : baseEnd_7803900 < baseStart_7803900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803954 : List Nat := [3, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2]
def baseStart_7803954 : Nat := 118140960795 + 7803954 * 2 ^ 59
def prefixEnd_7803954 : Nat := 4983230072969 + 3 ^ 40 * 7803954 * 2
def baseEnd_7803954 : Nat := 4007179407577465227785275

theorem tailTrace_7803954 : CollatzResearch.WordTrace tailWord_7803954 prefixEnd_7803954 4007179407577465227785275 := by
  unfold tailWord_7803954
  simp only [CollatzResearch.WordTrace]
  refine ⟨71158396492403735519486729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189755723979743294718631277 71158396492403735519486729)
  ·
    refine ⟨53368797369302801639615047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71158396492403735519486729 53368797369302801639615047)
    ·
      refine ⟨80053196053954202459422571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53368797369302801639615047 80053196053954202459422571)
      ·
        refine ⟨120079794080931303689133857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80053196053954202459422571 120079794080931303689133857)
        ·
          refine ⟨90059845560698477766850393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120079794080931303689133857 90059845560698477766850393)
          ·
            refine ⟨67544884170523858325137795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90059845560698477766850393 67544884170523858325137795)
            ·
              refine ⟨101317326255785787487706693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67544884170523858325137795 101317326255785787487706693)
              ·
                refine ⟨18996998672959835153945005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101317326255785787487706693 18996998672959835153945005)
                ·
                  refine ⟨7123874502359938182729377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18996998672959835153945005 7123874502359938182729377)
                  ·
                    refine ⟨5342905876769953637047033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7123874502359938182729377 5342905876769953637047033)
                    ·
                      refine ⟨4007179407577465227785275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5342905876769953637047033 4007179407577465227785275)
                      ·
                        rfl

theorem cell23_7803954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_7803954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803954 prefixEnd_7803954 := by exact prefixLift 7803954
  have htrace : WordTrace (prefixWord ++ tailWord_7803954) baseStart_7803954 baseEnd_7803954 := by
    simpa [prefixWord, tailWord_7803954, baseEnd_7803954] using wordTrace_append hprefix tailTrace_7803954
  have hstable : (prefixWord ++ tailWord_7803954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803954).length < 2 ^ (prefixWord ++ tailWord_7803954).sum := by decide
  have hdescent : baseEnd_7803954 < baseStart_7803954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803960 : List Nat := [2, 1, 2, 1, 5, 2, 1, 9]
def baseStart_7803960 : Nat := 118140960795 + 7803960 * 2 ^ 59
def prefixEnd_7803960 : Nat := 4983230072969 + 3 ^ 40 * 7803960 * 2
def baseEnd_7803960 : Nat := 148414166239310822381861

theorem tailTrace_7803960 : CollatzResearch.WordTrace tailWord_7803960 prefixEnd_7803960 148414166239310822381861 := by
  unfold tailWord_7803960
  simp only [CollatzResearch.WordTrace]
  refine ⟨142316902403796602551332667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189755869871728803401776889 142316902403796602551332667)
  ·
    refine ⟨213475353605694903826999001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142316902403796602551332667 213475353605694903826999001)
    ·
      refine ⟨160106515204271177870249251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213475353605694903826999001 160106515204271177870249251)
      ·
        refine ⟨240159772806406766805373877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160106515204271177870249251 240159772806406766805373877)
        ·
          refine ⟨22514978700600634388003801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240159772806406766805373877 22514978700600634388003801)
          ·
            refine ⟨16886234025450475791002851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22514978700600634388003801 16886234025450475791002851)
            ·
              refine ⟨25329351038175713686504277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16886234025450475791002851 25329351038175713686504277)
              ·
                refine ⟨148414166239310822381861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25329351038175713686504277 148414166239310822381861)
                ·
                  rfl

theorem cell23_7803960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 9].length) (baseStart_7803960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803960 prefixEnd_7803960 := by exact prefixLift 7803960
  have htrace : WordTrace (prefixWord ++ tailWord_7803960) baseStart_7803960 baseEnd_7803960 := by
    simpa [prefixWord, tailWord_7803960, baseEnd_7803960] using wordTrace_append hprefix tailTrace_7803960
  have hstable : (prefixWord ++ tailWord_7803960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803960).length < 2 ^ (prefixWord ++ tailWord_7803960).sum := by decide
  have hdescent : baseEnd_7803960 < baseStart_7803960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803974 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_7803974 : Nat := 118140960795 + 7803974 * 2 ^ 59
def prefixEnd_7803974 : Nat := 4983230072969 + 3 ^ 40 * 7803974 * 2
def baseEnd_7803974 : Nat := 4007189677190555149535183

theorem tailTrace_7803974 : CollatzResearch.WordTrace tailWord_7803974 prefixEnd_7803974 4007189677190555149535183 := by
  unfold tailWord_7803974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8894822357173202671677343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 189756210286361656995783317 8894822357173202671677343)
  ·
    refine ⟨13342233535759804007516015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8894822357173202671677343 13342233535759804007516015)
    ·
      refine ⟨20013350303639706011274023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13342233535759804007516015 20013350303639706011274023)
      ·
        refine ⟨30020025455459559016911035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20013350303639706011274023 30020025455459559016911035)
        ·
          refine ⟨45030038183189338525366553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30020025455459559016911035 45030038183189338525366553)
          ·
            refine ⟨33772528637392003894024915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45030038183189338525366553 33772528637392003894024915)
            ·
              refine ⟨50658792956088005841037373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33772528637392003894024915 50658792956088005841037373)
              ·
                refine ⟨18997047358533002190389015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50658792956088005841037373 18997047358533002190389015)
                ·
                  refine ⟨28495571037799503285583523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18997047358533002190389015 28495571037799503285583523)
                  ·
                    refine ⟨42743356556699254928375285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28495571037799503285583523 42743356556699254928375285)
                    ·
                      refine ⟨4007189677190555149535183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42743356556699254928375285 4007189677190555149535183)
                      ·
                        rfl

theorem cell23_7803974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_7803974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803974 prefixEnd_7803974 := by exact prefixLift 7803974
  have htrace : WordTrace (prefixWord ++ tailWord_7803974) baseStart_7803974 baseEnd_7803974 := by
    simpa [prefixWord, tailWord_7803974, baseEnd_7803974] using wordTrace_append hprefix tailTrace_7803974
  have hstable : (prefixWord ++ tailWord_7803974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803974).length < 2 ^ (prefixWord ++ tailWord_7803974).sum := by decide
  have hdescent : baseEnd_7803974 < baseStart_7803974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7803998 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_7803998 : Nat := 118140960795 + 7803998 * 2 ^ 59
def prefixEnd_7803998 : Nat := 4983230072969 + 3 ^ 40 * 7803998 * 2
def baseEnd_7803998 : Nat := 1335734000242087685211691

theorem tailTrace_7803998 : CollatzResearch.WordTrace tailWord_7803998 prefixEnd_7803998 1335734000242087685211691 := by
  unfold tailWord_7803998
  simp only [CollatzResearch.WordTrace]
  refine ⟨35579398847681942199068581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189756793854303691728365765 35579398847681942199068581)
  ·
    refine ⟨6671137283940364162325359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35579398847681942199068581 6671137283940364162325359)
    ·
      refine ⟨10006705925910546243488039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6671137283940364162325359 10006705925910546243488039)
      ·
        refine ⟨15010058888865819365232059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10006705925910546243488039 15010058888865819365232059)
        ·
          refine ⟨22515088333298729047848089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15010058888865819365232059 22515088333298729047848089)
          ·
            refine ⟨16886316249974046785886067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22515088333298729047848089 16886316249974046785886067)
            ·
              refine ⟨25329474374961070178829101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16886316249974046785886067 25329474374961070178829101)
              ·
                refine ⟨9498552890610401317060913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25329474374961070178829101 9498552890610401317060913)
                ·
                  refine ⟨7123914667957800987795685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9498552890610401317060913 7123914667957800987795685)
                  ·
                    refine ⟨1335734000242087685211691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7123914667957800987795685 1335734000242087685211691)
                    ·
                      rfl

theorem cell23_7803998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_7803998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7803998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7803998 prefixEnd_7803998 := by exact prefixLift 7803998
  have htrace : WordTrace (prefixWord ++ tailWord_7803998) baseStart_7803998 baseEnd_7803998 := by
    simpa [prefixWord, tailWord_7803998, baseEnd_7803998] using wordTrace_append hprefix tailTrace_7803998
  have hstable : (prefixWord ++ tailWord_7803998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7803998).length < 2 ^ (prefixWord ++ tailWord_7803998).sum := by decide
  have hdescent : baseEnd_7803998 < baseStart_7803998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7803998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804008 : List Nat := [2, 1, 4, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7804008 : Nat := 118140960795 + 7804008 * 2 ^ 59
def prefixEnd_7804008 : Nat := 4983230072969 + 3 ^ 40 * 7804008 * 2
def baseEnd_7804008 : Nat := 4007207135532808016510027

theorem tailTrace_7804008 : CollatzResearch.WordTrace tailWord_7804008 prefixEnd_7804008 4007207135532808016510027 := by
  unfold tailWord_7804008
  simp only [CollatzResearch.WordTrace]
  refine ⟨142317777755709654650206339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189757037007612872866941785 142317777755709654650206339)
  ·
    refine ⟨213476666633564481975309509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142317777755709654650206339 213476666633564481975309509)
    ·
      refine ⟨40026874993793340370370533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213476666633564481975309509 40026874993793340370370533)
      ·
        refine ⟨7505039061336251319444475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40026874993793340370370533 7505039061336251319444475)
        ·
          refine ⟨11257558592004376979166713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7505039061336251319444475 11257558592004376979166713)
          ·
            refine ⟨8443168944003282734375035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11257558592004376979166713 8443168944003282734375035)
            ·
              refine ⟨12664753416004924101562553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443168944003282734375035 12664753416004924101562553)
              ·
                refine ⟨9498565062003693076171915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12664753416004924101562553 9498565062003693076171915)
                ·
                  refine ⟨14247847593005539614257873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9498565062003693076171915 14247847593005539614257873)
                  ·
                    refine ⟨10685885694754154710693405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14247847593005539614257873 10685885694754154710693405)
                    ·
                      refine ⟨4007207135532808016510027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10685885694754154710693405 4007207135532808016510027)
                      ·
                        rfl

theorem cell23_7804008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7804008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804008 prefixEnd_7804008 := by exact prefixLift 7804008
  have htrace : WordTrace (prefixWord ++ tailWord_7804008) baseStart_7804008 baseEnd_7804008 := by
    simpa [prefixWord, tailWord_7804008, baseEnd_7804008] using wordTrace_append hprefix tailTrace_7804008
  have hstable : (prefixWord ++ tailWord_7804008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804008).length < 2 ^ (prefixWord ++ tailWord_7804008).sum := by decide
  have hdescent : baseEnd_7804008 < baseStart_7804008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804021 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7804021 : Nat := 118140960795 + 7804021 * 2 ^ 59
def prefixEnd_7804021 : Nat := 4983230072969 + 3 ^ 40 * 7804021 * 2
def baseEnd_7804021 : Nat := 4007213810781316465647467

theorem tailTrace_7804021 : CollatzResearch.WordTrace tailWord_7804021 prefixEnd_7804021 4007213810781316465647467 := by
  unfold tailWord_7804021
  simp only [CollatzResearch.WordTrace]
  refine ⟨284636029660372212520635917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189757353106914808347090611 284636029660372212520635917)
  ·
    refine ⟨106738511122639579695238469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284636029660372212520635917 106738511122639579695238469)
    ·
      refine ⟨20013470835494921192857213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106738511122639579695238469 20013470835494921192857213)
      ·
        refine ⟨7505051563310595447321455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20013470835494921192857213 7505051563310595447321455)
        ·
          refine ⟨11257577344965893170982183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7505051563310595447321455 11257577344965893170982183)
          ·
            refine ⟨16886366017448839756473275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11257577344965893170982183 16886366017448839756473275)
            ·
              refine ⟨25329549026173259634709913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16886366017448839756473275 25329549026173259634709913)
              ·
                refine ⟨18997161769629944726032435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25329549026173259634709913 18997161769629944726032435)
                ·
                  refine ⟨28495742654444917089048653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18997161769629944726032435 28495742654444917089048653)
                  ·
                    refine ⟨10685903495416843908393245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28495742654444917089048653 10685903495416843908393245)
                    ·
                      refine ⟨4007213810781316465647467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10685903495416843908393245 4007213810781316465647467)
                      ·
                        rfl

theorem cell23_7804021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7804021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804021 prefixEnd_7804021 := by exact prefixLift 7804021
  have htrace : WordTrace (prefixWord ++ tailWord_7804021) baseStart_7804021 baseEnd_7804021 := by
    simpa [prefixWord, tailWord_7804021, baseEnd_7804021] using wordTrace_append hprefix tailTrace_7804021
  have hstable : (prefixWord ++ tailWord_7804021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804021).length < 2 ^ (prefixWord ++ tailWord_7804021).sum := by decide
  have hdescent : baseEnd_7804021 < baseStart_7804021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804044 : List Nat := [2, 2, 1, 2, 1, 1, 1, 5, 4, 2, 2]
def baseStart_7804044 : Nat := 118140960795 + 7804044 * 2 ^ 59
def prefixEnd_7804044 : Nat := 4983230072969 + 3 ^ 40 * 7804044 * 2
def baseEnd_7804044 : Nat := 4007225620836369875659861

theorem tailTrace_7804044 : CollatzResearch.WordTrace tailWord_7804044 prefixEnd_7804044 4007225620836369875659861 := by
  unfold tailWord_7804044
  simp only [CollatzResearch.WordTrace]
  refine ⟨142318434269644443724361593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189757912359525924965815457 142318434269644443724361593)
  ·
    refine ⟨106738825702233332793271195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142318434269644443724361593 106738825702233332793271195)
    ·
      refine ⟨160108238553349999189906793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106738825702233332793271195 160108238553349999189906793)
      ·
        refine ⟨120081178915012499392430095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160108238553349999189906793 120081178915012499392430095)
        ·
          refine ⟨180121768372518749088645143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120081178915012499392430095 180121768372518749088645143)
          ·
            refine ⟨270182652558778123632967715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180121768372518749088645143 270182652558778123632967715)
            ·
              refine ⟨405273978838167185449451573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270182652558778123632967715 405273978838167185449451573)
              ·
                refine ⟨37994435516078173635886085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405273978838167185449451573 37994435516078173635886085)
                ·
                  refine ⟨7123956659264657556728641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37994435516078173635886085 7123956659264657556728641)
                  ·
                    refine ⟨5342967494448493167546481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7123956659264657556728641 5342967494448493167546481)
                    ·
                      refine ⟨4007225620836369875659861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5342967494448493167546481 4007225620836369875659861)
                      ·
                        rfl

theorem cell23_7804044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_7804044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804044 prefixEnd_7804044 := by exact prefixLift 7804044
  have htrace : WordTrace (prefixWord ++ tailWord_7804044) baseStart_7804044 baseEnd_7804044 := by
    simpa [prefixWord, tailWord_7804044, baseEnd_7804044] using wordTrace_append hprefix tailTrace_7804044
  have hstable : (prefixWord ++ tailWord_7804044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804044).length < 2 ^ (prefixWord ++ tailWord_7804044).sum := by decide
  have hdescent : baseEnd_7804044 < baseStart_7804044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804061 : List Nat := [1, 4, 2, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_7804061 : Nat := 118140960795 + 7804061 * 2 ^ 59
def prefixEnd_7804061 : Nat := 4983230072969 + 3 ^ 40 * 7804061 * 2
def baseEnd_7804061 : Nat := 4007234350007496309147283

theorem tailTrace_7804061 : CollatzResearch.WordTrace tailWord_7804061 prefixEnd_7804061 4007234350007496309147283 := by
  unfold tailWord_7804061
  simp only [CollatzResearch.WordTrace]
  refine ⟨284637488580227299352092037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189758325720151532901394691 284637488580227299352092037)
  ·
    refine ⟨53369529108792618628517257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284637488580227299352092037 53369529108792618628517257)
    ·
      refine ⟨40027146831594463971387943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53369529108792618628517257 40027146831594463971387943)
      ·
        refine ⟨60040720247391695957081915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40027146831594463971387943 60040720247391695957081915)
        ·
          refine ⟨90061080371087543935622873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60040720247391695957081915 90061080371087543935622873)
          ·
            refine ⟨67545810278315657951717155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90061080371087543935622873 67545810278315657951717155)
            ·
              refine ⟨101318715417473486927575733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67545810278315657951717155 101318715417473486927575733)
              ·
                refine ⟨9498629570388139399460225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101318715417473486927575733 9498629570388139399460225)
                ·
                  refine ⟨7123972177791104549595169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9498629570388139399460225 7123972177791104549595169)
                  ·
                    refine ⟨5342979133343328412196377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7123972177791104549595169 5342979133343328412196377)
                    ·
                      refine ⟨4007234350007496309147283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5342979133343328412196377 4007234350007496309147283)
                      ·
                        rfl

theorem cell23_7804061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_7804061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804061 prefixEnd_7804061 := by exact prefixLift 7804061
  have htrace : WordTrace (prefixWord ++ tailWord_7804061) baseStart_7804061 baseEnd_7804061 := by
    simpa [prefixWord, tailWord_7804061, baseEnd_7804061] using wordTrace_append hprefix tailTrace_7804061
  have hstable : (prefixWord ++ tailWord_7804061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804061).length < 2 ^ (prefixWord ++ tailWord_7804061).sum := by decide
  have hdescent : baseEnd_7804061 < baseStart_7804061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804080 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 1, 7]
def baseStart_7804080 : Nat := 118140960795 + 7804080 * 2 ^ 59
def prefixEnd_7804080 : Nat := 4983230072969 + 3 ^ 40 * 7804080 * 2
def baseEnd_7804080 : Nat := 1335748035379977244936565

theorem tailTrace_7804080 : CollatzResearch.WordTrace tailWord_7804080 prefixEnd_7804080 1335748035379977244936565 := by
  unfold tailWord_7804080
  simp only [CollatzResearch.WordTrace]
  refine ⟨142319090783579232798516847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189758787711438977064689129 142319090783579232798516847)
  ·
    refine ⟨213478636175368849197775271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142319090783579232798516847 213478636175368849197775271)
    ·
      refine ⟨320217954263053273796662907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213478636175368849197775271 320217954263053273796662907)
      ·
        refine ⟨480326931394579910694994361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320217954263053273796662907 480326931394579910694994361)
        ·
          refine ⟨360245198545934933021245771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480326931394579910694994361 360245198545934933021245771)
          ·
            refine ⟨540367797818902399531868657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360245198545934933021245771 540367797818902399531868657)
            ·
              refine ⟨405275848364176799648901493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540367797818902399531868657 405275848364176799648901493)
              ·
                refine ⟨37994610784141574967084515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 405275848364176799648901493 37994610784141574967084515)
                ·
                  refine ⟨56991916176212362450626773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37994610784141574967084515 56991916176212362450626773)
                  ·
                    refine ⟨1335748035379977244936565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56991916176212362450626773 1335748035379977244936565)
                    ·
                      rfl

theorem cell23_7804080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_7804080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804080 prefixEnd_7804080 := by exact prefixLift 7804080
  have htrace : WordTrace (prefixWord ++ tailWord_7804080) baseStart_7804080 baseEnd_7804080 := by
    simpa [prefixWord, tailWord_7804080, baseEnd_7804080] using wordTrace_append hprefix tailTrace_7804080
  have hstable : (prefixWord ++ tailWord_7804080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804080).length < 2 ^ (prefixWord ++ tailWord_7804080).sum := by decide
  have hdescent : baseEnd_7804080 < baseStart_7804080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804094 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_7804094 : Nat := 118140960795 + 7804094 * 2 ^ 59
def prefixEnd_7804094 : Nat := 4983230072969 + 3 ^ 40 * 7804094 * 2
def baseEnd_7804094 : Nat := 4007251294869094680034631

theorem tailTrace_7804094 : CollatzResearch.WordTrace tailWord_7804094 prefixEnd_7804094 4007251294869094680034631 := by
  unfold tailWord_7804094
  simp only [CollatzResearch.WordTrace]
  refine ⟨35579836523638468248505417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189759128126071830658695557 35579836523638468248505417)
  ·
    refine ⟨26684877392728851186379063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35579836523638468248505417 26684877392728851186379063)
    ·
      refine ⟨40027316089093276779568595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26684877392728851186379063 40027316089093276779568595)
      ·
        refine ⟨60040974133639915169352893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40027316089093276779568595 60040974133639915169352893)
        ·
          refine ⟨22515365300114968188507335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60040974133639915169352893 22515365300114968188507335)
          ·
            refine ⟨33773047950172452282761003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22515365300114968188507335 33773047950172452282761003)
            ·
              refine ⟨50659571925258678424141505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33773047950172452282761003 50659571925258678424141505)
              ·
                refine ⟨37994678943944008818106129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50659571925258678424141505 37994678943944008818106129)
                ·
                  refine ⟨28496009207958006613579597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37994678943944008818106129 28496009207958006613579597)
                  ·
                    refine ⟨10686003452984252480092349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28496009207958006613579597 10686003452984252480092349)
                    ·
                      refine ⟨4007251294869094680034631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10686003452984252480092349 4007251294869094680034631)
                      ·
                        rfl

theorem cell23_7804094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_7804094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804094 prefixEnd_7804094 := by exact prefixLift 7804094
  have htrace : WordTrace (prefixWord ++ tailWord_7804094) baseStart_7804094 baseEnd_7804094 := by
    simpa [prefixWord, tailWord_7804094, baseEnd_7804094] using wordTrace_append hprefix tailTrace_7804094
  have hstable : (prefixWord ++ tailWord_7804094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804094).length < 2 ^ (prefixWord ++ tailWord_7804094).sum := by decide
  have hdescent : baseEnd_7804094 < baseStart_7804094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804154 : List Nat := [3, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3]
def baseStart_7804154 : Nat := 118140960795 + 7804154 * 2 ^ 59
def prefixEnd_7804154 : Nat := 4983230072969 + 3 ^ 40 * 7804154 * 2
def baseEnd_7804154 : Nat := 4007282103708364445284355

theorem tailTrace_7804154 : CollatzResearch.WordTrace tailWord_7804154 prefixEnd_7804154 4007282103708364445284355 := by
  unfold tailWord_7804154
  simp only [CollatzResearch.WordTrace]
  refine ⟨71160220142222594058806879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189760587045926917490151677 71160220142222594058806879)
  ·
    refine ⟨106740330213333891088210319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71160220142222594058806879 106740330213333891088210319)
    ·
      refine ⟨160110495320000836632315479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106740330213333891088210319 160110495320000836632315479)
      ·
        refine ⟨240165742980001254948473219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160110495320000836632315479 240165742980001254948473219)
        ·
          refine ⟨360248614470001882422709829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240165742980001254948473219 360248614470001882422709829)
          ·
            refine ⟨67546615213125352954258093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360248614470001882422709829 67546615213125352954258093)
            ·
              refine ⟨25329980704922007357846785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67546615213125352954258093 25329980704922007357846785)
              ·
                refine ⟨18997485528691505518385089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25329980704922007357846785 18997485528691505518385089)
                ·
                  refine ⟨14248114146518629138788817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18997485528691505518385089 14248114146518629138788817)
                  ·
                    refine ⟨10686085609888971854091613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14248114146518629138788817 10686085609888971854091613)
                    ·
                      refine ⟨4007282103708364445284355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10686085609888971854091613 4007282103708364445284355)
                      ·
                        rfl

theorem cell23_7804154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_7804154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804154 prefixEnd_7804154 := by exact prefixLift 7804154
  have htrace : WordTrace (prefixWord ++ tailWord_7804154) baseStart_7804154 baseEnd_7804154 := by
    simpa [prefixWord, tailWord_7804154, baseEnd_7804154] using wordTrace_append hprefix tailTrace_7804154
  have hstable : (prefixWord ++ tailWord_7804154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804154).length < 2 ^ (prefixWord ++ tailWord_7804154).sum := by decide
  have hdescent : baseEnd_7804154 < baseStart_7804154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804161 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 3, 4]
def baseStart_7804161 : Nat := 118140960795 + 7804161 * 2 ^ 59
def prefixEnd_7804161 : Nat := 4983230072969 + 3 ^ 40 * 7804161 * 2
def baseEnd_7804161 : Nat := 1335761899357648639298941

theorem tailTrace_7804161 : CollatzResearch.WordTrace tailWord_7804161 prefixEnd_7804161 1335761899357648639298941 := by
  unfold tailWord_7804161
  simp only [CollatzResearch.WordTrace]
  refine ⟨284641135879865016430732337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189760757253243344287154891 284641135879865016430732337)
  ·
    refine ⟨213480851909898762323049253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284641135879865016430732337 213480851909898762323049253)
    ·
      refine ⟨40027659733106017935571735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213480851909898762323049253 40027659733106017935571735)
      ·
        refine ⟨60041489599659026903357603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40027659733106017935571735 60041489599659026903357603)
        ·
          refine ⟨90062234399488540355036405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60041489599659026903357603 90062234399488540355036405)
          ·
            refine ⟨8443334474952050658284663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90062234399488540355036405 8443334474952050658284663)
            ·
              refine ⟨12665001712428075987426995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443334474952050658284663 12665001712428075987426995)
              ·
                refine ⟨18997502568642113981140493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12665001712428075987426995 18997502568642113981140493)
                ·
                  refine ⟨7124063463240792742927685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18997502568642113981140493 7124063463240792742927685)
                  ·
                    refine ⟨1335761899357648639298941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7124063463240792742927685 1335761899357648639298941)
                    ·
                      rfl

theorem cell23_7804161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_7804161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804161 prefixEnd_7804161 := by exact prefixLift 7804161
  have htrace : WordTrace (prefixWord ++ tailWord_7804161) baseStart_7804161 baseEnd_7804161 := by
    simpa [prefixWord, tailWord_7804161, baseEnd_7804161] using wordTrace_append hprefix tailTrace_7804161
  have hstable : (prefixWord ++ tailWord_7804161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804161).length < 2 ^ (prefixWord ++ tailWord_7804161).sum := by decide
  have hdescent : baseEnd_7804161 < baseStart_7804161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804174 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_7804174 : Nat := 118140960795 + 7804174 * 2 ^ 59
def prefixEnd_7804174 : Nat := 4983230072969 + 3 ^ 40 * 7804174 * 2
def baseEnd_7804174 : Nat := 445254708146828263003807

theorem tailTrace_7804174 : CollatzResearch.WordTrace tailWord_7804174 prefixEnd_7804174 445254708146828263003807 := by
  unfold tailWord_7804174
  simp only [CollatzResearch.WordTrace]
  refine ⟨35580201253602239956369447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189761073352545279767303717 35580201253602239956369447)
  ·
    refine ⟨53370301880403359934554171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35580201253602239956369447 53370301880403359934554171)
    ·
      refine ⟨80055452820605039901831257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53370301880403359934554171 80055452820605039901831257)
      ·
        refine ⟨60041589615453779926373443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80055452820605039901831257 60041589615453779926373443)
        ·
          refine ⟨90062384423180669889560165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60041589615453779926373443 90062384423180669889560165)
          ·
            refine ⟨16886697079346375604292531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90062384423180669889560165 16886697079346375604292531)
            ·
              refine ⟨25330045619019563406438797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16886697079346375604292531 25330045619019563406438797)
              ·
                refine ⟨9498767107132336277414549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25330045619019563406438797 9498767107132336277414549)
                ·
                  refine ⟨445254708146828263003807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9498767107132336277414549 445254708146828263003807)
                  ·
                    rfl

theorem cell23_7804174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_7804174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804174 prefixEnd_7804174 := by exact prefixLift 7804174
  have htrace : WordTrace (prefixWord ++ tailWord_7804174) baseStart_7804174 baseEnd_7804174 := by
    simpa [prefixWord, tailWord_7804174, baseEnd_7804174] using wordTrace_append hprefix tailTrace_7804174
  have hstable : (prefixWord ++ tailWord_7804174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804174).length < 2 ^ (prefixWord ++ tailWord_7804174).sum := by decide
  have hdescent : baseEnd_7804174 < baseStart_7804174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804211 : List Nat := [1, 1, 1, 2, 5, 2, 2, 2, 2, 3, 2]
def baseStart_7804211 : Nat := 118140960795 + 7804211 * 2 ^ 59
def prefixEnd_7804211 : Nat := 4983230072969 + 3 ^ 40 * 7804211 * 2
def baseEnd_7804211 : Nat := 4007311372105670722271593

theorem tailTrace_7804211 : CollatzResearch.WordTrace tailWord_7804211 prefixEnd_7804211 4007311372105670722271593 := by
  unfold tailWord_7804211
  simp only [CollatzResearch.WordTrace]
  refine ⟨284642959529683874970052487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189761973019789249980034991 284642959529683874970052487)
  ·
    refine ⟨426964439294525812455078731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284642959529683874970052487 426964439294525812455078731)
    ·
      refine ⟨640446658941788718682618097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426964439294525812455078731 640446658941788718682618097)
      ·
        refine ⟨480334994206341539011963573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640446658941788718682618097 480334994206341539011963573)
        ·
          refine ⟨45031405706844519282371585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 480334994206341539011963573 45031405706844519282371585)
          ·
            refine ⟨33773554280133389461778689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45031405706844519282371585 33773554280133389461778689)
            ·
              refine ⟨25330165710100042096334017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33773554280133389461778689 25330165710100042096334017)
              ·
                refine ⟨18997624282575031572250513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25330165710100042096334017 18997624282575031572250513)
                ·
                  refine ⟨14248218211931273679187885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18997624282575031572250513 14248218211931273679187885)
                  ·
                    refine ⟨5343081829474227629695457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14248218211931273679187885 5343081829474227629695457)
                    ·
                      refine ⟨4007311372105670722271593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5343081829474227629695457 4007311372105670722271593)
                      ·
                        rfl

theorem cell23_7804211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 3, 2].length) (baseStart_7804211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804211 prefixEnd_7804211 := by exact prefixLift 7804211
  have htrace : WordTrace (prefixWord ++ tailWord_7804211) baseStart_7804211 baseEnd_7804211 := by
    simpa [prefixWord, tailWord_7804211, baseEnd_7804211] using wordTrace_append hprefix tailTrace_7804211
  have hstable : (prefixWord ++ tailWord_7804211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804211).length < 2 ^ (prefixWord ++ tailWord_7804211).sum := by decide
  have hdescent : baseEnd_7804211 < baseStart_7804211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804218 : List Nat := [3, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3]
def baseStart_7804218 : Nat := 118140960795 + 7804218 * 2 ^ 59
def prefixEnd_7804218 : Nat := 4983230072969 + 3 ^ 40 * 7804218 * 2
def baseEnd_7804218 : Nat := 4007314966470252194884061

theorem tailTrace_7804218 : CollatzResearch.WordTrace tailWord_7804218 prefixEnd_7804218 4007314966470252194884061 := by
  unfold tailWord_7804218
  simp only [CollatzResearch.WordTrace]
  refine ⟨71160803710164628791389327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189762143227105676777038205 71160803710164628791389327)
  ·
    refine ⟨106741205565246943187083991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71160803710164628791389327 106741205565246943187083991)
    ·
      refine ⟨160111808347870414780625987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106741205565246943187083991 160111808347870414780625987)
      ·
        refine ⟨240167712521805622170938981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160111808347870414780625987 240167712521805622170938981)
        ·
          refine ⟨45031446097838554157051059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240167712521805622170938981 45031446097838554157051059)
          ·
            refine ⟨67547169146757831235576589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45031446097838554157051059 67547169146757831235576589)
            ·
              refine ⟨25330188430034186713341221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67547169146757831235576589 25330188430034186713341221)
              ·
                refine ⟨4749410330631410008751479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25330188430034186713341221 4749410330631410008751479)
                ·
                  refine ⟨7124115495947115013127219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749410330631410008751479 7124115495947115013127219)
                  ·
                    refine ⟨10686173243920672519690829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7124115495947115013127219 10686173243920672519690829)
                    ·
                      refine ⟨4007314966470252194884061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10686173243920672519690829 4007314966470252194884061)
                      ·
                        rfl

theorem cell23_7804218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 1, 1, 3].length) (baseStart_7804218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804218 prefixEnd_7804218 := by exact prefixLift 7804218
  have htrace : WordTrace (prefixWord ++ tailWord_7804218) baseStart_7804218 baseEnd_7804218 := by
    simpa [prefixWord, tailWord_7804218, baseEnd_7804218] using wordTrace_append hprefix tailTrace_7804218
  have hstable : (prefixWord ++ tailWord_7804218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804218).length < 2 ^ (prefixWord ++ tailWord_7804218).sum := by decide
  have hdescent : baseEnd_7804218 < baseStart_7804218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804227 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 5]
def baseStart_7804227 : Nat := 118140960795 + 7804227 * 2 ^ 59
def prefixEnd_7804227 : Nat := 4983230072969 + 3 ^ 40 * 7804227 * 2
def baseEnd_7804227 : Nat := 4007319587796142659671519

theorem tailTrace_7804227 : CollatzResearch.WordTrace tailWord_7804227 prefixEnd_7804227 4007319587796142659671519 := by
  unfold tailWord_7804227
  simp only [CollatzResearch.WordTrace]
  refine ⟨284643543097625909702634935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189762362065083939801756623 284643543097625909702634935)
  ·
    refine ⟨426965314646438864553952403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284643543097625909702634935 426965314646438864553952403)
    ·
      refine ⟨640447971969658296830928605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426965314646438864553952403 640447971969658296830928605)
      ·
        refine ⟨240167989488621861311598227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640447971969658296830928605 240167989488621861311598227)
        ·
          refine ⟨360251984232932791967397341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240167989488621861311598227 360251984232932791967397341)
          ·
            refine ⟨135094494087349796987774003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360251984232932791967397341 135094494087349796987774003)
            ·
              refine ⟨202641741131024695481661005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135094494087349796987774003 202641741131024695481661005)
              ·
                refine ⟨75990652924134260805622877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202641741131024695481661005 75990652924134260805622877)
                ·
                  refine ⟨28496494846550347802108579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75990652924134260805622877 28496494846550347802108579)
                  ·
                    refine ⟨42744742269825521703162869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28496494846550347802108579 42744742269825521703162869)
                    ·
                      refine ⟨4007319587796142659671519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42744742269825521703162869 4007319587796142659671519)
                      ·
                        rfl

theorem cell23_7804227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_7804227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804227 prefixEnd_7804227 := by exact prefixLift 7804227
  have htrace : WordTrace (prefixWord ++ tailWord_7804227) baseStart_7804227 baseEnd_7804227 := by
    simpa [prefixWord, tailWord_7804227, baseEnd_7804227] using wordTrace_append hprefix tailTrace_7804227
  have hstable : (prefixWord ++ tailWord_7804227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804227).length < 2 ^ (prefixWord ++ tailWord_7804227).sum := by decide
  have hdescent : baseEnd_7804227 < baseStart_7804227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804258 : List Nat := [3, 3, 2, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_7804258 : Nat := 118140960795 + 7804258 * 2 ^ 59
def prefixEnd_7804258 : Nat := 4983230072969 + 3 ^ 40 * 7804258 * 2
def baseEnd_7804258 : Nat := 4007335505696432038383877

theorem tailTrace_7804258 : CollatzResearch.WordTrace tailWord_7804258 prefixEnd_7804258 4007335505696432038383877 := by
  unfold tailWord_7804258
  simp only [CollatzResearch.WordTrace]
  refine ⟨71161168440128400499253357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189763115840342401331342285 71161168440128400499253357)
  ·
    refine ⟨26685438165048150187220009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71161168440128400499253357 26685438165048150187220009)
    ·
      refine ⟨20014078623786112640415007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26685438165048150187220009 20014078623786112640415007)
      ·
        refine ⟨30021117935679168960622511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20014078623786112640415007 30021117935679168960622511)
        ·
          refine ⟨45031676903518753440933767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30021117935679168960622511 45031676903518753440933767)
          ·
            refine ⟨67547515355278130161400651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45031676903518753440933767 67547515355278130161400651)
            ·
              refine ⟨101321273032917195242100977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67547515355278130161400651 101321273032917195242100977)
              ·
                refine ⟨75990954774687896431575733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101321273032917195242100977 75990954774687896431575733)
                ·
                  refine ⟨7124152010126990290460225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75990954774687896431575733 7124152010126990290460225)
                  ·
                    refine ⟨5343114007595242717845169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7124152010126990290460225 5343114007595242717845169)
                    ·
                      refine ⟨4007335505696432038383877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5343114007595242717845169 4007335505696432038383877)
                      ·
                        rfl

theorem cell23_7804258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_7804258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804258 prefixEnd_7804258 := by exact prefixLift 7804258
  have htrace : WordTrace (prefixWord ++ tailWord_7804258) baseStart_7804258 baseEnd_7804258 := by
    simpa [prefixWord, tailWord_7804258, baseEnd_7804258] using wordTrace_append hprefix tailTrace_7804258
  have hstable : (prefixWord ++ tailWord_7804258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804258).length < 2 ^ (prefixWord ++ tailWord_7804258).sum := by decide
  have hdescent : baseEnd_7804258 < baseStart_7804258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804261 : List Nat := [1, 3, 1, 3, 1, 2, 3, 3, 1, 2, 3]
def baseStart_7804261 : Nat := 118140960795 + 7804261 * 2 ^ 59
def prefixEnd_7804261 : Nat := 4983230072969 + 3 ^ 40 * 7804261 * 2
def baseEnd_7804261 : Nat := 4007337046138395526646363

theorem tailTrace_7804261 : CollatzResearch.WordTrace tailWord_7804261 prefixEnd_7804261 4007337046138395526646363 := by
  unfold tailWord_7804261
  simp only [CollatzResearch.WordTrace]
  refine ⟨284644783179502733509372637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189763188786335155672915091 284644783179502733509372637)
  ·
    refine ⟨106741793692313525066014739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284644783179502733509372637 106741793692313525066014739)
    ·
      refine ⟨160112690538470287599022109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106741793692313525066014739 160112690538470287599022109)
      ·
        refine ⟨60042258951926357849633291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160112690538470287599022109 60042258951926357849633291)
        ·
          refine ⟨90063388427889536774449937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60042258951926357849633291 90063388427889536774449937)
          ·
            refine ⟨67547541320917152580837453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90063388427889536774449937 67547541320917152580837453)
            ·
              refine ⟨25330327995343932217814045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67547541320917152580837453 25330327995343932217814045)
              ·
                refine ⟨9498872998253974581680267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25330327995343932217814045 9498872998253974581680267)
                ·
                  refine ⟨14248309497380961872520401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9498872998253974581680267 14248309497380961872520401)
                  ·
                    refine ⟨10686232123035721404390301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14248309497380961872520401 10686232123035721404390301)
                    ·
                      refine ⟨4007337046138395526646363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10686232123035721404390301 4007337046138395526646363)
                      ·
                        rfl

theorem cell23_7804261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_7804261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804261 prefixEnd_7804261 := by exact prefixLift 7804261
  have htrace : WordTrace (prefixWord ++ tailWord_7804261) baseStart_7804261 baseEnd_7804261 := by
    simpa [prefixWord, tailWord_7804261, baseEnd_7804261] using wordTrace_append hprefix tailTrace_7804261
  have hstable : (prefixWord ++ tailWord_7804261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804261).length < 2 ^ (prefixWord ++ tailWord_7804261).sum := by decide
  have hdescent : baseEnd_7804261 < baseStart_7804261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804264 : List Nat := [2, 1, 4, 2, 3, 1, 10]
def baseStart_7804264 : Nat := 118140960795 + 7804264 * 2 ^ 59
def prefixEnd_7804264 : Nat := 4983230072969 + 3 ^ 40 * 7804264 * 2
def baseEnd_7804264 : Nat := 49473315883708135986529

theorem tailTrace_7804264 : CollatzResearch.WordTrace tailWord_7804264 prefixEnd_7804264 49473315883708135986529 := by
  unfold tailWord_7804264
  simp only [CollatzResearch.WordTrace]
  refine ⟨142322446299245932510865923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189763261732327910014487897 142322446299245932510865923)
  ·
    refine ⟨213483669448868898766298885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142322446299245932510865923 213483669448868898766298885)
    ·
      refine ⟨40028188021662918518681041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213483669448868898766298885 40028188021662918518681041)
      ·
        refine ⟨30021141016247188889010781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40028188021662918518681041 30021141016247188889010781)
        ·
          refine ⟨11257927881092695833379043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30021141016247188889010781 11257927881092695833379043)
          ·
            refine ⟨16886891821639043750068565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11257927881092695833379043 16886891821639043750068565)
            ·
              refine ⟨49473315883708135986529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16886891821639043750068565 49473315883708135986529)
              ·
                rfl

theorem cell23_7804264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 10].length) (baseStart_7804264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804264 prefixEnd_7804264 := by exact prefixLift 7804264
  have htrace : WordTrace (prefixWord ++ tailWord_7804264) baseStart_7804264 baseEnd_7804264 := by
    simpa [prefixWord, tailWord_7804264, baseEnd_7804264] using wordTrace_append hprefix tailTrace_7804264
  have hstable : (prefixWord ++ tailWord_7804264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804264).length < 2 ^ (prefixWord ++ tailWord_7804264).sum := by decide
  have hdescent : baseEnd_7804264 < baseStart_7804264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804268 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 2, 4]
def baseStart_7804268 : Nat := 118140960795 + 7804268 * 2 ^ 59
def prefixEnd_7804268 : Nat := 4983230072969 + 3 ^ 40 * 7804268 * 2
def baseEnd_7804268 : Nat := 1335780213500992333086277

theorem tailTrace_7804268 : CollatzResearch.WordTrace tailWord_7804268 prefixEnd_7804268 1335780213500992333086277 := by
  unfold tailWord_7804268
  simp only [CollatzResearch.WordTrace]
  refine ⟨142322519245238686852438729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189763358993651582469918305 142322519245238686852438729)
  ·
    refine ⟨106741889433929015139329047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142322519245238686852438729 106741889433929015139329047)
    ·
      refine ⟨160112834150893522708993571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106741889433929015139329047 160112834150893522708993571)
      ·
        refine ⟨240169251226340284063490357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160112834150893522708993571 240169251226340284063490357)
        ·
          refine ⟨22515867302469401630952221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240169251226340284063490357 22515867302469401630952221)
          ·
            refine ⟨8443450238426025611607083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22515867302469401630952221 8443450238426025611607083)
            ·
              refine ⟨12665175357639038417410625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443450238426025611607083 12665175357639038417410625)
              ·
                refine ⟨9498881518229278813057969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12665175357639038417410625 9498881518229278813057969)
                ·
                  refine ⟨7124161138671959109793477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9498881518229278813057969 7124161138671959109793477)
                  ·
                    refine ⟨1335780213500992333086277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7124161138671959109793477 1335780213500992333086277)
                    ·
                      rfl

theorem cell23_7804268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 4].length) (baseStart_7804268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804268 prefixEnd_7804268 := by exact prefixLift 7804268
  have htrace : WordTrace (prefixWord ++ tailWord_7804268) baseStart_7804268 baseEnd_7804268 := by
    simpa [prefixWord, tailWord_7804268, baseEnd_7804268] using wordTrace_append hprefix tailTrace_7804268
  have hstable : (prefixWord ++ tailWord_7804268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804268).length < 2 ^ (prefixWord ++ tailWord_7804268).sum := by decide
  have hdescent : baseEnd_7804268 < baseStart_7804268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804287 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 5]
def baseStart_7804287 : Nat := 118140960795 + 7804287 * 2 ^ 59
def prefixEnd_7804287 : Nat := 4983230072969 + 3 ^ 40 * 7804287 * 2
def baseEnd_7804287 : Nat := 4007350396635412424921243

theorem tailTrace_7804287 : CollatzResearch.WordTrace tailWord_7804287 prefixEnd_7804287 4007350396635412424921243 := by
  unfold tailWord_7804287
  simp only [CollatzResearch.WordTrace]
  refine ⟨284645731477408539949819115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189763820984939026633212743 284645731477408539949819115)
  ·
    refine ⟨426968597216112809924728673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284645731477408539949819115 426968597216112809924728673)
    ·
      refine ⟨320226447912084607443546505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426968597216112809924728673 320226447912084607443546505)
      ·
        refine ⟨240169835934063455582659879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320226447912084607443546505 240169835934063455582659879)
        ·
          refine ⟨360254753901095183373989819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240169835934063455582659879 360254753901095183373989819)
          ·
            refine ⟨540382130851642775060984729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360254753901095183373989819 540382130851642775060984729)
            ·
              refine ⟨405286598138732081295738547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540382130851642775060984729 405286598138732081295738547)
              ·
                refine ⟨607929897208098121943607821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405286598138732081295738547 607929897208098121943607821)
                ·
                  refine ⟨227973711453036795728852933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 607929897208098121943607821 227973711453036795728852933)
                  ·
                    refine ⟨42745070897444399199159925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 227973711453036795728852933 42745070897444399199159925)
                    ·
                      refine ⟨4007350396635412424921243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42745070897444399199159925 4007350396635412424921243)
                      ·
                        rfl

theorem cell23_7804287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_7804287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804287 prefixEnd_7804287 := by exact prefixLift 7804287
  have htrace : WordTrace (prefixWord ++ tailWord_7804287) baseStart_7804287 baseEnd_7804287 := by
    simpa [prefixWord, tailWord_7804287, baseEnd_7804287] using wordTrace_append hprefix tailTrace_7804287
  have hstable : (prefixWord ++ tailWord_7804287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804287).length < 2 ^ (prefixWord ++ tailWord_7804287).sum := by decide
  have hdescent : baseEnd_7804287 < baseStart_7804287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804291 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 3]
def baseStart_7804291 : Nat := 118140960795 + 7804291 * 2 ^ 59
def prefixEnd_7804291 : Nat := 4983230072969 + 3 ^ 40 * 7804291 * 2
def baseEnd_7804291 : Nat := 4007352450558030409271225

theorem tailTrace_7804291 : CollatzResearch.WordTrace tailWord_7804291 prefixEnd_7804291 4007352450558030409271225 := by
  unfold tailWord_7804291
  simp only [CollatzResearch.WordTrace]
  refine ⟨284645877369394048632964727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189763918246262699088643151 284645877369394048632964727)
  ·
    refine ⟨426968816054091072949447091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284645877369394048632964727 426968816054091072949447091)
    ·
      refine ⟨640453224081136609424170637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426968816054091072949447091 640453224081136609424170637)
      ·
        refine ⟨240169959030426228534063989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640453224081136609424170637 240169959030426228534063989)
        ·
          refine ⟨22515933659102458925068499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240169959030426228534063989 22515933659102458925068499)
          ·
            refine ⟨33773900488653688387602749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22515933659102458925068499 33773900488653688387602749)
            ·
              refine ⟨12665212683245133145351031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33773900488653688387602749 12665212683245133145351031)
              ·
                refine ⟨18997819024867699718026547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12665212683245133145351031 18997819024867699718026547)
                ·
                  refine ⟨28496728537301549577039821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18997819024867699718026547 28496728537301549577039821)
                  ·
                    refine ⟨10686273201488081091389933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28496728537301549577039821 10686273201488081091389933)
                    ·
                      refine ⟨4007352450558030409271225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10686273201488081091389933 4007352450558030409271225)
                      ·
                        rfl

theorem cell23_7804291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_7804291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804291 prefixEnd_7804291 := by exact prefixLift 7804291
  have htrace : WordTrace (prefixWord ++ tailWord_7804291) baseStart_7804291 baseEnd_7804291 := by
    simpa [prefixWord, tailWord_7804291, baseEnd_7804291] using wordTrace_append hprefix tailTrace_7804291
  have hstable : (prefixWord ++ tailWord_7804291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804291).length < 2 ^ (prefixWord ++ tailWord_7804291).sum := by decide
  have hdescent : baseEnd_7804291 < baseStart_7804291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804308 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 4, 1, 3]
def baseStart_7804308 : Nat := 118140960795 + 7804308 * 2 ^ 59
def prefixEnd_7804308 : Nat := 4983230072969 + 3 ^ 40 * 7804308 * 2
def baseEnd_7804308 : Nat := 4007361179729156842758647

theorem tailTrace_7804308 : CollatzResearch.WordTrace tailWord_7804308 prefixEnd_7804308 4007361179729156842758647 := by
  unfold tailWord_7804308
  simp only [CollatzResearch.WordTrace]
  refine ⟨142323248705166230268166789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189764331606888307024222385 142323248705166230268166789)
  ·
    refine ⟨26685609132218668175281273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142323248705166230268166789 26685609132218668175281273)
    ·
      refine ⟨20014206849164001131460955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26685609132218668175281273 20014206849164001131460955)
      ·
        refine ⟨30021310273746001697191433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20014206849164001131460955 30021310273746001697191433)
        ·
          refine ⟨22515982705309501272893575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30021310273746001697191433 22515982705309501272893575)
          ·
            refine ⟨33773974057964251909340363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22515982705309501272893575 33773974057964251909340363)
            ·
              refine ⟨50660961086946377864010545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33773974057964251909340363 50660961086946377864010545)
              ·
                refine ⟨37995720815209783398007909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50660961086946377864010545 37995720815209783398007909)
                ·
                  refine ⟨7124197652851834387126483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37995720815209783398007909 7124197652851834387126483)
                  ·
                    refine ⟨10686296479277751580689725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7124197652851834387126483 10686296479277751580689725)
                    ·
                      refine ⟨4007361179729156842758647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10686296479277751580689725 4007361179729156842758647)
                      ·
                        rfl

theorem cell23_7804308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_7804308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804308 prefixEnd_7804308 := by exact prefixLift 7804308
  have htrace : WordTrace (prefixWord ++ tailWord_7804308) baseStart_7804308 baseEnd_7804308 := by
    simpa [prefixWord, tailWord_7804308, baseEnd_7804308] using wordTrace_append hprefix tailTrace_7804308
  have hstable : (prefixWord ++ tailWord_7804308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804308).length < 2 ^ (prefixWord ++ tailWord_7804308).sum := by decide
  have hdescent : baseEnd_7804308 < baseStart_7804308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804344 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_7804344 : Nat := 118140960795 + 7804344 * 2 ^ 59
def prefixEnd_7804344 : Nat := 4983230072969 + 3 ^ 40 * 7804344 * 2
def baseEnd_7804344 : Nat := 4007379665032718701908481

theorem tailTrace_7804344 : CollatzResearch.WordTrace tailWord_7804344 prefixEnd_7804344 4007379665032718701908481 := by
  unfold tailWord_7804344
  simp only [CollatzResearch.WordTrace]
  refine ⟨142323905219101019342322043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189765206958801359123096057 142323905219101019342322043)
  ·
    refine ⟨213485857828651529013483065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142323905219101019342322043 213485857828651529013483065)
    ·
      refine ⟨160114393371488646760112299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213485857828651529013483065 160114393371488646760112299)
      ·
        refine ⟨240171590057232970140168449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160114393371488646760112299 240171590057232970140168449)
        ·
          refine ⟨180128692542924727605126337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240171590057232970140168449 180128692542924727605126337)
          ·
            refine ⟨135096519407193545703844753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180128692542924727605126337 135096519407193545703844753)
            ·
              refine ⟨101322389555395159277883565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135096519407193545703844753 101322389555395159277883565)
              ·
                refine ⟨37995896083273184729206337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101322389555395159277883565 37995896083273184729206337)
                ·
                  refine ⟨28496922062454888546904753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37995896083273184729206337 28496922062454888546904753)
                  ·
                    refine ⟨21372691546841166410178565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28496922062454888546904753 21372691546841166410178565)
                    ·
                      refine ⟨4007379665032718701908481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21372691546841166410178565 4007379665032718701908481)
                      ·
                        rfl

theorem cell23_7804344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_7804344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804344 prefixEnd_7804344 := by exact prefixLift 7804344
  have htrace : WordTrace (prefixWord ++ tailWord_7804344) baseStart_7804344 baseEnd_7804344 := by
    simpa [prefixWord, tailWord_7804344, baseEnd_7804344] using wordTrace_append hprefix tailTrace_7804344
  have hstable : (prefixWord ++ tailWord_7804344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804344).length < 2 ^ (prefixWord ++ tailWord_7804344).sum := by decide
  have hdescent : baseEnd_7804344 < baseStart_7804344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804384 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 4, 5]
def baseStart_7804384 : Nat := 118140960795 + 7804384 * 2 ^ 59
def prefixEnd_7804384 : Nat := 4983230072969 + 3 ^ 40 * 7804384 * 2
def baseEnd_7804384 : Nat := 1335800068086299515136099

theorem tailTrace_7804384 : CollatzResearch.WordTrace tailWord_7804384 prefixEnd_7804384 1335800068086299515136099 := by
  unfold tailWord_7804384
  simp only [CollatzResearch.WordTrace]
  refine ⟨142324634679028562758050103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189766179572038083677400137 142324634679028562758050103)
  ·
    refine ⟨213486952018542844137075155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142324634679028562758050103 213486952018542844137075155)
    ·
      refine ⟨320230428027814266205612733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213486952018542844137075155 320230428027814266205612733)
      ·
        refine ⟨120086410510430349827104775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320230428027814266205612733 120086410510430349827104775)
        ·
          refine ⟨180129615765645524740657163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120086410510430349827104775 180129615765645524740657163)
          ·
            refine ⟨270194423648468287110985745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180129615765645524740657163 270194423648468287110985745)
            ·
              refine ⟨202645817736351215333239309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270194423648468287110985745 202645817736351215333239309)
              ·
                refine ⟨75992181651131705749964741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 202645817736351215333239309 75992181651131705749964741)
                ·
                  refine ⟨14248534059587194828118389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75992181651131705749964741 14248534059587194828118389)
                  ·
                    refine ⟨1335800068086299515136099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14248534059587194828118389 1335800068086299515136099)
                    ·
                      rfl

theorem cell23_7804384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_7804384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804384 prefixEnd_7804384 := by exact prefixLift 7804384
  have htrace : WordTrace (prefixWord ++ tailWord_7804384) baseStart_7804384 baseEnd_7804384 := by
    simpa [prefixWord, tailWord_7804384, baseEnd_7804384] using wordTrace_append hprefix tailTrace_7804384
  have hstable : (prefixWord ++ tailWord_7804384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804384).length < 2 ^ (prefixWord ++ tailWord_7804384).sum := by decide
  have hdescent : baseEnd_7804384 < baseStart_7804384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804418 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_7804418 : Nat := 118140960795 + 7804418 * 2 ^ 59
def prefixEnd_7804418 : Nat := 4983230072969 + 3 ^ 40 * 7804418 * 2
def baseEnd_7804418 : Nat := 1335805887533717137461047

theorem tailTrace_7804418 : CollatzResearch.WordTrace tailWord_7804418 prefixEnd_7804418 1335805887533717137461047 := by
  unfold tailWord_7804418
  simp only [CollatzResearch.WordTrace]
  refine ⟨71162627359983487330709477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189767006293289299548558605 71162627359983487330709477)
  ·
    refine ⟨13342992629996903874508027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71162627359983487330709477 13342992629996903874508027)
    ·
      refine ⟨20014488944995355811762041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13342992629996903874508027 20014488944995355811762041)
      ·
        refine ⟨15010866708746516858821531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20014488944995355811762041 15010866708746516858821531)
        ·
          refine ⟨22516300063119775288232297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15010866708746516858821531 22516300063119775288232297)
          ·
            refine ⟨16887225047339831466174223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22516300063119775288232297 16887225047339831466174223)
            ·
              refine ⟨25330837571009747199261335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16887225047339831466174223 25330837571009747199261335)
              ·
                refine ⟨37996256356514620798892003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25330837571009747199261335 37996256356514620798892003)
                ·
                  refine ⟨56994384534771931198338005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37996256356514620798892003 56994384534771931198338005)
                  ·
                    refine ⟨1335805887533717137461047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56994384534771931198338005 1335805887533717137461047)
                    ·
                      rfl

theorem cell23_7804418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_7804418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804418 prefixEnd_7804418 := by exact prefixLift 7804418
  have htrace : WordTrace (prefixWord ++ tailWord_7804418) baseStart_7804418 baseEnd_7804418 := by
    simpa [prefixWord, tailWord_7804418, baseEnd_7804418] using wordTrace_append hprefix tailTrace_7804418
  have hstable : (prefixWord ++ tailWord_7804418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804418).length < 2 ^ (prefixWord ++ tailWord_7804418).sum := by decide
  have hdescent : baseEnd_7804418 < baseStart_7804418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804421 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 3, 6, 2]
def baseStart_7804421 : Nat := 118140960795 + 7804421 * 2 ^ 59
def prefixEnd_7804421 : Nat := 4983230072969 + 3 ^ 40 * 7804421 * 2
def baseEnd_7804421 : Nat := 4007419203043114900645627

theorem tailTrace_7804421 : CollatzResearch.WordTrace tailWord_7804421 prefixEnd_7804421 4007419203043114900645627 := by
  unfold tailWord_7804421
  simp only [CollatzResearch.WordTrace]
  refine ⟨284650618858923080835197117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189767079239282053890131411 284650618858923080835197117)
  ·
    refine ⟨106743982072096155313198919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284650618858923080835197117 106743982072096155313198919)
    ·
      refine ⟨160115973108144232969798379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106743982072096155313198919 160115973108144232969798379)
      ·
        refine ⟨240173959662216349454697569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160115973108144232969798379 240173959662216349454697569)
        ·
          refine ⟨180130469746662262091023177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240173959662216349454697569 180130469746662262091023177)
          ·
            refine ⟨135097852309996696568267383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180130469746662262091023177 135097852309996696568267383)
            ·
              refine ⟨202646778464995044852401075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135097852309996696568267383 202646778464995044852401075)
              ·
                refine ⟨303970167697492567278601613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202646778464995044852401075 303970167697492567278601613)
                ·
                  refine ⟨113988812886559712729475605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303970167697492567278601613 113988812886559712729475605)
                  ·
                    refine ⟨5343225604057486534194169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113988812886559712729475605 5343225604057486534194169)
                    ·
                      refine ⟨4007419203043114900645627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5343225604057486534194169 4007419203043114900645627)
                      ·
                        rfl

theorem cell23_7804421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_7804421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804421 prefixEnd_7804421 := by exact prefixLift 7804421
  have htrace : WordTrace (prefixWord ++ tailWord_7804421) baseStart_7804421 baseEnd_7804421 := by
    simpa [prefixWord, tailWord_7804421, baseEnd_7804421] using wordTrace_append hprefix tailTrace_7804421
  have hstable : (prefixWord ++ tailWord_7804421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804421).length < 2 ^ (prefixWord ++ tailWord_7804421).sum := by decide
  have hdescent : baseEnd_7804421 < baseStart_7804421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804448 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 3, 4]
def baseStart_7804448 : Nat := 118140960795 + 7804448 * 2 ^ 59
def prefixEnd_7804448 : Nat := 4983230072969 + 3 ^ 40 * 7804448 * 2
def baseEnd_7804448 : Nat := 1335811022340262098336001

theorem tailTrace_7804448 : CollatzResearch.WordTrace tailWord_7804448 prefixEnd_7804448 1335811022340262098336001 := by
  unfold tailWord_7804448
  simp only [CollatzResearch.WordTrace]
  refine ⟨142325801814912632223214999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189767735753216842964286665 142325801814912632223214999)
  ·
    refine ⟨213488702722368948334822499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142325801814912632223214999 213488702722368948334822499)
    ·
      refine ⟨320233054083553422502233749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213488702722368948334822499 320233054083553422502233749)
      ·
        refine ⟨15010924410166566679792207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 320233054083553422502233749 15010924410166566679792207)
        ·
          refine ⟨22516386615249850019688311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15010924410166566679792207 22516386615249850019688311)
          ·
            refine ⟨33774579922874775029532467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22516386615249850019688311 33774579922874775029532467)
            ·
              refine ⟨50661869884312162544298701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33774579922874775029532467 50661869884312162544298701)
              ·
                refine ⟨18998201206617060954112013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50661869884312162544298701 18998201206617060954112013)
                ·
                  refine ⟨7124325452481397857792005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18998201206617060954112013 7124325452481397857792005)
                  ·
                    refine ⟨1335811022340262098336001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7124325452481397857792005 1335811022340262098336001)
                    ·
                      rfl

theorem cell23_7804448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3, 4].length) (baseStart_7804448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804448 prefixEnd_7804448 := by exact prefixLift 7804448
  have htrace : WordTrace (prefixWord ++ tailWord_7804448) baseStart_7804448 baseEnd_7804448 := by
    simpa [prefixWord, tailWord_7804448, baseEnd_7804448] using wordTrace_append hprefix tailTrace_7804448
  have hstable : (prefixWord ++ tailWord_7804448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804448).length < 2 ^ (prefixWord ++ tailWord_7804448).sum := by decide
  have hdescent : baseEnd_7804448 < baseStart_7804448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804464 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_7804464 : Nat := 118140960795 + 7804464 * 2 ^ 59
def prefixEnd_7804464 : Nat := 4983230072969 + 3 ^ 40 * 7804464 * 2
def baseEnd_7804464 : Nat := 4007441282711258232407929

theorem tailTrace_7804464 : CollatzResearch.WordTrace tailWord_7804464 prefixEnd_7804464 4007441282711258232407929 := by
  unfold tailWord_7804464
  simp only [CollatzResearch.WordTrace]
  refine ⟨142326093598883649589506223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189768124798511532786008297 142326093598883649589506223)
  ·
    refine ⟨213489140398325474384259335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142326093598883649589506223 213489140398325474384259335)
    ·
      refine ⟨320233710597488211576389003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213489140398325474384259335 320233710597488211576389003)
      ·
        refine ⟨480350565896232317364583505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320233710597488211576389003 480350565896232317364583505)
        ·
          refine ⟨360262924422174238023437629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480350565896232317364583505 360262924422174238023437629)
          ·
            refine ⟨135098596658315339258789111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360262924422174238023437629 135098596658315339258789111)
            ·
              refine ⟨202647894987473008888183667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135098596658315339258789111 202647894987473008888183667)
              ·
                refine ⟨303971842481209513332275501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202647894987473008888183667 303971842481209513332275501)
                ·
                  refine ⟨113989440930453567499603313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 303971842481209513332275501 113989440930453567499603313)
                  ·
                    refine ⟨85492080697840175624702485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113989440930453567499603313 85492080697840175624702485)
                    ·
                      refine ⟨4007441282711258232407929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85492080697840175624702485 4007441282711258232407929)
                      ·
                        rfl

theorem cell23_7804464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_7804464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804464 prefixEnd_7804464 := by exact prefixLift 7804464
  have htrace : WordTrace (prefixWord ++ tailWord_7804464) baseStart_7804464 baseEnd_7804464 := by
    simpa [prefixWord, tailWord_7804464, baseEnd_7804464] using wordTrace_append hprefix tailTrace_7804464
  have hstable : (prefixWord ++ tailWord_7804464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804464).length < 2 ^ (prefixWord ++ tailWord_7804464).sum := by decide
  have hdescent : baseEnd_7804464 < baseStart_7804464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804505 : List Nat := [1, 2, 1, 2, 2, 1, 1, 8, 1, 1, 3]
def baseStart_7804505 : Nat := 118140960795 + 7804505 * 2 ^ 59
def prefixEnd_7804505 : Nat := 4983230072969 + 3 ^ 40 * 7804505 * 2
def baseEnd_7804505 : Nat := 4007462335418092571995241

theorem tailTrace_7804505 : CollatzResearch.WordTrace tailWord_7804505 prefixEnd_7804505 4007462335418092571995241 := by
  unfold tailWord_7804505
  simp only [CollatzResearch.WordTrace]
  refine ⟨284653682590618763181254969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189769121727079175454169979 284653682590618763181254969)
  ·
    refine ⟨213490261942964072385941227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284653682590618763181254969 213490261942964072385941227)
    ·
      refine ⟨320235392914446108578911841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213490261942964072385941227 320235392914446108578911841)
      ·
        refine ⟨240176544685834581434183881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320235392914446108578911841 240176544685834581434183881)
        ·
          refine ⟨180132408514375936075637911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240176544685834581434183881 180132408514375936075637911)
          ·
            refine ⟨270198612771563904113456867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180132408514375936075637911 270198612771563904113456867)
            ·
              refine ⟨405297919157345856170185301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270198612771563904113456867 405297919157345856170185301)
              ·
                refine ⟨4749584990125146751994359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 405297919157345856170185301 4749584990125146751994359)
                ·
                  refine ⟨7124377485187720127991539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749584990125146751994359 7124377485187720127991539)
                  ·
                    refine ⟨10686566227781580191987309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7124377485187720127991539 10686566227781580191987309)
                    ·
                      refine ⟨4007462335418092571995241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10686566227781580191987309 4007462335418092571995241)
                      ·
                        rfl

theorem cell23_7804505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 8, 1, 1, 3].length) (baseStart_7804505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804505 prefixEnd_7804505 := by exact prefixLift 7804505
  have htrace : WordTrace (prefixWord ++ tailWord_7804505) baseStart_7804505 baseEnd_7804505 := by
    simpa [prefixWord, tailWord_7804505, baseEnd_7804505] using wordTrace_append hprefix tailTrace_7804505
  have hstable : (prefixWord ++ tailWord_7804505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804505).length < 2 ^ (prefixWord ++ tailWord_7804505).sum := by decide
  have hdescent : baseEnd_7804505 < baseStart_7804505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804528 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 4]
def baseStart_7804528 : Nat := 118140960795 + 7804528 * 2 ^ 59
def prefixEnd_7804528 : Nat := 4983230072969 + 3 ^ 40 * 7804528 * 2
def baseEnd_7804528 : Nat := 4007474145473145982007635

theorem tailTrace_7804528 : CollatzResearch.WordTrace tailWord_7804528 prefixEnd_7804528 4007474145473145982007635 := by
  unfold tailWord_7804528
  simp only [CollatzResearch.WordTrace]
  refine ⟨142327260734767719054671119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189769680979690292072894825 142327260734767719054671119)
  ·
    refine ⟨213490891102151578582006679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142327260734767719054671119 213490891102151578582006679)
    ·
      refine ⟨320236336653227367873010019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213490891102151578582006679 320236336653227367873010019)
      ·
        refine ⟨480354504979841051809515029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320236336653227367873010019 480354504979841051809515029)
        ·
          refine ⟨22516617420930049303571017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 480354504979841051809515029 22516617420930049303571017)
          ·
            refine ⟨16887463065697536977678263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22516617420930049303571017 16887463065697536977678263)
            ·
              refine ⟨25331194598546305466517395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16887463065697536977678263 25331194598546305466517395)
              ·
                refine ⟨37996791897819458199776093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25331194598546305466517395 37996791897819458199776093)
                ·
                  refine ⟨14248796961682296824916035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37996791897819458199776093 14248796961682296824916035)
                  ·
                    refine ⟨21373195442523445237374053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14248796961682296824916035 21373195442523445237374053)
                    ·
                      refine ⟨4007474145473145982007635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21373195442523445237374053 4007474145473145982007635)
                      ·
                        rfl

theorem cell23_7804528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_7804528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804528 prefixEnd_7804528 := by exact prefixLift 7804528
  have htrace : WordTrace (prefixWord ++ tailWord_7804528) baseStart_7804528 baseEnd_7804528 := by
    simpa [prefixWord, tailWord_7804528, baseEnd_7804528] using wordTrace_append hprefix tailTrace_7804528
  have hstable : (prefixWord ++ tailWord_7804528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804528).length < 2 ^ (prefixWord ++ tailWord_7804528).sum := by decide
  have hdescent : baseEnd_7804528 < baseStart_7804528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804568 : List Nat := [2, 1, 2, 4, 1, 4, 1, 8]
def baseStart_7804568 : Nat := 118140960795 + 7804568 * 2 ^ 59
def prefixEnd_7804568 : Nat := 4983230072969 + 3 ^ 40 * 7804568 * 2
def baseEnd_7804568 : Nat := 148425729062937993537313

theorem tailTrace_7804568 : CollatzResearch.WordTrace tailWord_7804568 prefixEnd_7804568 148425729062937993537313 := by
  unfold tailWord_7804568
  simp only [CollatzResearch.WordTrace]
  refine ⟨142327990194695262470399179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189770653592927016627198905 142327990194695262470399179)
  ·
    refine ⟨213491985292042893705598769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142327990194695262470399179 213491985292042893705598769)
    ·
      refine ⟨160118988969032170279199077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213491985292042893705598769 160118988969032170279199077)
      ·
        refine ⟨30022310431693531927349827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160118988969032170279199077 30022310431693531927349827)
        ·
          refine ⟨45033465647540297891024741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30022310431693531927349827 45033465647540297891024741)
          ·
            refine ⟨8443774808913805854567139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45033465647540297891024741 8443774808913805854567139)
            ·
              refine ⟨12665662213370708781850709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443774808913805854567139 12665662213370708781850709)
              ·
                refine ⟨148425729062937993537313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12665662213370708781850709 148425729062937993537313)
                ·
                  rfl

theorem cell23_7804568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 8].length) (baseStart_7804568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804568 prefixEnd_7804568 := by exact prefixLift 7804568
  have htrace : WordTrace (prefixWord ++ tailWord_7804568) baseStart_7804568 baseEnd_7804568 := by
    simpa [prefixWord, tailWord_7804568, baseEnd_7804568] using wordTrace_append hprefix tailTrace_7804568
  have hstable : (prefixWord ++ tailWord_7804568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804568).length < 2 ^ (prefixWord ++ tailWord_7804568).sum := by decide
  have hdescent : baseEnd_7804568 < baseStart_7804568 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804591 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 5]
def baseStart_7804591 : Nat := 118140960795 + 7804591 * 2 ^ 59
def prefixEnd_7804591 : Nat := 4983230072969 + 3 ^ 40 * 7804591 * 2
def baseEnd_7804591 : Nat := 4007506494754379235519845

theorem tailTrace_7804591 : CollatzResearch.WordTrace tailWord_7804591 prefixEnd_7804591 4007506494754379235519845 := by
  unfold tailWord_7804591
  simp only [CollatzResearch.WordTrace]
  refine ⟨284656819268307199868885627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189771212845538133245923751 284656819268307199868885627)
  ·
    refine ⟨426985228902460799803328441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284656819268307199868885627 426985228902460799803328441)
    ·
      refine ⟨320238921676845599852496331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426985228902460799803328441 320238921676845599852496331)
      ·
        refine ⟨480358382515268399778744497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320238921676845599852496331 480358382515268399778744497)
        ·
          refine ⟨360268786886451299834058373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480358382515268399778744497 360268786886451299834058373)
          ·
            refine ⟨67550397541209618718885945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360268786886451299834058373 67550397541209618718885945)
            ·
              refine ⟨50662798155907214039164459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67550397541209618718885945 50662798155907214039164459)
              ·
                refine ⟨75994197233860821058746689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50662798155907214039164459 75994197233860821058746689)
                ·
                  refine ⟨56995647925395615794060017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75994197233860821058746689 56995647925395615794060017)
                  ·
                    refine ⟨42746735944046711845545013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56995647925395615794060017 42746735944046711845545013)
                    ·
                      refine ⟨4007506494754379235519845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42746735944046711845545013 4007506494754379235519845)
                      ·
                        rfl

theorem cell23_7804591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_7804591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804591 prefixEnd_7804591 := by exact prefixLift 7804591
  have htrace : WordTrace (prefixWord ++ tailWord_7804591) baseStart_7804591 baseEnd_7804591 := by
    simpa [prefixWord, tailWord_7804591, baseEnd_7804591] using wordTrace_append hprefix tailTrace_7804591
  have hstable : (prefixWord ++ tailWord_7804591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804591).length < 2 ^ (prefixWord ++ tailWord_7804591).sum := by decide
  have hdescent : baseEnd_7804591 < baseStart_7804591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804705 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 2, 5]
def baseStart_7804705 : Nat := 118140960795 + 7804705 * 2 ^ 59
def prefixEnd_7804705 : Nat := 4983230072969 + 3 ^ 40 * 7804705 * 2
def baseEnd_7804705 : Nat := 1335855010516330596498107

theorem tailTrace_7804705 : CollatzResearch.WordTrace tailWord_7804705 prefixEnd_7804705 1335855010516330596498107 := by
  unfold tailWord_7804705
  simp only [CollatzResearch.WordTrace]
  refine ⟨284660977189894197338535569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189773984793262798225690379 284660977189894197338535569)
  ·
    refine ⟨213495732892420648003901677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284660977189894197338535569 213495732892420648003901677)
    ·
      refine ⟨80060899834657743001463129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213495732892420648003901677 80060899834657743001463129)
      ·
        refine ⟨60045674875993307251097347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80060899834657743001463129 60045674875993307251097347)
        ·
          refine ⟨90068512313989960876646021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60045674875993307251097347 90068512313989960876646021)
          ·
            refine ⟨16887846058873117664371129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90068512313989960876646021 16887846058873117664371129)
            ·
              refine ⟨12665884544154838248278347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16887846058873117664371129 12665884544154838248278347)
              ·
                refine ⟨18998826816232257372417521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12665884544154838248278347 18998826816232257372417521)
                ·
                  refine ⟨14249120112174193029313141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18998826816232257372417521 14249120112174193029313141)
                  ·
                    refine ⟨1335855010516330596498107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14249120112174193029313141 1335855010516330596498107)
                    ·
                      rfl

theorem cell23_7804705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_7804705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804705 prefixEnd_7804705 := by exact prefixLift 7804705
  have htrace : WordTrace (prefixWord ++ tailWord_7804705) baseStart_7804705 baseEnd_7804705 := by
    simpa [prefixWord, tailWord_7804705, baseEnd_7804705] using wordTrace_append hprefix tailTrace_7804705
  have hstable : (prefixWord ++ tailWord_7804705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804705).length < 2 ^ (prefixWord ++ tailWord_7804705).sum := by decide
  have hdescent : baseEnd_7804705 < baseStart_7804705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804726 : List Nat := [5, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_7804726 : Nat := 118140960795 + 7804726 * 2 ^ 59
def prefixEnd_7804726 : Nat := 4983230072969 + 3 ^ 40 * 7804726 * 2
def baseEnd_7804726 : Nat := 445286201626970689703525

theorem tailTrace_7804726 : CollatzResearch.WordTrace tailWord_7804726 prefixEnd_7804726 445286201626970689703525 := by
  unfold tailWord_7804726
  simp only [CollatzResearch.WordTrace]
  refine ⟨17791358945176132370315627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189774495415212078616700021 17791358945176132370315627)
  ·
    refine ⟨26687038417764198555473441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17791358945176132370315627 26687038417764198555473441)
    ·
      refine ⟨20015278813323148916605081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26687038417764198555473441 20015278813323148916605081)
      ·
        refine ⟨15011459109992361687453811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20015278813323148916605081 15011459109992361687453811)
        ·
          refine ⟨22517188664988542531180717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15011459109992361687453811 22517188664988542531180717)
          ·
            refine ⟨8443945749370703449192769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22517188664988542531180717 8443945749370703449192769)
            ·
              refine ⟨6332959312028027586894577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8443945749370703449192769 6332959312028027586894577)
              ·
                refine ⟨4749719484021020690170933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6332959312028027586894577 4749719484021020690170933)
                ·
                  refine ⟨445286201626970689703525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4749719484021020690170933 445286201626970689703525)
                  ·
                    rfl

theorem cell23_7804726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_7804726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804726 prefixEnd_7804726 := by exact prefixLift 7804726
  have htrace : WordTrace (prefixWord ++ tailWord_7804726) baseStart_7804726 baseEnd_7804726 := by
    simpa [prefixWord, tailWord_7804726, baseEnd_7804726] using wordTrace_append hprefix tailTrace_7804726
  have hstable : (prefixWord ++ tailWord_7804726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804726).length < 2 ^ (prefixWord ++ tailWord_7804726).sum := by decide
  have hdescent : baseEnd_7804726 < baseStart_7804726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804759 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 2, 1, 4]
def baseStart_7804759 : Nat := 118140960795 + 7804759 * 2 ^ 59
def prefixEnd_7804759 : Nat := 4983230072969 + 3 ^ 40 * 7804759 * 2
def baseEnd_7804759 : Nat := 4007592759504334578219073

theorem tailTrace_7804759 : CollatzResearch.WordTrace tailWord_7804759 prefixEnd_7804759 4007592759504334578219073 := by
  unfold tailWord_7804759
  simp only [CollatzResearch.WordTrace]
  refine ⟨284662946731698564561001331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189775297821132376374000887 284662946731698564561001331)
  ·
    refine ⟨426994420097547846841501997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284662946731698564561001331 426994420097547846841501997)
    ·
      refine ⟨160122907536580442565563249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 426994420097547846841501997 160122907536580442565563249)
      ·
        refine ⟨120092180652435331924172437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160122907536580442565563249 120092180652435331924172437)
        ·
          refine ⟨5629320968082906183945583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120092180652435331924172437 5629320968082906183945583)
          ·
            refine ⟨8443981452124359275918375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5629320968082906183945583 8443981452124359275918375)
            ·
              refine ⟨12665972178186538913877563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8443981452124359275918375 12665972178186538913877563)
              ·
                refine ⟨18998958267279808370816345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12665972178186538913877563 18998958267279808370816345)
                ·
                  refine ⟨14249218700459856278112259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18998958267279808370816345 14249218700459856278112259)
                  ·
                    refine ⟨21373828050689784417168389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14249218700459856278112259 21373828050689784417168389)
                    ·
                      refine ⟨4007592759504334578219073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21373828050689784417168389 4007592759504334578219073)
                      ·
                        rfl

theorem cell23_7804759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 1, 4].length) (baseStart_7804759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804759 prefixEnd_7804759 := by exact prefixLift 7804759
  have htrace : WordTrace (prefixWord ++ tailWord_7804759) baseStart_7804759 baseEnd_7804759 := by
    simpa [prefixWord, tailWord_7804759, baseEnd_7804759] using wordTrace_append hprefix tailTrace_7804759
  have hstable : (prefixWord ++ tailWord_7804759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804759).length < 2 ^ (prefixWord ++ tailWord_7804759).sum := by decide
  have hdescent : baseEnd_7804759 < baseStart_7804759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804782 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_7804782 : Nat := 118140960795 + 7804782 * 2 ^ 59
def prefixEnd_7804782 : Nat := 4983230072969 + 3 ^ 40 * 7804782 * 2
def baseEnd_7804782 : Nat := 445289396617709776470163

theorem tailTrace_7804782 : CollatzResearch.WordTrace tailWord_7804782 prefixEnd_7804782 445289396617709776470163 := by
  unfold tailWord_7804782
  simp only [CollatzResearch.WordTrace]
  refine ⟨35582973201326904936136075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189775857073743492992725733 35582973201326904936136075)
  ·
    refine ⟨53374459801990357404204113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35582973201326904936136075 53374459801990357404204113)
    ·
      refine ⟨40030844851492768053153085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53374459801990357404204113 40030844851492768053153085)
      ·
        refine ⟨15011566819309788019932407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40030844851492768053153085 15011566819309788019932407)
        ·
          refine ⟨22517350228964682029898611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15011566819309788019932407 22517350228964682029898611)
          ·
            refine ⟨33776025343447023044847917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22517350228964682029898611 33776025343447023044847917)
            ·
              refine ⟨12666009503792633641817969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33776025343447023044847917 12666009503792633641817969)
              ·
                refine ⟨9499507127844475231363477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12666009503792633641817969 9499507127844475231363477)
                ·
                  refine ⟨445289396617709776470163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9499507127844475231363477 445289396617709776470163)
                  ·
                    rfl

theorem cell23_7804782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_7804782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804782 prefixEnd_7804782 := by exact prefixLift 7804782
  have htrace : WordTrace (prefixWord ++ tailWord_7804782) baseStart_7804782 baseEnd_7804782 := by
    simpa [prefixWord, tailWord_7804782, baseEnd_7804782] using wordTrace_append hprefix tailTrace_7804782
  have hstable : (prefixWord ++ tailWord_7804782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804782).length < 2 ^ (prefixWord ++ tailWord_7804782).sum := by decide
  have hdescent : baseEnd_7804782 < baseStart_7804782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804825 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 4, 4]
def baseStart_7804825 : Nat := 118140960795 + 7804825 * 2 ^ 59
def prefixEnd_7804825 : Nat := 4983230072969 + 3 ^ 40 * 7804825 * 2
def baseEnd_7804825 : Nat := 1335875549742510439997923

theorem tailTrace_7804825 : CollatzResearch.WordTrace tailWord_7804825 prefixEnd_7804825 1335875549742510439997923 := by
  unfold tailWord_7804825
  simp only [CollatzResearch.WordTrace]
  refine ⟨284665353949459457832903929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189776902632972971888602619 284665353949459457832903929)
  ·
    refine ⟨213499015462094593374677947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284665353949459457832903929 213499015462094593374677947)
    ·
      refine ⟨320248523193141890062016921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213499015462094593374677947 320248523193141890062016921)
      ·
        refine ⟨240186392394856417546512691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320248523193141890062016921 240186392394856417546512691)
        ·
          refine ⟨360279588592284626319769037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240186392394856417546512691 360279588592284626319769037)
          ·
            refine ⟨135104845722106734869913389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360279588592284626319769037 135104845722106734869913389)
            ·
              refine ⟨50664317145790025576217521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135104845722106734869913389 50664317145790025576217521)
              ·
                refine ⟨37998237859342519182163141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50664317145790025576217521 37998237859342519182163141)
                ·
                  refine ⟨7124669598626722346655589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37998237859342519182163141 7124669598626722346655589)
                  ·
                    refine ⟨1335875549742510439997923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7124669598626722346655589 1335875549742510439997923)
                    ·
                      rfl

theorem cell23_7804825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 4].length) (baseStart_7804825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804825 prefixEnd_7804825 := by exact prefixLift 7804825
  have htrace : WordTrace (prefixWord ++ tailWord_7804825) baseStart_7804825 baseEnd_7804825 := by
    simpa [prefixWord, tailWord_7804825, baseEnd_7804825] using wordTrace_append hprefix tailTrace_7804825
  have hstable : (prefixWord ++ tailWord_7804825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804825).length < 2 ^ (prefixWord ++ tailWord_7804825).sum := by decide
  have hdescent : baseEnd_7804825 < baseStart_7804825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804826 : List Nat := [3, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3]
def baseStart_7804826 : Nat := 118140960795 + 7804826 * 2 ^ 59
def prefixEnd_7804826 : Nat := 4983230072969 + 3 ^ 40 * 7804826 * 2
def baseEnd_7804826 : Nat := 4007627162708185816081265

theorem tailTrace_7804826 : CollatzResearch.WordTrace tailWord_7804826 prefixEnd_7804826 4007627162708185816081265 := by
  unfold tailWord_7804826
  simp only [CollatzResearch.WordTrace]
  refine ⟨71166347605613958750922583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189776926948303890002460221 71166347605613958750922583)
  ·
    refine ⟨106749521408420938126383875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71166347605613958750922583 106749521408420938126383875)
    ·
      refine ⟨160124282112631407189575813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106749521408420938126383875 160124282112631407189575813)
      ·
        refine ⟨30023302896118388848045465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160124282112631407189575813 30023302896118388848045465)
        ·
          refine ⟨22517477172088791636034099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30023302896118388848045465 22517477172088791636034099)
          ·
            refine ⟨33776215758133187454051149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22517477172088791636034099 33776215758133187454051149)
            ·
              refine ⟨12666080909299945295269181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33776215758133187454051149 12666080909299945295269181)
              ·
                refine ⟨4749780340987479485725943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12666080909299945295269181 4749780340987479485725943)
                ·
                  refine ⟨7124670511481219228588915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749780340987479485725943 7124670511481219228588915)
                  ·
                    refine ⟨10687005767221828842883373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7124670511481219228588915 10687005767221828842883373)
                    ·
                      refine ⟨4007627162708185816081265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687005767221828842883373 4007627162708185816081265)
                      ·
                        rfl

theorem cell23_7804826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_7804826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804826 prefixEnd_7804826 := by exact prefixLift 7804826
  have htrace : WordTrace (prefixWord ++ tailWord_7804826) baseStart_7804826 baseEnd_7804826 := by
    simpa [prefixWord, tailWord_7804826, baseEnd_7804826] using wordTrace_append hprefix tailTrace_7804826
  have hstable : (prefixWord ++ tailWord_7804826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804826).length < 2 ^ (prefixWord ++ tailWord_7804826).sum := by decide
  have hdescent : baseEnd_7804826 < baseStart_7804826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804835 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 3]
def baseStart_7804835 : Nat := 118140960795 + 7804835 * 2 ^ 59
def prefixEnd_7804835 : Nat := 4983230072969 + 3 ^ 40 * 7804835 * 2
def baseEnd_7804835 : Nat := 4007631784034076280868723

theorem tailTrace_7804835 : CollatzResearch.WordTrace tailWord_7804835 prefixEnd_7804835 4007631784034076280868723 := by
  unfold tailWord_7804835
  simp only [CollatzResearch.WordTrace]
  refine ⟨284665718679423229540767959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189777145786282153027178639 284665718679423229540767959)
  ·
    refine ⟨426998578019134844311151939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284665718679423229540767959 426998578019134844311151939)
    ·
      refine ⟨640497867028702266466727909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 426998578019134844311151939 640497867028702266466727909)
      ·
        refine ⟨120093350067881674962511483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 640497867028702266466727909 120093350067881674962511483)
        ·
          refine ⟨180140025101822512443767225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120093350067881674962511483 180140025101822512443767225)
          ·
            refine ⟨135105018826366884332825419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180140025101822512443767225 135105018826366884332825419)
            ·
              refine ⟨202657528239550326499238129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135105018826366884332825419 202657528239550326499238129)
              ·
                refine ⟨151993146179662744874428597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202657528239550326499238129 151993146179662744874428597)
                ·
                  refine ⟨14249357454343382331977681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 151993146179662744874428597 14249357454343382331977681)
                  ·
                    refine ⟨10687018090757536748983261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14249357454343382331977681 10687018090757536748983261)
                    ·
                      refine ⟨4007631784034076280868723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687018090757536748983261 4007631784034076280868723)
                      ·
                        rfl

theorem cell23_7804835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_7804835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804835 prefixEnd_7804835 := by exact prefixLift 7804835
  have htrace : WordTrace (prefixWord ++ tailWord_7804835) baseStart_7804835 baseEnd_7804835 := by
    simpa [prefixWord, tailWord_7804835, baseEnd_7804835] using wordTrace_append hprefix tailTrace_7804835
  have hstable : (prefixWord ++ tailWord_7804835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804835).length < 2 ^ (prefixWord ++ tailWord_7804835).sum := by decide
  have hdescent : baseEnd_7804835 < baseStart_7804835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804886 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_7804886 : Nat := 118140960795 + 7804886 * 2 ^ 59
def prefixEnd_7804886 : Nat := 4983230072969 + 3 ^ 40 * 7804886 * 2
def baseEnd_7804886 : Nat := 4007657971547455581330989

theorem tailTrace_7804886 : CollatzResearch.WordTrace tailWord_7804886 prefixEnd_7804886 4007657971547455581330989 := by
  unfold tailWord_7804886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17791723675139904078179657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189778385868158976833916341 17791723675139904078179657)
  ·
    refine ⟨13343792756354928058634743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17791723675139904078179657 13343792756354928058634743)
    ·
      refine ⟨20015689134532392087952115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13343792756354928058634743 20015689134532392087952115)
      ·
        refine ⟨30023533701798588131928173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20015689134532392087952115 30023533701798588131928173)
        ·
          refine ⟨11258825138174470549473065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30023533701798588131928173 11258825138174470549473065)
          ·
            refine ⟨8444118853630852912104799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11258825138174470549473065 8444118853630852912104799)
            ·
              refine ⟨12666178280446279368157199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8444118853630852912104799 12666178280446279368157199)
              ·
                refine ⟨18999267420669419052235799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12666178280446279368157199 18999267420669419052235799)
                ·
                  refine ⟨28498901131004128578353699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18999267420669419052235799 28498901131004128578353699)
                  ·
                    refine ⟨42748351696506192867530549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28498901131004128578353699 42748351696506192867530549)
                    ·
                      refine ⟨4007657971547455581330989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42748351696506192867530549 4007657971547455581330989)
                      ·
                        rfl

theorem cell23_7804886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_7804886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804886 prefixEnd_7804886 := by exact prefixLift 7804886
  have htrace : WordTrace (prefixWord ++ tailWord_7804886) baseStart_7804886 baseEnd_7804886 := by
    simpa [prefixWord, tailWord_7804886, baseEnd_7804886] using wordTrace_append hprefix tailTrace_7804886
  have hstable : (prefixWord ++ tailWord_7804886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804886).length < 2 ^ (prefixWord ++ tailWord_7804886).sum := by decide
  have hdescent : baseEnd_7804886 < baseStart_7804886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804899 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 2, 1, 3]
def baseStart_7804899 : Nat := 118140960795 + 7804899 * 2 ^ 59
def prefixEnd_7804899 : Nat := 4983230072969 + 3 ^ 40 * 7804899 * 2
def baseEnd_7804899 : Nat := 4007664646795964030468429

theorem tailTrace_7804899 : CollatzResearch.WordTrace tailWord_7804899 prefixEnd_7804899 4007664646795964030468429 := by
  unfold tailWord_7804899
  simp only [CollatzResearch.WordTrace]
  refine ⟨284668052951191368471097751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189778701967460912314065167 284668052951191368471097751)
  ·
    refine ⟨427002079426787052706646627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284668052951191368471097751 427002079426787052706646627)
    ·
      refine ⟨640503119140180579059969941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427002079426787052706646627 640503119140180579059969941)
      ·
        refine ⟨30023583709695964643436091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 640503119140180579059969941 30023583709695964643436091)
        ·
          refine ⟨45035375564543946965154137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30023583709695964643436091 45035375564543946965154137)
          ·
            refine ⟨33776531673407960223865603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45035375564543946965154137 33776531673407960223865603)
            ·
              refine ⟨50664797510111940335798405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33776531673407960223865603 50664797510111940335798405)
              ·
                refine ⟨9499649533145988812962201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50664797510111940335798405 9499649533145988812962201)
                ·
                  refine ⟨7124737149859491609721651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9499649533145988812962201 7124737149859491609721651)
                  ·
                    refine ⟨10687105724789237414582477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7124737149859491609721651 10687105724789237414582477)
                    ·
                      refine ⟨4007664646795964030468429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687105724789237414582477 4007664646795964030468429)
                      ·
                        rfl

theorem cell23_7804899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_7804899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804899 prefixEnd_7804899 := by exact prefixLift 7804899
  have htrace : WordTrace (prefixWord ++ tailWord_7804899) baseStart_7804899 baseEnd_7804899 := by
    simpa [prefixWord, tailWord_7804899, baseEnd_7804899] using wordTrace_append hprefix tailTrace_7804899
  have hstable : (prefixWord ++ tailWord_7804899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804899).length < 2 ^ (prefixWord ++ tailWord_7804899).sum := by decide
  have hdescent : baseEnd_7804899 < baseStart_7804899 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804925 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 5]
def baseStart_7804925 : Nat := 118140960795 + 7804925 * 2 ^ 59
def prefixEnd_7804925 : Nat := 4983230072969 + 3 ^ 40 * 7804925 * 2
def baseEnd_7804925 : Nat := 4007677997292980928743309

theorem tailTrace_7804925 : CollatzResearch.WordTrace tailWord_7804925 prefixEnd_7804925 4007677997292980928743309 := by
  unfold tailWord_7804925
  simp only [CollatzResearch.WordTrace]
  refine ⟨284669001249097174911544229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189779334166064783274362819 284669001249097174911544229)
  ·
    refine ⟨53375437734205720295914543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284669001249097174911544229 53375437734205720295914543)
    ·
      refine ⟨80063156601308580443871815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53375437734205720295914543 80063156601308580443871815)
      ·
        refine ⟨120094734901962870665807723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80063156601308580443871815 120094734901962870665807723)
        ·
          refine ⟨180142102352944305998711585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120094734901962870665807723 180142102352944305998711585)
          ·
            refine ⟨135106576764708229499033689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180142102352944305998711585 135106576764708229499033689)
            ·
              refine ⟨101329932573531172124275267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135106576764708229499033689 101329932573531172124275267)
              ·
                refine ⟨151994898860296758186412901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101329932573531172124275267 151994898860296758186412901)
                ·
                  refine ⟨28499043536305642159952419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151994898860296758186412901 28499043536305642159952419)
                  ·
                    refine ⟨42748565304458463239928629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28499043536305642159952419 42748565304458463239928629)
                    ·
                      refine ⟨4007677997292980928743309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42748565304458463239928629 4007677997292980928743309)
                      ·
                        rfl

theorem cell23_7804925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_7804925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804925 prefixEnd_7804925 := by exact prefixLift 7804925
  have htrace : WordTrace (prefixWord ++ tailWord_7804925) baseStart_7804925 baseEnd_7804925 := by
    simpa [prefixWord, tailWord_7804925, baseEnd_7804925] using wordTrace_append hprefix tailTrace_7804925
  have hstable : (prefixWord ++ tailWord_7804925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804925).length < 2 ^ (prefixWord ++ tailWord_7804925).sum := by decide
  have hdescent : baseEnd_7804925 < baseStart_7804925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804926 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_7804926 : Nat := 118140960795 + 7804926 * 2 ^ 59
def prefixEnd_7804926 : Nat := 4983230072969 + 3 ^ 40 * 7804926 * 2
def baseEnd_7804926 : Nat := 4007678510773635424830805

theorem tailTrace_7804926 : CollatzResearch.WordTrace tailWord_7804926 prefixEnd_7804926 4007678510773635424830805 := by
  unfold tailWord_7804926
  simp only [CollatzResearch.WordTrace]
  refine ⟨35583629715261694010291329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189779358481395701388220421 35583629715261694010291329)
  ·
    refine ⟨26687722286446270507718497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35583629715261694010291329 26687722286446270507718497)
    ·
      refine ⟨20015791714834702880788873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26687722286446270507718497 20015791714834702880788873)
      ·
        refine ⟨15011843786126027160591655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20015791714834702880788873 15011843786126027160591655)
        ·
          refine ⟨22517765679189040740887483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15011843786126027160591655 22517765679189040740887483)
          ·
            refine ⟨33776648518783561111331225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22517765679189040740887483 33776648518783561111331225)
            ·
              refine ⟨25332486389087670833498419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33776648518783561111331225 25332486389087670833498419)
              ·
                refine ⟨37998729583631506250247629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25332486389087670833498419 37998729583631506250247629)
                ·
                  refine ⟨14249523593861814843842861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37998729583631506250247629 14249523593861814843842861)
                  ·
                    refine ⟨5343571347698180566441073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14249523593861814843842861 5343571347698180566441073)
                    ·
                      refine ⟨4007678510773635424830805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5343571347698180566441073 4007678510773635424830805)
                      ·
                        rfl

theorem cell23_7804926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_7804926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804926 prefixEnd_7804926 := by exact prefixLift 7804926
  have htrace : WordTrace (prefixWord ++ tailWord_7804926) baseStart_7804926 baseEnd_7804926 := by
    simpa [prefixWord, tailWord_7804926, baseEnd_7804926] using wordTrace_append hprefix tailTrace_7804926
  have hstable : (prefixWord ++ tailWord_7804926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804926).length < 2 ^ (prefixWord ++ tailWord_7804926).sum := by decide
  have hdescent : baseEnd_7804926 < baseStart_7804926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804934 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_7804934 : Nat := 118140960795 + 7804934 * 2 ^ 59
def prefixEnd_7804934 : Nat := 4983230072969 + 3 ^ 40 * 7804934 * 2
def baseEnd_7804934 : Nat := 4007682618618871393530769

theorem tailTrace_7804934 : CollatzResearch.WordTrace tailWord_7804934 prefixEnd_7804934 4007682618618871393530769 := by
  unfold tailWord_7804934
  simp only [CollatzResearch.WordTrace]
  refine ⟨8895916547064517795269433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 189779553004043046299081237 8895916547064517795269433)
  ·
    refine ⟨6671937410298388346452075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8895916547064517795269433 6671937410298388346452075)
    ·
      refine ⟨10007906115447582519678113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6671937410298388346452075 10007906115447582519678113)
      ·
        refine ⟨7505929586585686889758585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10007906115447582519678113 7505929586585686889758585)
        ·
          refine ⟨5629447189939265167318939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7505929586585686889758585 5629447189939265167318939)
          ·
            refine ⟨8444170784908897750978409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5629447189939265167318939 8444170784908897750978409)
            ·
              refine ⟨6333128088681673313233807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8444170784908897750978409 6333128088681673313233807)
              ·
                refine ⟨9499692133022509969850711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6333128088681673313233807 9499692133022509969850711)
                ·
                  refine ⟨14249538199533764954776067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9499692133022509969850711 14249538199533764954776067)
                  ·
                    refine ⟨21374307299300647432164101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14249538199533764954776067 21374307299300647432164101)
                    ·
                      refine ⟨4007682618618871393530769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21374307299300647432164101 4007682618618871393530769)
                      ·
                        rfl

theorem cell23_7804934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_7804934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804934 prefixEnd_7804934 := by exact prefixLift 7804934
  have htrace : WordTrace (prefixWord ++ tailWord_7804934) baseStart_7804934 baseEnd_7804934 := by
    simpa [prefixWord, tailWord_7804934, baseEnd_7804934] using wordTrace_append hprefix tailTrace_7804934
  have hstable : (prefixWord ++ tailWord_7804934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804934).length < 2 ^ (prefixWord ++ tailWord_7804934).sum := by decide
  have hdescent : baseEnd_7804934 < baseStart_7804934 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804939 : List Nat := [1, 1, 1, 1, 6, 1, 2, 2, 4, 2, 2]
def baseStart_7804939 : Nat := 118140960795 + 7804939 * 2 ^ 59
def prefixEnd_7804939 : Nat := 4983230072969 + 3 ^ 40 * 7804939 * 2
def baseEnd_7804939 : Nat := 4007685186022143873968245

theorem tailTrace_7804939 : CollatzResearch.WordTrace tailWord_7804939 prefixEnd_7804939 4007685186022143873968245 := by
  unfold tailWord_7804939
  simp only [CollatzResearch.WordTrace]
  refine ⟨284669511871046455302553871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189779674580697636868369247 284669511871046455302553871)
  ·
    refine ⟨427004267806569682953830807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284669511871046455302553871 427004267806569682953830807)
    ·
      refine ⟨640506401709854524430746211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427004267806569682953830807 640506401709854524430746211)
      ·
        refine ⟨960759602564781786646119317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640506401709854524430746211 960759602564781786646119317)
        ·
          refine ⟨45035606370224146249036843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 960759602564781786646119317 45035606370224146249036843)
          ·
            refine ⟨67553409555336219373555265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45035606370224146249036843 67553409555336219373555265)
            ·
              refine ⟨50665057166502164530166449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67553409555336219373555265 50665057166502164530166449)
              ·
                refine ⟨37998792874876623397624837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50665057166502164530166449 37998792874876623397624837)
                ·
                  refine ⟨7124773664039366887054657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37998792874876623397624837 7124773664039366887054657)
                  ·
                    refine ⟨5343580248029525165290993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7124773664039366887054657 5343580248029525165290993)
                    ·
                      refine ⟨4007685186022143873968245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5343580248029525165290993 4007685186022143873968245)
                      ·
                        rfl

theorem cell23_7804939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4, 2, 2].length) (baseStart_7804939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804939 prefixEnd_7804939 := by exact prefixLift 7804939
  have htrace : WordTrace (prefixWord ++ tailWord_7804939) baseStart_7804939 baseEnd_7804939 := by
    simpa [prefixWord, tailWord_7804939, baseEnd_7804939] using wordTrace_append hprefix tailTrace_7804939
  have hstable : (prefixWord ++ tailWord_7804939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804939).length < 2 ^ (prefixWord ++ tailWord_7804939).sum := by decide
  have hdescent : baseEnd_7804939 < baseStart_7804939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804956 : List Nat := [2, 2, 3, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_7804956 : Nat := 118140960795 + 7804956 * 2 ^ 59
def prefixEnd_7804956 : Nat := 4983230072969 + 3 ^ 40 * 7804956 * 2
def baseEnd_7804956 : Nat := 4007693915193270307455667

theorem tailTrace_7804956 : CollatzResearch.WordTrace tailWord_7804956 prefixEnd_7804956 4007693915193270307455667 := by
  unfold tailWord_7804956
  simp only [CollatzResearch.WordTrace]
  refine ⟨142335065955992433602961361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189780087941323244803948481 142335065955992433602961361)
  ·
    refine ⟨106751299466994325202221021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142335065955992433602961361 106751299466994325202221021)
    ·
      refine ⟨40031737300122871950832883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106751299466994325202221021 40031737300122871950832883)
      ·
        refine ⟨60047605950184307926249325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40031737300122871950832883 60047605950184307926249325)
        ·
          refine ⟨22517852231319115472343497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60047605950184307926249325 22517852231319115472343497)
          ·
            refine ⟨16888389173489336604257623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22517852231319115472343497 16888389173489336604257623)
            ·
              refine ⟨25332583760234004906386435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16888389173489336604257623 25332583760234004906386435)
              ·
                refine ⟨37998875640351007359579653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25332583760234004906386435 37998875640351007359579653)
                ·
                  refine ⟨7124789182565813879921185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37998875640351007359579653 7124789182565813879921185)
                  ·
                    refine ⟨5343591886924360409940889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7124789182565813879921185 5343591886924360409940889)
                    ·
                      refine ⟨4007693915193270307455667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5343591886924360409940889 4007693915193270307455667)
                      ·
                        rfl

theorem cell23_7804956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_7804956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804956 prefixEnd_7804956 := by exact prefixLift 7804956
  have htrace : WordTrace (prefixWord ++ tailWord_7804956) baseStart_7804956 baseEnd_7804956 := by
    simpa [prefixWord, tailWord_7804956, baseEnd_7804956] using wordTrace_append hprefix tailTrace_7804956
  have hstable : (prefixWord ++ tailWord_7804956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804956).length < 2 ^ (prefixWord ++ tailWord_7804956).sum := by decide
  have hdescent : baseEnd_7804956 < baseStart_7804956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804962 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 7]
def baseStart_7804962 : Nat := 118140960795 + 7804962 * 2 ^ 59
def prefixEnd_7804962 : Nat := 4983230072969 + 3 ^ 40 * 7804962 * 2
def baseEnd_7804962 : Nat := 445299666230799698220071

theorem tailTrace_7804962 : CollatzResearch.WordTrace tailWord_7804962 prefixEnd_7804962 445299666230799698220071 := by
  unfold tailWord_7804962
  simp only [CollatzResearch.WordTrace]
  refine ⟨71167587687490782557660285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189780233833308753487094093 71167587687490782557660285)
  ·
    refine ⟨26687845382809043459122607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71167587687490782557660285 26687845382809043459122607)
    ·
      refine ⟨40031768074213565188683911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26687845382809043459122607 40031768074213565188683911)
      ·
        refine ⟨60047652111320347783025867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40031768074213565188683911 60047652111320347783025867)
        ·
          refine ⟨90071478166980521674538801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60047652111320347783025867 90071478166980521674538801)
          ·
            refine ⟨67553608625235391255904101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90071478166980521674538801 67553608625235391255904101)
            ·
              refine ⟨12666301617231635860482019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67553608625235391255904101 12666301617231635860482019)
              ·
                refine ⟨18999452425847453790723029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12666301617231635860482019 18999452425847453790723029)
                ·
                  refine ⟨445299666230799698220071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18999452425847453790723029 445299666230799698220071)
                  ·
                    rfl

theorem cell23_7804962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_7804962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804962 prefixEnd_7804962 := by exact prefixLift 7804962
  have htrace : WordTrace (prefixWord ++ tailWord_7804962) baseStart_7804962 baseEnd_7804962 := by
    simpa [prefixWord, tailWord_7804962, baseEnd_7804962] using wordTrace_append hprefix tailTrace_7804962
  have hstable : (prefixWord ++ tailWord_7804962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804962).length < 2 ^ (prefixWord ++ tailWord_7804962).sum := by decide
  have hdescent : baseEnd_7804962 < baseStart_7804962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7804975 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 6, 5]
def baseStart_7804975 : Nat := 118140960795 + 7804975 * 2 ^ 59
def prefixEnd_7804975 : Nat := 4983230072969 + 3 ^ 40 * 7804975 * 2
def baseEnd_7804975 : Nat := 1335901223775235244372693

theorem tailTrace_7804975 : CollatzResearch.WordTrace tailWord_7804975 prefixEnd_7804975 1335901223775235244372693 := by
  unfold tailWord_7804975
  simp only [CollatzResearch.WordTrace]
  refine ⟨284670824898916033450864379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189780549932610688967242919 284670824898916033450864379)
  ·
    refine ⟨427006237348374050176296569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284670824898916033450864379 427006237348374050176296569)
    ·
      refine ⟨320254678011280537632222427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427006237348374050176296569 320254678011280537632222427)
      ·
        refine ⟨480382017016920806448333641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320254678011280537632222427 480382017016920806448333641)
        ·
          refine ⟨360286512762690604836250231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480382017016920806448333641 360286512762690604836250231)
          ·
            refine ⟨540429769144035907254375347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360286512762690604836250231 540429769144035907254375347)
            ·
              refine ⟨810644653716053860881563021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540429769144035907254375347 810644653716053860881563021)
              ·
                refine ⟨303991745143520197830586133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 810644653716053860881563021 303991745143520197830586133)
                ·
                  refine ⟨14249613053602509273308725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 303991745143520197830586133 14249613053602509273308725)
                  ·
                    refine ⟨1335901223775235244372693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14249613053602509273308725 1335901223775235244372693)
                    ·
                      rfl

theorem cell23_7804975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_7804975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7804975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7804975 prefixEnd_7804975 := by exact prefixLift 7804975
  have htrace : WordTrace (prefixWord ++ tailWord_7804975) baseStart_7804975 baseEnd_7804975 := by
    simpa [prefixWord, tailWord_7804975, baseEnd_7804975] using wordTrace_append hprefix tailTrace_7804975
  have hstable : (prefixWord ++ tailWord_7804975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7804975).length < 2 ^ (prefixWord ++ tailWord_7804975).sum := by decide
  have hdescent : baseEnd_7804975 < baseStart_7804975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7804975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805046 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_7805046 : Nat := 118140960795 + 7805046 * 2 ^ 59
def prefixEnd_7805046 : Nat := 4983230072969 + 3 ^ 40 * 7805046 * 2
def baseEnd_7805046 : Nat := 4007740128452174955330253

theorem tailTrace_7805046 : CollatzResearch.WordTrace tailWord_7805046 prefixEnd_7805046 4007740128452174955330253 := by
  unfold tailWord_7805046
  simp only [CollatzResearch.WordTrace]
  refine ⟨17792088405103675786043687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189782276321105875051132661 17792088405103675786043687)
  ·
    refine ⟨26688132607655513679065531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17792088405103675786043687 26688132607655513679065531)
    ·
      refine ⟨40032198911483270518598297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26688132607655513679065531 40032198911483270518598297)
      ·
        refine ⟨30024149183612452888948723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40032198911483270518598297 30024149183612452888948723)
        ·
          refine ⟨45036223775418679333423085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30024149183612452888948723 45036223775418679333423085)
          ·
            refine ⟨16888583915782004750033657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45036223775418679333423085 16888583915782004750033657)
            ·
              refine ⟨12666437936836503562525243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16888583915782004750033657 12666437936836503562525243)
              ·
                refine ⟨18999656905254755343787865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12666437936836503562525243 18999656905254755343787865)
                ·
                  refine ⟨14249742678941066507840899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18999656905254755343787865 14249742678941066507840899)
                  ·
                    refine ⟨21374614018411599761761349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14249742678941066507840899 21374614018411599761761349)
                    ·
                      refine ⟨4007740128452174955330253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21374614018411599761761349 4007740128452174955330253)
                      ·
                        rfl

theorem cell23_7805046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_7805046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805046 prefixEnd_7805046 := by exact prefixLift 7805046
  have htrace : WordTrace (prefixWord ++ tailWord_7805046) baseStart_7805046 baseEnd_7805046 := by
    simpa [prefixWord, tailWord_7805046, baseEnd_7805046] using wordTrace_append hprefix tailTrace_7805046
  have hstable : (prefixWord ++ tailWord_7805046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805046).length < 2 ^ (prefixWord ++ tailWord_7805046).sum := by decide
  have hdescent : baseEnd_7805046 < baseStart_7805046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805049 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 2, 2, 3]
def baseStart_7805049 : Nat := 118140960795 + 7805049 * 2 ^ 59
def prefixEnd_7805049 : Nat := 4983230072969 + 3 ^ 40 * 7805049 * 2
def baseEnd_7805049 : Nat := 4007741668894138443592739

theorem tailTrace_7805049 : CollatzResearch.WordTrace tailWord_7805049 prefixEnd_7805049 4007741668894138443592739 := by
  unfold tailWord_7805049
  simp only [CollatzResearch.WordTrace]
  refine ⟨284673523900647944089058201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189782349267098629392705467 284673523900647944089058201)
  ·
    refine ⟨213505142925485958066793651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284673523900647944089058201 213505142925485958066793651)
    ·
      refine ⟨320257714388228937100190477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213505142925485958066793651 320257714388228937100190477)
      ·
        refine ⟨120096642895585851412571429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320257714388228937100190477 120096642895585851412571429)
        ·
          refine ⟨22518120542922347139857143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120096642895585851412571429 22518120542922347139857143)
          ·
            refine ⟨33777180814383520709785715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22518120542922347139857143 33777180814383520709785715)
            ·
              refine ⟨50665771221575281064678573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33777180814383520709785715 50665771221575281064678573)
              ·
                refine ⟨18999664208090730399254465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50665771221575281064678573 18999664208090730399254465)
                ·
                  refine ⟨14249748156068047799440849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18999664208090730399254465 14249748156068047799440849)
                  ·
                    refine ⟨10687311117051035849580637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14249748156068047799440849 10687311117051035849580637)
                    ·
                      refine ⟨4007741668894138443592739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687311117051035849580637 4007741668894138443592739)
                      ·
                        rfl

theorem cell23_7805049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_7805049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805049 prefixEnd_7805049 := by exact prefixLift 7805049
  have htrace : WordTrace (prefixWord ++ tailWord_7805049) baseStart_7805049 baseEnd_7805049 := by
    simpa [prefixWord, tailWord_7805049, baseEnd_7805049] using wordTrace_append hprefix tailTrace_7805049
  have hstable : (prefixWord ++ tailWord_7805049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805049).length < 2 ^ (prefixWord ++ tailWord_7805049).sum := by decide
  have hdescent : baseEnd_7805049 < baseStart_7805049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805112 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 1, 6]
def baseStart_7805112 : Nat := 118140960795 + 7805112 * 2 ^ 59
def prefixEnd_7805112 : Nat := 4983230072969 + 3 ^ 40 * 7805112 * 2
def baseEnd_7805112 : Nat := 1335924672725123899034983

theorem tailTrace_7805112 : CollatzResearch.WordTrace tailWord_7805112 prefixEnd_7805112 1335924672725123899034983 := by
  unfold tailWord_7805112
  simp only [CollatzResearch.WordTrace]
  refine ⟨142337910849709852924300795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189783881132946470565734393 142337910849709852924300795)
  ·
    refine ⟨213506866274564779386451193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142337910849709852924300795 213506866274564779386451193)
    ·
      refine ⟨160130149705923584539838395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213506866274564779386451193 160130149705923584539838395)
      ·
        refine ⟨240195224558885376809757593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160130149705923584539838395 240195224558885376809757593)
        ·
          refine ⟨180146418419164032607318195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240195224558885376809757593 180146418419164032607318195)
          ·
            refine ⟨270219627628746048910977293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180146418419164032607318195 270219627628746048910977293)
            ·
              refine ⟨101332360360779768341616485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270219627628746048910977293 101332360360779768341616485)
              ·
                refine ⟨18999817567646206564053091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101332360360779768341616485 18999817567646206564053091)
                ·
                  refine ⟨28499726351469309846079637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18999817567646206564053091 28499726351469309846079637)
                  ·
                    refine ⟨1335924672725123899034983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28499726351469309846079637 1335924672725123899034983)
                    ·
                      rfl

theorem cell23_7805112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_7805112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805112 prefixEnd_7805112 := by exact prefixLift 7805112
  have htrace : WordTrace (prefixWord ++ tailWord_7805112) baseStart_7805112 baseEnd_7805112 := by
    simpa [prefixWord, tailWord_7805112, baseEnd_7805112] using wordTrace_append hprefix tailTrace_7805112
  have hstable : (prefixWord ++ tailWord_7805112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805112).length < 2 ^ (prefixWord ++ tailWord_7805112).sum := by decide
  have hdescent : baseEnd_7805112 < baseStart_7805112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805113 : List Nat := [1, 2, 1, 4, 1, 2, 4, 3, 1, 1, 3]
def baseStart_7805113 : Nat := 118140960795 + 7805113 * 2 ^ 59
def prefixEnd_7805113 : Nat := 4983230072969 + 3 ^ 40 * 7805113 * 2
def baseEnd_7805113 : Nat := 4007774531656026193192445

theorem tailTrace_7805113 : CollatzResearch.WordTrace tailWord_7805113 prefixEnd_7805113 4007774531656026193192445 := by
  unfold tailWord_7805113
  simp only [CollatzResearch.WordTrace]
  refine ⟨284675858172416083019387993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189783905448277388679591995 284675858172416083019387993)
  ·
    refine ⟨213506893629312062264540995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284675858172416083019387993 213506893629312062264540995)
    ·
      refine ⟨320260340443968093396811493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213506893629312062264540995 320260340443968093396811493)
      ·
        refine ⟨60048813833244017511902155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320260340443968093396811493 60048813833244017511902155)
        ·
          refine ⟨90073220749866026267853233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60048813833244017511902155 90073220749866026267853233)
          ·
            refine ⟨67554915562399519700889925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90073220749866026267853233 67554915562399519700889925)
            ·
              refine ⟨12666546667949909943916861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67554915562399519700889925 12666546667949909943916861)
              ·
                refine ⟨4749955000481216228968823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12666546667949909943916861 4749955000481216228968823)
                ·
                  refine ⟨7124932500721824343453235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4749955000481216228968823 7124932500721824343453235)
                  ·
                    refine ⟨10687398751082736515179853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7124932500721824343453235 10687398751082736515179853)
                    ·
                      refine ⟨4007774531656026193192445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687398751082736515179853 4007774531656026193192445)
                      ·
                        rfl

theorem cell23_7805113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_7805113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805113 prefixEnd_7805113 := by exact prefixLift 7805113
  have htrace : WordTrace (prefixWord ++ tailWord_7805113) baseStart_7805113 baseEnd_7805113 := by
    simpa [prefixWord, tailWord_7805113, baseEnd_7805113] using wordTrace_append hprefix tailTrace_7805113
  have hstable : (prefixWord ++ tailWord_7805113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805113).length < 2 ^ (prefixWord ++ tailWord_7805113).sum := by decide
  have hdescent : baseEnd_7805113 < baseStart_7805113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805116 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 1, 5]
def baseStart_7805116 : Nat := 118140960795 + 7805116 * 2 ^ 59
def prefixEnd_7805116 : Nat := 4983230072969 + 3 ^ 40 * 7805116 * 2
def baseEnd_7805116 : Nat := 1335925357365996560484977

theorem tailTrace_7805116 : CollatzResearch.WordTrace tailWord_7805116 prefixEnd_7805116 1335925357365996560484977 := by
  unfold tailWord_7805116
  simp only [CollatzResearch.WordTrace]
  refine ⟨142337983795702607265873601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189783978394270143021164801 142337983795702607265873601)
  ·
    refine ⟨106753487846776955449405201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142337983795702607265873601 106753487846776955449405201)
    ·
      refine ⟨80065115885082716587053901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106753487846776955449405201 80065115885082716587053901)
      ·
        refine ⟨30024418456906018720145213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80065115885082716587053901 30024418456906018720145213)
        ·
          refine ⟨11259156921339757020054455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30024418456906018720145213 11259156921339757020054455)
          ·
            refine ⟨16888735382009635530081683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11259156921339757020054455 16888735382009635530081683)
            ·
              refine ⟨25333103073014453295122525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16888735382009635530081683 25333103073014453295122525)
              ·
                refine ⟨9499913652380419985670947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25333103073014453295122525 9499913652380419985670947)
                ·
                  refine ⟨14249870478570629978506421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9499913652380419985670947 14249870478570629978506421)
                  ·
                    refine ⟨1335925357365996560484977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14249870478570629978506421 1335925357365996560484977)
                    ·
                      rfl

theorem cell23_7805116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_7805116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805116 prefixEnd_7805116 := by exact prefixLift 7805116
  have htrace : WordTrace (prefixWord ++ tailWord_7805116) baseStart_7805116 baseEnd_7805116 := by
    simpa [prefixWord, tailWord_7805116, baseEnd_7805116] using wordTrace_append hprefix tailTrace_7805116
  have hstable : (prefixWord ++ tailWord_7805116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805116).length < 2 ^ (prefixWord ++ tailWord_7805116).sum := by decide
  have hdescent : baseEnd_7805116 < baseStart_7805116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805129 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 2, 4]
def baseStart_7805129 : Nat := 118140960795 + 7805129 * 2 ^ 59
def prefixEnd_7805129 : Nat := 4983230072969 + 3 ^ 40 * 7805129 * 2
def baseEnd_7805129 : Nat := 1335927582448832710197457

theorem tailTrace_7805129 : CollatzResearch.WordTrace tailWord_7805129 prefixEnd_7805129 1335927582448832710197457 := by
  unfold tailWord_7805129
  simp only [CollatzResearch.WordTrace]
  refine ⟨284676441740358117751970441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189784294493572078501313627 284676441740358117751970441)
  ·
    refine ⟨213507331305268588313977831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284676441740358117751970441 213507331305268588313977831)
    ·
      refine ⟨320260996957902882470966747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213507331305268588313977831 320260996957902882470966747)
      ·
        refine ⟨480391495436854323706450121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320260996957902882470966747 480391495436854323706450121)
        ·
          refine ⟨360293621577640742779837591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480391495436854323706450121 360293621577640742779837591)
          ·
            refine ⟨540440432366461114169756387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360293621577640742779837591 540440432366461114169756387)
            ·
              refine ⟨810660648549691671254634581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540440432366461114169756387 810660648549691671254634581)
              ·
                refine ⟨9499929475191699272515249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 810660648549691671254634581 9499929475191699272515249)
                ·
                  refine ⟨7124947106393774454386437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9499929475191699272515249 7124947106393774454386437)
                  ·
                    refine ⟨1335927582448832710197457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7124947106393774454386437 1335927582448832710197457)
                    ·
                      rfl

theorem cell23_7805129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 4].length) (baseStart_7805129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805129 prefixEnd_7805129 := by exact prefixLift 7805129
  have htrace : WordTrace (prefixWord ++ tailWord_7805129) baseStart_7805129 baseEnd_7805129 := by
    simpa [prefixWord, tailWord_7805129, baseEnd_7805129] using wordTrace_append hprefix tailTrace_7805129
  have hstable : (prefixWord ++ tailWord_7805129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805129).length < 2 ^ (prefixWord ++ tailWord_7805129).sum := by decide
  have hdescent : baseEnd_7805129 < baseStart_7805129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805159 : List Nat := [1, 1, 5, 3, 1, 2, 1, 9]
def baseStart_7805159 : Nat := 118140960795 + 7805159 * 2 ^ 59
def prefixEnd_7805159 : Nat := 4983230072969 + 3 ^ 40 * 7805159 * 2
def baseEnd_7805159 : Nat := 148436968583930852341379

theorem tailTrace_7805159 : CollatzResearch.WordTrace tailWord_7805159 prefixEnd_7805159 148436968583930852341379 := by
  unfold tailWord_7805159
  simp only [CollatzResearch.WordTrace]
  refine ⟨284677535930249432875562531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189785023953499621917041687 284677535930249432875562531)
  ·
    refine ⟨427016303895374149313343797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284677535930249432875562531 427016303895374149313343797)
    ·
      refine ⟨40032778490191326498125981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 427016303895374149313343797 40032778490191326498125981)
      ·
        refine ⟨15012291933821747436797243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40032778490191326498125981 15012291933821747436797243)
        ·
          refine ⟨22518437900732621155195865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15012291933821747436797243 22518437900732621155195865)
          ·
            refine ⟨16888828425549465866396899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22518437900732621155195865 16888828425549465866396899)
            ·
              refine ⟨25333242638324198799595349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16888828425549465866396899 25333242638324198799595349)
              ·
                refine ⟨148436968583930852341379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25333242638324198799595349 148436968583930852341379)
                ·
                  rfl

theorem cell23_7805159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 9].length) (baseStart_7805159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805159 prefixEnd_7805159 := by exact prefixLift 7805159
  have htrace : WordTrace (prefixWord ++ tailWord_7805159) baseStart_7805159 baseEnd_7805159 := by
    simpa [prefixWord, tailWord_7805159, baseEnd_7805159] using wordTrace_append hprefix tailTrace_7805159
  have hstable : (prefixWord ++ tailWord_7805159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805159).length < 2 ^ (prefixWord ++ tailWord_7805159).sum := by decide
  have hdescent : baseEnd_7805159 < baseStart_7805159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805169 : List Nat := [1, 2, 2, 2, 2, 1, 2, 4, 1, 3, 3]
def baseStart_7805169 : Nat := 118140960795 + 7805169 * 2 ^ 59
def prefixEnd_7805169 : Nat := 4983230072969 + 3 ^ 40 * 7805169 * 2
def baseEnd_7805169 : Nat := 4007803286572677974092187

theorem tailTrace_7805169 : CollatzResearch.WordTrace tailWord_7805169 prefixEnd_7805169 4007803286572677974092187 := by
  unfold tailWord_7805169
  simp only [CollatzResearch.WordTrace]
  refine ⟨284677900660213204583426561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189785267106808803055617707 284677900660213204583426561)
  ·
    refine ⟨213508425495159903437569921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284677900660213204583426561 213508425495159903437569921)
    ·
      refine ⟨160131319121369927578177441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213508425495159903437569921 160131319121369927578177441)
      ·
        refine ⟨120098489341027445683633081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160131319121369927578177441 120098489341027445683633081)
        ·
          refine ⟨90073867005770584262724811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120098489341027445683633081 90073867005770584262724811)
          ·
            refine ⟨135110800508655876394087217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90073867005770584262724811 135110800508655876394087217)
            ·
              refine ⟨101333100381491907295565413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135110800508655876394087217 101333100381491907295565413)
              ·
                refine ⟨18999956321529732617918515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101333100381491907295565413 18999956321529732617918515)
                ·
                  refine ⟨28499934482294598926877773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18999956321529732617918515 28499934482294598926877773)
                  ·
                    refine ⟨10687475430860474597579165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28499934482294598926877773 10687475430860474597579165)
                    ·
                      refine ⟨4007803286572677974092187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687475430860474597579165 4007803286572677974092187)
                      ·
                        rfl

theorem cell23_7805169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_7805169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805169 prefixEnd_7805169 := by exact prefixLift 7805169
  have htrace : WordTrace (prefixWord ++ tailWord_7805169) baseStart_7805169 baseEnd_7805169 := by
    simpa [prefixWord, tailWord_7805169, baseEnd_7805169] using wordTrace_append hprefix tailTrace_7805169
  have hstable : (prefixWord ++ tailWord_7805169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805169).length < 2 ^ (prefixWord ++ tailWord_7805169).sum := by decide
  have hdescent : baseEnd_7805169 < baseStart_7805169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805196 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 3, 3, 2]
def baseStart_7805196 : Nat := 118140960795 + 7805196 * 2 ^ 59
def prefixEnd_7805196 : Nat := 4983230072969 + 3 ^ 40 * 7805196 * 2
def baseEnd_7805196 : Nat := 4007817150550349368454563

theorem tailTrace_7805196 : CollatzResearch.WordTrace tailWord_7805196 prefixEnd_7805196 4007817150550349368454563 := by
  unfold tailWord_7805196
  simp only [CollatzResearch.WordTrace]
  refine ⟨142339442715557694097329721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189785923620743592129772961 142339442715557694097329721)
  ·
    refine ⟨106754582036668270572997291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142339442715557694097329721 106754582036668270572997291)
    ·
      refine ⟨160131873055002405859495937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106754582036668270572997291 160131873055002405859495937)
      ·
        refine ⟨120098904791251804394621953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160131873055002405859495937 120098904791251804394621953)
        ·
          refine ⟨90074178593438853295966465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120098904791251804394621953 90074178593438853295966465)
          ·
            refine ⟨67555633945079139971974849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90074178593438853295966465 67555633945079139971974849)
            ·
              refine ⟨50666725458809354978981137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67555633945079139971974849 50666725458809354978981137)
              ·
                refine ⟨38000044094107016234235853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50666725458809354978981137 38000044094107016234235853)
                ·
                  refine ⟨14250016535290131087838445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38000044094107016234235853 14250016535290131087838445)
                  ·
                    refine ⟨5343756200733799157939417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14250016535290131087838445 5343756200733799157939417)
                    ·
                      refine ⟨4007817150550349368454563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5343756200733799157939417 4007817150550349368454563)
                      ·
                        rfl

theorem cell23_7805196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_7805196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805196 prefixEnd_7805196 := by exact prefixLift 7805196
  have htrace : WordTrace (prefixWord ++ tailWord_7805196) baseStart_7805196 baseEnd_7805196 := by
    simpa [prefixWord, tailWord_7805196, baseEnd_7805196] using wordTrace_append hprefix tailTrace_7805196
  have hstable : (prefixWord ++ tailWord_7805196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805196).length < 2 ^ (prefixWord ++ tailWord_7805196).sum := by decide
  have hdescent : baseEnd_7805196 < baseStart_7805196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805232 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 11]
def baseStart_7805232 : Nat := 118140960795 + 7805232 * 2 ^ 59
def prefixEnd_7805232 : Nat := 4983230072969 + 3 ^ 40 * 7805232 * 2
def baseEnd_7805232 : Nat := 445315070650434580844933

theorem tailTrace_7805232 : CollatzResearch.WordTrace tailWord_7805232 prefixEnd_7805232 445315070650434580844933 := by
  unfold tailWord_7805232
  simp only [CollatzResearch.WordTrace]
  refine ⟨142340099229492483171484975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189786798972656644228646633 142340099229492483171484975)
  ·
    refine ⟨213510148844238724757227463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142340099229492483171484975 213510148844238724757227463)
    ·
      refine ⟨320265223266358087135841195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213510148844238724757227463 320265223266358087135841195)
      ·
        refine ⟨480397834899537130703761793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320265223266358087135841195 480397834899537130703761793)
        ·
          refine ⟨360298376174652848027821345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480397834899537130703761793 360298376174652848027821345)
          ·
            refine ⟨270223782130989636020866009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360298376174652848027821345 270223782130989636020866009)
            ·
              refine ⟨202667836598242227015649507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270223782130989636020866009 202667836598242227015649507)
              ·
                refine ⟨304001754897363340523474261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202667836598242227015649507 304001754897363340523474261)
                ·
                  refine ⟨445315070650434580844933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 304001754897363340523474261 445315070650434580844933)
                  ·
                    rfl

theorem cell23_7805232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 11].length) (baseStart_7805232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805232 prefixEnd_7805232 := by exact prefixLift 7805232
  have htrace : WordTrace (prefixWord ++ tailWord_7805232) baseStart_7805232 baseEnd_7805232 := by
    simpa [prefixWord, tailWord_7805232, baseEnd_7805232] using wordTrace_append hprefix tailTrace_7805232
  have hstable : (prefixWord ++ tailWord_7805232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805232).length < 2 ^ (prefixWord ++ tailWord_7805232).sum := by decide
  have hdescent : baseEnd_7805232 < baseStart_7805232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805246 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_7805246 : Nat := 118140960795 + 7805246 * 2 ^ 59
def prefixEnd_7805246 : Nat := 4983230072969 + 3 ^ 40 * 7805246 * 2
def baseEnd_7805246 : Nat := 4007842824583074172829333

theorem tailTrace_7805246 : CollatzResearch.WordTrace tailWord_7805246 prefixEnd_7805246 4007842824583074172829333 := by
  unfold tailWord_7805246
  simp only [CollatzResearch.WordTrace]
  refine ⟨35585088635116780841747449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189787139387289497822653061 35585088635116780841747449)
  ·
    refine ⟨26688816476337585631310587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35585088635116780841747449 26688816476337585631310587)
    ·
      refine ⟨40033224714506378446965881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26688816476337585631310587 40033224714506378446965881)
      ·
        refine ⟨30024918535879783835224411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40033224714506378446965881 30024918535879783835224411)
        ·
          refine ⟨45037377803819675752836617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30024918535879783835224411 45037377803819675752836617)
          ·
            refine ⟨33778033352864756814627463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45037377803819675752836617 33778033352864756814627463)
            ·
              refine ⟨50667050029297135221941195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33778033352864756814627463 50667050029297135221941195)
              ·
                refine ⟨76000575043945702832911793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50667050029297135221941195 76000575043945702832911793)
                ·
                  refine ⟨57000431282959277124683845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76000575043945702832911793 57000431282959277124683845)
                  ·
                    refine ⟨10687580865554864460878221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57000431282959277124683845 10687580865554864460878221)
                    ·
                      refine ⟨4007842824583074172829333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687580865554864460878221 4007842824583074172829333)
                      ·
                        rfl

theorem cell23_7805246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_7805246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805246 prefixEnd_7805246 := by exact prefixLift 7805246
  have htrace : WordTrace (prefixWord ++ tailWord_7805246) baseStart_7805246 baseEnd_7805246 := by
    simpa [prefixWord, tailWord_7805246, baseEnd_7805246] using wordTrace_append hprefix tailTrace_7805246
  have hstable : (prefixWord ++ tailWord_7805246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805246).length < 2 ^ (prefixWord ++ tailWord_7805246).sum := by decide
  have hdescent : baseEnd_7805246 < baseStart_7805246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805373 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 6]
def baseStart_7805373 : Nat := 118140960795 + 7805373 * 2 ^ 59
def prefixEnd_7805373 : Nat := 4983230072969 + 3 ^ 40 * 7805373 * 2
def baseEnd_7805373 : Nat := 445323115180688352882361

theorem tailTrace_7805373 : CollatzResearch.WordTrace tailWord_7805373 prefixEnd_7805373 445323115180688352882361 := by
  unfold tailWord_7805373
  simp only [CollatzResearch.WordTrace]
  refine ⟨284685341151474147423852773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189790227434316098282568515 284685341151474147423852773)
  ·
    refine ⟨53378501465901402641972395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284685341151474147423852773 53378501465901402641972395)
    ·
      refine ⟨80067752198852103962958593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53378501465901402641972395 80067752198852103962958593)
      ·
        refine ⟨60050814149139077972218945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80067752198852103962958593 60050814149139077972218945)
        ·
          refine ⟨45038110611854308479164209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60050814149139077972218945 45038110611854308479164209)
          ·
            refine ⟨33778582958890731359373157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45038110611854308479164209 33778582958890731359373157)
            ·
              refine ⟨6333484304792012129882467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33778582958890731359373157 6333484304792012129882467)
              ·
                refine ⟨9500226457188018194823701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6333484304792012129882467 9500226457188018194823701)
                ·
                  refine ⟨445323115180688352882361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9500226457188018194823701 445323115180688352882361)
                  ·
                    rfl

theorem cell23_7805373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_7805373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805373 prefixEnd_7805373 := by exact prefixLift 7805373
  have htrace : WordTrace (prefixWord ++ tailWord_7805373) baseStart_7805373 baseEnd_7805373 := by
    simpa [prefixWord, tailWord_7805373, baseEnd_7805373] using wordTrace_append hprefix tailTrace_7805373
  have hstable : (prefixWord ++ tailWord_7805373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805373).length < 2 ^ (prefixWord ++ tailWord_7805373).sum := by decide
  have hdescent : baseEnd_7805373 < baseStart_7805373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805386 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 3, 5]
def baseStart_7805386 : Nat := 118140960795 + 7805386 * 2 ^ 59
def prefixEnd_7805386 : Nat := 4983230072969 + 3 ^ 40 * 7805386 * 2
def baseEnd_7805386 : Nat := 1335971570624901208359563

theorem tailTrace_7805386 : CollatzResearch.WordTrace tailWord_7805386 prefixEnd_7805386 1335971570624901208359563 := by
  unfold tailWord_7805386
  simp only [CollatzResearch.WordTrace]
  refine ⟨71171453825106762661019003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189790543533618033762717341 71171453825106762661019003)
  ·
    refine ⟨106757180737660143991528505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71171453825106762661019003 106757180737660143991528505)
    ·
      refine ⟨80067885553245107993646379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106757180737660143991528505 80067885553245107993646379)
      ·
        refine ⟨120101828329867661990469569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80067885553245107993646379 120101828329867661990469569)
        ·
          refine ⟨90076371247400746492852177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120101828329867661990469569 90076371247400746492852177)
          ·
            refine ⟨67557278435550559869639133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90076371247400746492852177 67557278435550559869639133)
            ·
              refine ⟨25333979413331459951114675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67557278435550559869639133 25333979413331459951114675)
              ·
                refine ⟨38000969119997189926672013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25333979413331459951114675 38000969119997189926672013)
                ·
                  refine ⟨14250363419998946222502005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38000969119997189926672013 14250363419998946222502005)
                  ·
                    refine ⟨1335971570624901208359563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14250363419998946222502005 1335971570624901208359563)
                    ·
                      rfl

theorem cell23_7805386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_7805386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805386 prefixEnd_7805386 := by exact prefixLift 7805386
  have htrace : WordTrace (prefixWord ++ tailWord_7805386) baseStart_7805386 baseEnd_7805386 := by
    simpa [prefixWord, tailWord_7805386, baseEnd_7805386] using wordTrace_append hprefix tailTrace_7805386
  have hstable : (prefixWord ++ tailWord_7805386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805386).length < 2 ^ (prefixWord ++ tailWord_7805386).sum := by decide
  have hdescent : baseEnd_7805386 < baseStart_7805386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805400 : List Nat := [2, 1, 2, 2, 2, 1, 1, 7, 1, 1, 3]
def baseStart_7805400 : Nat := 118140960795 + 7805400 * 2 ^ 59
def prefixEnd_7805400 : Nat := 4983230072969 + 3 ^ 40 * 7805400 * 2
def baseEnd_7805400 : Nat := 4007921900603866570303625

theorem tailTrace_7805400 : CollatzResearch.WordTrace tailWord_7805400 prefixEnd_7805400 4007921900603866570303625 := by
  unfold tailWord_7805400
  simp only [CollatzResearch.WordTrace]
  refine ⟨142343162961188165517542827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189790883948250887356723769 142343162961188165517542827)
  ·
    refine ⟨213514744441782248276314241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142343162961188165517542827 213514744441782248276314241)
    ·
      refine ⟨160136058331336686207235681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213514744441782248276314241 160136058331336686207235681)
      ·
        refine ⟨120102043748502514655426761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160136058331336686207235681 120102043748502514655426761)
        ·
          refine ⟨90076532811376885991570071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120102043748502514655426761 90076532811376885991570071)
          ·
            refine ⟨135114799217065328987355107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90076532811376885991570071 135114799217065328987355107)
            ·
              refine ⟨202672198825597993481032661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135114799217065328987355107 202672198825597993481032661)
              ·
                refine ⟨4750129659974952972211703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 202672198825597993481032661 4750129659974952972211703)
                ·
                  refine ⟨7125194489962429458317555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4750129659974952972211703 7125194489962429458317555)
                  ·
                    refine ⟨10687791734943644187476333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7125194489962429458317555 10687791734943644187476333)
                    ·
                      refine ⟨4007921900603866570303625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687791734943644187476333 4007921900603866570303625)
                      ·
                        rfl

theorem cell23_7805400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 1, 1, 3].length) (baseStart_7805400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805400 prefixEnd_7805400 := by exact prefixLift 7805400
  have htrace : WordTrace (prefixWord ++ tailWord_7805400) baseStart_7805400 baseEnd_7805400 := by
    simpa [prefixWord, tailWord_7805400, baseEnd_7805400] using wordTrace_append hprefix tailTrace_7805400
  have hstable : (prefixWord ++ tailWord_7805400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805400).length < 2 ^ (prefixWord ++ tailWord_7805400).sum := by decide
  have hdescent : baseEnd_7805400 < baseStart_7805400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805433 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 2, 4]
def baseStart_7805433 : Nat := 118140960795 + 7805433 * 2 ^ 59
def prefixEnd_7805433 : Nat := 4983230072969 + 3 ^ 40 * 7805433 * 2
def baseEnd_7805433 : Nat := 1335979615155154980396991

theorem tailTrace_7805433 : CollatzResearch.WordTrace tailWord_7805433 prefixEnd_7805433 1335979615155154980396991 := by
  unfold tailWord_7805433
  simp only [CollatzResearch.WordTrace]
  refine ⟨284687529531256777671036953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189791686354171185114024635 284687529531256777671036953)
  ·
    refine ⟨213515647148442583253277715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284687529531256777671036953 213515647148442583253277715)
    ·
      refine ⟨320273470722663874879916573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213515647148442583253277715 320273470722663874879916573)
      ·
        refine ⟨120102551520998953079968715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320273470722663874879916573 120102551520998953079968715)
        ·
          refine ⟨180153827281498429619953073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120102551520998953079968715 180153827281498429619953073)
          ·
            refine ⟨135115370461123822214964805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180153827281498429619953073 135115370461123822214964805)
            ·
              refine ⟨25334131961460716665305901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135115370461123822214964805 25334131961460716665305901)
              ·
                refine ⟨9500299485547768749489713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25334131961460716665305901 9500299485547768749489713)
                ·
                  refine ⟨7125224614160826562117285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9500299485547768749489713 7125224614160826562117285)
                  ·
                    refine ⟨1335979615155154980396991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7125224614160826562117285 1335979615155154980396991)
                    ·
                      rfl

theorem cell23_7805433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 4].length) (baseStart_7805433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805433 prefixEnd_7805433 := by exact prefixLift 7805433
  have htrace : WordTrace (prefixWord ++ tailWord_7805433) baseStart_7805433 baseEnd_7805433 := by
    simpa [prefixWord, tailWord_7805433, baseEnd_7805433] using wordTrace_append hprefix tailTrace_7805433
  have hstable : (prefixWord ++ tailWord_7805433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805433).length < 2 ^ (prefixWord ++ tailWord_7805433).sum := by decide
  have hdescent : baseEnd_7805433 < baseStart_7805433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805443 : List Nat := [1, 1, 1, 3, 2, 1, 4, 4, 1, 2, 3]
def baseStart_7805443 : Nat := 118140960795 + 7805443 * 2 ^ 59
def prefixEnd_7805443 : Nat := 4983230072969 + 3 ^ 40 * 7805443 * 2
def baseEnd_7805443 : Nat := 4007943980272009902065927

theorem tailTrace_7805443 : CollatzResearch.WordTrace tailWord_7805443 prefixEnd_7805443 4007943980272009902065927 := by
  unfold tailWord_7805443
  simp only [CollatzResearch.WordTrace]
  refine ⟨284687894261220549378900983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189791929507480366252600655 284687894261220549378900983)
  ·
    refine ⟨427031841391830824068351475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284687894261220549378900983 427031841391830824068351475)
    ·
      refine ⟨640547762087746236102527213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427031841391830824068351475 640547762087746236102527213)
      ·
        refine ⟨240205410782904838538447705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640547762087746236102527213 240205410782904838538447705)
        ·
          refine ⟨180154058087178628903835779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240205410782904838538447705 180154058087178628903835779)
          ·
            refine ⟨270231087130767943355753669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180154058087178628903835779 270231087130767943355753669)
            ·
              refine ⟨50668328837018989379203813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270231087130767943355753669 50668328837018989379203813)
              ·
                refine ⟨9500311656941060508600715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50668328837018989379203813 9500311656941060508600715)
                ·
                  refine ⟨14250467485411590762901073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9500311656941060508600715 14250467485411590762901073)
                  ·
                    refine ⟨10687850614058693072175805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14250467485411590762901073 10687850614058693072175805)
                    ·
                      refine ⟨4007943980272009902065927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687850614058693072175805 4007943980272009902065927)
                      ·
                        rfl

theorem cell23_7805443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_7805443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805443 prefixEnd_7805443 := by exact prefixLift 7805443
  have htrace : WordTrace (prefixWord ++ tailWord_7805443) baseStart_7805443 baseEnd_7805443 := by
    simpa [prefixWord, tailWord_7805443, baseEnd_7805443] using wordTrace_append hprefix tailTrace_7805443
  have hstable : (prefixWord ++ tailWord_7805443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805443).length < 2 ^ (prefixWord ++ tailWord_7805443).sum := by decide
  have hdescent : baseEnd_7805443 < baseStart_7805443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805456 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 3]
def baseStart_7805456 : Nat := 118140960795 + 7805456 * 2 ^ 59
def prefixEnd_7805456 : Nat := 4983230072969 + 3 ^ 40 * 7805456 * 2
def baseEnd_7805456 : Nat := 4007950655520518351203367

theorem tailTrace_7805456 : CollatzResearch.WordTrace tailWord_7805456 prefixEnd_7805456 4007950655520518351203367 := by
  unfold tailWord_7805456
  simp only [CollatzResearch.WordTrace]
  refine ⟨142344184205086726299562111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189792245606782301732749481 142344184205086726299562111)
  ·
    refine ⟨213516276307630089449343167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142344184205086726299562111 213516276307630089449343167)
    ·
      refine ⟨320274414461445134174014751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213516276307630089449343167 320274414461445134174014751)
      ·
        refine ⟨480411621692167701261022127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320274414461445134174014751 480411621692167701261022127)
        ·
          refine ⟨720617432538251551891533191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480411621692167701261022127 720617432538251551891533191)
          ·
            refine ⟨1080926148807377327837299787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720617432538251551891533191 1080926148807377327837299787)
            ·
              refine ⟨1621389223211065991755949681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080926148807377327837299787 1621389223211065991755949681)
              ·
                refine ⟨1216041917408299493816962261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1621389223211065991755949681 1216041917408299493816962261)
                ·
                  refine ⟨28500982439257019386335053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1216041917408299493816962261 28500982439257019386335053)
                  ·
                    refine ⟨10687868414721382269875645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28500982439257019386335053 10687868414721382269875645)
                    ·
                      refine ⟨4007950655520518351203367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687868414721382269875645 4007950655520518351203367)
                      ·
                        rfl

theorem cell23_7805456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 3].length) (baseStart_7805456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805456 prefixEnd_7805456 := by exact prefixLift 7805456
  have htrace : WordTrace (prefixWord ++ tailWord_7805456) baseStart_7805456 baseEnd_7805456 := by
    simpa [prefixWord, tailWord_7805456, baseEnd_7805456] using wordTrace_append hprefix tailTrace_7805456
  have hstable : (prefixWord ++ tailWord_7805456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805456).length < 2 ^ (prefixWord ++ tailWord_7805456).sum := by decide
  have hdescent : baseEnd_7805456 < baseStart_7805456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805463 : List Nat := [1, 1, 3, 6, 1, 1, 10]
def baseStart_7805463 : Nat := 118140960795 + 7805463 * 2 ^ 59
def prefixEnd_7805463 : Nat := 4983230072969 + 3 ^ 40 * 7805463 * 2
def baseEnd_7805463 : Nat := 49480916665248145973035

theorem tailTrace_7805463 : CollatzResearch.WordTrace tailWord_7805463 prefixEnd_7805463 49480916665248145973035 := by
  unfold tailWord_7805463
  simp only [CollatzResearch.WordTrace]
  refine ⟨284688623721148092794629043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189792415814098728529752695 284688623721148092794629043)
  ·
    refine ⟨427032935581722139191943565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284688623721148092794629043 427032935581722139191943565)
    ·
      refine ⟨160137350843145802196978837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427032935581722139191943565 160137350843145802196978837)
      ·
        refine ⟨7506438320772459477983383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160137350843145802196978837 7506438320772459477983383)
        ·
          refine ⟨11259657481158689216975075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7506438320772459477983383 11259657481158689216975075)
          ·
            refine ⟨16889486221738033825462613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11259657481158689216975075 16889486221738033825462613)
            ·
              refine ⟨49480916665248145973035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16889486221738033825462613 49480916665248145973035)
              ·
                rfl

theorem cell23_7805463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 10].length) (baseStart_7805463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805463 prefixEnd_7805463 := by exact prefixLift 7805463
  have htrace : WordTrace (prefixWord ++ tailWord_7805463) baseStart_7805463 baseEnd_7805463 := by
    simpa [prefixWord, tailWord_7805463, baseEnd_7805463] using wordTrace_append hprefix tailTrace_7805463
  have hstable : (prefixWord ++ tailWord_7805463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805463).length < 2 ^ (prefixWord ++ tailWord_7805463).sum := by decide
  have hdescent : baseEnd_7805463 < baseStart_7805463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805483 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 5, 3, 2]
def baseStart_7805483 : Nat := 118140960795 + 7805483 * 2 ^ 59
def prefixEnd_7805483 : Nat := 4983230072969 + 3 ^ 40 * 7805483 * 2
def baseEnd_7805483 : Nat := 4007964519498189745565743

theorem tailTrace_7805483 : CollatzResearch.WordTrace tailWord_7805483 prefixEnd_7805483 4007964519498189745565743 := by
  unfold tailWord_7805483
  simp only [CollatzResearch.WordTrace]
  refine ⟨284689353181075636210357103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189792902120717090806904735 284689353181075636210357103)
  ·
    refine ⟨427034029771613454315535655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284689353181075636210357103 427034029771613454315535655)
    ·
      refine ⟨640551044657420181473303483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427034029771613454315535655 640551044657420181473303483)
      ·
        refine ⟨960826566986130272209955225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640551044657420181473303483 960826566986130272209955225)
        ·
          refine ⟨720619925239597704157466419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 960826566986130272209955225 720619925239597704157466419)
          ·
            refine ⟨1080929887859396556236199629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720619925239597704157466419 1080929887859396556236199629)
            ·
              refine ⟨405348707947273708588574861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1080929887859396556236199629 405348707947273708588574861)
              ·
                refine ⟨152005765480227640720715573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405348707947273708588574861 152005765480227640720715573)
                ·
                  refine ⟨14250540513771341317567085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152005765480227640720715573 14250540513771341317567085)
                  ·
                    refine ⟨5343952692664252994087657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14250540513771341317567085 5343952692664252994087657)
                    ·
                      refine ⟨4007964519498189745565743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5343952692664252994087657 4007964519498189745565743)
                      ·
                        rfl

theorem cell23_7805483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 3, 2].length) (baseStart_7805483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805483 prefixEnd_7805483 := by exact prefixLift 7805483
  have htrace : WordTrace (prefixWord ++ tailWord_7805483) baseStart_7805483 baseEnd_7805483 := by
    simpa [prefixWord, tailWord_7805483, baseEnd_7805483] using wordTrace_append hprefix tailTrace_7805483
  have hstable : (prefixWord ++ tailWord_7805483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805483).length < 2 ^ (prefixWord ++ tailWord_7805483).sum := by decide
  have hdescent : baseEnd_7805483 < baseStart_7805483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805490 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3]
def baseStart_7805490 : Nat := 118140960795 + 7805490 * 2 ^ 59
def prefixEnd_7805490 : Nat := 4983230072969 + 3 ^ 40 * 7805490 * 2
def baseEnd_7805490 : Nat := 4007968113862771218178211

theorem tailTrace_7805490 : CollatzResearch.WordTrace tailWord_7805490 prefixEnd_7805490 4007968113862771218178211 := by
  unfold tailWord_7805490
  simp only [CollatzResearch.WordTrace]
  refine ⟨71172402123012569101465481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189793072328033517603907949 71172402123012569101465481)
  ·
    refine ⟨53379301592259426826099111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71172402123012569101465481 53379301592259426826099111)
    ·
      refine ⟨80068952388389140239148667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53379301592259426826099111 80068952388389140239148667)
      ·
        refine ⟨120103428582583710358723001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80068952388389140239148667 120103428582583710358723001)
        ·
          refine ⟨90077571436937782769042251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120103428582583710358723001 90077571436937782769042251)
          ·
            refine ⟨135116357155406674153563377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90077571436937782769042251 135116357155406674153563377)
            ·
              refine ⟨101337267866555005615172533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135116357155406674153563377 101337267866555005615172533)
              ·
                refine ⟨9500368862489531776422425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101337267866555005615172533 9500368862489531776422425)
                ·
                  refine ⟨7125276646867148832316819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9500368862489531776422425 7125276646867148832316819)
                  ·
                    refine ⟨10687914970300723248475229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7125276646867148832316819 10687914970300723248475229)
                    ·
                      refine ⟨4007968113862771218178211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687914970300723248475229 4007968113862771218178211)
                      ·
                        rfl

theorem cell23_7805490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_7805490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805490 prefixEnd_7805490 := by exact prefixLift 7805490
  have htrace : WordTrace (prefixWord ++ tailWord_7805490) baseStart_7805490 baseEnd_7805490 := by
    simpa [prefixWord, tailWord_7805490, baseEnd_7805490] using wordTrace_append hprefix tailTrace_7805490
  have hstable : (prefixWord ++ tailWord_7805490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805490).length < 2 ^ (prefixWord ++ tailWord_7805490).sum := by decide
  have hdescent : baseEnd_7805490 < baseStart_7805490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805541 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 2, 1, 3]
def baseStart_7805541 : Nat := 118140960795 + 7805541 * 2 ^ 59
def prefixEnd_7805541 : Nat := 4983230072969 + 3 ^ 40 * 7805541 * 2
def baseEnd_7805541 : Nat := 4007994301376150518640477

theorem tailTrace_7805541 : CollatzResearch.WordTrace tailWord_7805541 prefixEnd_7805541 4007994301376150518640477 := by
  unfold tailWord_7805541
  simp only [CollatzResearch.WordTrace]
  refine ⟨284691468614865512115968477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189794312409910341410645651 284691468614865512115968477)
  ·
    refine ⟨106759300730574567043488179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284691468614865512115968477 106759300730574567043488179)
    ·
      refine ⟨160138951095861850565232269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106759300730574567043488179 160138951095861850565232269)
      ·
        refine ⟨60052106660948193961962101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160138951095861850565232269 60052106660948193961962101)
        ·
          refine ⟨5629884999463893183933947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60052106660948193961962101 5629884999463893183933947)
          ·
            refine ⟨8444827499195839775900921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5629884999463893183933947 8444827499195839775900921)
            ·
              refine ⟨6333620624396879831925691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8444827499195839775900921 6333620624396879831925691)
              ·
                refine ⟨9500430936595319747888537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6333620624396879831925691 9500430936595319747888537)
                ·
                  refine ⟨7125323202446489810916403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9500430936595319747888537 7125323202446489810916403)
                  ·
                    refine ⟨10687984803669734716374605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7125323202446489810916403 10687984803669734716374605)
                    ·
                      refine ⟨4007994301376150518640477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10687984803669734716374605 4007994301376150518640477)
                      ·
                        rfl

theorem cell23_7805541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_7805541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805541 prefixEnd_7805541 := by exact prefixLift 7805541
  have htrace : WordTrace (prefixWord ++ tailWord_7805541) baseStart_7805541 baseEnd_7805541 := by
    simpa [prefixWord, tailWord_7805541, baseEnd_7805541] using wordTrace_append hprefix tailTrace_7805541
  have hstable : (prefixWord ++ tailWord_7805541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805541).length < 2 ^ (prefixWord ++ tailWord_7805541).sum := by decide
  have hdescent : baseEnd_7805541 < baseStart_7805541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805630 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_7805630 : Nat := 118140960795 + 7805630 * 2 ^ 59
def prefixEnd_7805630 : Nat := 4983230072969 + 3 ^ 40 * 7805630 * 2
def baseEnd_7805630 : Nat := 1336013333718133556809189

theorem tailTrace_7805630 : CollatzResearch.WordTrace tailWord_7805630 prefixEnd_7805630 1336013333718133556809189 := by
  unfold tailWord_7805630
  simp only [CollatzResearch.WordTrace]
  refine ⟨35586839338942885039494793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189796476474362053543972229 35586839338942885039494793)
  ·
    refine ⟨26690129504207163779621095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35586839338942885039494793 26690129504207163779621095)
    ·
      refine ⟨40035194256310745669431643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26690129504207163779621095 40035194256310745669431643)
      ·
        refine ⟨60052791384466118504147465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40035194256310745669431643 60052791384466118504147465)
        ·
          refine ⟨45039593538349588878110599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60052791384466118504147465 45039593538349588878110599)
          ·
            refine ⟨67559390307524383317165899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45039593538349588878110599 67559390307524383317165899)
            ·
              refine ⟨101339085461286574975748849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67559390307524383317165899 101339085461286574975748849)
              ·
                refine ⟨76004314095964931231811637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101339085461286574975748849 76004314095964931231811637)
                ·
                  refine ⟨7125404446496712302982341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76004314095964931231811637 7125404446496712302982341)
                  ·
                    refine ⟨1336013333718133556809189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7125404446496712302982341 1336013333718133556809189)
                    ·
                      rfl

theorem cell23_7805630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_7805630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805630 prefixEnd_7805630 := by exact prefixLift 7805630
  have htrace : WordTrace (prefixWord ++ tailWord_7805630) baseStart_7805630 baseEnd_7805630 := by
    simpa [prefixWord, tailWord_7805630, baseEnd_7805630] using wordTrace_append hprefix tailTrace_7805630
  have hstable : (prefixWord ++ tailWord_7805630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805630).length < 2 ^ (prefixWord ++ tailWord_7805630).sum := by decide
  have hdescent : baseEnd_7805630 < baseStart_7805630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805673 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 3, 5]
def baseStart_7805673 : Nat := 118140960795 + 7805673 * 2 ^ 59
def prefixEnd_7805673 : Nat := 4983230072969 + 3 ^ 40 * 7805673 * 2
def baseEnd_7805673 : Nat := 1336020693607514667396623

theorem tailTrace_7805673 : CollatzResearch.WordTrace tailWord_7805673 prefixEnd_7805673 1336020693607514667396623 := by
  unfold tailWord_7805673
  simp only [CollatzResearch.WordTrace]
  refine ⟨284696283050387298659773673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189797522033591532439849115 284696283050387298659773673)
  ·
    refine ⟨213522212287790473994830255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284696283050387298659773673 213522212287790473994830255)
    ·
      refine ⟨320283318431685710992245383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213522212287790473994830255 320283318431685710992245383)
      ·
        refine ⟨480424977647528566488368075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320283318431685710992245383 480424977647528566488368075)
        ·
          refine ⟨720637466471292849732552113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480424977647528566488368075 720637466471292849732552113)
          ·
            refine ⟨540478099853469637299414085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720637466471292849732552113 540478099853469637299414085)
            ·
              refine ⟨101339643722525556993640141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 540478099853469637299414085 101339643722525556993640141)
              ·
                refine ⟨38002366395947083872615053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101339643722525556993640141 38002366395947083872615053)
                ·
                  refine ⟨14250887398480156452230645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38002366395947083872615053 14250887398480156452230645)
                  ·
                    refine ⟨1336020693607514667396623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14250887398480156452230645 1336020693607514667396623)
                    ·
                      rfl

theorem cell23_7805673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_7805673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805673 prefixEnd_7805673 := by exact prefixLift 7805673
  have htrace : WordTrace (prefixWord ++ tailWord_7805673) baseStart_7805673 baseEnd_7805673 := by
    simpa [prefixWord, tailWord_7805673, baseEnd_7805673] using wordTrace_append hprefix tailTrace_7805673
  have hstable : (prefixWord ++ tailWord_7805673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805673).length < 2 ^ (prefixWord ++ tailWord_7805673).sum := by decide
  have hdescent : baseEnd_7805673 < baseStart_7805673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805680 : List Nat := [2, 1, 1, 1, 3, 1, 3, 3, 1, 5, 2]
def baseStart_7805680 : Nat := 118140960795 + 7805680 * 2 ^ 59
def prefixEnd_7805680 : Nat := 4983230072969 + 3 ^ 40 * 7805680 * 2
def baseEnd_7805680 : Nat := 4008065675187125474802337

theorem tailTrace_7805680 : CollatzResearch.WordTrace tailWord_7805680 prefixEnd_7805680 4008065675187125474802337 := by
  unfold tailWord_7805680
  simp only [CollatzResearch.WordTrace]
  refine ⟨142348269180680969427639247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189797692240907959236852329 142348269180680969427639247)
  ·
    refine ⟨213522403771021454141458871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142348269180680969427639247 213522403771021454141458871)
    ·
      refine ⟨320283605656532181212188307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213522403771021454141458871 320283605656532181212188307)
      ·
        refine ⟨480425408484798271818282461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320283605656532181212188307 480425408484798271818282461)
        ·
          refine ⟨180159528181799351931855923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 480425408484798271818282461 180159528181799351931855923)
          ·
            refine ⟨270239292272699027897783885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180159528181799351931855923 270239292272699027897783885)
            ·
              refine ⟨101339734602262135461668957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270239292272699027897783885 101339734602262135461668957)
              ·
                refine ⟨38002400475848300798125859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101339734602262135461668957 38002400475848300798125859)
                ·
                  refine ⟨57003600713772451197188789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38002400475848300798125859 57003600713772451197188789)
                  ·
                    refine ⟨5344087566916167299736449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57003600713772451197188789 5344087566916167299736449)
                    ·
                      refine ⟨4008065675187125474802337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344087566916167299736449 4008065675187125474802337)
                      ·
                        rfl

theorem cell23_7805680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 5, 2].length) (baseStart_7805680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805680 prefixEnd_7805680 := by exact prefixLift 7805680
  have htrace : WordTrace (prefixWord ++ tailWord_7805680) baseStart_7805680 baseEnd_7805680 := by
    simpa [prefixWord, tailWord_7805680, baseEnd_7805680] using wordTrace_append hprefix tailTrace_7805680
  have hstable : (prefixWord ++ tailWord_7805680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805680).length < 2 ^ (prefixWord ++ tailWord_7805680).sum := by decide
  have hdescent : baseEnd_7805680 < baseStart_7805680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805690 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 1, 5]
def baseStart_7805690 : Nat := 118140960795 + 7805690 * 2 ^ 59
def prefixEnd_7805690 : Nat := 4983230072969 + 3 ^ 40 * 7805690 * 2
def baseEnd_7805690 : Nat := 1336023603331223478559097

theorem tailTrace_7805690 : CollatzResearch.WordTrace tailWord_7805690 prefixEnd_7805690 1336023603331223478559097 := by
  unfold tailWord_7805690
  simp only [CollatzResearch.WordTrace]
  refine ⟨71174225772831427640785631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189797935394217140375428349 71174225772831427640785631)
  ·
    refine ⟨106761338659247141461178447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71174225772831427640785631 106761338659247141461178447)
    ·
      refine ⟨160142007988870712191767671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106761338659247141461178447 160142007988870712191767671)
      ·
        refine ⟨240213011983306068287651507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160142007988870712191767671 240213011983306068287651507)
        ·
          refine ⟨360319517974959102431477261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240213011983306068287651507 360319517974959102431477261)
          ·
            refine ⟨135119819240609663411803973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360319517974959102431477261 135119819240609663411803973)
            ·
              refine ⟨25334966107614311889713245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135119819240609663411803973 25334966107614311889713245)
              ·
                refine ⟨9500612290355366958642467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25334966107614311889713245 9500612290355366958642467)
                ·
                  refine ⟨14250918435533050437963701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9500612290355366958642467 14250918435533050437963701)
                  ·
                    refine ⟨1336023603331223478559097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14250918435533050437963701 1336023603331223478559097)
                    ·
                      rfl

theorem cell23_7805690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_7805690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805690 prefixEnd_7805690 := by exact prefixLift 7805690
  have htrace : WordTrace (prefixWord ++ tailWord_7805690) baseStart_7805690 baseEnd_7805690 := by
    simpa [prefixWord, tailWord_7805690, baseEnd_7805690] using wordTrace_append hprefix tailTrace_7805690
  have hstable : (prefixWord ++ tailWord_7805690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805690).length < 2 ^ (prefixWord ++ tailWord_7805690).sum := by decide
  have hdescent : baseEnd_7805690 < baseStart_7805690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805704 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 3, 1, 3]
def baseStart_7805704 : Nat := 118140960795 + 7805704 * 2 ^ 59
def prefixEnd_7805704 : Nat := 4983230072969 + 3 ^ 40 * 7805704 * 2
def baseEnd_7805704 : Nat := 4008077998722833380902227

theorem tailTrace_7805704 : CollatzResearch.WordTrace tailWord_7805704 prefixEnd_7805704 4008077998722833380902227 := by
  unfold tailWord_7805704
  simp only [CollatzResearch.WordTrace]
  refine ⟨142348706856637495477076083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189798275808849993969434777 142348706856637495477076083)
  ·
    refine ⟨213523060284956243215614125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142348706856637495477076083 213523060284956243215614125)
    ·
      refine ⟨80071147606858591205855297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213523060284956243215614125 80071147606858591205855297)
      ·
        refine ⟨60053360705143943404391473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80071147606858591205855297 60053360705143943404391473)
        ·
          refine ⟨45040020528857957553293605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60053360705143943404391473 45040020528857957553293605)
          ·
            refine ⟨8445003849160867041242551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45040020528857957553293605 8445003849160867041242551)
            ·
              refine ⟨12667505773741300561863827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8445003849160867041242551 12667505773741300561863827)
              ·
                refine ⟨19001258660611950842795741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12667505773741300561863827 19001258660611950842795741)
                ·
                  refine ⟨7125471997729481566048403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19001258660611950842795741 7125471997729481566048403)
                  ·
                    refine ⟨10688207996594222349072605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7125471997729481566048403 10688207996594222349072605)
                    ·
                      refine ⟨4008077998722833380902227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10688207996594222349072605 4008077998722833380902227)
                      ·
                        rfl

theorem cell23_7805704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_7805704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805704 prefixEnd_7805704 := by exact prefixLift 7805704
  have htrace : WordTrace (prefixWord ++ tailWord_7805704) baseStart_7805704 baseEnd_7805704 := by
    simpa [prefixWord, tailWord_7805704, baseEnd_7805704] using wordTrace_append hprefix tailTrace_7805704
  have hstable : (prefixWord ++ tailWord_7805704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805704).length < 2 ^ (prefixWord ++ tailWord_7805704).sum := by decide
  have hdescent : baseEnd_7805704 < baseStart_7805704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805710 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_7805710 : Nat := 118140960795 + 7805710 * 2 ^ 59
def prefixEnd_7805710 : Nat := 4983230072969 + 3 ^ 40 * 7805710 * 2
def baseEnd_7805710 : Nat := 4008081079606760357427199

theorem tailTrace_7805710 : CollatzResearch.WordTrace tailWord_7805710 prefixEnd_7805710 4008081079606760357427199 := by
  unfold tailWord_7805710
  simp only [CollatzResearch.WordTrace]
  refine ⟨35587204068906656747358823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189798421700835502652580389 35587204068906656747358823)
  ·
    refine ⟨53380806103359985121038235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35587204068906656747358823 53380806103359985121038235)
    ·
      refine ⟨80071209155039977681557353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53380806103359985121038235 80071209155039977681557353)
      ·
        refine ⟨60053406866279983261168015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80071209155039977681557353 60053406866279983261168015)
        ·
          refine ⟨90080110299419974891752023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60053406866279983261168015 90080110299419974891752023)
          ·
            refine ⟨135120165449129962337628035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90080110299419974891752023 135120165449129962337628035)
            ·
              refine ⟨202680248173694943506442053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135120165449129962337628035 202680248173694943506442053)
              ·
                refine ⟨38002546532567801907457885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202680248173694943506442053 38002546532567801907457885)
                ·
                  refine ⟨14250954949712925715296707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38002546532567801907457885 14250954949712925715296707)
                  ·
                    refine ⟨21376432424569388572945061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14250954949712925715296707 21376432424569388572945061)
                    ·
                      refine ⟨4008081079606760357427199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21376432424569388572945061 4008081079606760357427199)
                      ·
                        rfl

theorem cell23_7805710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_7805710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805710 prefixEnd_7805710 := by exact prefixLift 7805710
  have htrace : WordTrace (prefixWord ++ tailWord_7805710) baseStart_7805710 baseEnd_7805710 := by
    simpa [prefixWord, tailWord_7805710, baseEnd_7805710] using wordTrace_append hprefix tailTrace_7805710
  have hstable : (prefixWord ++ tailWord_7805710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805710).length < 2 ^ (prefixWord ++ tailWord_7805710).sum := by decide
  have hdescent : baseEnd_7805710 < baseStart_7805710 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805727 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 4]
def baseStart_7805727 : Nat := 118140960795 + 7805727 * 2 ^ 59
def prefixEnd_7805727 : Nat := 4983230072969 + 3 ^ 40 * 7805727 * 2
def baseEnd_7805727 : Nat := 4008089808777886790914621

theorem tailTrace_7805727 : CollatzResearch.WordTrace tailWord_7805727 prefixEnd_7805727 4008089808777886790914621 := by
  unfold tailWord_7805727
  simp only [CollatzResearch.WordTrace]
  refine ⟨284698252592191665882239435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189798835061461110588159623 284698252592191665882239435)
  ·
    refine ⟨427047378888287498823359153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284698252592191665882239435 427047378888287498823359153)
    ·
      refine ⟨320285534166215624117519365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427047378888287498823359153 320285534166215624117519365)
      ·
        refine ⟨60053537656165429522034881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 320285534166215624117519365 60053537656165429522034881)
        ·
          refine ⟨45040153242124072141526161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60053537656165429522034881 45040153242124072141526161)
          ·
            refine ⟨33780114931593054106144621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45040153242124072141526161 33780114931593054106144621)
            ·
              refine ⟨12667543099347395289804233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33780114931593054106144621 12667543099347395289804233)
              ·
                refine ⟨9500657324510546467353175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12667543099347395289804233 9500657324510546467353175)
                ·
                  refine ⟨14250985986765819701029763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9500657324510546467353175 14250985986765819701029763)
                  ·
                    refine ⟨21376478980148729551544645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14250985986765819701029763 21376478980148729551544645)
                    ·
                      refine ⟨4008089808777886790914621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21376478980148729551544645 4008089808777886790914621)
                      ·
                        rfl

theorem cell23_7805727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_7805727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805727 prefixEnd_7805727 := by exact prefixLift 7805727
  have htrace : WordTrace (prefixWord ++ tailWord_7805727) baseStart_7805727 baseEnd_7805727 := by
    simpa [prefixWord, tailWord_7805727, baseEnd_7805727] using wordTrace_append hprefix tailTrace_7805727
  have hstable : (prefixWord ++ tailWord_7805727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805727).length < 2 ^ (prefixWord ++ tailWord_7805727).sum := by decide
  have hdescent : baseEnd_7805727 < baseStart_7805727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805733 : List Nat := [1, 3, 1, 2, 3, 1, 1, 11]
def baseStart_7805733 : Nat := 118140960795 + 7805733 * 2 ^ 59
def prefixEnd_7805733 : Nat := 4983230072969 + 3 ^ 40 * 7805733 * 2
def baseEnd_7805733 : Nat := 148447884802289398794059

theorem tailTrace_7805733 : CollatzResearch.WordTrace tailWord_7805733 prefixEnd_7805733 148447884802289398794059 := by
  unfold tailWord_7805733
  simp only [CollatzResearch.WordTrace]
  refine ⟨284698471430169928906957853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189798980953446619271305235 284698471430169928906957853)
  ·
    refine ⟨106761926786313723340109195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284698471430169928906957853 106761926786313723340109195)
    ·
      refine ⟨160142890179470585010163793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106761926786313723340109195 160142890179470585010163793)
      ·
        refine ⟨120107167634602938757622845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160142890179470585010163793 120107167634602938757622845)
        ·
          refine ⟨45040187862976102034108567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120107167634602938757622845 45040187862976102034108567)
          ·
            refine ⟨67560281794464153051162851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45040187862976102034108567 67560281794464153051162851)
            ·
              refine ⟨101340422691696229576744277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67560281794464153051162851 101340422691696229576744277)
              ·
                refine ⟨148447884802289398794059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 101340422691696229576744277 148447884802289398794059)
                ·
                  rfl

theorem cell23_7805733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 11].length) (baseStart_7805733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805733 prefixEnd_7805733 := by exact prefixLift 7805733
  have htrace : WordTrace (prefixWord ++ tailWord_7805733) baseStart_7805733 baseEnd_7805733 := by
    simpa [prefixWord, tailWord_7805733, baseEnd_7805733] using wordTrace_append hprefix tailTrace_7805733
  have hstable : (prefixWord ++ tailWord_7805733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805733).length < 2 ^ (prefixWord ++ tailWord_7805733).sum := by decide
  have hdescent : baseEnd_7805733 < baseStart_7805733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805740 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 4]
def baseStart_7805740 : Nat := 118140960795 + 7805740 * 2 ^ 59
def prefixEnd_7805740 : Nat := 4983230072969 + 3 ^ 40 * 7805740 * 2
def baseEnd_7805740 : Nat := 4008096484026395240052061

theorem tailTrace_7805740 : CollatzResearch.WordTrace tailWord_7805740 prefixEnd_7805740 4008096484026395240052061 := by
  unfold tailWord_7805740
  simp only [CollatzResearch.WordTrace]
  refine ⟨142349363370572284551231337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189799151160763046068308449 142349363370572284551231337)
  ·
    refine ⟨106762022527929213413423503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142349363370572284551231337 106762022527929213413423503)
    ·
      refine ⟨160143033791893820120135255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106762022527929213413423503 160143033791893820120135255)
      ·
        refine ⟨240214550687840730180202883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160143033791893820120135255 240214550687840730180202883)
        ·
          refine ⟨360321826031761095270304325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240214550687840730180202883 360321826031761095270304325)
          ·
            refine ⟨67560342380955205363182061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360321826031761095270304325 67560342380955205363182061)
            ·
              refine ⟨25335128392858202011193273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67560342380955205363182061 25335128392858202011193273)
              ·
                refine ⟨19001346294643651508394955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25335128392858202011193273 19001346294643651508394955)
                ·
                  refine ⟨28502019441965477262592433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19001346294643651508394955 28502019441965477262592433)
                  ·
                    refine ⟨21376514581474107946944325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28502019441965477262592433 21376514581474107946944325)
                    ·
                      refine ⟨4008096484026395240052061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21376514581474107946944325 4008096484026395240052061)
                      ·
                        rfl

theorem cell23_7805740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_7805740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805740 prefixEnd_7805740 := by exact prefixLift 7805740
  have htrace : WordTrace (prefixWord ++ tailWord_7805740) baseStart_7805740 baseEnd_7805740 := by
    simpa [prefixWord, tailWord_7805740, baseEnd_7805740] using wordTrace_append hprefix tailTrace_7805740
  have hstable : (prefixWord ++ tailWord_7805740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805740).length < 2 ^ (prefixWord ++ tailWord_7805740).sum := by decide
  have hdescent : baseEnd_7805740 < baseStart_7805740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805747 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 5]
def baseStart_7805747 : Nat := 118140960795 + 7805747 * 2 ^ 59
def prefixEnd_7805747 : Nat := 4983230072969 + 3 ^ 40 * 7805747 * 2
def baseEnd_7805747 : Nat := 4008100078390976712664529

theorem tailTrace_7805747 : CollatzResearch.WordTrace tailWord_7805747 prefixEnd_7805747 4008100078390976712664529 := by
  unfold tailWord_7805747
  simp only [CollatzResearch.WordTrace]
  refine ⟨284698982052119209297967495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189799321368079472865311663 284698982052119209297967495)
  ·
    refine ⟨427048473078178813946951243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284698982052119209297967495 427048473078178813946951243)
    ·
      refine ⟨640572709617268220920426865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427048473078178813946951243 640572709617268220920426865)
      ·
        refine ⟨480429532212951165690320149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 640572709617268220920426865 480429532212951165690320149)
        ·
          refine ⟨22520134322482085891733757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 480429532212951165690320149 22520134322482085891733757)
          ·
            refine ⟨8445050370930782209400159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22520134322482085891733757 8445050370930782209400159)
            ·
              refine ⟨12667575556396173314100239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8445050370930782209400159 12667575556396173314100239)
              ·
                refine ⟨19001363334594259971150359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12667575556396173314100239 19001363334594259971150359)
                ·
                  refine ⟨28502045001891389956725539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19001363334594259971150359 28502045001891389956725539)
                  ·
                    refine ⟨42753067502837084935088309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28502045001891389956725539 42753067502837084935088309)
                    ·
                      refine ⟨4008100078390976712664529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42753067502837084935088309 4008100078390976712664529)
                      ·
                        rfl

theorem cell23_7805747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 5].length) (baseStart_7805747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805747 prefixEnd_7805747 := by exact prefixLift 7805747
  have htrace : WordTrace (prefixWord ++ tailWord_7805747) baseStart_7805747 baseEnd_7805747 := by
    simpa [prefixWord, tailWord_7805747, baseEnd_7805747] using wordTrace_append hprefix tailTrace_7805747
  have hstable : (prefixWord ++ tailWord_7805747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805747).length < 2 ^ (prefixWord ++ tailWord_7805747).sum := by decide
  have hdescent : baseEnd_7805747 < baseStart_7805747 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805750 : List Nat := [5, 1, 2, 2, 13]
def baseStart_7805750 : Nat := 118140960795 + 7805750 * 2 ^ 59
def prefixEnd_7805750 : Nat := 4983230072969 + 3 ^ 40 * 7805750 * 2
def baseEnd_7805750 : Nat := 5498081781663841153535

theorem tailTrace_7805750 : CollatzResearch.WordTrace tailWord_7805750 prefixEnd_7805750 5498081781663841153535 := by
  unfold tailWord_7805750
  simp only [CollatzResearch.WordTrace]
  refine ⟨17793693216944271300645419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 189799394314072227206884469 17793693216944271300645419)
  ·
    refine ⟨26690539825416406950968129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17793693216944271300645419 26690539825416406950968129)
    ·
      refine ⟨20017904869062305213226097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26690539825416406950968129 20017904869062305213226097)
      ·
        refine ⟨15013428651796728909919573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20017904869062305213226097 15013428651796728909919573)
        ·
          refine ⟨5498081781663841153535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15013428651796728909919573 5498081781663841153535)
          ·
            rfl

theorem cell23_7805750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 13].length) (baseStart_7805750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805750 prefixEnd_7805750 := by exact prefixLift 7805750
  have htrace : WordTrace (prefixWord ++ tailWord_7805750) baseStart_7805750 baseEnd_7805750 := by
    simpa [prefixWord, tailWord_7805750, baseEnd_7805750] using wordTrace_append hprefix tailTrace_7805750
  have hstable : (prefixWord ++ tailWord_7805750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805750).length < 2 ^ (prefixWord ++ tailWord_7805750).sum := by decide
  have hdescent : baseEnd_7805750 < baseStart_7805750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805754 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 2, 4]
def baseStart_7805754 : Nat := 118140960795 + 7805754 * 2 ^ 59
def prefixEnd_7805754 : Nat := 4983230072969 + 3 ^ 40 * 7805754 * 2
def baseEnd_7805754 : Nat := 1336034557585186061758999

theorem tailTrace_7805754 : CollatzResearch.WordTrace tailWord_7805754 prefixEnd_7805754 1336034557585186061758999 := by
  unfold tailWord_7805754
  simp only [CollatzResearch.WordTrace]
  refine ⟨71174809340773462373368079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189799491575395899662314877 71174809340773462373368079)
  ·
    refine ⟨106762214011160193560052119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71174809340773462373368079 106762214011160193560052119)
    ·
      refine ⟨160143321016740290340078179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106762214011160193560052119 160143321016740290340078179)
      ·
        refine ⟨240214981525110435510117269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160143321016740290340078179 240214981525110435510117269)
        ·
          refine ⟨11260077258989551664536747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 240214981525110435510117269 11260077258989551664536747)
          ·
            refine ⟨16890115888484327496805121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11260077258989551664536747 16890115888484327496805121)
            ·
              refine ⟨12667586916363245622603841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16890115888484327496805121 12667586916363245622603841)
              ·
                refine ⟨9500690187272434216952881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12667586916363245622603841 9500690187272434216952881)
                ·
                  refine ⟨7125517640454325662714661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9500690187272434216952881 7125517640454325662714661)
                  ·
                    refine ⟨1336034557585186061758999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7125517640454325662714661 1336034557585186061758999)
                    ·
                      rfl

theorem cell23_7805754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_7805754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805754 prefixEnd_7805754 := by exact prefixLift 7805754
  have htrace : WordTrace (prefixWord ++ tailWord_7805754) baseStart_7805754 baseEnd_7805754 := by
    simpa [prefixWord, tailWord_7805754, baseEnd_7805754] using wordTrace_append hprefix tailTrace_7805754
  have hstable : (prefixWord ++ tailWord_7805754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805754).length < 2 ^ (prefixWord ++ tailWord_7805754).sum := by decide
  have hdescent : baseEnd_7805754 < baseStart_7805754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805763 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 1, 9]
def baseStart_7805763 : Nat := 118140960795 + 7805763 * 2 ^ 59
def prefixEnd_7805763 : Nat := 4983230072969 + 3 ^ 40 * 7805763 * 2
def baseEnd_7805763 : Nat := 1336036098027149550021485

theorem tailTrace_7805763 : CollatzResearch.WordTrace tailWord_7805763 prefixEnd_7805763 1336036098027149550021485 := by
  unfold tailWord_7805763
  simp only [CollatzResearch.WordTrace]
  refine ⟨284699565620061244030549943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189799710413374162687033295 284699565620061244030549943)
  ·
    refine ⟨427049348430091866045824915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284699565620061244030549943 427049348430091866045824915)
    ·
      refine ⟨640574022645137799068737373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427049348430091866045824915 640574022645137799068737373)
      ·
        refine ⟨240215258491926674650776515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640574022645137799068737373 240215258491926674650776515)
        ·
          refine ⟨360322887737890011976164773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240215258491926674650776515 360322887737890011976164773)
          ·
            refine ⟨67560541450854377245530895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 360322887737890011976164773 67560541450854377245530895)
            ·
              refine ⟨101340812176281565868296343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67560541450854377245530895 101340812176281565868296343)
              ·
                refine ⟨152011218264422348802444515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101340812176281565868296343 152011218264422348802444515)
                ·
                  refine ⟨228016827396633523203666773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152011218264422348802444515 228016827396633523203666773)
                  ·
                    refine ⟨1336036098027149550021485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 228016827396633523203666773 1336036098027149550021485)
                    ·
                      rfl

theorem cell23_7805763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 9].length) (baseStart_7805763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805763 prefixEnd_7805763 := by exact prefixLift 7805763
  have htrace : WordTrace (prefixWord ++ tailWord_7805763) baseStart_7805763 baseEnd_7805763 := by
    simpa [prefixWord, tailWord_7805763, baseEnd_7805763] using wordTrace_append hprefix tailTrace_7805763
  have hstable : (prefixWord ++ tailWord_7805763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805763).length < 2 ^ (prefixWord ++ tailWord_7805763).sum := by decide
  have hdescent : baseEnd_7805763 < baseStart_7805763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805804 : List Nat := [2, 2, 1, 1, 4, 1, 3, 3, 1, 3, 2]
def baseStart_7805804 : Nat := 118140960795 + 7805804 * 2 ^ 59
def prefixEnd_7805804 : Nat := 4983230072969 + 3 ^ 40 * 7805804 * 2
def baseEnd_7805804 : Nat := 4008129346788282989651767

theorem tailTrace_7805804 : CollatzResearch.WordTrace tailWord_7805804 prefixEnd_7805804 4008129346788282989651767 := by
  unfold tailWord_7805804
  simp only [CollatzResearch.WordTrace]
  refine ⟨142350530506456354016396233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189800707341941805355194977 142350530506456354016396233)
  ·
    refine ⟨106762897879842265512297175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142350530506456354016396233 106762897879842265512297175)
    ·
      refine ⟨160144346819763398268445763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106762897879842265512297175 160144346819763398268445763)
      ·
        refine ⟨240216520229645097402668645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160144346819763398268445763 240216520229645097402668645)
        ·
          refine ⟨45040597543058455763000371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240216520229645097402668645 45040597543058455763000371)
          ·
            refine ⟨67560896314587683644500557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45040597543058455763000371 67560896314587683644500557)
            ·
              refine ⟨25335336117970381366687709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67560896314587683644500557 25335336117970381366687709)
              ·
                refine ⟨9500751044238893012507891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25335336117970381366687709 9500751044238893012507891)
                ·
                  refine ⟨14251126566358339518761837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9500751044238893012507891 14251126566358339518761837)
                  ·
                    refine ⟨5344172462384377319535689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14251126566358339518761837 5344172462384377319535689)
                    ·
                      refine ⟨4008129346788282989651767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344172462384377319535689 4008129346788282989651767)
                      ·
                        rfl

theorem cell23_7805804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 3, 2].length) (baseStart_7805804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805804 prefixEnd_7805804 := by exact prefixLift 7805804
  have htrace : WordTrace (prefixWord ++ tailWord_7805804) baseStart_7805804 baseEnd_7805804 := by
    simpa [prefixWord, tailWord_7805804, baseEnd_7805804] using wordTrace_append hprefix tailTrace_7805804
  have hstable : (prefixWord ++ tailWord_7805804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805804).length < 2 ^ (prefixWord ++ tailWord_7805804).sum := by decide
  have hdescent : baseEnd_7805804 < baseStart_7805804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805810 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_7805810 : Nat := 118140960795 + 7805810 * 2 ^ 59
def prefixEnd_7805810 : Nat := 4983230072969 + 3 ^ 40 * 7805810 * 2
def baseEnd_7805810 : Nat := 1336044142557403322058913

theorem tailTrace_7805810 : CollatzResearch.WordTrace tailWord_7805810 prefixEnd_7805810 1336044142557403322058913 := by
  unfold tailWord_7805810
  simp only [CollatzResearch.WordTrace]
  refine ⟨71175319962722742764377721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189800853233927314038340589 71175319962722742764377721)
  ·
    refine ⟨53381489972042057073283291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71175319962722742764377721 53381489972042057073283291)
    ·
      refine ⟨80072234958063085609924937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53381489972042057073283291 80072234958063085609924937)
      ·
        refine ⟨60054176218547314207443703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80072234958063085609924937 60054176218547314207443703)
        ·
          refine ⟨90081264327820971311165555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60054176218547314207443703 90081264327820971311165555)
          ·
            refine ⟨135121896491731456966748333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90081264327820971311165555 135121896491731456966748333)
            ·
              refine ⟨50670711184399296362530625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135121896491731456966748333 50670711184399296362530625)
              ·
                refine ⟨38003033388299472271897969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50670711184399296362530625 38003033388299472271897969)
                ·
                  refine ⟨28502275041224604203923477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38003033388299472271897969 28502275041224604203923477)
                  ·
                    refine ⟨1336044142557403322058913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28502275041224604203923477 1336044142557403322058913)
                    ·
                      rfl

theorem cell23_7805810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_7805810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805810 prefixEnd_7805810 := by exact prefixLift 7805810
  have htrace : WordTrace (prefixWord ++ tailWord_7805810) baseStart_7805810 baseEnd_7805810 := by
    simpa [prefixWord, tailWord_7805810, baseEnd_7805810] using wordTrace_append hprefix tailTrace_7805810
  have hstable : (prefixWord ++ tailWord_7805810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805810).length < 2 ^ (prefixWord ++ tailWord_7805810).sum := by decide
  have hdescent : baseEnd_7805810 < baseStart_7805810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805820 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_7805820 : Nat := 118140960795 + 7805820 * 2 ^ 59
def prefixEnd_7805820 : Nat := 4983230072969 + 3 ^ 40 * 7805820 * 2
def baseEnd_7805820 : Nat := 4008137562478754927051693

theorem tailTrace_7805820 : CollatzResearch.WordTrace tailWord_7805820 prefixEnd_7805820 4008137562478754927051693 := by
  unfold tailWord_7805820
  simp only [CollatzResearch.WordTrace]
  refine ⟨142350822290427371382687457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189801096387236495176916609 142350822290427371382687457)
  ·
    refine ⟨106763116717820528537015593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142350822290427371382687457 106763116717820528537015593)
    ·
      refine ⟨80072337538365396402761695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106763116717820528537015593 80072337538365396402761695)
      ·
        refine ⟨120108506307548094604142543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80072337538365396402761695 120108506307548094604142543)
        ·
          refine ⟨180162759461322141906213815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120108506307548094604142543 180162759461322141906213815)
          ·
            refine ⟨270244139191983212859320723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180162759461322141906213815 270244139191983212859320723)
            ·
              refine ⟨405366208787974819288981085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270244139191983212859320723 405366208787974819288981085)
              ·
                refine ⟨152012328295490557233367907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 405366208787974819288981085 152012328295490557233367907)
                ·
                  refine ⟨228018492443235835850051861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152012328295490557233367907 228018492443235835850051861)
                  ·
                    refine ⟨10688366833276679805471181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 228018492443235835850051861 10688366833276679805471181)
                    ·
                      refine ⟨4008137562478754927051693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10688366833276679805471181 4008137562478754927051693)
                      ·
                        rfl

theorem cell23_7805820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_7805820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805820 prefixEnd_7805820 := by exact prefixLift 7805820
  have htrace : WordTrace (prefixWord ++ tailWord_7805820) baseStart_7805820 baseEnd_7805820 := by
    simpa [prefixWord, tailWord_7805820, baseEnd_7805820] using wordTrace_append hprefix tailTrace_7805820
  have hstable : (prefixWord ++ tailWord_7805820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805820).length < 2 ^ (prefixWord ++ tailWord_7805820).sum := by decide
  have hdescent : baseEnd_7805820 < baseStart_7805820 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805880 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_7805880 : Nat := 118140960795 + 7805880 * 2 ^ 59
def prefixEnd_7805880 : Nat := 4983230072969 + 3 ^ 40 * 7805880 * 2
def baseEnd_7805880 : Nat := 4008168371318024692301417

theorem tailTrace_7805880 : CollatzResearch.WordTrace tailWord_7805880 prefixEnd_7805880 4008168371318024692301417 := by
  unfold tailWord_7805880
  simp only [CollatzResearch.WordTrace]
  refine ⟨142351916480318686506279547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189802555307091582008372729 142351916480318686506279547)
  ·
    refine ⟨213527874720478029759419321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142351916480318686506279547 213527874720478029759419321)
    ·
      refine ⟨160145906040358522319564491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213527874720478029759419321 160145906040358522319564491)
      ·
        refine ⟨240218859060537783479346737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160145906040358522319564491 240218859060537783479346737)
        ·
          refine ⟨180164144295403337609510053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240218859060537783479346737 180164144295403337609510053)
          ·
            refine ⟨33780777055388125801783135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180164144295403337609510053 33780777055388125801783135)
            ·
              refine ⟨50671165583082188702674703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33780777055388125801783135 50671165583082188702674703)
              ·
                refine ⟨76006748374623283054012055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50671165583082188702674703 76006748374623283054012055)
                ·
                  refine ⟨114010122561934924581018083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76006748374623283054012055 114010122561934924581018083)
                  ·
                    refine ⟨171015183842902386871527125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114010122561934924581018083 171015183842902386871527125)
                    ·
                      refine ⟨4008168371318024692301417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171015183842902386871527125 4008168371318024692301417)
                      ·
                        rfl

theorem cell23_7805880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_7805880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805880 prefixEnd_7805880 := by exact prefixLift 7805880
  have htrace : WordTrace (prefixWord ++ tailWord_7805880) baseStart_7805880 baseEnd_7805880 := by
    simpa [prefixWord, tailWord_7805880, baseEnd_7805880] using wordTrace_append hprefix tailTrace_7805880
  have hstable : (prefixWord ++ tailWord_7805880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805880).length < 2 ^ (prefixWord ++ tailWord_7805880).sum := by decide
  have hdescent : baseEnd_7805880 < baseStart_7805880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805885 : List Nat := [1, 4, 1, 2, 4, 2, 2, 1, 2, 2, 2]
def baseStart_7805885 : Nat := 118140960795 + 7805885 * 2 ^ 59
def prefixEnd_7805885 : Nat := 4983230072969 + 3 ^ 40 * 7805885 * 2
def baseEnd_7805885 : Nat := 4008170938721297172738895

theorem tailTrace_7805885 : CollatzResearch.WordTrace tailWord_7805885 prefixEnd_7805885 4008170938721297172738895 := by
  unfold tailWord_7805885
  simp only [CollatzResearch.WordTrace]
  refine ⟨284704015325619258866491109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189802676883746172577660739 284704015325619258866491109)
  ·
    refine ⟨53382002873553611037467083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284704015325619258866491109 53382002873553611037467083)
    ·
      refine ⟨80073004310330416556200625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53382002873553611037467083 80073004310330416556200625)
      ·
        refine ⟨60054753232747812417150469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80073004310330416556200625 60054753232747812417150469)
        ·
          refine ⟨11260266231140214828215713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60054753232747812417150469 11260266231140214828215713)
          ·
            refine ⟨8445199673355161121161785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11260266231140214828215713 8445199673355161121161785)
            ·
              refine ⟨6333899755016370840871339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8445199673355161121161785 6333899755016370840871339)
              ·
                refine ⟨9500849632524556261307009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6333899755016370840871339 9500849632524556261307009)
                ·
                  refine ⟨7125637224393417195980257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9500849632524556261307009 7125637224393417195980257)
                  ·
                    refine ⟨5344227918295062896985193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7125637224393417195980257 5344227918295062896985193)
                    ·
                      refine ⟨4008170938721297172738895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344227918295062896985193 4008170938721297172738895)
                      ·
                        rfl

theorem cell23_7805885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_7805885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805885 prefixEnd_7805885 := by exact prefixLift 7805885
  have htrace : WordTrace (prefixWord ++ tailWord_7805885) baseStart_7805885 baseEnd_7805885 := by
    simpa [prefixWord, tailWord_7805885, baseEnd_7805885] using wordTrace_append hprefix tailTrace_7805885
  have hstable : (prefixWord ++ tailWord_7805885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805885).length < 2 ^ (prefixWord ++ tailWord_7805885).sum := by decide
  have hdescent : baseEnd_7805885 < baseStart_7805885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805925 : List Nat := [1, 3, 1, 6, 2, 1, 2, 2, 5]
def baseStart_7805925 : Nat := 118140960795 + 7805925 * 2 ^ 59
def prefixEnd_7805925 : Nat := 4983230072969 + 3 ^ 40 * 7805925 * 2
def baseEnd_7805925 : Nat := 445354608660830779582079

theorem tailTrace_7805925 : CollatzResearch.WordTrace tailWord_7805925 prefixEnd_7805925 445354608660830779582079 := by
  unfold tailWord_7805925
  simp only [CollatzResearch.WordTrace]
  refine ⟨284705474245474345697947229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189803649496982897131964819 284705474245474345697947229)
  ·
    refine ⟨106764552842052879636730211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 284705474245474345697947229 106764552842052879636730211)
    ·
      refine ⟨160146829263079319455095317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106764552842052879636730211 160146829263079319455095317)
      ·
        refine ⟨7506882621706843099457593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 160146829263079319455095317 7506882621706843099457593)
        ·
          refine ⟨5630161966280132324593195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7506882621706843099457593 5630161966280132324593195)
          ·
            refine ⟨8445242949420198486889793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5630161966280132324593195 8445242949420198486889793)
            ·
              refine ⟨6333932212065148865167345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8445242949420198486889793 6333932212065148865167345)
              ·
                refine ⟨4750449159048861648875509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6333932212065148865167345 4750449159048861648875509)
                ·
                  refine ⟨445354608660830779582079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4750449159048861648875509 445354608660830779582079)
                  ·
                    rfl

theorem cell23_7805925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 5].length) (baseStart_7805925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805925 prefixEnd_7805925 := by exact prefixLift 7805925
  have htrace : WordTrace (prefixWord ++ tailWord_7805925) baseStart_7805925 baseEnd_7805925 := by
    simpa [prefixWord, tailWord_7805925, baseEnd_7805925] using wordTrace_append hprefix tailTrace_7805925
  have hstable : (prefixWord ++ tailWord_7805925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805925).length < 2 ^ (prefixWord ++ tailWord_7805925).sum := by decide
  have hdescent : baseEnd_7805925 < baseStart_7805925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7805981 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 6]
def baseStart_7805981 : Nat := 118140960795 + 7805981 * 2 ^ 59
def prefixEnd_7805981 : Nat := 4983230072969 + 3 ^ 40 * 7805981 * 2
def baseEnd_7805981 : Nat := 445357803651569866348717

theorem tailTrace_7805981 : CollatzResearch.WordTrace tailWord_7805981 prefixEnd_7805981 445357803651569866348717 := by
  unfold tailWord_7805981
  simp only [CollatzResearch.WordTrace]
  refine ⟨284707516733271467261985797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189805011155514311507990531 284707516733271467261985797)
  ·
    refine ⟨53382659387488400111622337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 284707516733271467261985797 53382659387488400111622337)
    ·
      refine ⟨40036994540616300083716753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53382659387488400111622337 40036994540616300083716753)
      ·
        refine ⟨30027745905462225062787565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40036994540616300083716753 30027745905462225062787565)
        ·
          refine ⟨11260404714548334398545337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30027745905462225062787565 11260404714548334398545337)
          ·
            refine ⟨8445303535911250798909003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11260404714548334398545337 8445303535911250798909003)
            ·
              refine ⟨12667955303866876198363505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8445303535911250798909003 12667955303866876198363505)
              ·
                refine ⟨9500966477900157148772629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12667955303866876198363505 9500966477900157148772629)
                ·
                  refine ⟨445357803651569866348717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9500966477900157148772629 445357803651569866348717)
                  ·
                    rfl

theorem cell23_7805981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_7805981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7805981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7805981 prefixEnd_7805981 := by exact prefixLift 7805981
  have htrace : WordTrace (prefixWord ++ tailWord_7805981) baseStart_7805981 baseEnd_7805981 := by
    simpa [prefixWord, tailWord_7805981, baseEnd_7805981] using wordTrace_append hprefix tailTrace_7805981
  have hstable : (prefixWord ++ tailWord_7805981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7805981).length < 2 ^ (prefixWord ++ tailWord_7805981).sum := by decide
  have hdescent : baseEnd_7805981 < baseStart_7805981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7805981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806034 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_7806034 : Nat := 118140960795 + 7806034 * 2 ^ 59
def prefixEnd_7806034 : Nat := 4983230072969 + 3 ^ 40 * 7806034 * 2
def baseEnd_7806034 : Nat := 4008247447338817089775709

theorem tailTrace_7806034 : CollatzResearch.WordTrace tailWord_7806034 prefixEnd_7806034 4008247447338817089775709 := by
  unfold tailWord_7806034
  simp only [CollatzResearch.WordTrace]
  refine ⟨71177362450519864328416289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189806299868052971542443437 71177362450519864328416289)
  ·
    refine ⟨53383021837889898246312217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71177362450519864328416289 53383021837889898246312217)
    ·
      refine ⟨40037266378417423684734163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53383021837889898246312217 40037266378417423684734163)
      ·
        refine ⟨60055899567626135527101245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40037266378417423684734163 60055899567626135527101245)
        ·
          refine ⟨22520962337859800822662967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60055899567626135527101245 22520962337859800822662967)
          ·
            refine ⟨33781443506789701233994451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22520962337859800822662967 33781443506789701233994451)
            ·
              refine ⟨50672165260184551850991677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33781443506789701233994451 50672165260184551850991677)
              ·
                refine ⟨19002061972569206944121879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50672165260184551850991677 19002061972569206944121879)
                ·
                  refine ⟨28503092958853810416182819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19002061972569206944121879 28503092958853810416182819)
                  ·
                    refine ⟨42754639438280715624274229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28503092958853810416182819 42754639438280715624274229)
                    ·
                      refine ⟨4008247447338817089775709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42754639438280715624274229 4008247447338817089775709)
                      ·
                        rfl

theorem cell23_7806034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_7806034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806034 prefixEnd_7806034 := by exact prefixLift 7806034
  have htrace : WordTrace (prefixWord ++ tailWord_7806034) baseStart_7806034 baseEnd_7806034 := by
    simpa [prefixWord, tailWord_7806034, baseEnd_7806034] using wordTrace_append hprefix tailTrace_7806034
  have hstable : (prefixWord ++ tailWord_7806034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806034).length < 2 ^ (prefixWord ++ tailWord_7806034).sum := by decide
  have hdescent : baseEnd_7806034 < baseStart_7806034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806058 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 2, 4]
def baseStart_7806058 : Nat := 118140960795 + 7806058 * 2 ^ 59
def prefixEnd_7806058 : Nat := 4983230072969 + 3 ^ 40 * 7806058 * 2
def baseEnd_7806058 : Nat := 1336086590291508331958533

theorem tailTrace_7806058 : CollatzResearch.WordTrace tailWord_7806058 prefixEnd_7806058 1336086590291508331958533 := by
  unfold tailWord_7806058
  simp only [CollatzResearch.WordTrace]
  refine ⟨71177581288498127353134707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189806883435995006275025885 71177581288498127353134707)
  ·
    refine ⟨106766371932747191029702061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71177581288498127353134707 106766371932747191029702061)
    ·
      refine ⟨40037389474780196636138273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106766371932747191029702061 40037389474780196636138273)
      ·
        refine ⟨30028042106085147477103705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40037389474780196636138273 30028042106085147477103705)
        ·
          refine ⟨22521031579563860607827779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30028042106085147477103705 22521031579563860607827779)
          ·
            refine ⟨33781547369345790911741669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22521031579563860607827779 33781547369345790911741669)
            ·
              refine ⟨6334040131752335795951563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33781547369345790911741669 6334040131752335795951563)
              ·
                refine ⟨9501060197628503693927345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6334040131752335795951563 9501060197628503693927345)
                ·
                  refine ⟨7125795148221377770445509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9501060197628503693927345 7125795148221377770445509)
                  ·
                    refine ⟨1336086590291508331958533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7125795148221377770445509 1336086590291508331958533)
                    ·
                      rfl

theorem cell23_7806058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_7806058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806058 prefixEnd_7806058 := by exact prefixLift 7806058
  have htrace : WordTrace (prefixWord ++ tailWord_7806058) baseStart_7806058 baseEnd_7806058 := by
    simpa [prefixWord, tailWord_7806058, baseEnd_7806058] using wordTrace_append hprefix tailTrace_7806058
  have hstable : (prefixWord ++ tailWord_7806058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806058).length < 2 ^ (prefixWord ++ tailWord_7806058).sum := by decide
  have hdescent : baseEnd_7806058 < baseStart_7806058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806064 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 3]
def baseStart_7806064 : Nat := 118140960795 + 7806064 * 2 ^ 59
def prefixEnd_7806064 : Nat := 4983230072969 + 3 ^ 40 * 7806064 * 2
def baseEnd_7806064 : Nat := 4008262851758451972400571

theorem tailTrace_7806064 : CollatzResearch.WordTrace tailWord_7806064 prefixEnd_7806064 4008262851758451972400571 := by
  unfold tailWord_7806064
  simp only [CollatzResearch.WordTrace]
  refine ⟨142355271995985386218628623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189807029327980514958171497 142355271995985386218628623)
  ·
    refine ⟨213532907993978079327942935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142355271995985386218628623 213532907993978079327942935)
    ·
      refine ⟨320299361990967118991914403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213532907993978079327942935 320299361990967118991914403)
      ·
        refine ⟨480449042986450678487871605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320299361990967118991914403 480449042986450678487871605)
        ·
          refine ⟨45042097779979751108237963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 480449042986450678487871605 45042097779979751108237963)
          ·
            refine ⟨67563146669969626662356945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45042097779979751108237963 67563146669969626662356945)
            ·
              refine ⟨50672360002477219996767709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67563146669969626662356945 50672360002477219996767709)
              ·
                refine ⟨19002135000928957498787891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50672360002477219996767709 19002135000928957498787891)
                ·
                  refine ⟨28503202501393436248181837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19002135000928957498787891 28503202501393436248181837)
                  ·
                    refine ⟨10688700938022538593068189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28503202501393436248181837 10688700938022538593068189)
                    ·
                      refine ⟨4008262851758451972400571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10688700938022538593068189 4008262851758451972400571)
                      ·
                        rfl

theorem cell23_7806064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 3].length) (baseStart_7806064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806064 prefixEnd_7806064 := by exact prefixLift 7806064
  have htrace : WordTrace (prefixWord ++ tailWord_7806064) baseStart_7806064 baseEnd_7806064 := by
    simpa [prefixWord, tailWord_7806064, baseEnd_7806064] using wordTrace_append hprefix tailTrace_7806064
  have hstable : (prefixWord ++ tailWord_7806064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806064).length < 2 ^ (prefixWord ++ tailWord_7806064).sum := by decide
  have hdescent : baseEnd_7806064 < baseStart_7806064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806081 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_7806081 : Nat := 118140960795 + 7806081 * 2 ^ 59
def prefixEnd_7806081 : Nat := 4983230072969 + 3 ^ 40 * 7806081 * 2
def baseEnd_7806081 : Nat := 4008271580929578405887993

theorem tailTrace_7806081 : CollatzResearch.WordTrace tailWord_7806081 prefixEnd_7806081 4008271580929578405887993 := by
  unfold tailWord_7806081
  simp only [CollatzResearch.WordTrace]
  refine ⟨284711164032909184340626097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189807442688606122893750731 284711164032909184340626097)
  ·
    refine ⟨213533373024681888255469573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 284711164032909184340626097 213533373024681888255469573)
    ·
      refine ⟨40037507442127854047900545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213533373024681888255469573 40037507442127854047900545)
      ·
        refine ⟨30028130581595890535925409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40037507442127854047900545 30028130581595890535925409)
        ·
          refine ⟨22521097936196917901944057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30028130581595890535925409 22521097936196917901944057)
          ·
            refine ⟨16890823452147688426458043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22521097936196917901944057 16890823452147688426458043)
            ·
              refine ⟨25336235178221532639687065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16890823452147688426458043 25336235178221532639687065)
              ·
                refine ⟨19002176383666149479765299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25336235178221532639687065 19002176383666149479765299)
                ·
                  refine ⟨28503264575499224219647949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19002176383666149479765299 28503264575499224219647949)
                  ·
                    refine ⟨10688724215812209082367981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28503264575499224219647949 10688724215812209082367981)
                    ·
                      refine ⟨4008271580929578405887993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10688724215812209082367981 4008271580929578405887993)
                      ·
                        rfl

theorem cell23_7806081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_7806081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806081 prefixEnd_7806081 := by exact prefixLift 7806081
  have htrace : WordTrace (prefixWord ++ tailWord_7806081) baseStart_7806081 baseEnd_7806081 := by
    simpa [prefixWord, tailWord_7806081, baseEnd_7806081] using wordTrace_append hprefix tailTrace_7806081
  have hstable : (prefixWord ++ tailWord_7806081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806081).length < 2 ^ (prefixWord ++ tailWord_7806081).sum := by decide
  have hdescent : baseEnd_7806081 < baseStart_7806081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806091 : List Nat := [1, 1, 1, 1, 4, 1, 1, 7, 1, 3, 2]
def baseStart_7806091 : Nat := 118140960795 + 7806091 * 2 ^ 59
def prefixEnd_7806091 : Nat := 4983230072969 + 3 ^ 40 * 7806091 * 2
def baseEnd_7806091 : Nat := 4008276715736123366762947

theorem tailTrace_7806091 : CollatzResearch.WordTrace tailWord_7806091 prefixEnd_7806091 4008276715736123366762947 := by
  unfold tailWord_7806091
  simp only [CollatzResearch.WordTrace]
  refine ⟨284711528762872956048490127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189807685841915304032326751 284711528762872956048490127)
  ·
    refine ⟨427067293144309434072735191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284711528762872956048490127 427067293144309434072735191)
    ·
      refine ⟨640600939716464151109102787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427067293144309434072735191 640600939716464151109102787)
      ·
        refine ⟨960901409574696226663654181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640600939716464151109102787 960901409574696226663654181)
        ·
          refine ⟨180169014295255542499435159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 960901409574696226663654181 180169014295255542499435159)
          ·
            refine ⟨270253521442883313749152739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180169014295255542499435159 270253521442883313749152739)
            ·
              refine ⟨405380282164324970623729109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270253521442883313749152739 405380282164324970623729109)
              ·
                refine ⟨9501100363226366498993651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 405380282164324970623729109 9501100363226366498993651)
                ·
                  refine ⟨14251650544839549748490477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9501100363226366498993651 14251650544839549748490477)
                  ·
                    refine ⟨5344368954314831155683929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14251650544839549748490477 5344368954314831155683929)
                    ·
                      refine ⟨4008276715736123366762947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344368954314831155683929 4008276715736123366762947)
                      ·
                        rfl

theorem cell23_7806091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 3, 2].length) (baseStart_7806091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806091 prefixEnd_7806091 := by exact prefixLift 7806091
  have htrace : WordTrace (prefixWord ++ tailWord_7806091) baseStart_7806091 baseEnd_7806091 := by
    simpa [prefixWord, tailWord_7806091, baseEnd_7806091] using wordTrace_append hprefix tailTrace_7806091
  have hstable : (prefixWord ++ tailWord_7806091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806091).length < 2 ^ (prefixWord ++ tailWord_7806091).sum := by decide
  have hdescent : baseEnd_7806091 < baseStart_7806091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806098 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_7806098 : Nat := 118140960795 + 7806098 * 2 ^ 59
def prefixEnd_7806098 : Nat := 4983230072969 + 3 ^ 40 * 7806098 * 2
def baseEnd_7806098 : Nat := 4008280310100704839375415

theorem tailTrace_7806098 : CollatzResearch.WordTrace tailWord_7806098 prefixEnd_7806098 4008280310100704839375415 := by
  unfold tailWord_7806098
  simp only [CollatzResearch.WordTrace]
  refine ⟨71177946018461899060998737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 189807856049231730829329965 71177946018461899060998737)
  ·
    refine ⟨53383459513846424295749053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71177946018461899060998737 53383459513846424295749053)
    ·
      refine ⟨20018797317692409110905895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53383459513846424295749053 20018797317692409110905895)
      ·
        refine ⟨30028195976538613666358843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20018797317692409110905895 30028195976538613666358843)
        ·
          refine ⟨45042293964807920499538265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30028195976538613666358843 45042293964807920499538265)
          ·
            refine ⟨33781720473605940374653699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45042293964807920499538265 33781720473605940374653699)
            ·
              refine ⟨50672580710408910561980549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33781720473605940374653699 50672580710408910561980549)
              ·
                refine ⟨9501108883201670730371353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50672580710408910561980549 9501108883201670730371353)
                ·
                  refine ⟨7125831662401253047778515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9501108883201670730371353 7125831662401253047778515)
                  ·
                    refine ⟨10688747493601879571667773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7125831662401253047778515 10688747493601879571667773)
                    ·
                      refine ⟨4008280310100704839375415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10688747493601879571667773 4008280310100704839375415)
                      ·
                        rfl

theorem cell23_7806098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_7806098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806098 prefixEnd_7806098 := by exact prefixLift 7806098
  have htrace : WordTrace (prefixWord ++ tailWord_7806098) baseStart_7806098 baseEnd_7806098 := by
    simpa [prefixWord, tailWord_7806098, baseEnd_7806098] using wordTrace_append hprefix tailTrace_7806098
  have hstable : (prefixWord ++ tailWord_7806098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806098).length < 2 ^ (prefixWord ++ tailWord_7806098).sum := by decide
  have hdescent : baseEnd_7806098 < baseStart_7806098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806104 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_7806104 : Nat := 118140960795 + 7806104 * 2 ^ 59
def prefixEnd_7806104 : Nat := 4983230072969 + 3 ^ 40 * 7806104 * 2
def baseEnd_7806104 : Nat := 4008283390984631815900387

theorem tailTrace_7806104 : CollatzResearch.WordTrace tailWord_7806104 prefixEnd_7806104 4008283390984631815900387 := by
  unfold tailWord_7806104
  simp only [CollatzResearch.WordTrace]
  refine ⟨142356001455912929634356683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 189808001941217239512475577 142356001455912929634356683)
  ·
    refine ⟨213534002183869394451535025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142356001455912929634356683 213534002183869394451535025)
    ·
      refine ⟨160150501637902045838651269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213534002183869394451535025 160150501637902045838651269)
      ·
        refine ⟨30028219057106633594747113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160150501637902045838651269 30028219057106633594747113)
        ·
          refine ⟨22521164292829975196060335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30028219057106633594747113 22521164292829975196060335)
          ·
            refine ⟨33781746439244962794090503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22521164292829975196060335 33781746439244962794090503)
            ·
              refine ⟨50672619658867444191135755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33781746439244962794090503 50672619658867444191135755)
              ·
                refine ⟨76008929488301166286703633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50672619658867444191135755 76008929488301166286703633)
                ·
                  refine ⟨57006697116225874715027725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76008929488301166286703633 57006697116225874715027725)
                  ·
                    refine ⟨21377511418584703018135397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57006697116225874715027725 21377511418584703018135397)
                    ·
                      refine ⟨4008283390984631815900387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21377511418584703018135397 4008283390984631815900387)
                      ·
                        rfl

theorem cell23_7806104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_7806104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806104 prefixEnd_7806104 := by exact prefixLift 7806104
  have htrace : WordTrace (prefixWord ++ tailWord_7806104) baseStart_7806104 baseEnd_7806104 := by
    simpa [prefixWord, tailWord_7806104, baseEnd_7806104] using wordTrace_append hprefix tailTrace_7806104
  have hstable : (prefixWord ++ tailWord_7806104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806104).length < 2 ^ (prefixWord ++ tailWord_7806104).sum := by decide
  have hdescent : baseEnd_7806104 < baseStart_7806104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806107 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 5]
def baseStart_7806107 : Nat := 118140960795 + 7806107 * 2 ^ 59
def prefixEnd_7806107 : Nat := 4983230072969 + 3 ^ 40 * 7806107 * 2
def baseEnd_7806107 : Nat := 4008284931426595304162873

theorem tailTrace_7806107 : CollatzResearch.WordTrace tailWord_7806107 prefixEnd_7806107 4008284931426595304162873 := by
  unfold tailWord_7806107
  simp only [CollatzResearch.WordTrace]
  refine ⟨284712112330814990781072575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189808074887209993854048383 284712112330814990781072575)
  ·
    refine ⟨427068168496222486171608863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284712112330814990781072575 427068168496222486171608863)
    ·
      refine ⟨640602252744333729257413295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427068168496222486171608863 640602252744333729257413295)
      ·
        refine ⟨960903379116500593886119943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 640602252744333729257413295 960903379116500593886119943)
        ·
          refine ⟨1441355068674750890829179915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 960903379116500593886119943 1441355068674750890829179915)
          ·
            refine ⟨2162032603012126336243769873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1441355068674750890829179915 2162032603012126336243769873)
            ·
              refine ⟨1621524452259094752182827405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2162032603012126336243769873 1621524452259094752182827405)
              ·
                refine ⟨608071669597160532068560277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1621524452259094752182827405 608071669597160532068560277)
                ·
                  refine ⟨28503359512366899940713763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 608071669597160532068560277 28503359512366899940713763)
                  ·
                    refine ⟨42755039268550349911070645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28503359512366899940713763 42755039268550349911070645)
                    ·
                      refine ⟨4008284931426595304162873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42755039268550349911070645 4008284931426595304162873)
                      ·
                        rfl

theorem cell23_7806107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 5].length) (baseStart_7806107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806107 prefixEnd_7806107 := by exact prefixLift 7806107
  have htrace : WordTrace (prefixWord ++ tailWord_7806107) baseStart_7806107 baseEnd_7806107 := by
    simpa [prefixWord, tailWord_7806107, baseEnd_7806107] using wordTrace_append hprefix tailTrace_7806107
  have hstable : (prefixWord ++ tailWord_7806107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806107).length < 2 ^ (prefixWord ++ tailWord_7806107).sum := by decide
  have hdescent : baseEnd_7806107 < baseStart_7806107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806127 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 9]
def baseStart_7806127 : Nat := 118140960795 + 7806127 * 2 ^ 59
def prefixEnd_7806127 : Nat := 4983230072969 + 3 ^ 40 * 7806127 * 2
def baseEnd_7806127 : Nat := 445366133448853913990309

theorem tailTrace_7806127 : CollatzResearch.WordTrace tailWord_7806127 prefixEnd_7806127 445366133448853913990309 := by
  unfold tailWord_7806127
  simp only [CollatzResearch.WordTrace]
  refine ⟨284712841790742534196800635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189808561193828356131200423 284712841790742534196800635)
  ·
    refine ⟨427069262686113801295200953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284712841790742534196800635 427069262686113801295200953)
    ·
      refine ⟨320301947014585350971400715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 427069262686113801295200953 320301947014585350971400715)
      ·
        refine ⟨480452920521878026457101073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320301947014585350971400715 480452920521878026457101073)
        ·
          refine ⟨360339690391408519842825805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480452920521878026457101073 360339690391408519842825805)
          ·
            refine ⟨135127383896778194941059677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360339690391408519842825805 135127383896778194941059677)
            ·
              refine ⟨50672768961291823102897379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135127383896778194941059677 50672768961291823102897379)
              ·
                refine ⟨76009153441937734654346069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50672768961291823102897379 76009153441937734654346069)
                ·
                  refine ⟨445366133448853913990309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76009153441937734654346069 445366133448853913990309)
                  ·
                    rfl

theorem cell23_7806127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 9].length) (baseStart_7806127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806127 prefixEnd_7806127 := by exact prefixLift 7806127
  have htrace : WordTrace (prefixWord ++ tailWord_7806127) baseStart_7806127 baseEnd_7806127 := by
    simpa [prefixWord, tailWord_7806127, baseEnd_7806127] using wordTrace_append hprefix tailTrace_7806127
  have hstable : (prefixWord ++ tailWord_7806127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806127).length < 2 ^ (prefixWord ++ tailWord_7806127).sum := by decide
  have hdescent : baseEnd_7806127 < baseStart_7806127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806142 : List Nat := [4, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_7806142 : Nat := 118140960795 + 7806142 * 2 ^ 59
def prefixEnd_7806142 : Nat := 4983230072969 + 3 ^ 40 * 7806142 * 2
def baseEnd_7806142 : Nat := 4008302903249502667225213

theorem tailTrace_7806142 : CollatzResearch.WordTrace tailWord_7806142 prefixEnd_7806142 4008302903249502667225213 := by
  unfold tailWord_7806142
  simp only [CollatzResearch.WordTrace]
  refine ⟨35589173610711023969824585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 189808925923792127839064453 35589173610711023969824585)
  ·
    refine ⟨26691880208033267977368439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35589173610711023969824585 26691880208033267977368439)
    ·
      refine ⟨40037820312049901966052659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26691880208033267977368439 40037820312049901966052659)
      ·
        refine ⟨60056730468074852949078989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40037820312049901966052659 60056730468074852949078989)
        ·
          refine ⟨22521273925528069855904621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60056730468074852949078989 22521273925528069855904621)
          ·
            refine ⟨8445477722073026195964233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22521273925528069855904621 8445477722073026195964233)
            ·
              refine ⟨6334108291554769646973175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8445477722073026195964233 6334108291554769646973175)
              ·
                refine ⟨9501162437332154470459763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6334108291554769646973175 9501162437332154470459763)
                ·
                  refine ⟨14251743655998231705689645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9501162437332154470459763 14251743655998231705689645)
                  ·
                    refine ⟨5344403870999336889633617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14251743655998231705689645 5344403870999336889633617)
                    ·
                      refine ⟨4008302903249502667225213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5344403870999336889633617 4008302903249502667225213)
                      ·
                        rfl

theorem cell23_7806142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_7806142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806142 prefixEnd_7806142 := by exact prefixLift 7806142
  have htrace : WordTrace (prefixWord ++ tailWord_7806142) baseStart_7806142 baseEnd_7806142 := by
    simpa [prefixWord, tailWord_7806142, baseEnd_7806142] using wordTrace_append hprefix tailTrace_7806142
  have hstable : (prefixWord ++ tailWord_7806142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806142).length < 2 ^ (prefixWord ++ tailWord_7806142).sum := by decide
  have hdescent : baseEnd_7806142 < baseStart_7806142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806211 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 4]
def baseStart_7806211 : Nat := 118140960795 + 7806211 * 2 ^ 59
def prefixEnd_7806211 : Nat := 4983230072969 + 3 ^ 40 * 7806211 * 2
def baseEnd_7806211 : Nat := 4008338333414662897262395

theorem tailTrace_7806211 : CollatzResearch.WordTrace tailWord_7806211 prefixEnd_7806211 4008338333414662897262395 := by
  unfold tailWord_7806211
  simp only [CollatzResearch.WordTrace]
  refine ⟨284715905522438216542858487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189810603681625477695238991 284715905522438216542858487)
  ·
    refine ⟨427073858283657324814287731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284715905522438216542858487 427073858283657324814287731)
    ·
      refine ⟨640610787425485987221431597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 427073858283657324814287731 640610787425485987221431597)
      ·
        refine ⟨240229045284557245208036849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 640610787425485987221431597 240229045284557245208036849)
        ·
          refine ⟨180171783963417933906027637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240229045284557245208036849 180171783963417933906027637)
          ·
            refine ⟨16891104746570431303690091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180171783963417933906027637 16891104746570431303690091)
            ·
              refine ⟨25336657119855646955535137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16891104746570431303690091 25336657119855646955535137)
              ·
                refine ⟨19002492839891735216651353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25336657119855646955535137 19002492839891735216651353)
                ·
                  refine ⟨14251869629918801412488515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19002492839891735216651353 14251869629918801412488515)
                  ·
                    refine ⟨21377804444878202118732773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14251869629918801412488515 21377804444878202118732773)
                    ·
                      refine ⟨4008338333414662897262395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21377804444878202118732773 4008338333414662897262395)
                      ·
                        rfl

theorem cell23_7806211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_7806211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806211 prefixEnd_7806211 := by exact prefixLift 7806211
  have htrace : WordTrace (prefixWord ++ tailWord_7806211) baseStart_7806211 baseEnd_7806211 := by
    simpa [prefixWord, tailWord_7806211, baseEnd_7806211] using wordTrace_append hprefix tailTrace_7806211
  have hstable : (prefixWord ++ tailWord_7806211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806211).length < 2 ^ (prefixWord ++ tailWord_7806211).sum := by decide
  have hdescent : baseEnd_7806211 < baseStart_7806211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7806231 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 3]
def baseStart_7806231 : Nat := 118140960795 + 7806231 * 2 ^ 59
def prefixEnd_7806231 : Nat := 4983230072969 + 3 ^ 40 * 7806231 * 2
def baseEnd_7806231 : Nat := 4008348603027752819012303

theorem tailTrace_7806231 : CollatzResearch.WordTrace tailWord_7806231 prefixEnd_7806231 4008348603027752819012303 := by
  unfold tailWord_7806231
  simp only [CollatzResearch.WordTrace]
  refine ⟨284716634982365759958586547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 189811089988243839972391031 284716634982365759958586547)
  ·
    refine ⟨427074952473548639937879821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 284716634982365759958586547 427074952473548639937879821)
    ·
      refine ⟨160153107177580739976704933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 427074952473548639937879821 160153107177580739976704933)
      ·
        refine ⟨30028707595796388745632175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160153107177580739976704933 30028707595796388745632175)
        ·
          refine ⟨45043061393694583118448263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30028707595796388745632175 45043061393694583118448263)
          ·
            refine ⟨67564592090541874677672395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45043061393694583118448263 67564592090541874677672395)
            ·
              refine ⟨101346888135812812016508593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67564592090541874677672395 101346888135812812016508593)
              ·
                refine ⟨76010166101859609012381445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101346888135812812016508593 76010166101859609012381445)
                ·
                  refine ⟨14251906144098676689821521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76010166101859609012381445 14251906144098676689821521)
                  ·
                    refine ⟨10688929608074007517366141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14251906144098676689821521 10688929608074007517366141)
                    ·
                      refine ⟨4008348603027752819012303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10688929608074007517366141 4008348603027752819012303)
                      ·
                        rfl

theorem cell23_7806231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_7806231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7806231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7806231 prefixEnd_7806231 := by exact prefixLift 7806231
  have htrace : WordTrace (prefixWord ++ tailWord_7806231) baseStart_7806231 baseEnd_7806231 := by
    simpa [prefixWord, tailWord_7806231, baseEnd_7806231] using wordTrace_append hprefix tailTrace_7806231
  have hstable : (prefixWord ++ tailWord_7806231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7806231).length < 2 ^ (prefixWord ++ tailWord_7806231).sum := by decide
  have hdescent : baseEnd_7806231 < baseStart_7806231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7806231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
