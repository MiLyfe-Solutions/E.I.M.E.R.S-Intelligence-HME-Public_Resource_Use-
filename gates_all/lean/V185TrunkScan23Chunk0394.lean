import V185TrunkScan23Chunk0393

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2329236 : List Nat := [2, 4, 2, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_2329236 : Nat := 118140960795 + 2329236 * 2 ^ 59
def prefixEnd_2329236 : Nat := 4983230072969 + 3 ^ 40 * 2329236 * 2
def baseEnd_2329236 : Nat := 1196017625755954087138045

theorem tailTrace_2329236 : CollatzResearch.WordTrace tailWord_2329236 prefixEnd_2329236 1196017625755954087138045 := by
  unfold tailWord_2329236
  simp only [CollatzResearch.WordTrace]
  refine ⟨42477108094791624341643781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56636144126388832455525041 42477108094791624341643781)
  ·
    refine ⟨7964457767773429564058209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42477108094791624341643781 7964457767773429564058209)
    ·
      refine ⟨5973343325830072173043657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7964457767773429564058209 5973343325830072173043657)
      ·
        refine ⟨4480007494372554129782743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5973343325830072173043657 4480007494372554129782743)
        ·
          refine ⟨6720011241558831194674115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4480007494372554129782743 6720011241558831194674115)
          ·
            refine ⟨10080016862338246792011173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6720011241558831194674115 10080016862338246792011173)
            ·
              refine ⟨1890003161688421273502095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10080016862338246792011173 1890003161688421273502095)
              ·
                refine ⟨2835004742532631910253143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890003161688421273502095 2835004742532631910253143)
                ·
                  refine ⟨4252507113798947865379715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835004742532631910253143 4252507113798947865379715)
                  ·
                    refine ⟨6378760670698421798069573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4252507113798947865379715 6378760670698421798069573)
                    ·
                      refine ⟨1196017625755954087138045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6378760670698421798069573 1196017625755954087138045)
                      ·
                        rfl

theorem cell23_2329236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_2329236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329236 prefixEnd_2329236 := by exact prefixLift 2329236
  have htrace : WordTrace (prefixWord ++ tailWord_2329236) baseStart_2329236 baseEnd_2329236 := by
    simpa [prefixWord, tailWord_2329236, baseEnd_2329236] using wordTrace_append hprefix tailTrace_2329236
  have hstable : (prefixWord ++ tailWord_2329236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329236).length < 2 ^ (prefixWord ++ tailWord_2329236).sum := by decide
  have hdescent : baseEnd_2329236 < baseStart_2329236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329242 : List Nat := [3, 1, 1, 6, 1, 1, 10]
def baseStart_2329242 : Nat := 118140960795 + 2329242 * 2 ^ 59
def prefixEnd_2329242 : Nat := 4983230072969 + 3 ^ 40 * 2329242 * 2
def baseEnd_2329242 : Nat := 14765687736294827946457

theorem tailTrace_2329242 : CollatzResearch.WordTrace tailWord_2329242 prefixEnd_2329242 14765687736294827946457 := by
  unfold tailWord_2329242
  simp only [CollatzResearch.WordTrace]
  refine ⟨21238608756890377927001495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56636290018374341138670653 21238608756890377927001495)
  ·
    refine ⟨31857913135335566890502243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21238608756890377927001495 31857913135335566890502243)
    ·
      refine ⟨47786869703003350335753365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31857913135335566890502243 47786869703003350335753365)
      ·
        refine ⟨2240009517328282046988439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47786869703003350335753365 2240009517328282046988439)
        ·
          refine ⟨3360014275992423070482659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240009517328282046988439 3360014275992423070482659)
          ·
            refine ⟨5040021413988634605723989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360014275992423070482659 5040021413988634605723989)
            ·
              refine ⟨14765687736294827946457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5040021413988634605723989 14765687736294827946457)
              ·
                rfl

theorem cell23_2329242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 10].length) (baseStart_2329242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329242 prefixEnd_2329242 := by exact prefixLift 2329242
  have htrace : WordTrace (prefixWord ++ tailWord_2329242) baseStart_2329242 baseEnd_2329242 := by
    simpa [prefixWord, tailWord_2329242, baseEnd_2329242] using wordTrace_append hprefix tailTrace_2329242
  have hstable : (prefixWord ++ tailWord_2329242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329242).length < 2 ^ (prefixWord ++ tailWord_2329242).sum := by decide
  have hdescent : baseEnd_2329242 < baseStart_2329242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329269 : List Nat := [1, 3, 3, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2329269 : Nat := 118140960795 + 2329269 * 2 ^ 59
def prefixEnd_2329269 : Nat := 4983230072969 + 3 ^ 40 * 2329269 * 2
def baseEnd_2329269 : Nat := 1196034570617552458025393

theorem tailTrace_2329269 : CollatzResearch.WordTrace tailWord_2329269 prefixEnd_2329269 1196034570617552458025393 := by
  unfold tailWord_2329269
  simp only [CollatzResearch.WordTrace]
  refine ⟨84955419798463695319238861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56636946532309130212825907 84955419798463695319238861)
  ·
    refine ⟨31858282424423885744714573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84955419798463695319238861 31858282424423885744714573)
    ·
      refine ⟨11946855909158957154267965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31858282424423885744714573 11946855909158957154267965)
      ·
        refine ⟨4480070965934608932850487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11946855909158957154267965 4480070965934608932850487)
        ·
          refine ⟨6720106448901913399275731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4480070965934608932850487 6720106448901913399275731)
          ·
            refine ⟨10080159673352870098913597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6720106448901913399275731 10080159673352870098913597)
            ·
              refine ⟨3780059877507326287092599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10080159673352870098913597 3780059877507326287092599)
              ·
                refine ⟨5670089816260989430638899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3780059877507326287092599 5670089816260989430638899)
                ·
                  refine ⟨8505134724391484145958349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5670089816260989430638899 8505134724391484145958349)
                  ·
                    refine ⟨3189425521646806554734381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8505134724391484145958349 3189425521646806554734381)
                    ·
                      refine ⟨1196034570617552458025393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3189425521646806554734381 1196034570617552458025393)
                      ·
                        rfl

theorem cell23_2329269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2329269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329269 prefixEnd_2329269 := by exact prefixLift 2329269
  have htrace : WordTrace (prefixWord ++ tailWord_2329269) baseStart_2329269 baseEnd_2329269 := by
    simpa [prefixWord, tailWord_2329269, baseEnd_2329269] using wordTrace_append hprefix tailTrace_2329269
  have hstable : (prefixWord ++ tailWord_2329269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329269).length < 2 ^ (prefixWord ++ tailWord_2329269).sum := by decide
  have hdescent : baseEnd_2329269 < baseStart_2329269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329279 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 1, 3, 2]
def baseStart_2329279 : Nat := 118140960795 + 2329279 * 2 ^ 59
def prefixEnd_2329279 : Nat := 4983230072969 + 3 ^ 40 * 2329279 * 2
def baseEnd_2329279 : Nat := 1196039705424097418900347

theorem tailTrace_2329279 : CollatzResearch.WordTrace tailWord_2329279 prefixEnd_2329279 1196039705424097418900347 := by
  unfold tailWord_2329279
  simp only [CollatzResearch.WordTrace]
  refine ⟨84955784528427467027102891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56637189685618311351401927 84955784528427467027102891)
  ·
    refine ⟨127433676792641200540654337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84955784528427467027102891 127433676792641200540654337)
    ·
      refine ⟨95575257594480900405490753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127433676792641200540654337 95575257594480900405490753)
      ·
        refine ⟨71681443195860675304118065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95575257594480900405490753 71681443195860675304118065)
        ·
          refine ⟨53761082396895506478088549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71681443195860675304118065 53761082396895506478088549)
          ·
            refine ⟨10080202949417907464641603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53761082396895506478088549 10080202949417907464641603)
            ·
              refine ⟨15120304424126861196962405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10080202949417907464641603 15120304424126861196962405)
              ·
                refine ⟨2835057079523786474430451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15120304424126861196962405 2835057079523786474430451)
                ·
                  refine ⟨4252585619285679711645677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835057079523786474430451 4252585619285679711645677)
                  ·
                    refine ⟨1594719607232129891867129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4252585619285679711645677 1594719607232129891867129)
                    ·
                      refine ⟨1196039705424097418900347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594719607232129891867129 1196039705424097418900347)
                      ·
                        rfl

theorem cell23_2329279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_2329279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329279 prefixEnd_2329279 := by exact prefixLift 2329279
  have htrace : WordTrace (prefixWord ++ tailWord_2329279) baseStart_2329279 baseEnd_2329279 := by
    simpa [prefixWord, tailWord_2329279, baseEnd_2329279] using wordTrace_append hprefix tailTrace_2329279
  have hstable : (prefixWord ++ tailWord_2329279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329279).length < 2 ^ (prefixWord ++ tailWord_2329279).sum := by decide
  have hdescent : baseEnd_2329279 < baseStart_2329279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329295 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 3]
def baseStart_2329295 : Nat := 118140960795 + 2329295 * 2 ^ 59
def prefixEnd_2329295 : Nat := 4983230072969 + 3 ^ 40 * 2329295 * 2
def baseEnd_2329295 : Nat := 1196047921114569356300273

theorem tailTrace_2329295 : CollatzResearch.WordTrace tailWord_2329295 prefixEnd_2329295 1196047921114569356300273 := by
  unfold tailWord_2329295
  simp only [CollatzResearch.WordTrace]
  refine ⟨84956368096369501759685339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56637578730913001173123559 84956368096369501759685339)
  ·
    refine ⟨127434552144554252639528009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84956368096369501759685339 127434552144554252639528009)
    ·
      refine ⟨95575914108415689479646007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127434552144554252639528009 95575914108415689479646007)
      ·
        refine ⟨143363871162623534219469011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95575914108415689479646007 143363871162623534219469011)
        ·
          refine ⟨215045806743935301329203517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143363871162623534219469011 215045806743935301329203517)
          ·
            refine ⟨80642177528975737998451319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215045806743935301329203517 80642177528975737998451319)
            ·
              refine ⟨120963266293463606997676979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80642177528975737998451319 120963266293463606997676979)
              ·
                refine ⟨181444899440195410496515469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120963266293463606997676979 181444899440195410496515469)
                ·
                  refine ⟨68041837290073278936193301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 181444899440195410496515469 68041837290073278936193301)
                  ·
                    refine ⟨3189461122972184950134061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 68041837290073278936193301 3189461122972184950134061)
                    ·
                      refine ⟨1196047921114569356300273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3189461122972184950134061 1196047921114569356300273)
                      ·
                        rfl

theorem cell23_2329295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 6, 3].length) (baseStart_2329295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329295 prefixEnd_2329295 := by exact prefixLift 2329295
  have htrace : WordTrace (prefixWord ++ tailWord_2329295) baseStart_2329295 baseEnd_2329295 := by
    simpa [prefixWord, tailWord_2329295, baseEnd_2329295] using wordTrace_append hprefix tailTrace_2329295
  have hstable : (prefixWord ++ tailWord_2329295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329295).length < 2 ^ (prefixWord ++ tailWord_2329295).sum := by decide
  have hdescent : baseEnd_2329295 < baseStart_2329295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329320 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_2329320 : Nat := 118140960795 + 2329320 * 2 ^ 59
def prefixEnd_2329320 : Nat := 4983230072969 + 3 ^ 40 * 2329320 * 2
def baseEnd_2329320 : Nat := 1196060758130931758487659

theorem tailTrace_2329320 : CollatzResearch.WordTrace tailWord_2329320 prefixEnd_2329320 1196060758130931758487659 := by
  unfold tailWord_2329320
  simp only [CollatzResearch.WordTrace]
  refine ⟨42478639960639465514672707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56638186614185954019563609 42478639960639465514672707)
  ·
    refine ⟨63717959940959198272009061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42478639960639465514672707 63717959940959198272009061)
    ·
      refine ⟨11947117488929849676001699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63717959940959198272009061 11947117488929849676001699)
      ·
        refine ⟨17920676233394774514002549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11947117488929849676001699 17920676233394774514002549)
        ·
          refine ⟨1680063396880760110687739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17920676233394774514002549 1680063396880760110687739)
          ·
            refine ⟨2520095095321140166031609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680063396880760110687739 2520095095321140166031609)
            ·
              refine ⟨1890071321490855124523707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2520095095321140166031609 1890071321490855124523707)
              ·
                refine ⟨2835106982236282686785561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890071321490855124523707 2835106982236282686785561)
                ·
                  refine ⟨2126330236677212015089171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2835106982236282686785561 2126330236677212015089171)
                  ·
                    refine ⟨3189495355015818022633757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2126330236677212015089171 3189495355015818022633757)
                    ·
                      refine ⟨1196060758130931758487659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3189495355015818022633757 1196060758130931758487659)
                      ·
                        rfl

theorem cell23_2329320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_2329320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329320 prefixEnd_2329320 := by exact prefixLift 2329320
  have htrace : WordTrace (prefixWord ++ tailWord_2329320) baseStart_2329320 baseEnd_2329320 := by
    simpa [prefixWord, tailWord_2329320, baseEnd_2329320] using wordTrace_append hprefix tailTrace_2329320
  have hstable : (prefixWord ++ tailWord_2329320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329320).length < 2 ^ (prefixWord ++ tailWord_2329320).sum := by decide
  have hdescent : baseEnd_2329320 < baseStart_2329320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329372 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_2329372 : Nat := 118140960795 + 2329372 * 2 ^ 59
def prefixEnd_2329372 : Nat := 4983230072969 + 3 ^ 40 * 2329372 * 2
def baseEnd_2329372 : Nat := 1196087459124965555037419

theorem tailTrace_2329372 : CollatzResearch.WordTrace tailWord_2329372 prefixEnd_2329372 1196087459124965555037419 := by
  unfold tailWord_2329372
  simp only [CollatzResearch.WordTrace]
  refine ⟨42479588258545271955119185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56639451011393695940158913 42479588258545271955119185)
  ·
    refine ⟨31859691193908953966339389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42479588258545271955119185 31859691193908953966339389)
    ·
      refine ⟨11947384197715857737377271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31859691193908953966339389 11947384197715857737377271)
      ·
        refine ⟨17921076296573786606065907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11947384197715857737377271 17921076296573786606065907)
        ·
          refine ⟨26881614444860679909098861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17921076296573786606065907 26881614444860679909098861)
          ·
            refine ⟨10080605416822754965912073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26881614444860679909098861 10080605416822754965912073)
            ·
              refine ⟨7560454062617066224434055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10080605416822754965912073 7560454062617066224434055)
              ·
                refine ⟨11340681093925599336651083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7560454062617066224434055 11340681093925599336651083)
                ·
                  refine ⟨17011021640888399004976625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11340681093925599336651083 17011021640888399004976625)
                  ·
                    refine ⟨12758266230666299253732469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17011021640888399004976625 12758266230666299253732469)
                    ·
                      refine ⟨1196087459124965555037419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12758266230666299253732469 1196087459124965555037419)
                      ·
                        rfl

theorem cell23_2329372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_2329372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329372 prefixEnd_2329372 := by exact prefixLift 2329372
  have htrace : WordTrace (prefixWord ++ tailWord_2329372) baseStart_2329372 baseEnd_2329372 := by
    simpa [prefixWord, tailWord_2329372, baseEnd_2329372] using wordTrace_append hprefix tailTrace_2329372
  have hstable : (prefixWord ++ tailWord_2329372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329372).length < 2 ^ (prefixWord ++ tailWord_2329372).sum := by decide
  have hdescent : baseEnd_2329372 < baseStart_2329372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329385 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_2329385 : Nat := 118140960795 + 2329385 * 2 ^ 59
def prefixEnd_2329385 : Nat := 4983230072969 + 3 ^ 40 * 2329385 * 2
def baseEnd_2329385 : Nat := 1196094134373474004174859

theorem tailTrace_2329385 : CollatzResearch.WordTrace tailWord_2329385 prefixEnd_2329385 1196094134373474004174859 := by
  unfold tailWord_2329385
  simp only [CollatzResearch.WordTrace]
  refine ⟨84959650666043447130461609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56639767110695631420307739 84959650666043447130461609)
  ·
    refine ⟨63719737999532585347846207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84959650666043447130461609 63719737999532585347846207)
    ·
      refine ⟨95579606999298878021769311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63719737999532585347846207 95579606999298878021769311)
      ·
        refine ⟨143369410498948317032653967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95579606999298878021769311 143369410498948317032653967)
        ·
          refine ⟨215054115748422475548980951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143369410498948317032653967 215054115748422475548980951)
          ·
            refine ⟨322581173622633713323471427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215054115748422475548980951 322581173622633713323471427)
            ·
              refine ⟨483871760433950569985207141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322581173622633713323471427 483871760433950569985207141)
              ·
                refine ⟨90725955081365731872226339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 483871760433950569985207141 90725955081365731872226339)
                ·
                  refine ⟨136088932622048597808339509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90725955081365731872226339 136088932622048597808339509)
                  ·
                    refine ⟨12758337433317056044531829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 136088932622048597808339509 12758337433317056044531829)
                    ·
                      refine ⟨1196094134373474004174859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12758337433317056044531829 1196094134373474004174859)
                      ·
                        rfl

theorem cell23_2329385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_2329385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329385 prefixEnd_2329385 := by exact prefixLift 2329385
  have htrace : WordTrace (prefixWord ++ tailWord_2329385) baseStart_2329385 baseEnd_2329385 := by
    simpa [prefixWord, tailWord_2329385, baseEnd_2329385] using wordTrace_append hprefix tailTrace_2329385
  have hstable : (prefixWord ++ tailWord_2329385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329385).length < 2 ^ (prefixWord ++ tailWord_2329385).sum := by decide
  have hdescent : baseEnd_2329385 < baseStart_2329385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329426 : List Nat := [3, 2, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_2329426 : Nat := 118140960795 + 2329426 * 2 ^ 59
def prefixEnd_2329426 : Nat := 4983230072969 + 3 ^ 40 * 2329426 * 2
def baseEnd_2329426 : Nat := 398705062360102781254057

theorem tailTrace_2329426 : CollatzResearch.WordTrace tailWord_2329426 prefixEnd_2329426 398705062360102781254057 := by
  unfold tailWord_2329426
  simp only [CollatzResearch.WordTrace]
  refine ⟨21240286514723727783176033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56640764039263274088469421 21240286514723727783176033)
  ·
    refine ⟨15930214886042795837382025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21240286514723727783176033 15930214886042795837382025)
    ·
      refine ⟨11947661164532096878036519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15930214886042795837382025 11947661164532096878036519)
      ·
        refine ⟨17921491746798145317054779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11947661164532096878036519 17921491746798145317054779)
        ·
          refine ⟨26882237620197217975582169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17921491746798145317054779 26882237620197217975582169)
          ·
            refine ⟨20161678215147913481686627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26882237620197217975582169 20161678215147913481686627)
            ·
              refine ⟨30242517322721870222529941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20161678215147913481686627 30242517322721870222529941)
              ·
                refine ⟨1417617999502587666681091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30242517322721870222529941 1417617999502587666681091)
                ·
                  refine ⟨2126426999253881500021637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417617999502587666681091 2126426999253881500021637)
                  ·
                    refine ⟨398705062360102781254057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2126426999253881500021637 398705062360102781254057)
                    ·
                      rfl

theorem cell23_2329426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_2329426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329426 prefixEnd_2329426 := by exact prefixLift 2329426
  have htrace : WordTrace (prefixWord ++ tailWord_2329426) baseStart_2329426 baseEnd_2329426 := by
    simpa [prefixWord, tailWord_2329426, baseEnd_2329426] using wordTrace_append hprefix tailTrace_2329426
  have hstable : (prefixWord ++ tailWord_2329426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329426).length < 2 ^ (prefixWord ++ tailWord_2329426).sum := by decide
  have hdescent : baseEnd_2329426 < baseStart_2329426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329439 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 6]
def baseStart_2329439 : Nat := 118140960795 + 2329439 * 2 ^ 59
def prefixEnd_2329439 : Nat := 4983230072969 + 3 ^ 40 * 2329439 * 2
def baseEnd_2329439 : Nat := 132902429147646310322179

theorem tailTrace_2329439 : CollatzResearch.WordTrace tailWord_2329439 prefixEnd_2329439 132902429147646310322179 := by
  unfold tailWord_2329439
  simp only [CollatzResearch.WordTrace]
  refine ⟨84961620207847814352927371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56641080138565209568618247 84961620207847814352927371)
  ·
    refine ⟨127442430311771721529391057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84961620207847814352927371 127442430311771721529391057)
    ·
      refine ⟨95581822733828791147043293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127442430311771721529391057 95581822733828791147043293)
      ·
        refine ⟨35843183525185796680141235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95581822733828791147043293 35843183525185796680141235)
        ·
          refine ⟨53764775287778695020211853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35843183525185796680141235 53764775287778695020211853)
          ·
            refine ⟨20161790732917010632579445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53764775287778695020211853 20161790732917010632579445)
            ·
              refine ⟨1890167881210969746804323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20161790732917010632579445 1890167881210969746804323)
              ·
                refine ⟨2835251821816454620206485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890167881210969746804323 2835251821816454620206485)
                ·
                  refine ⟨132902429147646310322179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2835251821816454620206485 132902429147646310322179)
                  ·
                    rfl

theorem cell23_2329439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 6].length) (baseStart_2329439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329439 prefixEnd_2329439 := by exact prefixLift 2329439
  have htrace : WordTrace (prefixWord ++ tailWord_2329439) baseStart_2329439 baseEnd_2329439 := by
    simpa [prefixWord, tailWord_2329439, baseEnd_2329439] using wordTrace_append hprefix tailTrace_2329439
  have hstable : (prefixWord ++ tailWord_2329439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329439).length < 2 ^ (prefixWord ++ tailWord_2329439).sum := by decide
  have hdescent : baseEnd_2329439 < baseStart_2329439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329459 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 1, 5, 2]
def baseStart_2329459 : Nat := 118140960795 + 2329459 * 2 ^ 59
def prefixEnd_2329459 : Nat := 4983230072969 + 3 ^ 40 * 2329459 * 2
def baseEnd_2329459 : Nat := 1196132131941906714649519

theorem tailTrace_2329459 : CollatzResearch.WordTrace tailWord_2329459 prefixEnd_2329459 1196132131941906714649519 := by
  unfold tailWord_2329459
  simp only [CollatzResearch.WordTrace]
  refine ⟨84962349667775357768655431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56641566445183571845770287 84962349667775357768655431)
  ·
    refine ⟨127443524501663036652983147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84962349667775357768655431 127443524501663036652983147)
    ·
      refine ⟨191165286752494554979474721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127443524501663036652983147 191165286752494554979474721)
      ·
        refine ⟨143373965064370916234606041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191165286752494554979474721 143373965064370916234606041)
        ·
          refine ⟨107530473798278187175954531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143373965064370916234606041 107530473798278187175954531)
          ·
            refine ⟨161295710697417280763931797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107530473798278187175954531 161295710697417280763931797)
            ·
              refine ⟨7560736438941435035809303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 161295710697417280763931797 7560736438941435035809303)
              ·
                refine ⟨11341104658412152553713955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7560736438941435035809303 11341104658412152553713955)
                ·
                  refine ⟨17011656987618228830570933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11341104658412152553713955 17011656987618228830570933)
                  ·
                    refine ⟨1594842842589208952866025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17011656987618228830570933 1594842842589208952866025)
                    ·
                      refine ⟨1196132131941906714649519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594842842589208952866025 1196132131941906714649519)
                      ·
                        rfl

theorem cell23_2329459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 5, 2].length) (baseStart_2329459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329459 prefixEnd_2329459 := by exact prefixLift 2329459
  have htrace : WordTrace (prefixWord ++ tailWord_2329459) baseStart_2329459 baseEnd_2329459 := by
    simpa [prefixWord, tailWord_2329459, baseEnd_2329459] using wordTrace_append hprefix tailTrace_2329459
  have hstable : (prefixWord ++ tailWord_2329459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329459).length < 2 ^ (prefixWord ++ tailWord_2329459).sum := by decide
  have hdescent : baseEnd_2329459 < baseStart_2329459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329469 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_2329469 : Nat := 118140960795 + 2329469 * 2 ^ 59
def prefixEnd_2329469 : Nat := 4983230072969 + 3 ^ 40 * 2329469 * 2
def baseEnd_2329469 : Nat := 398712422249483891841491

theorem tailTrace_2329469 : CollatzResearch.WordTrace tailWord_2329469 prefixEnd_2329469 398712422249483891841491 := by
  unfold tailWord_2329469
  simp only [CollatzResearch.WordTrace]
  refine ⟨84962714397739129476519461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56641809598492752984346307 84962714397739129476519461)
  ·
    refine ⟨15930508949576086776847399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84962714397739129476519461 15930508949576086776847399)
    ·
      refine ⟨23895763424364130165271099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15930508949576086776847399 23895763424364130165271099)
      ·
        refine ⟨35843645136546195247906649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23895763424364130165271099 35843645136546195247906649)
        ·
          refine ⟨26882733852409646435929987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35843645136546195247906649 26882733852409646435929987)
          ·
            refine ⟨40324100778614469653894981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26882733852409646435929987 40324100778614469653894981)
            ·
              refine ⟨7560768895990213060105309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40324100778614469653894981 7560768895990213060105309)
              ·
                refine ⟨2835288335996329897539491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7560768895990213060105309 2835288335996329897539491)
                ·
                  refine ⟨4252932503994494846309237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835288335996329897539491 4252932503994494846309237)
                  ·
                    refine ⟨398712422249483891841491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4252932503994494846309237 398712422249483891841491)
                    ·
                      rfl

theorem cell23_2329469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_2329469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329469 prefixEnd_2329469 := by exact prefixLift 2329469
  have htrace : WordTrace (prefixWord ++ tailWord_2329469) baseStart_2329469 baseEnd_2329469 := by
    simpa [prefixWord, tailWord_2329469, baseEnd_2329469] using wordTrace_append hprefix tailTrace_2329469
  have hstable : (prefixWord ++ tailWord_2329469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329469).length < 2 ^ (prefixWord ++ tailWord_2329469).sum := by decide
  have hdescent : baseEnd_2329469 < baseStart_2329469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329490 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 6]
def baseStart_2329490 : Nat := 118140960795 + 2329490 * 2 ^ 59
def prefixEnd_2329490 : Nat := 4983230072969 + 3 ^ 40 * 2329490 * 2
def baseEnd_2329490 : Nat := 132905338871355121484653

theorem tailTrace_2329490 : CollatzResearch.WordTrace tailWord_2329490 prefixEnd_2329490 132905338871355121484653 := by
  unfold tailWord_2329490
  simp only [CollatzResearch.WordTrace]
  refine ⟨21240870082665762515758481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56642320220442033375355949 21240870082665762515758481)
  ·
    refine ⟨15930652561999321886818861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21240870082665762515758481 15930652561999321886818861)
    ·
      refine ⟨5973994710749745707557073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15930652561999321886818861 5973994710749745707557073)
      ·
        refine ⟨4480496033062309280667805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5973994710749745707557073 4480496033062309280667805)
        ·
          refine ⟨1680186012398365980250427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4480496033062309280667805 1680186012398365980250427)
          ·
            refine ⟨2520279018597548970375641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680186012398365980250427 2520279018597548970375641)
            ·
              refine ⟨1890209263948161727781731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2520279018597548970375641 1890209263948161727781731)
              ·
                refine ⟨2835313895922242591672597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890209263948161727781731 2835313895922242591672597)
                ·
                  refine ⟨132905338871355121484653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2835313895922242591672597 132905338871355121484653)
                  ·
                    rfl

theorem cell23_2329490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_2329490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329490 prefixEnd_2329490 := by exact prefixLift 2329490
  have htrace : WordTrace (prefixWord ++ tailWord_2329490) baseStart_2329490 baseEnd_2329490 := by
    simpa [prefixWord, tailWord_2329490, baseEnd_2329490] using wordTrace_append hprefix tailTrace_2329490
  have hstable : (prefixWord ++ tailWord_2329490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329490).length < 2 ^ (prefixWord ++ tailWord_2329490).sum := by decide
  have hdescent : baseEnd_2329490 < baseStart_2329490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329506 : List Nat := [3, 3, 1, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2329506 : Nat := 118140960795 + 2329506 * 2 ^ 59
def prefixEnd_2329506 : Nat := 4983230072969 + 3 ^ 40 * 2329506 * 2
def baseEnd_2329506 : Nat := 1196156265532668030761803

theorem tailTrace_2329506 : CollatzResearch.WordTrace tailWord_2329506 prefixEnd_2329506 1196156265532668030761803 := by
  unfold tailWord_2329506
  simp only [CollatzResearch.WordTrace]
  refine ⟨21241015974651271198904093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56642709265736723197077581 21241015974651271198904093)
  ·
    refine ⟨7965380990494226699589035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21241015974651271198904093 7965380990494226699589035)
    ·
      refine ⟨11948071485741340049383553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7965380990494226699589035 11948071485741340049383553)
      ·
        refine ⟨8961053614306005037037665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11948071485741340049383553 8961053614306005037037665)
        ·
          refine ⟨6720790210729503777778249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8961053614306005037037665 6720790210729503777778249)
          ·
            refine ⟨5040592658047127833333687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6720790210729503777778249 5040592658047127833333687)
            ·
              refine ⟨7560888987070691750000531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5040592658047127833333687 7560888987070691750000531)
              ·
                refine ⟨11341333480606037625000797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7560888987070691750000531 11341333480606037625000797)
                ·
                  refine ⟨4253000055227264109375299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11341333480606037625000797 4253000055227264109375299)
                  ·
                    refine ⟨6379500082840896164062949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4253000055227264109375299 6379500082840896164062949)
                    ·
                      refine ⟨1196156265532668030761803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6379500082840896164062949 1196156265532668030761803)
                      ·
                        rfl

theorem cell23_2329506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2329506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329506 prefixEnd_2329506 := by exact prefixLift 2329506
  have htrace : WordTrace (prefixWord ++ tailWord_2329506) baseStart_2329506 baseEnd_2329506 := by
    simpa [prefixWord, tailWord_2329506, baseEnd_2329506] using wordTrace_append hprefix tailTrace_2329506
  have hstable : (prefixWord ++ tailWord_2329506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329506).length < 2 ^ (prefixWord ++ tailWord_2329506).sum := by decide
  have hdescent : baseEnd_2329506 < baseStart_2329506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329533 : List Nat := [1, 4, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_2329533 : Nat := 118140960795 + 2329533 * 2 ^ 59
def prefixEnd_2329533 : Nat := 4983230072969 + 3 ^ 40 * 2329533 * 2
def baseEnd_2329533 : Nat := 398723376503446475041393

theorem tailTrace_2329533 : CollatzResearch.WordTrace tailWord_2329533 prefixEnd_2329533 398723376503446475041393 := by
  unfold tailWord_2329533
  simp only [CollatzResearch.WordTrace]
  refine ⟨84965048669507268406849253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56643365779671512271232835 84965048669507268406849253)
  ·
    refine ⟨15930946625532612826284235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84965048669507268406849253 15930946625532612826284235)
    ·
      refine ⟨23896419938298919239426353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15930946625532612826284235 23896419938298919239426353)
      ·
        refine ⟨17922314953724189429569765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23896419938298919239426353 17922314953724189429569765)
        ·
          refine ⟨3360434053823285518044331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17922314953724189429569765 3360434053823285518044331)
          ·
            refine ⟨5040651080734928277066497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360434053823285518044331 5040651080734928277066497)
            ·
              refine ⟨3780488310551196207799873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5040651080734928277066497 3780488310551196207799873)
              ·
                refine ⟨2835366232913397155849905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3780488310551196207799873 2835366232913397155849905)
                ·
                  refine ⟨2126524674685047866887429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2835366232913397155849905 2126524674685047866887429)
                  ·
                    refine ⟨398723376503446475041393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2126524674685047866887429 398723376503446475041393)
                    ·
                      rfl

theorem cell23_2329533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_2329533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329533 prefixEnd_2329533 := by exact prefixLift 2329533
  have htrace : WordTrace (prefixWord ++ tailWord_2329533) baseStart_2329533 baseEnd_2329533 := by
    simpa [prefixWord, tailWord_2329533, baseEnd_2329533] using wordTrace_append hprefix tailTrace_2329533
  have hstable : (prefixWord ++ tailWord_2329533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329533).length < 2 ^ (prefixWord ++ tailWord_2329533).sum := by decide
  have hdescent : baseEnd_2329533 < baseStart_2329533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329552 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 5]
def baseStart_2329552 : Nat := 118140960795 + 2329552 * 2 ^ 59
def prefixEnd_2329552 : Nat := 4983230072969 + 3 ^ 40 * 2329552 * 2
def baseEnd_2329552 : Nat := 1196179885642774850786591

theorem tailTrace_2329552 : CollatzResearch.WordTrace tailWord_2329552 prefixEnd_2329552 1196179885642774850786591 := by
  unfold tailWord_2329552
  simp only [CollatzResearch.WordTrace]
  refine ⟨42482870828219217325895455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56643827770958956434527273 42482870828219217325895455)
  ·
    refine ⟨63724306242328825988843183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42482870828219217325895455 63724306242328825988843183)
    ·
      refine ⟨95586459363493238983264775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63724306242328825988843183 95586459363493238983264775)
      ·
        refine ⟨143379689045239858474897163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95586459363493238983264775 143379689045239858474897163)
        ·
          refine ⟨215069533567859787712345745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143379689045239858474897163 215069533567859787712345745)
          ·
            refine ⟨161302150175894840784259309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215069533567859787712345745 161302150175894840784259309)
            ·
              refine ⟨60488306315960565294097241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161302150175894840784259309 60488306315960565294097241)
              ·
                refine ⟨45366229736970423970572931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60488306315960565294097241 45366229736970423970572931)
                ·
                  refine ⟨68049344605455635955859397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45366229736970423970572931 68049344605455635955859397)
                  ·
                    refine ⟨12759252113522931741723637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68049344605455635955859397 12759252113522931741723637)
                    ·
                      refine ⟨1196179885642774850786591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12759252113522931741723637 1196179885642774850786591)
                      ·
                        rfl

theorem cell23_2329552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_2329552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329552 prefixEnd_2329552 := by exact prefixLift 2329552
  have htrace : WordTrace (prefixWord ++ tailWord_2329552) baseStart_2329552 baseEnd_2329552 := by
    simpa [prefixWord, tailWord_2329552, baseEnd_2329552] using wordTrace_append hprefix tailTrace_2329552
  have hstable : (prefixWord ++ tailWord_2329552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329552).length < 2 ^ (prefixWord ++ tailWord_2329552).sum := by decide
  have hdescent : baseEnd_2329552 < baseStart_2329552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329556 : List Nat := [2, 4, 1, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2329556 : Nat := 118140960795 + 2329556 * 2 ^ 59
def prefixEnd_2329556 : Nat := 4983230072969 + 3 ^ 40 * 2329556 * 2
def baseEnd_2329556 : Nat := 1196181939565392835136573

theorem tailTrace_2329556 : CollatzResearch.WordTrace tailWord_2329556 prefixEnd_2329556 1196181939565392835136573 := by
  unfold tailWord_2329556
  simp only [CollatzResearch.WordTrace]
  refine ⟨42482943774211971667468261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56643925032282628889957681 42482943774211971667468261)
  ·
    refine ⟨7965551957664744687650299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42482943774211971667468261 7965551957664744687650299)
    ·
      refine ⟨11948327936497117031475449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7965551957664744687650299 11948327936497117031475449)
      ·
        refine ⟨8961245952372837773606587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11948327936497117031475449 8961245952372837773606587)
        ·
          refine ⟨13441868928559256660409881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8961245952372837773606587 13441868928559256660409881)
          ·
            refine ⟨10081401696419442495307411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13441868928559256660409881 10081401696419442495307411)
            ·
              refine ⟨15122102544629163742961117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10081401696419442495307411 15122102544629163742961117)
              ·
                refine ⟨5670788454235936403610419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15122102544629163742961117 5670788454235936403610419)
                ·
                  refine ⟨8506182681353904605415629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5670788454235936403610419 8506182681353904605415629)
                  ·
                    refine ⟨3189818505507714227030861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8506182681353904605415629 3189818505507714227030861)
                    ·
                      refine ⟨1196181939565392835136573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3189818505507714227030861 1196181939565392835136573)
                      ·
                        rfl

theorem cell23_2329556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2329556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329556 prefixEnd_2329556 := by exact prefixLift 2329556
  have htrace : WordTrace (prefixWord ++ tailWord_2329556) baseStart_2329556 baseEnd_2329556 := by
    simpa [prefixWord, tailWord_2329556, baseEnd_2329556] using wordTrace_append hprefix tailTrace_2329556
  have hstable : (prefixWord ++ tailWord_2329556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329556).length < 2 ^ (prefixWord ++ tailWord_2329556).sum := by decide
  have hdescent : baseEnd_2329556 < baseStart_2329556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329583 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 1, 3, 2]
def baseStart_2329583 : Nat := 118140960795 + 2329583 * 2 ^ 59
def prefixEnd_2329583 : Nat := 4983230072969 + 3 ^ 40 * 2329583 * 2
def baseEnd_2329583 : Nat := 1196195803543064229498949

theorem tailTrace_2329583 : CollatzResearch.WordTrace tailWord_2329583 prefixEnd_2329583 1196195803543064229498949 := by
  unfold tailWord_2329583
  simp only [CollatzResearch.WordTrace]
  refine ⟨84966872319326126946169403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56644581546217417964112935 84966872319326126946169403)
  ·
    refine ⟨127450308478989190419254105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84966872319326126946169403 127450308478989190419254105)
    ·
      refine ⟨95587731359241892814440579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127450308478989190419254105 95587731359241892814440579)
      ·
        refine ⟨143381597038862839221660869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95587731359241892814440579 143381597038862839221660869)
        ·
          refine ⟨26884049444786782354061413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143381597038862839221660869 26884049444786782354061413)
          ·
            refine ⟨5040759270897521691386515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26884049444786782354061413 5040759270897521691386515)
            ·
              refine ⟨7561138906346282537079773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5040759270897521691386515 7561138906346282537079773)
              ·
                refine ⟨2835427089879855951404915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7561138906346282537079773 2835427089879855951404915)
                ·
                  refine ⟨4253140634819783927107373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835427089879855951404915 4253140634819783927107373)
                  ·
                    refine ⟨1594927738057418972665265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4253140634819783927107373 1594927738057418972665265)
                    ·
                      refine ⟨1196195803543064229498949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1594927738057418972665265 1196195803543064229498949)
                      ·
                        rfl

theorem cell23_2329583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 3, 2].length) (baseStart_2329583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329583 prefixEnd_2329583 := by exact prefixLift 2329583
  have htrace : WordTrace (prefixWord ++ tailWord_2329583) baseStart_2329583 baseEnd_2329583 := by
    simpa [prefixWord, tailWord_2329583, baseEnd_2329583] using wordTrace_append hprefix tailTrace_2329583
  have hstable : (prefixWord ++ tailWord_2329583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329583).length < 2 ^ (prefixWord ++ tailWord_2329583).sum := by decide
  have hdescent : baseEnd_2329583 < baseStart_2329583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329590 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_2329590 : Nat := 118140960795 + 2329590 * 2 ^ 59
def prefixEnd_2329590 : Nat := 4983230072969 + 3 ^ 40 * 2329590 * 2
def baseEnd_2329590 : Nat := 1196199397907645702111417

theorem tailTrace_2329590 : CollatzResearch.WordTrace tailWord_2329590 prefixEnd_2329590 1196199397907645702111417 := by
  unfold tailWord_2329590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5310445476893797946354639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56644751753533844761116149 5310445476893797946354639)
  ·
    refine ⟨7965668215340696919531959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5310445476893797946354639 7965668215340696919531959)
    ·
      refine ⟨11948502323011045379297939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7965668215340696919531959 11948502323011045379297939)
      ·
        refine ⟨17922753484516568068946909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11948502323011045379297939 17922753484516568068946909)
        ·
          refine ⟨6721032556693713025855091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17922753484516568068946909 6721032556693713025855091)
          ·
            refine ⟨10081548835040569538782637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6721032556693713025855091 10081548835040569538782637)
            ·
              refine ⟨3780580813140213577043489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10081548835040569538782637 3780580813140213577043489)
              ·
                refine ⟨2835435609855160182782617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3780580813140213577043489 2835435609855160182782617)
                ·
                  refine ⟨2126576707391370137086963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2835435609855160182782617 2126576707391370137086963)
                  ·
                    refine ⟨3189865061087055205630445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2126576707391370137086963 3189865061087055205630445)
                    ·
                      refine ⟨1196199397907645702111417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3189865061087055205630445 1196199397907645702111417)
                      ·
                        rfl

theorem cell23_2329590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_2329590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329590 prefixEnd_2329590 := by exact prefixLift 2329590
  have htrace : WordTrace (prefixWord ++ tailWord_2329590) baseStart_2329590 baseEnd_2329590 := by
    simpa [prefixWord, tailWord_2329590, baseEnd_2329590] using wordTrace_append hprefix tailTrace_2329590
  have hstable : (prefixWord ++ tailWord_2329590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329590).length < 2 ^ (prefixWord ++ tailWord_2329590).sum := by decide
  have hdescent : baseEnd_2329590 < baseStart_2329590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329669 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_2329669 : Nat := 118140960795 + 2329669 * 2 ^ 59
def prefixEnd_2329669 : Nat := 4983230072969 + 3 ^ 40 * 2329669 * 2
def baseEnd_2329669 : Nat := 1196239962879350893023553

theorem tailTrace_2329669 : CollatzResearch.WordTrace tailWord_2329669 prefixEnd_2329669 1196239962879350893023553 := by
  unfold tailWord_2329669
  simp only [CollatzResearch.WordTrace]
  refine ⟨84970008997014563633800061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56646672664676375755866707 84970008997014563633800061)
  ·
    refine ⟨31863753373880461362675023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84970008997014563633800061 31863753373880461362675023)
    ·
      refine ⟨47795630060820692044012535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31863753373880461362675023 47795630060820692044012535)
      ·
        refine ⟨71693445091231038066018803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47795630060820692044012535 71693445091231038066018803)
        ·
          refine ⟨107540167636846557099028205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71693445091231038066018803 107540167636846557099028205)
          ·
            refine ⟨40327562863817458912135577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107540167636846557099028205 40327562863817458912135577)
            ·
              refine ⟨30245672147863094184101683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40327562863817458912135577 30245672147863094184101683)
              ·
                refine ⟨45368508221794641276152525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30245672147863094184101683 45368508221794641276152525)
                ·
                  refine ⟨17013190583172990478557197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45368508221794641276152525 17013190583172990478557197)
                  ·
                    refine ⟨6379946468689871429458949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17013190583172990478557197 6379946468689871429458949)
                    ·
                      refine ⟨1196239962879350893023553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6379946468689871429458949 1196239962879350893023553)
                      ·
                        rfl

theorem cell23_2329669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_2329669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329669 prefixEnd_2329669 := by exact prefixLift 2329669
  have htrace : WordTrace (prefixWord ++ tailWord_2329669) baseStart_2329669 baseEnd_2329669 := by
    simpa [prefixWord, tailWord_2329669, baseEnd_2329669] using wordTrace_append hprefix tailTrace_2329669
  have hstable : (prefixWord ++ tailWord_2329669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329669).length < 2 ^ (prefixWord ++ tailWord_2329669).sum := by decide
  have hdescent : baseEnd_2329669 < baseStart_2329669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329699 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2329699 : Nat := 118140960795 + 2329699 * 2 ^ 59
def prefixEnd_2329699 : Nat := 4983230072969 + 3 ^ 40 * 2329699 * 2
def baseEnd_2329699 : Nat := 1196255367298985775648415

theorem tailTrace_2329699 : CollatzResearch.WordTrace tailWord_2329699 prefixEnd_2329699 1196255367298985775648415 := by
  unfold tailWord_2329699
  simp only [CollatzResearch.WordTrace]
  refine ⟨84971103186905878757392151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56647402124603919171594767 84971103186905878757392151)
  ·
    refine ⟨127456654780358818136088227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84971103186905878757392151 127456654780358818136088227)
    ·
      refine ⟨191184982170538227204132341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127456654780358818136088227 191184982170538227204132341)
      ·
        refine ⟨17923592078487958800387407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 191184982170538227204132341 17923592078487958800387407)
        ·
          refine ⟨26885388117731938200581111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17923592078487958800387407 26885388117731938200581111)
          ·
            refine ⟨40328082176597907300871667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26885388117731938200581111 40328082176597907300871667)
            ·
              refine ⟨60492123264896860951307501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40328082176597907300871667 60492123264896860951307501)
              ·
                refine ⟨22684546224336322856740313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60492123264896860951307501 22684546224336322856740313)
                ·
                  refine ⟨17013409668252242142555235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22684546224336322856740313 17013409668252242142555235)
                  ·
                    refine ⟨25520114502378363213832853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17013409668252242142555235 25520114502378363213832853)
                    ·
                      refine ⟨1196255367298985775648415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25520114502378363213832853 1196255367298985775648415)
                      ·
                        rfl

theorem cell23_2329699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2329699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329699 prefixEnd_2329699 := by exact prefixLift 2329699
  have htrace : WordTrace (prefixWord ++ tailWord_2329699) baseStart_2329699 baseEnd_2329699 := by
    simpa [prefixWord, tailWord_2329699, baseEnd_2329699] using wordTrace_append hprefix tailTrace_2329699
  have hstable : (prefixWord ++ tailWord_2329699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329699).length < 2 ^ (prefixWord ++ tailWord_2329699).sum := by decide
  have hdescent : baseEnd_2329699 < baseStart_2329699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329704 : List Nat := [2, 1, 4, 4, 2, 1, 2, 2, 5]
def baseStart_2329704 : Nat := 118140960795 + 2329704 * 2 ^ 59
def prefixEnd_2329704 : Nat := 4983230072969 + 3 ^ 40 * 2329704 * 2
def baseEnd_2329704 : Nat := 132917548300250917342877

theorem tailTrace_2329704 : CollatzResearch.WordTrace tailWord_2329704 prefixEnd_2329704 132917548300250917342877 := by
  unfold tailWord_2329704
  simp only [CollatzResearch.WordTrace]
  refine ⟨42485642775943882305662083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56647523701258509740882777 42485642775943882305662083)
  ·
    refine ⟨63728464163915823458493125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42485642775943882305662083 63728464163915823458493125)
    ·
      refine ⟨11949087030734216898467461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63728464163915823458493125 11949087030734216898467461)
      ·
        refine ⟨2240453818262665668462649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11949087030734216898467461 2240453818262665668462649)
        ·
          refine ⟨1680340363696999251346987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2240453818262665668462649 1680340363696999251346987)
          ·
            refine ⟨2520510545545498877020481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680340363696999251346987 2520510545545498877020481)
            ·
              refine ⟨1890382909159124157765361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2520510545545498877020481 1890382909159124157765361)
              ·
                refine ⟨1417787181869343118324021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890382909159124157765361 1417787181869343118324021)
                ·
                  refine ⟨132917548300250917342877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1417787181869343118324021 132917548300250917342877)
                  ·
                    rfl

theorem cell23_2329704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 2, 2, 5].length) (baseStart_2329704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329704 prefixEnd_2329704 := by exact prefixLift 2329704
  have htrace : WordTrace (prefixWord ++ tailWord_2329704) baseStart_2329704 baseEnd_2329704 := by
    simpa [prefixWord, tailWord_2329704, baseEnd_2329704] using wordTrace_append hprefix tailTrace_2329704
  have hstable : (prefixWord ++ tailWord_2329704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329704).length < 2 ^ (prefixWord ++ tailWord_2329704).sum := by decide
  have hdescent : baseEnd_2329704 < baseStart_2329704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329763 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 2, 3, 2]
def baseStart_2329763 : Nat := 118140960795 + 2329763 * 2 ^ 59
def prefixEnd_2329763 : Nat := 4983230072969 + 3 ^ 40 * 2329763 * 2
def baseEnd_2329763 : Nat := 1196288230060873525248121

theorem tailTrace_2329763 : CollatzResearch.WordTrace tailWord_2329763 prefixEnd_2329763 1196288230060873525248121 := by
  unfold tailWord_2329763
  simp only [CollatzResearch.WordTrace]
  refine ⟨84973437458674017687721943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56648958305782678458481295 84973437458674017687721943)
  ·
    refine ⟨127460156188011026531582915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84973437458674017687721943 127460156188011026531582915)
    ·
      refine ⟨191190234282016539797374373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127460156188011026531582915 191190234282016539797374373)
      ·
        refine ⟨35848168927878101212007695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191190234282016539797374373 35848168927878101212007695)
        ·
          refine ⟨53772253391817151818011543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35848168927878101212007695 53772253391817151818011543)
          ·
            refine ⟨80658380087725727727017315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53772253391817151818011543 80658380087725727727017315)
            ·
              refine ⟨120987570131588591590525973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80658380087725727727017315 120987570131588591590525973)
              ·
                refine ⟨5671292349918215230805905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120987570131588591590525973 5671292349918215230805905)
                ·
                  refine ⟨4253469262438661423104429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5671292349918215230805905 4253469262438661423104429)
                  ·
                    refine ⟨1595050973414498033664161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4253469262438661423104429 1595050973414498033664161)
                    ·
                      refine ⟨1196288230060873525248121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595050973414498033664161 1196288230060873525248121)
                      ·
                        rfl

theorem cell23_2329763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_2329763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329763 prefixEnd_2329763 := by exact prefixLift 2329763
  have htrace : WordTrace (prefixWord ++ tailWord_2329763) baseStart_2329763 baseEnd_2329763 := by
    simpa [prefixWord, tailWord_2329763, baseEnd_2329763] using wordTrace_append hprefix tailTrace_2329763
  have hstable : (prefixWord ++ tailWord_2329763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329763).length < 2 ^ (prefixWord ++ tailWord_2329763).sum := by decide
  have hdescent : baseEnd_2329763 < baseStart_2329763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329790 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_2329790 : Nat := 118140960795 + 2329790 * 2 ^ 59
def prefixEnd_2329790 : Nat := 4983230072969 + 3 ^ 40 * 2329790 * 2
def baseEnd_2329790 : Nat := 398767364679514973203499

theorem tailTrace_2329790 : CollatzResearch.WordTrace tailWord_2329790 prefixEnd_2329790 398767364679514973203499 := by
  unfold tailWord_2329790
  simp only [CollatzResearch.WordTrace]
  refine ⟨10621802778697025162369353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56649614819717467532636549 10621802778697025162369353)
  ·
    refine ⟨7966352084022768871777015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10621802778697025162369353 7966352084022768871777015)
    ·
      refine ⟨11949528126034153307665523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7966352084022768871777015 11949528126034153307665523)
      ·
        refine ⟨17924292189051229961498285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11949528126034153307665523 17924292189051229961498285)
        ·
          refine ⟨6721609570894211235561857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17924292189051229961498285 6721609570894211235561857)
          ·
            refine ⟨5041207178170658426671393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6721609570894211235561857 5041207178170658426671393)
            ·
              refine ⟨3780905383627993820003545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5041207178170658426671393 3780905383627993820003545)
              ·
                refine ⟨2835679037720995365002659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3780905383627993820003545 2835679037720995365002659)
                ·
                  refine ⟨4253518556581493047503989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835679037720995365002659 4253518556581493047503989)
                  ·
                    refine ⟨398767364679514973203499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4253518556581493047503989 398767364679514973203499)
                    ·
                      rfl

theorem cell23_2329790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_2329790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329790 prefixEnd_2329790 := by exact prefixLift 2329790
  have htrace : WordTrace (prefixWord ++ tailWord_2329790) baseStart_2329790 baseEnd_2329790 := by
    simpa [prefixWord, tailWord_2329790, baseEnd_2329790] using wordTrace_append hprefix tailTrace_2329790
  have hstable : (prefixWord ++ tailWord_2329790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329790).length < 2 ^ (prefixWord ++ tailWord_2329790).sum := by decide
  have hdescent : baseEnd_2329790 < baseStart_2329790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329798 : List Nat := [6, 1, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_2329798 : Nat := 118140960795 + 2329798 * 2 ^ 59
def prefixEnd_2329798 : Nat := 4983230072969 + 3 ^ 40 * 2329798 * 2
def baseEnd_2329798 : Nat := 398768733961260296103487

theorem tailTrace_2329798 : CollatzResearch.WordTrace tailWord_2329798 prefixEnd_2329798 398768733961260296103487 := by
  unfold tailWord_2329798
  simp only [CollatzResearch.WordTrace]
  refine ⟨2655459812923350583288939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 56649809342364812443497365 2655459812923350583288939)
  ·
    refine ⟨3983189719385025874933409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2655459812923350583288939 3983189719385025874933409)
    ·
      refine ⟨2987392289538769406200057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3983189719385025874933409 2987392289538769406200057)
      ·
        refine ⟨2240544217154077054650043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2987392289538769406200057 2240544217154077054650043)
        ·
          refine ⟨3360816325731115581975065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240544217154077054650043 3360816325731115581975065)
          ·
            refine ⟨2520612244298336686481299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3360816325731115581975065 2520612244298336686481299)
            ·
              refine ⟨3780918366447505029721949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2520612244298336686481299 3780918366447505029721949)
              ·
                refine ⟨1417844387417814386145731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3780918366447505029721949 1417844387417814386145731)
                ·
                  refine ⟨2126766581126721579218597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417844387417814386145731 2126766581126721579218597)
                  ·
                    refine ⟨398768733961260296103487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2126766581126721579218597 398768733961260296103487)
                    ·
                      rfl

theorem cell23_2329798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_2329798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329798 prefixEnd_2329798 := by exact prefixLift 2329798
  have htrace : WordTrace (prefixWord ++ tailWord_2329798) baseStart_2329798 baseEnd_2329798 := by
    simpa [prefixWord, tailWord_2329798, baseEnd_2329798] using wordTrace_append hprefix tailTrace_2329798
  have hstable : (prefixWord ++ tailWord_2329798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329798).length < 2 ^ (prefixWord ++ tailWord_2329798).sum := by decide
  have hdescent : baseEnd_2329798 < baseStart_2329798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329813 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2329813 : Nat := 118140960795 + 2329813 * 2 ^ 59
def prefixEnd_2329813 : Nat := 4983230072969 + 3 ^ 40 * 2329813 * 2
def baseEnd_2329813 : Nat := 1196313904093598329622891

theorem tailTrace_2329813 : CollatzResearch.WordTrace tailWord_2329813 prefixEnd_2329813 1196313904093598329622891 := by
  unfold tailWord_2329813
  simp only [CollatzResearch.WordTrace]
  refine ⟨84975261108492876227042093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56650174072328584151361395 84975261108492876227042093)
  ·
    refine ⟨31865722915684828585140785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84975261108492876227042093 31865722915684828585140785)
    ·
      refine ⟨23899292186763621438855589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31865722915684828585140785 23899292186763621438855589)
      ·
        refine ⟨4481117285018179019785423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23899292186763621438855589 4481117285018179019785423)
        ·
          refine ⟨6721675927527268529678135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4481117285018179019785423 6721675927527268529678135)
          ·
            refine ⟨10082513891290902794517203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6721675927527268529678135 10082513891290902794517203)
            ·
              refine ⟨15123770836936354191775805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10082513891290902794517203 15123770836936354191775805)
              ·
                refine ⟨5671414063851132821915927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15123770836936354191775805 5671414063851132821915927)
                ·
                  refine ⟨8507121095776699232873891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5671414063851132821915927 8507121095776699232873891)
                  ·
                    refine ⟨12760681643665048849310837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8507121095776699232873891 12760681643665048849310837)
                    ·
                      refine ⟨1196313904093598329622891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12760681643665048849310837 1196313904093598329622891)
                      ·
                        rfl

theorem cell23_2329813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2329813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329813 prefixEnd_2329813 := by exact prefixLift 2329813
  have htrace : WordTrace (prefixWord ++ tailWord_2329813) baseStart_2329813 baseEnd_2329813 := by
    simpa [prefixWord, tailWord_2329813, baseEnd_2329813] using wordTrace_append hprefix tailTrace_2329813
  have hstable : (prefixWord ++ tailWord_2329813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329813).length < 2 ^ (prefixWord ++ tailWord_2329813).sum := by decide
  have hdescent : baseEnd_2329813 < baseStart_2329813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329814 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 2, 3, 2]
def baseStart_2329814 : Nat := 118140960795 + 2329814 * 2 ^ 59
def prefixEnd_2329814 : Nat := 4983230072969 + 3 ^ 40 * 2329814 * 2
def baseEnd_2329814 : Nat := 1196314417574252825710387

theorem tailTrace_2329814 : CollatzResearch.WordTrace tailWord_2329814 prefixEnd_2329814 1196314417574252825710387 := by
  unfold tailWord_2329814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5310956098843078337364281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56650198387659502265218997 5310956098843078337364281)
  ·
    refine ⟨3983217074132308753023211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5310956098843078337364281 3983217074132308753023211)
    ·
      refine ⟨5974825611198463129534817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3983217074132308753023211 5974825611198463129534817)
      ·
        refine ⟨4481119208398847347151113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5974825611198463129534817 4481119208398847347151113)
        ·
          refine ⟨3360839406299135510363335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4481119208398847347151113 3360839406299135510363335)
          ·
            refine ⟨5041259109448703265545003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360839406299135510363335 5041259109448703265545003)
            ·
              refine ⟨7561888664173054898317505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041259109448703265545003 7561888664173054898317505)
              ·
                refine ⟨5671416498129791173738129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7561888664173054898317505 5671416498129791173738129)
                ·
                  refine ⟨4253562373597343380303597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5671416498129791173738129 4253562373597343380303597)
                  ·
                    refine ⟨1595085890099003767613849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4253562373597343380303597 1595085890099003767613849)
                    ·
                      refine ⟨1196314417574252825710387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595085890099003767613849 1196314417574252825710387)
                      ·
                        rfl

theorem cell23_2329814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_2329814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329814 prefixEnd_2329814 := by exact prefixLift 2329814
  have htrace : WordTrace (prefixWord ++ tailWord_2329814) baseStart_2329814 baseEnd_2329814 := by
    simpa [prefixWord, tailWord_2329814, baseEnd_2329814] using wordTrace_append hprefix tailTrace_2329814
  have hstable : (prefixWord ++ tailWord_2329814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329814).length < 2 ^ (prefixWord ++ tailWord_2329814).sum := by decide
  have hdescent : baseEnd_2329814 < baseStart_2329814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329821 : List Nat := [1, 4, 3, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_2329821 : Nat := 118140960795 + 2329821 * 2 ^ 59
def prefixEnd_2329821 : Nat := 4983230072969 + 3 ^ 40 * 2329821 * 2
def baseEnd_2329821 : Nat := 1196318011938834298322855

theorem tailTrace_2329821 : CollatzResearch.WordTrace tailWord_2329821 prefixEnd_2329821 1196318011938834298322855 := by
  unfold tailWord_2329821
  simp only [CollatzResearch.WordTrace]
  refine ⟨84975552892463893593333317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56650368594975929062222211 84975552892463893593333317)
  ·
    refine ⟨15932916167336980048749997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84975552892463893593333317 15932916167336980048749997)
    ·
      refine ⟨5974843562751367518281249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15932916167336980048749997 5974843562751367518281249)
      ·
        refine ⟨4481132672063525638710937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5974843562751367518281249 4481132672063525638710937)
        ·
          refine ⟨3360849504047644229033203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4481132672063525638710937 3360849504047644229033203)
          ·
            refine ⟨5041274256071466343549805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360849504047644229033203 5041274256071466343549805)
            ·
              refine ⟨1890477846026799878831177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5041274256071466343549805 1890477846026799878831177)
              ·
                refine ⟨1417858384520099909123383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1890477846026799878831177 1417858384520099909123383)
                ·
                  refine ⟨2126787576780149863685075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1417858384520099909123383 2126787576780149863685075)
                  ·
                    refine ⟨3190181365170224795527613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2126787576780149863685075 3190181365170224795527613)
                    ·
                      refine ⟨1196318011938834298322855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3190181365170224795527613 1196318011938834298322855)
                      ·
                        rfl

theorem cell23_2329821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_2329821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329821 prefixEnd_2329821 := by exact prefixLift 2329821
  have htrace : WordTrace (prefixWord ++ tailWord_2329821) baseStart_2329821 baseEnd_2329821 := by
    simpa [prefixWord, tailWord_2329821, baseEnd_2329821] using wordTrace_append hprefix tailTrace_2329821
  have hstable : (prefixWord ++ tailWord_2329821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329821).length < 2 ^ (prefixWord ++ tailWord_2329821).sum := by decide
  have hdescent : baseEnd_2329821 < baseStart_2329821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329837 : List Nat := [1, 5, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_2329837 : Nat := 118140960795 + 2329837 * 2 ^ 59
def prefixEnd_2329837 : Nat := 4983230072969 + 3 ^ 40 * 2329837 * 2
def baseEnd_2329837 : Nat := 398775409209768745240927

theorem tailTrace_2329837 : CollatzResearch.WordTrace tailWord_2329837 prefixEnd_2329837 398775409209768745240927 := by
  unfold tailWord_2329837
  simp only [CollatzResearch.WordTrace]
  refine ⟨84976136460405928325915765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56650757640270618883943843 84976136460405928325915765)
  ·
    refine ⟨7966512793163055780554603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84976136460405928325915765 7966512793163055780554603)
    ·
      refine ⟨11949769189744583670831905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7966512793163055780554603 11949769189744583670831905)
      ·
        refine ⟨8962326892308437753123929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11949769189744583670831905 8962326892308437753123929)
        ·
          refine ⟨6721745169231328314842947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8962326892308437753123929 6721745169231328314842947)
          ·
            refine ⟨10082617753846992472264421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6721745169231328314842947 10082617753846992472264421)
            ·
              refine ⟨1890490828846311088549579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10082617753846992472264421 1890490828846311088549579)
              ·
                refine ⟨2835736243269466632824369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890490828846311088549579 2835736243269466632824369)
                ·
                  refine ⟨2126802182452099974618277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2835736243269466632824369 2126802182452099974618277)
                  ·
                    refine ⟨398775409209768745240927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2126802182452099974618277 398775409209768745240927)
                    ·
                      rfl

theorem cell23_2329837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_2329837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329837 prefixEnd_2329837 := by exact prefixLift 2329837
  have htrace : WordTrace (prefixWord ++ tailWord_2329837) baseStart_2329837 baseEnd_2329837 := by
    simpa [prefixWord, tailWord_2329837, baseEnd_2329837] using wordTrace_append hprefix tailTrace_2329837
  have hstable : (prefixWord ++ tailWord_2329837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329837).length < 2 ^ (prefixWord ++ tailWord_2329837).sum := by decide
  have hdescent : baseEnd_2329837 < baseStart_2329837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329844 : List Nat := [2, 6, 1, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2329844 : Nat := 118140960795 + 2329844 * 2 ^ 59
def prefixEnd_2329844 : Nat := 4983230072969 + 3 ^ 40 * 2329844 * 2
def baseEnd_2329844 : Nat := 1196329821993887708335249

theorem tailTrace_2329844 : CollatzResearch.WordTrace tailWord_2329844 prefixEnd_2329844 1196329821993887708335249 := by
  unfold tailWord_2329844
  simp only [CollatzResearch.WordTrace]
  refine ⟨42488195885690284260710293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56650927847587045680947057 42488195885690284260710293)
  ·
    refine ⟨1991634182141732074720795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 42488195885690284260710293 1991634182141732074720795)
    ·
      refine ⟨2987451273212598112081193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1991634182141732074720795 2987451273212598112081193)
      ·
        refine ⟨2240588454909448584060895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2987451273212598112081193 2240588454909448584060895)
        ·
          refine ⟨3360882682364172876091343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240588454909448584060895 3360882682364172876091343)
          ·
            refine ⟨5041324023546259314137015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3360882682364172876091343 5041324023546259314137015)
            ·
              refine ⟨7561986035319388971205523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041324023546259314137015 7561986035319388971205523)
              ·
                refine ⟨11342979052979083456808285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7561986035319388971205523 11342979052979083456808285)
                ·
                  refine ⟨4253617144867156296303107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11342979052979083456808285 4253617144867156296303107)
                  ·
                    refine ⟨6380425717300734444454661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4253617144867156296303107 6380425717300734444454661)
                    ·
                      refine ⟨1196329821993887708335249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6380425717300734444454661 1196329821993887708335249)
                      ·
                        rfl

theorem cell23_2329844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2329844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329844 prefixEnd_2329844 := by exact prefixLift 2329844
  have htrace : WordTrace (prefixWord ++ tailWord_2329844) baseStart_2329844 baseEnd_2329844 := by
    simpa [prefixWord, tailWord_2329844, baseEnd_2329844] using wordTrace_append hprefix tailTrace_2329844
  have hstable : (prefixWord ++ tailWord_2329844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329844).length < 2 ^ (prefixWord ++ tailWord_2329844).sum := by decide
  have hdescent : baseEnd_2329844 < baseStart_2329844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329860 : List Nat := [2, 3, 2, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_2329860 : Nat := 118140960795 + 2329860 * 2 ^ 59
def prefixEnd_2329860 : Nat := 4983230072969 + 3 ^ 40 * 2329860 * 2
def baseEnd_2329860 : Nat := 1196338037684359645735175

theorem tailTrace_2329860 : CollatzResearch.WordTrace tailWord_2329860 prefixEnd_2329860 1196338037684359645735175 := by
  unfold tailWord_2329860
  simp only [CollatzResearch.WordTrace]
  refine ⟨42488487669661301627001517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56651316892881735502668689 42488487669661301627001517)
  ·
    refine ⟨15933182876122988110125569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42488487669661301627001517 15933182876122988110125569)
    ·
      refine ⟨11949887157092241082594177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15933182876122988110125569 11949887157092241082594177)
      ·
        refine ⟨8962415367819180811945633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11949887157092241082594177 8962415367819180811945633)
        ·
          refine ⟨6721811525864385608959225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8962415367819180811945633 6721811525864385608959225)
          ·
            refine ⟨5041358644398289206719419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6721811525864385608959225 5041358644398289206719419)
            ·
              refine ⟨7562037966597433810079129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041358644398289206719419 7562037966597433810079129)
              ·
                refine ⟨5671528474948075357559347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7562037966597433810079129 5671528474948075357559347)
                ·
                  refine ⟨8507292712422113036339021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5671528474948075357559347 8507292712422113036339021)
                  ·
                    refine ⟨3190234767158292388627133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8507292712422113036339021 3190234767158292388627133)
                    ·
                      refine ⟨1196338037684359645735175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3190234767158292388627133 1196338037684359645735175)
                      ·
                        rfl

theorem cell23_2329860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_2329860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329860 prefixEnd_2329860 := by exact prefixLift 2329860
  have htrace : WordTrace (prefixWord ++ tailWord_2329860) baseStart_2329860 baseEnd_2329860 := by
    simpa [prefixWord, tailWord_2329860, baseEnd_2329860] using wordTrace_append hprefix tailTrace_2329860
  have hstable : (prefixWord ++ tailWord_2329860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329860).length < 2 ^ (prefixWord ++ tailWord_2329860).sum := by decide
  have hdescent : baseEnd_2329860 < baseStart_2329860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329883 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 5, 4, 2]
def baseStart_2329883 : Nat := 118140960795 + 2329883 * 2 ^ 59
def prefixEnd_2329883 : Nat := 4983230072969 + 3 ^ 40 * 2329883 * 2
def baseEnd_2329883 : Nat := 1196349847739413055747569

theorem tailTrace_2329883 : CollatzResearch.WordTrace tailWord_2329883 prefixEnd_2329883 1196349847739413055747569 := by
  unfold tailWord_2329883
  simp only [CollatzResearch.WordTrace]
  refine ⟨84977814218239278182090303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56651876145492852121393535 84977814218239278182090303)
  ·
    refine ⟨127466721327358917273135455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84977814218239278182090303 127466721327358917273135455)
    ·
      refine ⟨191200081991038375909703183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127466721327358917273135455 191200081991038375909703183)
      ·
        refine ⟨286800122986557563864554775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191200081991038375909703183 286800122986557563864554775)
        ·
          refine ⟨430200184479836345796832163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286800122986557563864554775 430200184479836345796832163)
          ·
            refine ⟨645300276719754518695248245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 430200184479836345796832163 645300276719754518695248245)
            ·
              refine ⟨60496900942476986127679523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 645300276719754518695248245 60496900942476986127679523)
              ·
                refine ⟨90745351413715479191519285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60496900942476986127679523 90745351413715479191519285)
                ·
                  refine ⟨8507376695035826174204933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90745351413715479191519285 8507376695035826174204933)
                  ·
                    refine ⟨1595133130319217407663425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8507376695035826174204933 1595133130319217407663425)
                    ·
                      refine ⟨1196349847739413055747569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595133130319217407663425 1196349847739413055747569)
                      ·
                        rfl

theorem cell23_2329883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 4, 2].length) (baseStart_2329883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329883 prefixEnd_2329883 := by exact prefixLift 2329883
  have htrace : WordTrace (prefixWord ++ tailWord_2329883) baseStart_2329883 baseEnd_2329883 := by
    simpa [prefixWord, tailWord_2329883, baseEnd_2329883] using wordTrace_append hprefix tailTrace_2329883
  have hstable : (prefixWord ++ tailWord_2329883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329883).length < 2 ^ (prefixWord ++ tailWord_2329883).sum := by decide
  have hdescent : baseEnd_2329883 < baseStart_2329883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329893 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_2329893 : Nat := 118140960795 + 2329893 * 2 ^ 59
def prefixEnd_2329893 : Nat := 4983230072969 + 3 ^ 40 * 2329893 * 2
def baseEnd_2329893 : Nat := 398784994181986005540841

theorem tailTrace_2329893 : CollatzResearch.WordTrace tailWord_2329893 prefixEnd_2329893 398784994181986005540841 := by
  unfold tailWord_2329893
  simp only [CollatzResearch.WordTrace]
  refine ⟨84978178948203049889954333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56652119298802033259969555 84978178948203049889954333)
  ·
    refine ⟨31866817105576143708732875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84978178948203049889954333 31866817105576143708732875)
    ·
      refine ⟨47800225658364215563099313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31866817105576143708732875 47800225658364215563099313)
      ·
        refine ⟨35850169243773161672324485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47800225658364215563099313 35850169243773161672324485)
        ·
          refine ⟨6721906733207467813560841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35850169243773161672324485 6721906733207467813560841)
          ·
            refine ⟨5041430049905600860170631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6721906733207467813560841 5041430049905600860170631)
            ·
              refine ⟨7562145074858401290255947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041430049905600860170631 7562145074858401290255947)
              ·
                refine ⟨11343217612287601935383921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7562145074858401290255947 11343217612287601935383921)
                ·
                  refine ⟨8507413209215701451537941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11343217612287601935383921 8507413209215701451537941)
                  ·
                    refine ⟨398784994181986005540841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8507413209215701451537941 398784994181986005540841)
                    ·
                      rfl

theorem cell23_2329893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_2329893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329893 prefixEnd_2329893 := by exact prefixLift 2329893
  have htrace : WordTrace (prefixWord ++ tailWord_2329893) baseStart_2329893 baseEnd_2329893 := by
    simpa [prefixWord, tailWord_2329893, baseEnd_2329893] using wordTrace_append hprefix tailTrace_2329893
  have hstable : (prefixWord ++ tailWord_2329893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329893).length < 2 ^ (prefixWord ++ tailWord_2329893).sum := by decide
  have hdescent : baseEnd_2329893 < baseStart_2329893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329900 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 6, 2, 2]
def baseStart_2329900 : Nat := 118140960795 + 2329900 * 2 ^ 59
def prefixEnd_2329900 : Nat := 4983230072969 + 3 ^ 40 * 2329900 * 2
def baseEnd_2329900 : Nat := 1196358576910539489234991

theorem tailTrace_2329900 : CollatzResearch.WordTrace tailWord_2329900 prefixEnd_2329900 1196358576910539489234991 := by
  unfold tailWord_2329900
  simp only [CollatzResearch.WordTrace]
  refine ⟨42489217129588845042729577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56652289506118460056972769 42489217129588845042729577)
  ·
    refine ⟨31866912847191633782047183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42489217129588845042729577 31866912847191633782047183)
    ·
      refine ⟨47800369270787450673070775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31866912847191633782047183 47800369270787450673070775)
      ·
        refine ⟨71700553906181176009606163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47800369270787450673070775 71700553906181176009606163)
        ·
          refine ⟨107550830859271764014409245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71700553906181176009606163 107550830859271764014409245)
          ·
            refine ⟨40331561572226911505403467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107550830859271764014409245 40331561572226911505403467)
            ·
              refine ⟨60497342358340367258105201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40331561572226911505403467 60497342358340367258105201)
              ·
                refine ⟨45373006768755275443578901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60497342358340367258105201 45373006768755275443578901)
                ·
                  refine ⟨2126859692285403536417761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45373006768755275443578901 2126859692285403536417761)
                  ·
                    refine ⟨1595144769214052652313321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2126859692285403536417761 1595144769214052652313321)
                    ·
                      refine ⟨1196358576910539489234991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595144769214052652313321 1196358576910539489234991)
                      ·
                        rfl

theorem cell23_2329900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_2329900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329900 prefixEnd_2329900 := by exact prefixLift 2329900
  have htrace : WordTrace (prefixWord ++ tailWord_2329900) baseStart_2329900 baseEnd_2329900 := by
    simpa [prefixWord, tailWord_2329900, baseEnd_2329900] using wordTrace_append hprefix tailTrace_2329900
  have hstable : (prefixWord ++ tailWord_2329900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329900).length < 2 ^ (prefixWord ++ tailWord_2329900).sum := by decide
  have hdescent : baseEnd_2329900 < baseStart_2329900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329921 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2329921 : Nat := 118140960795 + 2329921 * 2 ^ 59
def prefixEnd_2329921 : Nat := 4983230072969 + 3 ^ 40 * 2329921 * 2
def baseEnd_2329921 : Nat := 1196369360004283907072395

theorem tailTrace_2329921 : CollatzResearch.WordTrace tailWord_2329921 prefixEnd_2329921 1196369360004283907072395 := by
  unfold tailWord_2329921
  simp only [CollatzResearch.WordTrace]
  refine ⟨84979200192101610671973617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56652800128067740447982411 84979200192101610671973617)
  ·
    refine ⟨63734400144076208003980213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84979200192101610671973617 63734400144076208003980213)
    ·
      refine ⟨5975100013507144500373145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63734400144076208003980213 5975100013507144500373145)
      ·
        refine ⟨4481325010130358375279859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5975100013507144500373145 4481325010130358375279859)
        ·
          refine ⟨6721987515195537562919789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4481325010130358375279859 6721987515195537562919789)
          ·
            refine ⟨2520745318198326586094921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6721987515195537562919789 2520745318198326586094921)
            ·
              refine ⟨1890558988648744939571191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2520745318198326586094921 1890558988648744939571191)
              ·
                refine ⟨2835838482973117409356787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1890558988648744939571191 2835838482973117409356787)
                ·
                  refine ⟨4253757724459676114035181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2835838482973117409356787 4253757724459676114035181)
                  ·
                    refine ⟨1595159146672378542763193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4253757724459676114035181 1595159146672378542763193)
                    ·
                      refine ⟨1196369360004283907072395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595159146672378542763193 1196369360004283907072395)
                      ·
                        rfl

theorem cell23_2329921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2329921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329921 prefixEnd_2329921 := by exact prefixLift 2329921
  have htrace : WordTrace (prefixWord ++ tailWord_2329921) baseStart_2329921 baseEnd_2329921 := by
    simpa [prefixWord, tailWord_2329921, baseEnd_2329921] using wordTrace_append hprefix tailTrace_2329921
  have hstable : (prefixWord ++ tailWord_2329921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329921).length < 2 ^ (prefixWord ++ tailWord_2329921).sum := by decide
  have hdescent : baseEnd_2329921 < baseStart_2329921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2329940 : List Nat := [2, 4, 1, 1, 2, 1, 1, 6, 5]
def baseStart_2329940 : Nat := 118140960795 + 2329940 * 2 ^ 59
def prefixEnd_2329940 : Nat := 4983230072969 + 3 ^ 40 * 2329940 * 2
def baseEnd_2329940 : Nat := 132931012904079925859423

theorem tailTrace_2329940 : CollatzResearch.WordTrace tailWord_2329940 prefixEnd_2329940 132931012904079925859423 := by
  unfold tailWord_2329940
  simp only [CollatzResearch.WordTrace]
  refine ⟨42489946589516388458457637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56653262119355184611276849 42489946589516388458457637)
  ·
    refine ⟨7966864985534322835960807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42489946589516388458457637 7966864985534322835960807)
    ·
      refine ⟨11950297478301484253941211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7966864985534322835960807 11950297478301484253941211)
      ·
        refine ⟨17925446217452226380911817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11950297478301484253941211 17925446217452226380911817)
        ·
          refine ⟨13444084663089169785683863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17925446217452226380911817 13444084663089169785683863)
          ·
            refine ⟨20166126994633754678525795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13444084663089169785683863 20166126994633754678525795)
            ·
              refine ⟨30249190491950632017788693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20166126994633754678525795 30249190491950632017788693)
              ·
                refine ⟨1417930804310185875833845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30249190491950632017788693 1417930804310185875833845)
                ·
                  refine ⟨132931012904079925859423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1417930804310185875833845 132931012904079925859423)
                  ·
                    rfl

theorem cell23_2329940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_2329940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2329940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2329940 prefixEnd_2329940 := by exact prefixLift 2329940
  have htrace : WordTrace (prefixWord ++ tailWord_2329940) baseStart_2329940 baseEnd_2329940 := by
    simpa [prefixWord, tailWord_2329940, baseEnd_2329940] using wordTrace_append hprefix tailTrace_2329940
  have hstable : (prefixWord ++ tailWord_2329940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2329940).length < 2 ^ (prefixWord ++ tailWord_2329940).sum := by decide
  have hdescent : baseEnd_2329940 < baseStart_2329940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2329940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330010 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3]
def baseStart_2330010 : Nat := 118140960795 + 2330010 * 2 ^ 59
def prefixEnd_2330010 : Nat := 4983230072969 + 3 ^ 40 * 2330010 * 2
def baseEnd_2330010 : Nat := 1196415059782534058859485

theorem tailTrace_2330010 : CollatzResearch.WordTrace tailWord_2330010 prefixEnd_2330010 1196415059782534058859485 := by
  unfold tailWord_2330010
  simp only [CollatzResearch.WordTrace]
  refine ⟨21245611572194794717990871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56654964192519452581308989 21245611572194794717990871)
  ·
    refine ⟨31868417358292192076986307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21245611572194794717990871 31868417358292192076986307)
    ·
      refine ⟨47802626037438288115479461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31868417358292192076986307 47802626037438288115479461)
      ·
        refine ⟨8962992382019679021652399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47802626037438288115479461 8962992382019679021652399)
        ·
          refine ⟨13444488573029518532478599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8962992382019679021652399 13444488573029518532478599)
          ·
            refine ⟨20166732859544277798717899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13444488573029518532478599 20166732859544277798717899)
            ·
              refine ⟨30250099289316416698076849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20166732859544277798717899 30250099289316416698076849)
              ·
                refine ⟨22687574466987312523557637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30250099289316416698076849 22687574466987312523557637)
                ·
                  refine ⟨4253920212560121098167057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22687574466987312523557637 4253920212560121098167057)
                  ·
                    refine ⟨3190440159420090823625293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4253920212560121098167057 3190440159420090823625293)
                    ·
                      refine ⟨1196415059782534058859485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3190440159420090823625293 1196415059782534058859485)
                      ·
                        rfl

theorem cell23_2330010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_2330010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330010 prefixEnd_2330010 := by exact prefixLift 2330010
  have htrace : WordTrace (prefixWord ++ tailWord_2330010) baseStart_2330010 baseEnd_2330010 := by
    simpa [prefixWord, tailWord_2330010, baseEnd_2330010] using wordTrace_append hprefix tailTrace_2330010
  have hstable : (prefixWord ++ tailWord_2330010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330010).length < 2 ^ (prefixWord ++ tailWord_2330010).sum := by decide
  have hdescent : baseEnd_2330010 < baseStart_2330010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330024 : List Nat := [2, 1, 6, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2330024 : Nat := 118140960795 + 2330024 * 2 ^ 59
def prefixEnd_2330024 : Nat := 4983230072969 + 3 ^ 40 * 2330024 * 2
def baseEnd_2330024 : Nat := 1196422248511697004084421

theorem tailTrace_2330024 : CollatzResearch.WordTrace tailWord_2330024 prefixEnd_2330024 1196422248511697004084421 := by
  unfold tailWord_2330024
  simp only [CollatzResearch.WordTrace]
  refine ⟨42491478455364229631486563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56655304607152306175315417 42491478455364229631486563)
  ·
    refine ⟨63737217683046344447229845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42491478455364229631486563 63737217683046344447229845)
    ·
      refine ⟨2987682078892797395963899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 63737217683046344447229845 2987682078892797395963899)
      ·
        refine ⟨4481523118339196093945849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2987682078892797395963899 4481523118339196093945849)
        ·
          refine ⟨3361142338754397070459387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4481523118339196093945849 3361142338754397070459387)
          ·
            refine ⟨5041713508131595605689081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361142338754397070459387 5041713508131595605689081)
            ·
              refine ⟨3781285131098696704266811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5041713508131595605689081 3781285131098696704266811)
              ·
                refine ⟨5671927696648045056400217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3781285131098696704266811 5671927696648045056400217)
                ·
                  refine ⟨4253945772486033792300163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5671927696648045056400217 4253945772486033792300163)
                  ·
                    refine ⟨6380918658729050688450245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4253945772486033792300163 6380918658729050688450245)
                    ·
                      refine ⟨1196422248511697004084421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6380918658729050688450245 1196422248511697004084421)
                      ·
                        rfl

theorem cell23_2330024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2330024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330024 prefixEnd_2330024 := by exact prefixLift 2330024
  have htrace : WordTrace (prefixWord ++ tailWord_2330024) baseStart_2330024 baseEnd_2330024 := by
    simpa [prefixWord, tailWord_2330024, baseEnd_2330024] using wordTrace_append hprefix tailTrace_2330024
  have hstable : (prefixWord ++ tailWord_2330024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330024).length < 2 ^ (prefixWord ++ tailWord_2330024).sum := by decide
  have hdescent : baseEnd_2330024 < baseStart_2330024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330060 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_2330060 : Nat := 118140960795 + 2330060 * 2 ^ 59
def prefixEnd_2330060 : Nat := 4983230072969 + 3 ^ 40 * 2330060 * 2
def baseEnd_2330060 : Nat := 398813577938419621078085

theorem tailTrace_2330060 : CollatzResearch.WordTrace tailWord_2330060 prefixEnd_2330060 398813577938419621078085 := by
  unfold tailWord_2330060
  simp only [CollatzResearch.WordTrace]
  refine ⟨42492134969299018705641817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56656179959065358274189089 42492134969299018705641817)
  ·
    refine ⟨31869101226974264029231363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42492134969299018705641817 31869101226974264029231363)
    ·
      refine ⟨47803651840461396043847045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31869101226974264029231363 47803651840461396043847045)
      ·
        refine ⟨8963184720086511758221321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47803651840461396043847045 8963184720086511758221321)
        ·
          refine ⟨6722388540064883818665991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8963184720086511758221321 6722388540064883818665991)
          ·
            refine ⟨10083582810097325727998987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6722388540064883818665991 10083582810097325727998987)
            ·
              refine ⟨15125374215145988591998481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10083582810097325727998987 15125374215145988591998481)
              ·
                refine ⟨11344030661359491443998861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15125374215145988591998481 11344030661359491443998861)
                ·
                  refine ⟨4254011498009809291499573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11344030661359491443998861 4254011498009809291499573)
                  ·
                    refine ⟨398813577938419621078085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4254011498009809291499573 398813577938419621078085)
                    ·
                      rfl

theorem cell23_2330060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_2330060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330060 prefixEnd_2330060 := by exact prefixLift 2330060
  have htrace : WordTrace (prefixWord ++ tailWord_2330060) baseStart_2330060 baseEnd_2330060 := by
    simpa [prefixWord, tailWord_2330060, baseEnd_2330060] using wordTrace_append hprefix tailTrace_2330060
  have hstable : (prefixWord ++ tailWord_2330060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330060).length < 2 ^ (prefixWord ++ tailWord_2330060).sum := by decide
  have hdescent : baseEnd_2330060 < baseStart_2330060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330080 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 1, 8, 2]
def baseStart_2330080 : Nat := 118140960795 + 2330080 * 2 ^ 59
def prefixEnd_2330080 : Nat := 4983230072969 + 3 ^ 40 * 2330080 * 2
def baseEnd_2330080 : Nat := 1196451003428348784984163

theorem tailTrace_2330080 : CollatzResearch.WordTrace tailWord_2330080 prefixEnd_2330080 1196451003428348784984163 := by
  unfold tailWord_2330080
  simp only [CollatzResearch.WordTrace]
  refine ⟨42492499699262790413505847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56656666265683720551341129 42492499699262790413505847)
  ·
    refine ⟨63738749548894185620258771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42492499699262790413505847 63738749548894185620258771)
    ·
      refine ⟨95608124323341278430388157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63738749548894185620258771 95608124323341278430388157)
      ·
        refine ⟨35853046621252979411395559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95608124323341278430388157 35853046621252979411395559)
        ·
          refine ⟨53779569931879469117093339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35853046621252979411395559 53779569931879469117093339)
          ·
            refine ⟨80669354897819203675640009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53779569931879469117093339 80669354897819203675640009)
            ·
              refine ⟨60502016173364402756730007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80669354897819203675640009 60502016173364402756730007)
              ·
                refine ⟨90753024260046604135095011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60502016173364402756730007 90753024260046604135095011)
                ·
                  refine ⟨136129536390069906202642517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90753024260046604135095011 136129536390069906202642517)
                  ·
                    refine ⟨1595268004571131713312217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 136129536390069906202642517 1595268004571131713312217)
                    ·
                      refine ⟨1196451003428348784984163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595268004571131713312217 1196451003428348784984163)
                      ·
                        rfl

theorem cell23_2330080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_2330080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330080 prefixEnd_2330080 := by exact prefixLift 2330080
  have htrace : WordTrace (prefixWord ++ tailWord_2330080) baseStart_2330080 baseEnd_2330080 := by
    simpa [prefixWord, tailWord_2330080, baseEnd_2330080] using wordTrace_append hprefix tailTrace_2330080
  have hstable : (prefixWord ++ tailWord_2330080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330080).length < 2 ^ (prefixWord ++ tailWord_2330080).sum := by decide
  have hdescent : baseEnd_2330080 < baseStart_2330080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330097 : List Nat := [1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 4]
def baseStart_2330097 : Nat := 118140960795 + 2330097 * 2 ^ 59
def prefixEnd_2330097 : Nat := 4983230072969 + 3 ^ 40 * 2330097 * 2
def baseEnd_2330097 : Nat := 1196459732599475218471585

theorem tailTrace_2330097 : CollatzResearch.WordTrace tailWord_2330097 prefixEnd_2330097 1196459732599475218471585 := by
  unfold tailWord_2330097
  simp only [CollatzResearch.WordTrace]
  refine ⟨84985619439463992730380545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56657079626309328486920363 84985619439463992730380545)
  ·
    refine ⟨63739214579597994547785409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84985619439463992730380545 63739214579597994547785409)
    ·
      refine ⟨47804410934698495910839057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63739214579597994547785409 47804410934698495910839057)
      ·
        refine ⟨35853308201023871933129293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47804410934698495910839057 35853308201023871933129293)
        ·
          refine ⟨13444990575383951974923485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35853308201023871933129293 13444990575383951974923485)
          ·
            refine ⟨5041871465768981990596307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13444990575383951974923485 5041871465768981990596307)
            ·
              refine ⟨7562807198653472985894461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5041871465768981990596307 7562807198653472985894461)
              ·
                refine ⟨2836052699495052369710423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7562807198653472985894461 2836052699495052369710423)
                ·
                  refine ⟨4254079049242578554565635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2836052699495052369710423 4254079049242578554565635)
                  ·
                    refine ⟨6381118573863867831848453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4254079049242578554565635 6381118573863867831848453)
                    ·
                      refine ⟨1196459732599475218471585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6381118573863867831848453 1196459732599475218471585)
                      ·
                        rfl

theorem cell23_2330097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_2330097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330097 prefixEnd_2330097 := by exact prefixLift 2330097
  have htrace : WordTrace (prefixWord ++ tailWord_2330097) baseStart_2330097 baseEnd_2330097 := by
    simpa [prefixWord, tailWord_2330097, baseEnd_2330097] using wordTrace_append hprefix tailTrace_2330097
  have hstable : (prefixWord ++ tailWord_2330097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330097).length < 2 ^ (prefixWord ++ tailWord_2330097).sum := by decide
  have hdescent : baseEnd_2330097 < baseStart_2330097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330124 : List Nat := [2, 2, 1, 2, 6, 1, 1, 1, 1, 6]
def baseStart_2330124 : Nat := 118140960795 + 2330124 * 2 ^ 59
def prefixEnd_2330124 : Nat := 4983230072969 + 3 ^ 40 * 2330124 * 2
def baseEnd_2330124 : Nat := 398824532192382204277987

theorem tailTrace_2330124 : CollatzResearch.WordTrace tailWord_2330124 prefixEnd_2330124 398824532192382204277987 := by
  unfold tailWord_2330124
  simp only [CollatzResearch.WordTrace]
  refine ⟨42493302105183088170806713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56657736140244117561075617 42493302105183088170806713)
  ·
    refine ⟨31869976578887316128105035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42493302105183088170806713 31869976578887316128105035)
    ·
      refine ⟨47804964868330974192157553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31869976578887316128105035 47804964868330974192157553)
      ·
        refine ⟨35853723651248230644118165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47804964868330974192157553 35853723651248230644118165)
        ·
          refine ⟨1680643296152260811443039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35853723651248230644118165 1680643296152260811443039)
          ·
            refine ⟨2520964944228391217164559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680643296152260811443039 2520964944228391217164559)
            ·
              refine ⟨3781447416342586825746839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2520964944228391217164559 3781447416342586825746839)
              ·
                refine ⟨5672171124513880238620259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3781447416342586825746839 5672171124513880238620259)
                ·
                  refine ⟨8508256686770820357930389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5672171124513880238620259 8508256686770820357930389)
                  ·
                    refine ⟨398824532192382204277987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8508256686770820357930389 398824532192382204277987)
                    ·
                      rfl

theorem cell23_2330124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_2330124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330124 prefixEnd_2330124 := by exact prefixLift 2330124
  have htrace : WordTrace (prefixWord ++ tailWord_2330124) baseStart_2330124 baseEnd_2330124 := by
    simpa [prefixWord, tailWord_2330124, baseEnd_2330124] using wordTrace_append hprefix tailTrace_2330124
  have hstable : (prefixWord ++ tailWord_2330124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330124).length < 2 ^ (prefixWord ++ tailWord_2330124).sum := by decide
  have hdescent : baseEnd_2330124 < baseStart_2330124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330170 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4]
def baseStart_2330170 : Nat := 118140960795 + 2330170 * 2 ^ 59
def prefixEnd_2330170 : Nat := 4983230072969 + 3 ^ 40 * 2330170 * 2
def baseEnd_2330170 : Nat := 1196497216687253432858749

theorem tailTrace_2330170 : CollatzResearch.WordTrace tailWord_2330170 prefixEnd_2330170 1196497216687253432858749 := by
  unfold tailWord_2330170
  simp only [CollatzResearch.WordTrace]
  refine ⟨21247070492049881549446991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56658854645466350798525309 21247070492049881549446991)
  ·
    refine ⟨31870605738074822324170487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21247070492049881549446991 31870605738074822324170487)
    ·
      refine ⟨47805908607112233486255731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31870605738074822324170487 47805908607112233486255731)
      ·
        refine ⟨71708862910668350229383597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47805908607112233486255731 71708862910668350229383597)
        ·
          refine ⟨26890823591500631336018849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71708862910668350229383597 26890823591500631336018849)
          ·
            refine ⟨20168117693625473502014137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26890823591500631336018849 20168117693625473502014137)
            ·
              refine ⟨15126088270219105126510603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20168117693625473502014137 15126088270219105126510603)
              ·
                refine ⟨22689132405328657689765905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15126088270219105126510603 22689132405328657689765905)
                ·
                  refine ⟨17016849303996493267324429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22689132405328657689765905 17016849303996493267324429)
                  ·
                    refine ⟨6381318488998684975246661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17016849303996493267324429 6381318488998684975246661)
                    ·
                      refine ⟨1196497216687253432858749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6381318488998684975246661 1196497216687253432858749)
                      ·
                        rfl

theorem cell23_2330170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_2330170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330170 prefixEnd_2330170 := by exact prefixLift 2330170
  have htrace : WordTrace (prefixWord ++ tailWord_2330170) baseStart_2330170 baseEnd_2330170 := by
    simpa [prefixWord, tailWord_2330170, baseEnd_2330170] using wordTrace_append hprefix tailTrace_2330170
  have hstable : (prefixWord ++ tailWord_2330170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330170).length < 2 ^ (prefixWord ++ tailWord_2330170).sum := by decide
  have hdescent : baseEnd_2330170 < baseStart_2330170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330187 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 1, 4, 2]
def baseStart_2330187 : Nat := 118140960795 + 2330187 * 2 ^ 59
def prefixEnd_2330187 : Nat := 4983230072969 + 3 ^ 40 * 2330187 * 2
def baseEnd_2330187 : Nat := 1196505945858379866346171

theorem tailTrace_2330187 : CollatzResearch.WordTrace tailWord_2330187 prefixEnd_2330187 1196505945858379866346171 := by
  unfold tailWord_2330187
  simp only [CollatzResearch.WordTrace]
  refine ⟨84988902009137938101156815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56659268006091958734104543 84988902009137938101156815)
  ·
    refine ⟨127483353013706907151735223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84988902009137938101156815 127483353013706907151735223)
    ·
      refine ⟨191225029520560360727602835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127483353013706907151735223 191225029520560360727602835)
      ·
        refine ⟨286837544280840541091404253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191225029520560360727602835 286837544280840541091404253)
        ·
          refine ⟨107564079105315202909276595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286837544280840541091404253 107564079105315202909276595)
          ·
            refine ⟨161346118657972804363914893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107564079105315202909276595 161346118657972804363914893)
            ·
              refine ⟨60504794496739801636468085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161346118657972804363914893 60504794496739801636468085)
              ·
                refine ⟨5672324484069356403418883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60504794496739801636468085 5672324484069356403418883)
                ·
                  refine ⟨8508486726104034605128325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5672324484069356403418883 8508486726104034605128325)
                  ·
                    refine ⟨1595341261144506488461561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8508486726104034605128325 1595341261144506488461561)
                    ·
                      refine ⟨1196505945858379866346171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595341261144506488461561 1196505945858379866346171)
                      ·
                        rfl

theorem cell23_2330187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 4, 2].length) (baseStart_2330187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330187 prefixEnd_2330187 := by exact prefixLift 2330187
  have htrace : WordTrace (prefixWord ++ tailWord_2330187) baseStart_2330187 baseEnd_2330187 := by
    simpa [prefixWord, tailWord_2330187, baseEnd_2330187] using wordTrace_append hprefix tailTrace_2330187
  have hstable : (prefixWord ++ tailWord_2330187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330187).length < 2 ^ (prefixWord ++ tailWord_2330187).sum := by decide
  have hdescent : baseEnd_2330187 < baseStart_2330187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330198 : List Nat := [5, 2, 2, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2330198 : Nat := 118140960795 + 2330198 * 2 ^ 59
def prefixEnd_2330198 : Nat := 4983230072969 + 3 ^ 40 * 2330198 * 2
def baseEnd_2330198 : Nat := 1196511594145579323308621

theorem tailTrace_2330198 : CollatzResearch.WordTrace tailWord_2330198 prefixEnd_2330198 1196511594145579323308621 := by
  unfold tailWord_2330198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5311831450756130436237953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56659535474732057986538165 5311831450756130436237953)
  ·
    refine ⟨3983873588067097827178465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5311831450756130436237953 3983873588067097827178465)
    ·
      refine ⟨2987905191050323370383849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3983873588067097827178465 2987905191050323370383849)
      ·
        refine ⟨2240928893287742527787887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2987905191050323370383849 2240928893287742527787887)
        ·
          refine ⟨3361393339931613791681831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2240928893287742527787887 3361393339931613791681831)
          ·
            refine ⟨5042090009897420687522747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3361393339931613791681831 5042090009897420687522747)
            ·
              refine ⟨7563135014846131031284121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5042090009897420687522747 7563135014846131031284121)
              ·
                refine ⟨5672351261134598273463091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7563135014846131031284121 5672351261134598273463091)
                ·
                  refine ⟨8508526891701897410194637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5672351261134598273463091 8508526891701897410194637)
                  ·
                    refine ⟨3190697584388211528822989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8508526891701897410194637 3190697584388211528822989)
                    ·
                      refine ⟨1196511594145579323308621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3190697584388211528822989 1196511594145579323308621)
                      ·
                        rfl

theorem cell23_2330198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2330198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330198 prefixEnd_2330198 := by exact prefixLift 2330198
  have htrace : WordTrace (prefixWord ++ tailWord_2330198) baseStart_2330198 baseEnd_2330198 := by
    simpa [prefixWord, tailWord_2330198, baseEnd_2330198] using wordTrace_append hprefix tailTrace_2330198
  have hstable : (prefixWord ++ tailWord_2330198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330198).length < 2 ^ (prefixWord ++ tailWord_2330198).sum := by decide
  have hdescent : baseEnd_2330198 < baseStart_2330198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330200 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2330200 : Nat := 118140960795 + 2330200 * 2 ^ 59
def prefixEnd_2330200 : Nat := 4983230072969 + 3 ^ 40 * 2330200 * 2
def baseEnd_2330200 : Nat := 1196512621106888315483611

theorem tailTrace_2330200 : CollatzResearch.WordTrace tailWord_2330200 prefixEnd_2330200 1196512621106888315483611 := by
  unfold tailWord_2330200
  simp only [CollatzResearch.WordTrace]
  refine ⟨42494688079045420660690027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56659584105393894214253369 42494688079045420660690027)
  ·
    refine ⟨63742032118568130991035041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42494688079045420660690027 63742032118568130991035041)
    ·
      refine ⟨47806524088926098243276281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63742032118568130991035041 47806524088926098243276281)
      ·
        refine ⟨35854893066694573682457211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47806524088926098243276281 35854893066694573682457211)
        ·
          refine ⟨53782339600041860523685817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35854893066694573682457211 53782339600041860523685817)
          ·
            refine ⟨40336754700031395392764363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53782339600041860523685817 40336754700031395392764363)
            ·
              refine ⟨60505132050047093089146545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40336754700031395392764363 60505132050047093089146545)
              ·
                refine ⟨45378849037535319816859909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60505132050047093089146545 45378849037535319816859909)
                ·
                  refine ⟨8508534194537872465661233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45378849037535319816859909 8508534194537872465661233)
                  ·
                    refine ⟨6381400645903404349245925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8508534194537872465661233 6381400645903404349245925)
                    ·
                      refine ⟨1196512621106888315483611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6381400645903404349245925 1196512621106888315483611)
                      ·
                        rfl

theorem cell23_2330200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2330200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330200 prefixEnd_2330200 := by exact prefixLift 2330200
  have htrace : WordTrace (prefixWord ++ tailWord_2330200) baseStart_2330200 baseEnd_2330200 := by
    simpa [prefixWord, tailWord_2330200, baseEnd_2330200] using wordTrace_append hprefix tailTrace_2330200
  have hstable : (prefixWord ++ tailWord_2330200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330200).length < 2 ^ (prefixWord ++ tailWord_2330200).sum := by decide
  have hdescent : baseEnd_2330200 < baseStart_2330200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330204 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_2330204 : Nat := 118140960795 + 2330204 * 2 ^ 59
def prefixEnd_2330204 : Nat := 4983230072969 + 3 ^ 40 * 2330204 * 2
def baseEnd_2330204 : Nat := 1196514675029506299833593

theorem tailTrace_2330204 : CollatzResearch.WordTrace tailWord_2330204 prefixEnd_2330204 1196514675029506299833593 := by
  unfold tailWord_2330204
  simp only [CollatzResearch.WordTrace]
  refine ⟨42494761025038175002262833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56659681366717566669683777 42494761025038175002262833)
  ·
    refine ⟨31871070768778631251697125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42494761025038175002262833 31871070768778631251697125)
    ·
      refine ⟨5975825769145993359693211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31871070768778631251697125 5975825769145993359693211)
      ·
        refine ⟨8963738653718990039539817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5975825769145993359693211 8963738653718990039539817)
        ·
          refine ⟨6722803990289242529654863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8963738653718990039539817 6722803990289242529654863)
          ·
            refine ⟨10084205985433863794482295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6722803990289242529654863 10084205985433863794482295)
            ·
              refine ⟨15126308978150795691723443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10084205985433863794482295 15126308978150795691723443)
              ·
                refine ⟨22689463467226193537585165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15126308978150795691723443 22689463467226193537585165)
                ·
                  refine ⟨8508548800209822576594437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22689463467226193537585165 8508548800209822576594437)
                  ·
                    refine ⟨1595352900039341733111457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8508548800209822576594437 1595352900039341733111457)
                    ·
                      refine ⟨1196514675029506299833593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595352900039341733111457 1196514675029506299833593)
                      ·
                        rfl

theorem cell23_2330204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_2330204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330204 prefixEnd_2330204 := by exact prefixLift 2330204
  have htrace : WordTrace (prefixWord ++ tailWord_2330204) baseStart_2330204 baseEnd_2330204 := by
    simpa [prefixWord, tailWord_2330204, baseEnd_2330204] using wordTrace_append hprefix tailTrace_2330204
  have hstable : (prefixWord ++ tailWord_2330204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330204).length < 2 ^ (prefixWord ++ tailWord_2330204).sum := by decide
  have hdescent : baseEnd_2330204 < baseStart_2330204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330237 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_2330237 : Nat := 118140960795 + 2330237 * 2 ^ 59
def prefixEnd_2330237 : Nat := 4983230072969 + 3 ^ 40 * 2330237 * 2
def baseEnd_2330237 : Nat := 1196531619891104670720941

theorem tailTrace_2330237 : CollatzResearch.WordTrace tailWord_2330237 prefixEnd_2330237 1196531619891104670720941 := by
  unfold tailWord_2330237
  simp only [CollatzResearch.WordTrace]
  refine ⟨84990725658956796640476965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56660483772637864426984643 84990725658956796640476965)
  ·
    refine ⟨15935761061054399370089431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84990725658956796640476965 15935761061054399370089431)
    ·
      refine ⟨23903641591581599055134147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15935761061054399370089431 23903641591581599055134147)
      ·
        refine ⟨35855462387372398582701221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23903641591581599055134147 35855462387372398582701221)
        ·
          refine ⟨6722899197632324734256479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35855462387372398582701221 6722899197632324734256479)
          ·
            refine ⟨10084348796448487101384719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6722899197632324734256479 10084348796448487101384719)
            ·
              refine ⟨15126523194672730652077079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10084348796448487101384719 15126523194672730652077079)
              ·
                refine ⟨22689784792009095978115619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15126523194672730652077079 22689784792009095978115619)
                ·
                  refine ⟨34034677188013643967173429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22689784792009095978115619 34034677188013643967173429)
                  ·
                    refine ⟨3190750986376279121922509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34034677188013643967173429 3190750986376279121922509)
                    ·
                      refine ⟨1196531619891104670720941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3190750986376279121922509 1196531619891104670720941)
                      ·
                        rfl

theorem cell23_2330237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_2330237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330237 prefixEnd_2330237 := by exact prefixLift 2330237
  have htrace : WordTrace (prefixWord ++ tailWord_2330237) baseStart_2330237 baseEnd_2330237 := by
    simpa [prefixWord, tailWord_2330237, baseEnd_2330237] using wordTrace_append hprefix tailTrace_2330237
  have hstable : (prefixWord ++ tailWord_2330237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330237).length < 2 ^ (prefixWord ++ tailWord_2330237).sum := by decide
  have hdescent : baseEnd_2330237 < baseStart_2330237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330240 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 1, 7]
def baseStart_2330240 : Nat := 118140960795 + 2330240 * 2 ^ 59
def prefixEnd_2330240 : Nat := 4983230072969 + 3 ^ 40 * 2330240 * 2
def baseEnd_2330240 : Nat := 398844386777689386327809

theorem tailTrace_2330240 : CollatzResearch.WordTrace tailWord_2330240 prefixEnd_2330240 398844386777689386327809 := by
  unfold tailWord_2330240
  simp only [CollatzResearch.WordTrace]
  refine ⟨42495417538972964076418087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56660556718630618768557449 42495417538972964076418087)
  ·
    refine ⟨63743126308459446114627131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42495417538972964076418087 63743126308459446114627131)
    ·
      refine ⟨95614689462689169171940697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63743126308459446114627131 95614689462689169171940697)
      ·
        refine ⟨71711017097016876878955523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95614689462689169171940697 71711017097016876878955523)
        ·
          refine ⟨107566525645525315318433285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71711017097016876878955523 107566525645525315318433285)
          ·
            refine ⟨20168723558535996622206241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107566525645525315318433285 20168723558535996622206241)
            ·
              refine ⟨15126542668901997466654681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20168723558535996622206241 15126542668901997466654681)
              ·
                refine ⟨11344907001676498099991011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15126542668901997466654681 11344907001676498099991011)
                ·
                  refine ⟨17017360502514747149986517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11344907001676498099991011 17017360502514747149986517)
                  ·
                    refine ⟨398844386777689386327809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17017360502514747149986517 398844386777689386327809)
                    ·
                      rfl

theorem cell23_2330240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_2330240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330240 prefixEnd_2330240 := by exact prefixLift 2330240
  have htrace : WordTrace (prefixWord ++ tailWord_2330240) baseStart_2330240 baseEnd_2330240 := by
    simpa [prefixWord, tailWord_2330240, baseEnd_2330240] using wordTrace_append hprefix tailTrace_2330240
  have hstable : (prefixWord ++ tailWord_2330240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330240).length < 2 ^ (prefixWord ++ tailWord_2330240).sum := by decide
  have hdescent : baseEnd_2330240 < baseStart_2330240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330277 : List Nat := [1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 4]
def baseStart_2330277 : Nat := 118140960795 + 2330277 * 2 ^ 59
def prefixEnd_2330277 : Nat := 4983230072969 + 3 ^ 40 * 2330277 * 2
def baseEnd_2330277 : Nat := 1196552159117284514220757

theorem tailTrace_2330277 : CollatzResearch.WordTrace tailWord_2330277 prefixEnd_2330277 1196552159117284514220757 := by
  unfold tailWord_2330277
  simp only [CollatzResearch.WordTrace]
  refine ⟨84992184578811883471933085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56661456385874588981288723 84992184578811883471933085)
  ·
    refine ⟨31872069217054456301974907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84992184578811883471933085 31872069217054456301974907)
    ·
      refine ⟨47808103825581684452962361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31872069217054456301974907 47808103825581684452962361)
      ·
        refine ⟨35856077869186263339721771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47808103825581684452962361 35856077869186263339721771)
        ·
          refine ⟨53784116803779395009582657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35856077869186263339721771 53784116803779395009582657)
          ·
            refine ⟨40338087602834546257186993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53784116803779395009582657 40338087602834546257186993)
            ·
              refine ⟨30253565702125909692890245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40338087602834546257186993 30253565702125909692890245)
              ·
                refine ⟨5672543569148608067416921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30253565702125909692890245 5672543569148608067416921)
                ·
                  refine ⟨4254407676861456050562691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5672543569148608067416921 4254407676861456050562691)
                  ·
                    refine ⟨6381611515292184075844037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4254407676861456050562691 6381611515292184075844037)
                    ·
                      refine ⟨1196552159117284514220757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6381611515292184075844037 1196552159117284514220757)
                      ·
                        rfl

theorem cell23_2330277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_2330277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330277 prefixEnd_2330277 := by exact prefixLift 2330277
  have htrace : WordTrace (prefixWord ++ tailWord_2330277) baseStart_2330277 baseEnd_2330277 := by
    simpa [prefixWord, tailWord_2330277, baseEnd_2330277] using wordTrace_append hprefix tailTrace_2330277
  have hstable : (prefixWord ++ tailWord_2330277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330277).length < 2 ^ (prefixWord ++ tailWord_2330277).sum := by decide
  have hdescent : baseEnd_2330277 < baseStart_2330277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330297 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 1, 4, 3]
def baseStart_2330297 : Nat := 118140960795 + 2330297 * 2 ^ 59
def prefixEnd_2330297 : Nat := 4983230072969 + 3 ^ 40 * 2330297 * 2
def baseEnd_2330297 : Nat := 1196562428730374435970665

theorem tailTrace_2330297 : CollatzResearch.WordTrace tailWord_2330297 prefixEnd_2330297 1196562428730374435970665 := by
  unfold tailWord_2330297
  simp only [CollatzResearch.WordTrace]
  refine ⟨84992914038739426887661145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56661942692492951258440763 84992914038739426887661145)
  ·
    refine ⟨63744685529054570165745859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84992914038739426887661145 63744685529054570165745859)
    ·
      refine ⟨95617028293581855248618789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63744685529054570165745859 95617028293581855248618789)
      ·
        refine ⟨17928192805046597859116023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95617028293581855248618789 17928192805046597859116023)
        ·
          refine ⟨26892289207569896788674035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17928192805046597859116023 26892289207569896788674035)
          ·
            refine ⟨40338433811354845183011053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26892289207569896788674035 40338433811354845183011053)
            ·
              refine ⟨15126912679258066943629145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40338433811354845183011053 15126912679258066943629145)
              ·
                refine ⟨11345184509443550207721859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15126912679258066943629145 11345184509443550207721859)
                ·
                  refine ⟨17017776764165325311582789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11345184509443550207721859 17017776764165325311582789)
                  ·
                    refine ⟨3190833143280998495921773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17017776764165325311582789 3190833143280998495921773)
                    ·
                      refine ⟨1196562428730374435970665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3190833143280998495921773 1196562428730374435970665)
                      ·
                        rfl

theorem cell23_2330297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_2330297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330297 prefixEnd_2330297 := by exact prefixLift 2330297
  have htrace : WordTrace (prefixWord ++ tailWord_2330297) baseStart_2330297 baseEnd_2330297 := by
    simpa [prefixWord, tailWord_2330297, baseEnd_2330297] using wordTrace_append hprefix tailTrace_2330297
  have hstable : (prefixWord ++ tailWord_2330297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330297).length < 2 ^ (prefixWord ++ tailWord_2330297).sum := by decide
  have hdescent : baseEnd_2330297 < baseStart_2330297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330320 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 8]
def baseStart_2330320 : Nat := 118140960795 + 2330320 * 2 ^ 59
def prefixEnd_2330320 : Nat := 4983230072969 + 3 ^ 40 * 2330320 * 2
def baseEnd_2330320 : Nat := 1196574238785427845983059

theorem tailTrace_2330320 : CollatzResearch.WordTrace tailWord_2330320 prefixEnd_2330320 1196574238785427845983059 := by
  unfold tailWord_2330320
  simp only [CollatzResearch.WordTrace]
  refine ⟨42496876458828050907874207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56662501945104067877165609 42496876458828050907874207)
  ·
    refine ⟨63745314688242076361811311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42496876458828050907874207 63745314688242076361811311)
    ·
      refine ⟨95617972032363114542716967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63745314688242076361811311 95617972032363114542716967)
      ·
        refine ⟨143426958048544671814075451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95617972032363114542716967 143426958048544671814075451)
        ·
          refine ⟨215140437072817007721113177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143426958048544671814075451 215140437072817007721113177)
          ·
            refine ⟨161355327804612755790834883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215140437072817007721113177 161355327804612755790834883)
            ·
              refine ⟨242032991706919133686252325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161355327804612755790834883 242032991706919133686252325)
              ·
                refine ⟨45381185945047337566172311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242032991706919133686252325 45381185945047337566172311)
                ·
                  refine ⟨68071778917571006349258467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45381185945047337566172311 68071778917571006349258467)
                  ·
                    refine ⟨102107668376356509523887701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68071778917571006349258467 102107668376356509523887701)
                    ·
                      refine ⟨1196574238785427845983059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 102107668376356509523887701 1196574238785427845983059)
                      ·
                        rfl

theorem cell23_2330320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 8].length) (baseStart_2330320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330320 prefixEnd_2330320 := by exact prefixLift 2330320
  have htrace : WordTrace (prefixWord ++ tailWord_2330320) baseStart_2330320 baseEnd_2330320 := by
    simpa [prefixWord, tailWord_2330320, baseEnd_2330320] using wordTrace_append hprefix tailTrace_2330320
  have hstable : (prefixWord ++ tailWord_2330320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330320).length < 2 ^ (prefixWord ++ tailWord_2330320).sum := by decide
  have hdescent : baseEnd_2330320 < baseStart_2330320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330321 : List Nat := [1, 2, 2, 1, 2, 4, 3, 3, 1, 4]
def baseStart_2330321 : Nat := 118140960795 + 2330321 * 2 ^ 59
def prefixEnd_2330321 : Nat := 4983230072969 + 3 ^ 40 * 2330321 * 2
def baseEnd_2330321 : Nat := 398858250755360780690185

theorem tailTrace_2330321 : CollatzResearch.WordTrace tailWord_2330321 prefixEnd_2330321 398858250755360780690185 := by
  unfold tailWord_2330321
  simp only [CollatzResearch.WordTrace]
  refine ⟨84993789390652478986534817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56662526260434985991023211 84993789390652478986534817)
  ·
    refine ⟨63745342042989359239901113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84993789390652478986534817 63745342042989359239901113)
    ·
      refine ⟨47809006532242019429925835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63745342042989359239901113 47809006532242019429925835)
      ·
        refine ⟨71713509798363029144888753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47809006532242019429925835 71713509798363029144888753)
        ·
          refine ⟨53785132348772271858666565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71713509798363029144888753 53785132348772271858666565)
          ·
            refine ⟨10084712315394800973499981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53785132348772271858666565 10084712315394800973499981)
            ·
              refine ⟨3781767118273050365062493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10084712315394800973499981 3781767118273050365062493)
              ·
                refine ⟨1418162669352393886898435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3781767118273050365062493 1418162669352393886898435)
                ·
                  refine ⟨2127244004028590830347653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418162669352393886898435 2127244004028590830347653)
                  ·
                    refine ⟨398858250755360780690185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2127244004028590830347653 398858250755360780690185)
                    ·
                      rfl

theorem cell23_2330321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_2330321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330321 prefixEnd_2330321 := by exact prefixLift 2330321
  have htrace : WordTrace (prefixWord ++ tailWord_2330321) baseStart_2330321 baseEnd_2330321 := by
    simpa [prefixWord, tailWord_2330321, baseEnd_2330321] using wordTrace_append hprefix tailTrace_2330321
  have hstable : (prefixWord ++ tailWord_2330321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330321).length < 2 ^ (prefixWord ++ tailWord_2330321).sum := by decide
  have hdescent : baseEnd_2330321 < baseStart_2330321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330387 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 5]
def baseStart_2330387 : Nat := 118140960795 + 2330387 * 2 ^ 59
def prefixEnd_2330387 : Nat := 4983230072969 + 3 ^ 40 * 2330387 * 2
def baseEnd_2330387 : Nat := 1196608641989279083845251

theorem tailTrace_2330387 : CollatzResearch.WordTrace tailWord_2330387 prefixEnd_2330387 1196608641989279083845251 := by
  unfold tailWord_2330387
  simp only [CollatzResearch.WordTrace]
  refine ⟨84996196608413372258437415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56664131072275581505624943 84996196608413372258437415)
  ·
    refine ⟨127494294912620058387656123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84996196608413372258437415 127494294912620058387656123)
    ·
      refine ⟨191241442368930087581484185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127494294912620058387656123 191241442368930087581484185)
      ·
        refine ⟨143431081776697565686113139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191241442368930087581484185 143431081776697565686113139)
        ·
          refine ⟨215146622665046348529169709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143431081776697565686113139 215146622665046348529169709)
          ·
            refine ⟨80679983499392380698438641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215146622665046348529169709 80679983499392380698438641)
            ·
              refine ⟨60509987624544285523828981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80679983499392380698438641 60509987624544285523828981)
              ·
                refine ⟨5672811339801026767858967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60509987624544285523828981 5672811339801026767858967)
                ·
                  refine ⟨8509217009701540151788451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5672811339801026767858967 8509217009701540151788451)
                  ·
                    refine ⟨12763825514552310227682677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8509217009701540151788451 12763825514552310227682677)
                    ·
                      refine ⟨1196608641989279083845251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12763825514552310227682677 1196608641989279083845251)
                      ·
                        rfl

theorem cell23_2330387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_2330387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330387 prefixEnd_2330387 := by exact prefixLift 2330387
  have htrace : WordTrace (prefixWord ++ tailWord_2330387) baseStart_2330387 baseEnd_2330387 := by
    simpa [prefixWord, tailWord_2330387, baseEnd_2330387] using wordTrace_append hprefix tailTrace_2330387
  have hstable : (prefixWord ++ tailWord_2330387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330387).length < 2 ^ (prefixWord ++ tailWord_2330387).sum := by decide
  have hdescent : baseEnd_2330387 < baseStart_2330387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330418 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2]
def baseStart_2330418 : Nat := 118140960795 + 2330418 * 2 ^ 59
def prefixEnd_2330418 : Nat := 4983230072969 + 3 ^ 40 * 2330418 * 2
def baseEnd_2330418 : Nat := 1196624559889568462557609

theorem tailTrace_2330418 : CollatzResearch.WordTrace tailWord_2330418 prefixEnd_2330418 1196624559889568462557609 := by
  unfold tailWord_2330418
  simp only [CollatzResearch.WordTrace]
  refine ⟨21249331817825266138203977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56664884847534043035210605 21249331817825266138203977)
  ·
    refine ⟨15936998863368949603652983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21249331817825266138203977 15936998863368949603652983)
    ·
      refine ⟨23905498295053424405479475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15936998863368949603652983 23905498295053424405479475)
      ·
        refine ⟨35858247442580136608219213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23905498295053424405479475 35858247442580136608219213)
        ·
          refine ⟨13446842790967551228082205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35858247442580136608219213 13446842790967551228082205)
          ·
            refine ⟨5042566046612831710530827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13446842790967551228082205 5042566046612831710530827)
            ·
              refine ⟨7563849069919247565796241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5042566046612831710530827 7563849069919247565796241)
              ·
                refine ⟨5672886802439435674347181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7563849069919247565796241 5672886802439435674347181)
                ·
                  refine ⟨2127332550914788377880193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5672886802439435674347181 2127332550914788377880193)
                  ·
                    refine ⟨1595499413186091283410145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2127332550914788377880193 1595499413186091283410145)
                    ·
                      refine ⟨1196624559889568462557609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595499413186091283410145 1196624559889568462557609)
                      ·
                        rfl

theorem cell23_2330418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_2330418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330418 prefixEnd_2330418 := by exact prefixLift 2330418
  have htrace : WordTrace (prefixWord ++ tailWord_2330418) baseStart_2330418 baseEnd_2330418 := by
    simpa [prefixWord, tailWord_2330418, baseEnd_2330418] using wordTrace_append hprefix tailTrace_2330418
  have hstable : (prefixWord ++ tailWord_2330418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330418).length < 2 ^ (prefixWord ++ tailWord_2330418).sum := by decide
  have hdescent : baseEnd_2330418 < baseStart_2330418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330424 : List Nat := [2, 1, 2, 1, 3, 4, 3, 7]
def baseStart_2330424 : Nat := 118140960795 + 2330424 * 2 ^ 59
def prefixEnd_2330424 : Nat := 4983230072969 + 3 ^ 40 * 2330424 * 2
def baseEnd_2330424 : Nat := 44319542250870201447503

theorem tailTrace_2330424 : CollatzResearch.WordTrace tailWord_2330424 prefixEnd_2330424 44319542250870201447503 := by
  unfold tailWord_2330424
  simp only [CollatzResearch.WordTrace]
  refine ⟨42498773054639663788767163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56665030739519551718356217 42498773054639663788767163)
  ·
    refine ⟨63748159581959495683150745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42498773054639663788767163 63748159581959495683150745)
    ·
      refine ⟨47811119686469621762363059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63748159581959495683150745 47811119686469621762363059)
      ·
        refine ⟨71716679529704432643544589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47811119686469621762363059 71716679529704432643544589)
        ·
          refine ⟨26893754823639162241329221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71716679529704432643544589 26893754823639162241329221)
          ·
            refine ⟨5042579029432342920249229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26893754823639162241329221 5042579029432342920249229)
            ·
              refine ⟨1890967136037128595093461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5042579029432342920249229 1890967136037128595093461)
              ·
                refine ⟨44319542250870201447503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1890967136037128595093461 44319542250870201447503)
                ·
                  rfl

theorem cell23_2330424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 7].length) (baseStart_2330424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330424 prefixEnd_2330424 := by exact prefixLift 2330424
  have htrace : WordTrace (prefixWord ++ tailWord_2330424) baseStart_2330424 baseEnd_2330424 := by
    simpa [prefixWord, tailWord_2330424, baseEnd_2330424] using wordTrace_append hprefix tailTrace_2330424
  have hstable : (prefixWord ++ tailWord_2330424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330424).length < 2 ^ (prefixWord ++ tailWord_2330424).sum := by decide
  have hdescent : baseEnd_2330424 < baseStart_2330424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330435 : List Nat := [1, 1, 1, 3, 1, 6, 2, 3, 1, 2, 2]
def baseStart_2330435 : Nat := 118140960795 + 2330435 * 2 ^ 59
def prefixEnd_2330435 : Nat := 4983230072969 + 3 ^ 40 * 2330435 * 2
def baseEnd_2330435 : Nat := 1196633289060694896045031

theorem tailTrace_2330435 : CollatzResearch.WordTrace tailWord_2330435 prefixEnd_2330435 1196633289060694896045031 := by
  unfold tailWord_2330435
  simp only [CollatzResearch.WordTrace]
  refine ⟨84997947312239476456184759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56665298208159650970789839 84997947312239476456184759)
  ·
    refine ⟨127496920968359214684277139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84997947312239476456184759 127496920968359214684277139)
    ·
      refine ⟨191245381452538822026415709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127496920968359214684277139 191245381452538822026415709)
      ·
        refine ⟨71717018044702058259905891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191245381452538822026415709 71717018044702058259905891)
        ·
          refine ⟨107575527067053087389858837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71717018044702058259905891 107575527067053087389858837)
          ·
            refine ⟨5042602831268113471399633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107575527067053087389858837 5042602831268113471399633)
            ·
              refine ⟨3781952123451085103549725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5042602831268113471399633 3781952123451085103549725)
              ·
                refine ⟨1418232046294156913831147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3781952123451085103549725 1418232046294156913831147)
                ·
                  refine ⟨2127348069441235370746721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418232046294156913831147 2127348069441235370746721)
                  ·
                    refine ⟨1595511052080926528060041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2127348069441235370746721 1595511052080926528060041)
                    ·
                      refine ⟨1196633289060694896045031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595511052080926528060041 1196633289060694896045031)
                      ·
                        rfl

theorem cell23_2330435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 1, 2, 2].length) (baseStart_2330435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330435 prefixEnd_2330435 := by exact prefixLift 2330435
  have htrace : WordTrace (prefixWord ++ tailWord_2330435) baseStart_2330435 baseEnd_2330435 := by
    simpa [prefixWord, tailWord_2330435, baseEnd_2330435] using wordTrace_append hprefix tailTrace_2330435
  have hstable : (prefixWord ++ tailWord_2330435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330435).length < 2 ^ (prefixWord ++ tailWord_2330435).sum := by decide
  have hdescent : baseEnd_2330435 < baseStart_2330435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330445 : List Nat := [1, 6, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_2330445 : Nat := 118140960795 + 2330445 * 2 ^ 59
def prefixEnd_2330445 : Nat := 4983230072969 + 3 ^ 40 * 2330445 * 2
def baseEnd_2330445 : Nat := 398879474622413285639995

theorem tailTrace_2330445 : CollatzResearch.WordTrace tailWord_2330445 prefixEnd_2330445 398879474622413285639995 := by
  unfold tailWord_2330445
  simp only [CollatzResearch.WordTrace]
  refine ⟨84998312042203248164048789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56665541361468832109365859 84998312042203248164048789)
  ·
    refine ⟨3984295876978277257689787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84998312042203248164048789 3984295876978277257689787)
    ·
      refine ⟨5976443815467415886534681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3984295876978277257689787 5976443815467415886534681)
      ·
        refine ⟨4482332861600561914901011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5976443815467415886534681 4482332861600561914901011)
        ·
          refine ⟨6723499292400842872351517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4482332861600561914901011 6723499292400842872351517)
          ·
            refine ⟨2521312234650316077131819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6723499292400842872351517 2521312234650316077131819)
            ·
              refine ⟨3781968351975474115697729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521312234650316077131819 3781968351975474115697729)
              ·
                refine ⟨2836476263981605586773297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3781968351975474115697729 2836476263981605586773297)
                ·
                  refine ⟨2127357197986204190079973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2836476263981605586773297 2127357197986204190079973)
                  ·
                    refine ⟨398879474622413285639995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2127357197986204190079973 398879474622413285639995)
                    ·
                      rfl

theorem cell23_2330445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_2330445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330445 prefixEnd_2330445 := by exact prefixLift 2330445
  have htrace : WordTrace (prefixWord ++ tailWord_2330445) baseStart_2330445 baseEnd_2330445 := by
    simpa [prefixWord, tailWord_2330445, baseEnd_2330445] using wordTrace_append hprefix tailTrace_2330445
  have hstable : (prefixWord ++ tailWord_2330445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330445).length < 2 ^ (prefixWord ++ tailWord_2330445).sum := by decide
  have hdescent : baseEnd_2330445 < baseStart_2330445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330468 : List Nat := [2, 3, 1, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_2330468 : Nat := 118140960795 + 2330468 * 2 ^ 59
def prefixEnd_2330468 : Nat := 4983230072969 + 3 ^ 40 * 2330468 * 2
def baseEnd_2330468 : Nat := 1196650233922293266932379

theorem tailTrace_2330468 : CollatzResearch.WordTrace tailWord_2330468 prefixEnd_2330468 1196650233922293266932379 := by
  unfold tailWord_2330468
  simp only [CollatzResearch.WordTrace]
  refine ⟨42499575460559961546068029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56666100614079948728090705 42499575460559961546068029)
  ·
    refine ⟨15937340797709985579775511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42499575460559961546068029 15937340797709985579775511)
    ·
      refine ⟨23906011196564978369663267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15937340797709985579775511 23906011196564978369663267)
      ·
        refine ⟨35859016794847467554494901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23906011196564978369663267 35859016794847467554494901)
        ·
          refine ⟨3361782824516950083233897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35859016794847467554494901 3361782824516950083233897)
          ·
            refine ⟨2521337118387712562425423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3361782824516950083233897 2521337118387712562425423)
            ·
              refine ⟨3782005677581568843638135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521337118387712562425423 3782005677581568843638135)
              ·
                refine ⟨5673008516372353265457203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3782005677581568843638135 5673008516372353265457203)
                ·
                  refine ⟨8509512774558529898185805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5673008516372353265457203 8509512774558529898185805)
                  ·
                    refine ⟨3191067290459448711819677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8509512774558529898185805 3191067290459448711819677)
                    ·
                      refine ⟨1196650233922293266932379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3191067290459448711819677 1196650233922293266932379)
                      ·
                        rfl

theorem cell23_2330468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_2330468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330468 prefixEnd_2330468 := by exact prefixLift 2330468
  have htrace : WordTrace (prefixWord ++ tailWord_2330468) baseStart_2330468 baseEnd_2330468 := by
    simpa [prefixWord, tailWord_2330468, baseEnd_2330468] using wordTrace_append hprefix tailTrace_2330468
  have hstable : (prefixWord ++ tailWord_2330468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330468).length < 2 ^ (prefixWord ++ tailWord_2330468).sum := by decide
  have hdescent : baseEnd_2330468 < baseStart_2330468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330486 : List Nat := [5, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2330486 : Nat := 118140960795 + 2330486 * 2 ^ 59
def prefixEnd_2330486 : Nat := 4983230072969 + 3 ^ 40 * 2330486 * 2
def baseEnd_2330486 : Nat := 1196659476574074196507297

theorem tailTrace_2330486 : CollatzResearch.WordTrace tailWord_2330486 prefixEnd_2330486 1196659476574074196507297 := by
  unfold tailWord_2330486
  simp only [CollatzResearch.WordTrace]
  refine ⟨5312487964690919510393207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56666538290036474777527541 5312487964690919510393207)
  ·
    refine ⟨7968731947036379265589811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5312487964690919510393207 7968731947036379265589811)
    ·
      refine ⟨11953097920554568898384717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7968731947036379265589811 11953097920554568898384717)
      ·
        refine ⟨4482411720207963336894269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11953097920554568898384717 4482411720207963336894269)
        ·
          refine ⟨1680904395077986251335351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4482411720207963336894269 1680904395077986251335351)
          ·
            refine ⟨2521356592616979377003027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1680904395077986251335351 2521356592616979377003027)
            ·
              refine ⟨3782034888925469065504541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2521356592616979377003027 3782034888925469065504541)
              ·
                refine ⟨1418263083347050899564203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3782034888925469065504541 1418263083347050899564203)
                ·
                  refine ⟨2127394625020576349346305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418263083347050899564203 2127394625020576349346305)
                  ·
                    refine ⟨1595545968765432262009729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2127394625020576349346305 1595545968765432262009729)
                    ·
                      refine ⟨1196659476574074196507297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595545968765432262009729 1196659476574074196507297)
                      ·
                        rfl

theorem cell23_2330486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2330486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330486 prefixEnd_2330486 := by exact prefixLift 2330486
  have htrace : WordTrace (prefixWord ++ tailWord_2330486) baseStart_2330486 baseEnd_2330486 := by
    simpa [prefixWord, tailWord_2330486, baseEnd_2330486] using wordTrace_append hprefix tailTrace_2330486
  have hstable : (prefixWord ++ tailWord_2330486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330486).length < 2 ^ (prefixWord ++ tailWord_2330486).sum := by decide
  have hdescent : baseEnd_2330486 < baseStart_2330486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330507 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 9]
def baseStart_2330507 : Nat := 118140960795 + 2330507 * 2 ^ 59
def prefixEnd_2330507 : Nat := 4983230072969 + 3 ^ 40 * 2330507 * 2
def baseEnd_2330507 : Nat := 1196670259667818614344699

theorem tailTrace_2330507 : CollatzResearch.WordTrace tailWord_2330507 prefixEnd_2330507 1196670259667818614344699 := by
  unfold tailWord_2330507
  simp only [CollatzResearch.WordTrace]
  refine ⟨85000573367978632752805775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56667048911985755168537183 85000573367978632752805775)
  ·
    refine ⟨127500860051967949129208663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85000573367978632752805775 127500860051967949129208663)
    ·
      refine ⟨191251290077951923693812995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127500860051967949129208663 191251290077951923693812995)
      ·
        refine ⟨286876935116927885540719493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191251290077951923693812995 286876935116927885540719493)
        ·
          refine ⟨53789425334423978538884905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 286876935116927885540719493 53789425334423978538884905)
          ·
            refine ⟨40342069000817983904163679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53789425334423978538884905 40342069000817983904163679)
            ·
              refine ⟨60513103501226975856245519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40342069000817983904163679 60513103501226975856245519)
              ·
                refine ⟨90769655251840463784368279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60513103501226975856245519 90769655251840463784368279)
                ·
                  refine ⟨136154482877760695676552419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90769655251840463784368279 136154482877760695676552419)
                  ·
                    refine ⟨204231724316641043514828629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 136154482877760695676552419 204231724316641043514828629)
                    ·
                      refine ⟨1196670259667818614344699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 204231724316641043514828629 1196670259667818614344699)
                      ·
                        rfl

theorem cell23_2330507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 9].length) (baseStart_2330507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330507 prefixEnd_2330507 := by exact prefixLift 2330507
  have htrace : WordTrace (prefixWord ++ tailWord_2330507) baseStart_2330507 baseEnd_2330507 := by
    simpa [prefixWord, tailWord_2330507, baseEnd_2330507] using wordTrace_append hprefix tailTrace_2330507
  have hstable : (prefixWord ++ tailWord_2330507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330507).length < 2 ^ (prefixWord ++ tailWord_2330507).sum := by decide
  have hdescent : baseEnd_2330507 < baseStart_2330507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330508 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 2, 2, 2]
def baseStart_2330508 : Nat := 118140960795 + 2330508 * 2 ^ 59
def prefixEnd_2330508 : Nat := 4983230072969 + 3 ^ 40 * 2330508 * 2
def baseEnd_2330508 : Nat := 1196670773148473110432195

theorem tailTrace_2330508 : CollatzResearch.WordTrace tailWord_2330508 prefixEnd_2330508 1196670773148473110432195 := by
  unfold tailWord_2330508
  simp only [CollatzResearch.WordTrace]
  refine ⟨42500304920487504961796089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56667073227316673282394785 42500304920487504961796089)
  ·
    refine ⟨31875228690365628721347067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42500304920487504961796089 31875228690365628721347067)
    ·
      refine ⟨47812843035548443082020601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31875228690365628721347067 47812843035548443082020601)
      ·
        refine ⟨35859632276661332311515451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47812843035548443082020601 35859632276661332311515451)
        ·
          refine ⟨53789448414991998467273177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35859632276661332311515451 53789448414991998467273177)
          ·
            refine ⟨40342086311243998850454883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53789448414991998467273177 40342086311243998850454883)
            ·
              refine ⟨60513129466865998275682325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40342086311243998850454883 60513129466865998275682325)
              ·
                refine ⟨2836552943759343669172609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60513129466865998275682325 2836552943759343669172609)
                ·
                  refine ⟨2127414707819507751879457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2836552943759343669172609 2127414707819507751879457)
                  ·
                    refine ⟨1595561030864630813909593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2127414707819507751879457 1595561030864630813909593)
                    ·
                      refine ⟨1196670773148473110432195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595561030864630813909593 1196670773148473110432195)
                      ·
                        rfl

theorem cell23_2330508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_2330508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330508 prefixEnd_2330508 := by exact prefixLift 2330508
  have htrace : WordTrace (prefixWord ++ tailWord_2330508) baseStart_2330508 baseEnd_2330508 := by
    simpa [prefixWord, tailWord_2330508, baseEnd_2330508] using wordTrace_append hprefix tailTrace_2330508
  have hstable : (prefixWord ++ tailWord_2330508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330508).length < 2 ^ (prefixWord ++ tailWord_2330508).sum := by decide
  have hdescent : baseEnd_2330508 < baseStart_2330508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330525 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_2330525 : Nat := 118140960795 + 2330525 * 2 ^ 59
def prefixEnd_2330525 : Nat := 4983230072969 + 3 ^ 40 * 2330525 * 2
def baseEnd_2330525 : Nat := 1196679502319599543919617

theorem tailTrace_2330525 : CollatzResearch.WordTrace tailWord_2330525 prefixEnd_2330525 1196679502319599543919617 := by
  unfold tailWord_2330525
  simp only [CollatzResearch.WordTrace]
  refine ⟨85001229881913421826961029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56667486587942281217974019 85001229881913421826961029)
  ·
    refine ⟨15937730602858766592555193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85001229881913421826961029 15937730602858766592555193)
    ·
      refine ⟨11953297952144074944416395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15937730602858766592555193 11953297952144074944416395)
      ·
        refine ⟨17929946928216112416624593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11953297952144074944416395 17929946928216112416624593)
        ·
          refine ⟨13447460196162084312468445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17929946928216112416624593 13447460196162084312468445)
          ·
            refine ⟨5042797573560781617175667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13447460196162084312468445 5042797573560781617175667)
            ·
              refine ⟨7564196360341172425763501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5042797573560781617175667 7564196360341172425763501)
              ·
                refine ⟨2836573635127939659661313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7564196360341172425763501 2836573635127939659661313)
                ·
                  refine ⟨2127430226345954744745985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2836573635127939659661313 2127430226345954744745985)
                  ·
                    refine ⟨1595572669759466058559489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2127430226345954744745985 1595572669759466058559489)
                    ·
                      refine ⟨1196679502319599543919617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595572669759466058559489 1196679502319599543919617)
                      ·
                        rfl

theorem cell23_2330525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_2330525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330525 prefixEnd_2330525 := by exact prefixLift 2330525
  have htrace : WordTrace (prefixWord ++ tailWord_2330525) baseStart_2330525 baseEnd_2330525 := by
    simpa [prefixWord, tailWord_2330525, baseEnd_2330525] using wordTrace_append hprefix tailTrace_2330525
  have hstable : (prefixWord ++ tailWord_2330525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330525).length < 2 ^ (prefixWord ++ tailWord_2330525).sum := by decide
  have hdescent : baseEnd_2330525 < baseStart_2330525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330591 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 5, 4]
def baseStart_2330591 : Nat := 118140960795 + 2330591 * 2 ^ 59
def prefixEnd_2330591 : Nat := 4983230072969 + 3 ^ 40 * 2330591 * 2
def baseEnd_2330591 : Nat := 398904464014265428564771

theorem tailTrace_2330591 : CollatzResearch.WordTrace tailWord_2330591 prefixEnd_2330591 398904464014265428564771 := by
  unfold tailWord_2330591
  simp only [CollatzResearch.WordTrace]
  refine ⟨85003637099674315098863627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56669091399782876732575751 85003637099674315098863627)
  ·
    refine ⟨127505455649511472648295441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85003637099674315098863627 127505455649511472648295441)
    ·
      refine ⟨95629091737133604486221581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127505455649511472648295441 95629091737133604486221581)
      ·
        refine ⟨35860909401425101682333093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95629091737133604486221581 35860909401425101682333093)
        ·
          refine ⟨6723920512767206565437455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35860909401425101682333093 6723920512767206565437455)
          ·
            refine ⟨10085880769150809848156183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6723920512767206565437455 10085880769150809848156183)
            ·
              refine ⟨15128821153726214772234275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10085880769150809848156183 15128821153726214772234275)
              ·
                refine ⟨22693231730589322158351413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15128821153726214772234275 22693231730589322158351413)
                ·
                  refine ⟨2127490474742748952345445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22693231730589322158351413 2127490474742748952345445)
                  ·
                    refine ⟨398904464014265428564771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2127490474742748952345445 398904464014265428564771)
                    ·
                      rfl

theorem cell23_2330591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 5, 4].length) (baseStart_2330591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330591 prefixEnd_2330591 := by exact prefixLift 2330591
  have htrace : WordTrace (prefixWord ++ tailWord_2330591) baseStart_2330591 baseEnd_2330591 := by
    simpa [prefixWord, tailWord_2330591, baseEnd_2330591] using wordTrace_append hprefix tailTrace_2330591
  have hstable : (prefixWord ++ tailWord_2330591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330591).length < 2 ^ (prefixWord ++ tailWord_2330591).sum := by decide
  have hdescent : baseEnd_2330591 < baseStart_2330591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330608 : List Nat := [2, 1, 1, 1, 3, 2, 3, 5, 1, 4]
def baseStart_2330608 : Nat := 118140960795 + 2330608 * 2 ^ 59
def prefixEnd_2330608 : Nat := 4983230072969 + 3 ^ 40 * 2330608 * 2
def baseEnd_2330608 : Nat := 398907373737974239727245

theorem tailTrace_2330608 : CollatzResearch.WordTrace tailWord_2330608 prefixEnd_2330608 398907373737974239727245 := by
  unfold tailWord_2330608
  simp only [CollatzResearch.WordTrace]
  refine ⟨42502128570306363501116239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56669504760408484668154985 42502128570306363501116239)
  ·
    refine ⟨63753192855459545251674359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42502128570306363501116239 63753192855459545251674359)
    ·
      refine ⟨95629789283189317877511539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63753192855459545251674359 95629789283189317877511539)
      ·
        refine ⟨143444683924783976816267309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95629789283189317877511539 143444683924783976816267309)
        ·
          refine ⟨53791756471793991306100241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143444683924783976816267309 53791756471793991306100241)
          ·
            refine ⟨40343817353845493479575181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53791756471793991306100241 40343817353845493479575181)
            ·
              refine ⟨15128931507692060054840693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40343817353845493479575181 15128931507692060054840693)
              ·
                refine ⟨1418337328846130630141315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15128931507692060054840693 1418337328846130630141315)
                ·
                  refine ⟨2127505993269195945211973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418337328846130630141315 2127505993269195945211973)
                  ·
                    refine ⟨398907373737974239727245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2127505993269195945211973 398907373737974239727245)
                    ·
                      rfl

theorem cell23_2330608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 1, 4].length) (baseStart_2330608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330608 prefixEnd_2330608 := by exact prefixLift 2330608
  have htrace : WordTrace (prefixWord ++ tailWord_2330608) baseStart_2330608 baseEnd_2330608 := by
    simpa [prefixWord, tailWord_2330608, baseEnd_2330608] using wordTrace_append hprefix tailTrace_2330608
  have hstable : (prefixWord ++ tailWord_2330608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330608).length < 2 ^ (prefixWord ++ tailWord_2330608).sum := by decide
  have hdescent : baseEnd_2330608 < baseStart_2330608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330621 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 6]
def baseStart_2330621 : Nat := 118140960795 + 2330621 * 2 ^ 59
def prefixEnd_2330621 : Nat := 4983230072969 + 3 ^ 40 * 2330621 * 2
def baseEnd_2330621 : Nat := 132969866273603463146575

theorem tailTrace_2330621 : CollatzResearch.WordTrace tailWord_2330621 prefixEnd_2330621 132969866273603463146575 := by
  unfold tailWord_2330621
  simp only [CollatzResearch.WordTrace]
  refine ⟨85004731289565630222455717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56669820859710420148303811 85004731289565630222455717)
  ·
    refine ⟨15938387116793555666710447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85004731289565630222455717 15938387116793555666710447)
    ·
      refine ⟨23907580675190333500065671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15938387116793555666710447 23907580675190333500065671)
      ·
        refine ⟨35861371012785500250098507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23907580675190333500065671 35861371012785500250098507)
        ·
          refine ⟨53792056519178250375147761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35861371012785500250098507 53792056519178250375147761)
          ·
            refine ⟨40344042389383687781360821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53792056519178250375147761 40344042389383687781360821)
            ·
              refine ⟨3782253974004720729502577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40344042389383687781360821 3782253974004720729502577)
              ·
                refine ⟨2836690480503540547126933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3782253974004720729502577 2836690480503540547126933)
                ·
                  refine ⟨132969866273603463146575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2836690480503540547126933 132969866273603463146575)
                  ·
                    rfl

theorem cell23_2330621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_2330621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330621 prefixEnd_2330621 := by exact prefixLift 2330621
  have htrace : WordTrace (prefixWord ++ tailWord_2330621) baseStart_2330621 baseEnd_2330621 := by
    simpa [prefixWord, tailWord_2330621, baseEnd_2330621] using wordTrace_append hprefix tailTrace_2330621
  have hstable : (prefixWord ++ tailWord_2330621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330621).length < 2 ^ (prefixWord ++ tailWord_2330621).sum := by decide
  have hdescent : baseEnd_2330621 < baseStart_2330621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330638 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 6]
def baseStart_2330638 : Nat := 118140960795 + 2330638 * 2 ^ 59
def prefixEnd_2330638 : Nat := 4983230072969 + 3 ^ 40 * 2330638 * 2
def baseEnd_2330638 : Nat := 132970836181506400200733

theorem tailTrace_2330638 : CollatzResearch.WordTrace tailWord_2330638 prefixEnd_2330638 132970836181506400200733 := by
  unfold tailWord_2330638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10625668916313005265728071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56670234220336028083883045 10625668916313005265728071)
  ·
    refine ⟨15938503374469507898592107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10625668916313005265728071 15938503374469507898592107)
    ·
      refine ⟨23907755061704261847888161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15938503374469507898592107 23907755061704261847888161)
      ·
        refine ⟨17930816296278196385916121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23907755061704261847888161 17930816296278196385916121)
        ·
          refine ⟨13448112222208647289437091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17930816296278196385916121 13448112222208647289437091)
          ·
            refine ⟨20172168333312970934155637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13448112222208647289437091 20172168333312970934155637)
            ·
              refine ⟨1891140781248091025077091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20172168333312970934155637 1891140781248091025077091)
              ·
                refine ⟨2836711171872136537615637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891140781248091025077091 2836711171872136537615637)
                ·
                  refine ⟨132970836181506400200733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2836711171872136537615637 132970836181506400200733)
                  ·
                    rfl

theorem cell23_2330638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 6].length) (baseStart_2330638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330638 prefixEnd_2330638 := by exact prefixLift 2330638
  have htrace : WordTrace (prefixWord ++ tailWord_2330638) baseStart_2330638 baseEnd_2330638 := by
    simpa [prefixWord, tailWord_2330638, baseEnd_2330638] using wordTrace_append hprefix tailTrace_2330638
  have hstable : (prefixWord ++ tailWord_2330638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330638).length < 2 ^ (prefixWord ++ tailWord_2330638).sum := by decide
  have hdescent : baseEnd_2330638 < baseStart_2330638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330648 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2330648 : Nat := 118140960795 + 2330648 * 2 ^ 59
def prefixEnd_2330648 : Nat := 4983230072969 + 3 ^ 40 * 2330648 * 2
def baseEnd_2330648 : Nat := 1196742660440102562681551

theorem tailTrace_2330648 : CollatzResearch.WordTrace tailWord_2330648 prefixEnd_2330648 1196742660440102562681551 := by
  unfold tailWord_2330648
  simp only [CollatzResearch.WordTrace]
  refine ⟨42502858030233906916844299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56670477373645209222459065 42502858030233906916844299)
  ·
    refine ⟨63754287045350860375266449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42502858030233906916844299 63754287045350860375266449)
    ·
      refine ⟨47815715284013145281449837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63754287045350860375266449 47815715284013145281449837)
      ·
        refine ⟨17930893231504929480543689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47815715284013145281449837 17930893231504929480543689)
        ·
          refine ⟨13448169923628697110407767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17930893231504929480543689 13448169923628697110407767)
          ·
            refine ⟨20172254885443045665611651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13448169923628697110407767 20172254885443045665611651)
            ·
              refine ⟨30258382328164568498417477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20172254885443045665611651 30258382328164568498417477)
              ·
                refine ⟨5673446686530856593453277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30258382328164568498417477 5673446686530856593453277)
                ·
                  refine ⟨2127542507449071222544979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5673446686530856593453277 2127542507449071222544979)
                  ·
                    refine ⟨3191313761173606833817469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2127542507449071222544979 3191313761173606833817469)
                    ·
                      refine ⟨1196742660440102562681551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3191313761173606833817469 1196742660440102562681551)
                      ·
                        rfl

theorem cell23_2330648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2330648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330648 prefixEnd_2330648 := by exact prefixLift 2330648
  have htrace : WordTrace (prefixWord ++ tailWord_2330648) baseStart_2330648 baseEnd_2330648 := by
    simpa [prefixWord, tailWord_2330648, baseEnd_2330648] using wordTrace_append hprefix tailTrace_2330648
  have hstable : (prefixWord ++ tailWord_2330648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330648).length < 2 ^ (prefixWord ++ tailWord_2330648).sum := by decide
  have hdescent : baseEnd_2330648 < baseStart_2330648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330658 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_2330658 : Nat := 118140960795 + 2330658 * 2 ^ 59
def prefixEnd_2330658 : Nat := 4983230072969 + 3 ^ 40 * 2330658 * 2
def baseEnd_2330658 : Nat := 1196747795246647523556505

theorem tailTrace_2330658 : CollatzResearch.WordTrace tailWord_2330658 prefixEnd_2330658 1196747795246647523556505 := by
  unfold tailWord_2330658
  simp only [CollatzResearch.WordTrace]
  refine ⟨21251520197607896385388157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56670720526954390361035085 21251520197607896385388157)
  ·
    refine ⟨7969320074102961144520559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21251520197607896385388157 7969320074102961144520559)
    ·
      refine ⟨11953980111154441716780839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7969320074102961144520559 11953980111154441716780839)
      ·
        refine ⟨17930970166731662575171259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11953980111154441716780839 17930970166731662575171259)
        ·
          refine ⟨26896455250097493862756889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17930970166731662575171259 26896455250097493862756889)
          ·
            refine ⟨20172341437573120397067667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26896455250097493862756889 20172341437573120397067667)
            ·
              refine ⟨30258512156359680595601501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20172341437573120397067667 30258512156359680595601501)
              ·
                refine ⟨11346942058634880223350563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30258512156359680595601501 11346942058634880223350563)
                ·
                  refine ⟨17020413087952320335025845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11346942058634880223350563 17020413087952320335025845)
                  ·
                    refine ⟨1595663726995530031408673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17020413087952320335025845 1595663726995530031408673)
                    ·
                      refine ⟨1196747795246647523556505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595663726995530031408673 1196747795246647523556505)
                      ·
                        rfl

theorem cell23_2330658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_2330658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330658 prefixEnd_2330658 := by exact prefixLift 2330658
  have htrace : WordTrace (prefixWord ++ tailWord_2330658) baseStart_2330658 baseEnd_2330658 := by
    simpa [prefixWord, tailWord_2330658, baseEnd_2330658] using wordTrace_append hprefix tailTrace_2330658
  have hstable : (prefixWord ++ tailWord_2330658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330658).length < 2 ^ (prefixWord ++ tailWord_2330658).sum := by decide
  have hdescent : baseEnd_2330658 < baseStart_2330658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330755 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 2, 1, 3]
def baseStart_2330755 : Nat := 118140960795 + 2330755 * 2 ^ 59
def prefixEnd_2330755 : Nat := 4983230072969 + 3 ^ 40 * 2330755 * 2
def baseEnd_2330755 : Nat := 1196797602870133644043559

theorem tailTrace_2330755 : CollatzResearch.WordTrace tailWord_2330755 prefixEnd_2330755 1196797602870133644043559 := by
  unfold tailWord_2330755
  simp only [CollatzResearch.WordTrace]
  refine ⟨85009618671080171107833719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56673079114053447405222479 85009618671080171107833719)
  ·
    refine ⟨127514428006620256661750579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85009618671080171107833719 127514428006620256661750579)
    ·
      refine ⟨191271642009930384992625869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127514428006620256661750579 191271642009930384992625869)
      ·
        refine ⟨71726865753723894372234701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191271642009930384992625869 71726865753723894372234701)
        ·
          refine ⟨26897574657646460389588013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71726865753723894372234701 26897574657646460389588013)
          ·
            refine ⟨10086590496617422646095505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26897574657646460389588013 10086590496617422646095505)
            ·
              refine ⟨7564942872463066984571629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10086590496617422646095505 7564942872463066984571629)
              ·
                refine ⟨2836853577173650119214361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7564942872463066984571629 2836853577173650119214361)
                ·
                  refine ⟨2127640182880237589410771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2836853577173650119214361 2127640182880237589410771)
                  ·
                    refine ⟨3191460274320356384116157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2127640182880237589410771 3191460274320356384116157)
                    ·
                      refine ⟨1196797602870133644043559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3191460274320356384116157 1196797602870133644043559)
                      ·
                        rfl

theorem cell23_2330755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_2330755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330755 prefixEnd_2330755 := by exact prefixLift 2330755
  have htrace : WordTrace (prefixWord ++ tailWord_2330755) baseStart_2330755 baseEnd_2330755 := by
    simpa [prefixWord, tailWord_2330755, baseEnd_2330755] using wordTrace_append hprefix tailTrace_2330755
  have hstable : (prefixWord ++ tailWord_2330755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330755).length < 2 ^ (prefixWord ++ tailWord_2330755).sum := by decide
  have hdescent : baseEnd_2330755 < baseStart_2330755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330761 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 4]
def baseStart_2330761 : Nat := 118140960795 + 2330761 * 2 ^ 59
def prefixEnd_2330761 : Nat := 4983230072969 + 3 ^ 40 * 2330761 * 2
def baseEnd_2330761 : Nat := 1196800683754060620568531

theorem tailTrace_2330761 : CollatzResearch.WordTrace tailWord_2330761 prefixEnd_2330761 1196800683754060620568531 := by
  unfold tailWord_2330761
  simp only [CollatzResearch.WordTrace]
  refine ⟨85009837509058434132552137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56673225006038956088368091 85009837509058434132552137)
  ·
    refine ⟨63757378131793825599414103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85009837509058434132552137 63757378131793825599414103)
    ·
      refine ⟨95636067197690738399121155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63757378131793825599414103 95636067197690738399121155)
      ·
        refine ⟨143454100796536107598681733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95636067197690738399121155 143454100796536107598681733)
        ·
          refine ⟨26897643899350520174752825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143454100796536107598681733 26897643899350520174752825)
          ·
            refine ⟨20173232924512890131064619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26897643899350520174752825 20173232924512890131064619)
            ·
              refine ⟨30259849386769335196596929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20173232924512890131064619 30259849386769335196596929)
              ·
                refine ⟨22694887040077001397447697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30259849386769335196596929 22694887040077001397447697)
                ·
                  refine ⟨17021165280057751048085773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22694887040077001397447697 17021165280057751048085773)
                  ·
                    refine ⟨6382936980021656643032165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17021165280057751048085773 6382936980021656643032165)
                    ·
                      refine ⟨1196800683754060620568531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6382936980021656643032165 1196800683754060620568531)
                      ·
                        rfl

theorem cell23_2330761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_2330761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330761 prefixEnd_2330761 := by exact prefixLift 2330761
  have htrace : WordTrace (prefixWord ++ tailWord_2330761) baseStart_2330761 baseEnd_2330761 := by
    simpa [prefixWord, tailWord_2330761, baseEnd_2330761] using wordTrace_append hprefix tailTrace_2330761
  have hstable : (prefixWord ++ tailWord_2330761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330761).length < 2 ^ (prefixWord ++ tailWord_2330761).sum := by decide
  have hdescent : baseEnd_2330761 < baseStart_2330761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330831 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 1, 7]
def baseStart_2330831 : Nat := 118140960795 + 2330831 * 2 ^ 59
def prefixEnd_2330831 : Nat := 4983230072969 + 3 ^ 40 * 2330831 * 2
def baseEnd_2330831 : Nat := 398945542466625115564403

theorem tailTrace_2330831 : CollatzResearch.WordTrace tailWord_2330831 prefixEnd_2330831 398945542466625115564403 := by
  unfold tailWord_2330831
  simp only [CollatzResearch.WordTrace]
  refine ⟨85012390618804836087600347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56674927079203224058400231 85012390618804836087600347)
  ·
    refine ⟨127518585928207254131400521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85012390618804836087600347 127518585928207254131400521)
    ·
      refine ⟨95638939446155440598550391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127518585928207254131400521 95638939446155440598550391)
      ·
        refine ⟨143458409169233160897825587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95638939446155440598550391 143458409169233160897825587)
        ·
          refine ⟨215187613753849741346738381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143458409169233160897825587 215187613753849741346738381)
          ·
            refine ⟨80695355157693653005026893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215187613753849741346738381 80695355157693653005026893)
            ·
              refine ⟨30260758184135119876885085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80695355157693653005026893 30260758184135119876885085)
              ·
                refine ⟨11347784319050669953831907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30260758184135119876885085 11347784319050669953831907)
                ·
                  refine ⟨17021676478576004930747861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11347784319050669953831907 17021676478576004930747861)
                  ·
                    refine ⟨398945542466625115564403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17021676478576004930747861 398945542466625115564403)
                    ·
                      rfl

theorem cell23_2330831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_2330831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330831 prefixEnd_2330831 := by exact prefixLift 2330831
  have htrace : WordTrace (prefixWord ++ tailWord_2330831) baseStart_2330831 baseEnd_2330831 := by
    simpa [prefixWord, tailWord_2330831, baseEnd_2330831] using wordTrace_append hprefix tailTrace_2330831
  have hstable : (prefixWord ++ tailWord_2330831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330831).length < 2 ^ (prefixWord ++ tailWord_2330831).sum := by decide
  have hdescent : baseEnd_2330831 < baseStart_2330831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330848 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 2, 5]
def baseStart_2330848 : Nat := 118140960795 + 2330848 * 2 ^ 59
def prefixEnd_2330848 : Nat := 4983230072969 + 3 ^ 40 * 2330848 * 2
def baseEnd_2330848 : Nat := 398948452190333926726877

theorem tailTrace_2330848 : CollatzResearch.WordTrace tailWord_2330848 prefixEnd_2330848 398948452190333926726877 := by
  unfold tailWord_2330848
  simp only [CollatzResearch.WordTrace]
  refine ⟨42506505329871623995484599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56675340439828831993979465 42506505329871623995484599)
  ·
    refine ⟨63759757994807435993226899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42506505329871623995484599 63759757994807435993226899)
    ·
      refine ⟨95639636992211153989840349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63759757994807435993226899 95639636992211153989840349)
      ·
        refine ⟨35864863872079182746190131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95639636992211153989840349 35864863872079182746190131)
        ·
          refine ⟨53797295808118774119285197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35864863872079182746190131 53797295808118774119285197)
          ·
            refine ⟨20173985928044540294731949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53797295808118774119285197 20173985928044540294731949)
            ·
              refine ⟨7565244723016702610524481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20173985928044540294731949 7565244723016702610524481)
              ·
                refine ⟨5673933542262526957893361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7565244723016702610524481 5673933542262526957893361)
                ·
                  refine ⟨4255450156696895218420021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5673933542262526957893361 4255450156696895218420021)
                  ·
                    refine ⟨398948452190333926726877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4255450156696895218420021 398948452190333926726877)
                    ·
                      rfl

theorem cell23_2330848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_2330848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330848 prefixEnd_2330848 := by exact prefixLift 2330848
  have htrace : WordTrace (prefixWord ++ tailWord_2330848) baseStart_2330848 baseEnd_2330848 := by
    simpa [prefixWord, tailWord_2330848, baseEnd_2330848] using wordTrace_append hprefix tailTrace_2330848
  have hstable : (prefixWord ++ tailWord_2330848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330848).length < 2 ^ (prefixWord ++ tailWord_2330848).sum := by decide
  have hdescent : baseEnd_2330848 < baseStart_2330848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330858 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2330858 : Nat := 118140960795 + 2330858 * 2 ^ 59
def prefixEnd_2330858 : Nat := 4983230072969 + 3 ^ 40 * 2330858 * 2
def baseEnd_2330858 : Nat := 1196850491377546741055585

theorem tailTrace_2330858 : CollatzResearch.WordTrace tailWord_2330858 prefixEnd_2330858 1196850491377546741055585 := by
  unfold tailWord_2330858
  simp only [CollatzResearch.WordTrace]
  refine ⟨21253343847426754924708307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56675583593138013132555485 21253343847426754924708307)
  ·
    refine ⟨31880015771140132387062461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21253343847426754924708307 31880015771140132387062461)
    ·
      refine ⟨11955005914177549645148423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31880015771140132387062461 11955005914177549645148423)
      ·
        refine ⟨17932508871266324467722635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11955005914177549645148423 17932508871266324467722635)
        ·
          refine ⟨26898763306899486701583953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17932508871266324467722635 26898763306899486701583953)
          ·
            refine ⟨20174072480174615026187965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26898763306899486701583953 20174072480174615026187965)
            ·
              refine ⟨7565277180065480634820487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20174072480174615026187965 7565277180065480634820487)
              ·
                refine ⟨11347915770098220952230731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7565277180065480634820487 11347915770098220952230731)
                ·
                  refine ⟨17021873655147331428346097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11347915770098220952230731 17021873655147331428346097)
                  ·
                    refine ⟨12766405241360498571259573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17021873655147331428346097 12766405241360498571259573)
                    ·
                      refine ⟨1196850491377546741055585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12766405241360498571259573 1196850491377546741055585)
                      ·
                        rfl

theorem cell23_2330858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2330858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330858 prefixEnd_2330858 := by exact prefixLift 2330858
  have htrace : WordTrace (prefixWord ++ tailWord_2330858) baseStart_2330858 baseEnd_2330858 := by
    simpa [prefixWord, tailWord_2330858, baseEnd_2330858] using wordTrace_append hprefix tailTrace_2330858
  have hstable : (prefixWord ++ tailWord_2330858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330858).length < 2 ^ (prefixWord ++ tailWord_2330858).sum := by decide
  have hdescent : baseEnd_2330858 < baseStart_2330858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330882 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2330882 : Nat := 118140960795 + 2330882 * 2 ^ 59
def prefixEnd_2330882 : Nat := 4983230072969 + 3 ^ 40 * 2330882 * 2
def baseEnd_2330882 : Nat := 398954271637751549051825

theorem tailTrace_2330882 : CollatzResearch.WordTrace tailWord_2330882 prefixEnd_2330882 398954271637751549051825 := by
  unfold tailWord_2330882
  simp only [CollatzResearch.WordTrace]
  refine ⟨21253562685405017949426725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56676167161080047865137933 21253562685405017949426725)
  ·
    refine ⟨3985043003513440865517511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21253562685405017949426725 3985043003513440865517511)
    ·
      refine ⟨5977564505270161298276267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3985043003513440865517511 5977564505270161298276267)
      ·
        refine ⟨8966346757905241947414401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5977564505270161298276267 8966346757905241947414401)
        ·
          refine ⟨6724760068428931460560801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8966346757905241947414401 6724760068428931460560801)
          ·
            refine ⟨5043570051321698595420601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6724760068428931460560801 5043570051321698595420601)
            ·
              refine ⟨3782677538491273946565451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5043570051321698595420601 3782677538491273946565451)
              ·
                refine ⟨5674016307736910919848177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3782677538491273946565451 5674016307736910919848177)
                ·
                  refine ⟨4255512230802683189886133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5674016307736910919848177 4255512230802683189886133)
                  ·
                    refine ⟨398954271637751549051825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4255512230802683189886133 398954271637751549051825)
                    ·
                      rfl

theorem cell23_2330882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2330882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330882 prefixEnd_2330882 := by exact prefixLift 2330882
  have htrace : WordTrace (prefixWord ++ tailWord_2330882) baseStart_2330882 baseEnd_2330882 := by
    simpa [prefixWord, tailWord_2330882, baseEnd_2330882] using wordTrace_append hprefix tailTrace_2330882
  have hstable : (prefixWord ++ tailWord_2330882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330882).length < 2 ^ (prefixWord ++ tailWord_2330882).sum := by decide
  have hdescent : baseEnd_2330882 < baseStart_2330882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330962 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_2330962 : Nat := 118140960795 + 2330962 * 2 ^ 59
def prefixEnd_2330962 : Nat := 4983230072969 + 3 ^ 40 * 2330962 * 2
def baseEnd_2330962 : Nat := 1196903893365614334155107

theorem tailTrace_2330962 : CollatzResearch.WordTrace tailWord_2330962 prefixEnd_2330962 1196903893365614334155107 := by
  unfold tailWord_2330962
  simp only [CollatzResearch.WordTrace]
  refine ⟨21254292145332561365154785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56678112387553496973746093 21254292145332561365154785)
  ·
    refine ⟨15940719108999421023866089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21254292145332561365154785 15940719108999421023866089)
    ·
      refine ⟨11955539331749565767899567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15940719108999421023866089 11955539331749565767899567)
      ·
        refine ⟨17933308997624348651849351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11955539331749565767899567 17933308997624348651849351)
        ·
          refine ⟨26899963496436522977774027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17933308997624348651849351 26899963496436522977774027)
          ·
            refine ⟨40349945244654784466661041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26899963496436522977774027 40349945244654784466661041)
            ·
              refine ⟨30262458933491088349995781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40349945244654784466661041 30262458933491088349995781)
              ·
                refine ⟨5674211050029579065624209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30262458933491088349995781 5674211050029579065624209)
                ·
                  refine ⟨4255658287522184299218157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5674211050029579065624209 4255658287522184299218157)
                  ·
                    refine ⟨1595871857820819112206809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4255658287522184299218157 1595871857820819112206809)
                    ·
                      refine ⟨1196903893365614334155107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595871857820819112206809 1196903893365614334155107)
                      ·
                        rfl

theorem cell23_2330962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_2330962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330962 prefixEnd_2330962 := by exact prefixLift 2330962
  have htrace : WordTrace (prefixWord ++ tailWord_2330962) baseStart_2330962 baseEnd_2330962 := by
    simpa [prefixWord, tailWord_2330962, baseEnd_2330962] using wordTrace_append hprefix tailTrace_2330962
  have hstable : (prefixWord ++ tailWord_2330962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330962).length < 2 ^ (prefixWord ++ tailWord_2330962).sum := by decide
  have hdescent : baseEnd_2330962 < baseStart_2330962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2330992 : List Nat := [2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 4]
def baseStart_2330992 : Nat := 118140960795 + 2330992 * 2 ^ 59
def prefixEnd_2330992 : Nat := 4983230072969 + 3 ^ 40 * 2330992 * 2
def baseEnd_2330992 : Nat := 1196919297785249216779969

theorem tailTrace_2330992 : CollatzResearch.WordTrace tailWord_2330992 prefixEnd_2330992 1196919297785249216779969 := by
  unfold tailWord_2330992
  simp only [CollatzResearch.WordTrace]
  refine ⟨42509131385610780292105615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56678841847481040389474153 42509131385610780292105615)
  ·
    refine ⟨63763697078416170438158423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42509131385610780292105615 63763697078416170438158423)
    ·
      refine ⟨95645545617624255657237635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63763697078416170438158423 95645545617624255657237635)
      ·
        refine ⟨143468318426436383485856453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95645545617624255657237635 143468318426436383485856453)
        ·
          refine ⟨26900309704956821903598085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 143468318426436383485856453 26900309704956821903598085)
          ·
            refine ⟨5043808069679404106924641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26900309704956821903598085 5043808069679404106924641)
            ·
              refine ⟨3782856052259553080193481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5043808069679404106924641 3782856052259553080193481)
              ·
                refine ⟨2837142039194664810145111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3782856052259553080193481 2837142039194664810145111)
                ·
                  refine ⟨4255713058791997215217667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837142039194664810145111 4255713058791997215217667)
                  ·
                    refine ⟨6383569588187995822826501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4255713058791997215217667 6383569588187995822826501)
                    ·
                      refine ⟨1196919297785249216779969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6383569588187995822826501 1196919297785249216779969)
                      ·
                        rfl

theorem cell23_2330992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 4].length) (baseStart_2330992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2330992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2330992 prefixEnd_2330992 := by exact prefixLift 2330992
  have htrace : WordTrace (prefixWord ++ tailWord_2330992) baseStart_2330992 baseEnd_2330992 := by
    simpa [prefixWord, tailWord_2330992, baseEnd_2330992] using wordTrace_append hprefix tailTrace_2330992
  have hstable : (prefixWord ++ tailWord_2330992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2330992).length < 2 ^ (prefixWord ++ tailWord_2330992).sum := by decide
  have hdescent : baseEnd_2330992 < baseStart_2330992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2330992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331012 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_2331012 : Nat := 118140960795 + 2331012 * 2 ^ 59
def prefixEnd_2331012 : Nat := 4983230072969 + 3 ^ 40 * 2331012 * 2
def baseEnd_2331012 : Nat := 1196929567398339138529877

theorem tailTrace_2331012 : CollatzResearch.WordTrace tailWord_2331012 prefixEnd_2331012 1196929567398339138529877 := by
  unfold tailWord_2331012
  simp only [CollatzResearch.WordTrace]
  refine ⟨42509496115574551999969645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56679328154099402666626193 42509496115574551999969645)
  ·
    refine ⟨15941061043340456999988617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42509496115574551999969645 15941061043340456999988617)
    ·
      refine ⟨11955795782505342749991463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15941061043340456999988617 11955795782505342749991463)
      ·
        refine ⟨17933693673758014124987195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11955795782505342749991463 17933693673758014124987195)
        ·
          refine ⟨26900540510637021187480793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17933693673758014124987195 26900540510637021187480793)
          ·
            refine ⟨20175405382977765890610595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26900540510637021187480793 20175405382977765890610595)
            ·
              refine ⟨30263108074466648835915893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20175405382977765890610595 30263108074466648835915893)
              ·
                refine ⟨2837166381981248328367115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30263108074466648835915893 2837166381981248328367115)
                ·
                  refine ⟨4255749572971872492550673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837166381981248328367115 4255749572971872492550673)
                  ·
                    refine ⟨3191812179728904369413005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4255749572971872492550673 3191812179728904369413005)
                    ·
                      refine ⟨1196929567398339138529877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3191812179728904369413005 1196929567398339138529877)
                      ·
                        rfl

theorem cell23_2331012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_2331012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331012 prefixEnd_2331012 := by exact prefixLift 2331012
  have htrace : WordTrace (prefixWord ++ tailWord_2331012) baseStart_2331012 baseEnd_2331012 := by
    simpa [prefixWord, tailWord_2331012, baseEnd_2331012] using wordTrace_append hprefix tailTrace_2331012
  have hstable : (prefixWord ++ tailWord_2331012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331012).length < 2 ^ (prefixWord ++ tailWord_2331012).sum := by decide
  have hdescent : baseEnd_2331012 < baseStart_2331012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331042 : List Nat := [3, 3, 1, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2331042 : Nat := 118140960795 + 2331042 * 2 ^ 59
def prefixEnd_2331042 : Nat := 4983230072969 + 3 ^ 40 * 2331042 * 2
def baseEnd_2331042 : Nat := 1196944971817974021154739

theorem tailTrace_2331042 : CollatzResearch.WordTrace tailWord_2331042 prefixEnd_2331042 1196944971817974021154739 := by
  unfold tailWord_2331042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21255021605260104780882845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56680057614026946082354253 21255021605260104780882845)
  ·
    refine ⟨7970633101972539292831067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21255021605260104780882845 7970633101972539292831067)
    ·
      refine ⟨11955949652958808939246601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7970633101972539292831067 11955949652958808939246601)
      ·
        refine ⟨8966962239719106704434951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11955949652958808939246601 8966962239719106704434951)
        ·
          refine ⟨13450443359578660056652427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8966962239719106704434951 13450443359578660056652427)
          ·
            refine ⟨20175665039367990084978641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13450443359578660056652427 20175665039367990084978641)
            ·
              refine ⟨15131748779525992563733981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20175665039367990084978641 15131748779525992563733981)
              ·
                refine ⟨5674405792322247211400243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15131748779525992563733981 5674405792322247211400243)
                ·
                  refine ⟨8511608688483370817100365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5674405792322247211400243 8511608688483370817100365)
                  ·
                    refine ⟨3191853258181264056412637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8511608688483370817100365 3191853258181264056412637)
                    ·
                      refine ⟨1196944971817974021154739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3191853258181264056412637 1196944971817974021154739)
                      ·
                        rfl

theorem cell23_2331042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2331042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331042 prefixEnd_2331042 := by exact prefixLift 2331042
  have htrace : WordTrace (prefixWord ++ tailWord_2331042) baseStart_2331042 baseEnd_2331042 := by
    simpa [prefixWord, tailWord_2331042, baseEnd_2331042] using wordTrace_append hprefix tailTrace_2331042
  have hstable : (prefixWord ++ tailWord_2331042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331042).length < 2 ^ (prefixWord ++ tailWord_2331042).sum := by decide
  have hdescent : baseEnd_2331042 < baseStart_2331042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331082 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2]
def baseStart_2331082 : Nat := 118140960795 + 2331082 * 2 ^ 59
def prefixEnd_2331082 : Nat := 4983230072969 + 3 ^ 40 * 2331082 * 2
def baseEnd_2331082 : Nat := 1196965511044153864654555

theorem tailTrace_2331082 : CollatzResearch.WordTrace tailWord_2331082 prefixEnd_2331082 1196965511044153864654555 := by
  unfold tailWord_2331082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21255386335223876488746875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56681030227263670636658333 21255386335223876488746875)
  ·
    refine ⟨31883079502835814733120313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21255386335223876488746875 31883079502835814733120313)
    ·
      refine ⟨23912309627126861049840235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31883079502835814733120313 23912309627126861049840235)
      ·
        refine ⟨35868464440690291574760353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23912309627126861049840235 35868464440690291574760353)
        ·
          refine ⟨26901348330517718681070265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35868464440690291574760353 26901348330517718681070265)
          ·
            refine ⟨20176011247888289010802699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26901348330517718681070265 20176011247888289010802699)
            ·
              refine ⟨30264016871832433516204049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20176011247888289010802699 30264016871832433516204049)
              ·
                refine ⟨22698012653874325137153037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30264016871832433516204049 22698012653874325137153037)
                ·
                  refine ⟨8511754745202871926432389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22698012653874325137153037 8511754745202871926432389)
                  ·
                    refine ⟨1595954014725538486206073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8511754745202871926432389 1595954014725538486206073)
                    ·
                      refine ⟨1196965511044153864654555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1595954014725538486206073 1196965511044153864654555)
                      ·
                        rfl

theorem cell23_2331082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_2331082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331082 prefixEnd_2331082 := by exact prefixLift 2331082
  have htrace : WordTrace (prefixWord ++ tailWord_2331082) baseStart_2331082 baseEnd_2331082 := by
    simpa [prefixWord, tailWord_2331082, baseEnd_2331082] using wordTrace_append hprefix tailTrace_2331082
  have hstable : (prefixWord ++ tailWord_2331082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331082).length < 2 ^ (prefixWord ++ tailWord_2331082).sum := by decide
  have hdescent : baseEnd_2331082 < baseStart_2331082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331092 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_2331092 : Nat := 118140960795 + 2331092 * 2 ^ 59
def prefixEnd_2331092 : Nat := 4983230072969 + 3 ^ 40 * 2331092 * 2
def baseEnd_2331092 : Nat := 398990215283566275176503

theorem tailTrace_2331092 : CollatzResearch.WordTrace tailWord_2331092 prefixEnd_2331092 398990215283566275176503 := by
  unfold tailWord_2331092
  simp only [CollatzResearch.WordTrace]
  refine ⟨42510955035429638831425765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56681273380572851775234353 42510955035429638831425765)
  ·
    refine ⟨7970804069143057280892331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42510955035429638831425765 7970804069143057280892331)
    ·
      refine ⟨11956206103714585921338497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7970804069143057280892331 11956206103714585921338497)
      ·
        refine ⟨8967154577785939441003873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11956206103714585921338497 8967154577785939441003873)
        ·
          refine ⟨6725365933339454580752905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8967154577785939441003873 6725365933339454580752905)
          ·
            refine ⟨5044024450004590935564679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6725365933339454580752905 5044024450004590935564679)
            ·
              refine ⟨7566036675006886403347019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5044024450004590935564679 7566036675006886403347019)
              ·
                refine ⟨11349055012510329605020529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7566036675006886403347019 11349055012510329605020529)
                ·
                  refine ⟨8511791259382747203765397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11349055012510329605020529 8511791259382747203765397)
                  ·
                    refine ⟨398990215283566275176503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8511791259382747203765397 398990215283566275176503)
                    ·
                      rfl

theorem cell23_2331092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_2331092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331092 prefixEnd_2331092 := by exact prefixLift 2331092
  have htrace : WordTrace (prefixWord ++ tailWord_2331092) baseStart_2331092 baseEnd_2331092 := by
    simpa [prefixWord, tailWord_2331092, baseEnd_2331092] using wordTrace_append hprefix tailTrace_2331092
  have hstable : (prefixWord ++ tailWord_2331092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331092).length < 2 ^ (prefixWord ++ tailWord_2331092).sum := by decide
  have hdescent : baseEnd_2331092 < baseStart_2331092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331105 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 7]
def baseStart_2331105 : Nat := 118140960795 + 2331105 * 2 ^ 59
def prefixEnd_2331105 : Nat := 4983230072969 + 3 ^ 40 * 2331105 * 2
def baseEnd_2331105 : Nat := 132997480122134141629661

theorem tailTrace_2331105 : CollatzResearch.WordTrace tailWord_2331105 prefixEnd_2331105 132997480122134141629661 := by
  unfold tailWord_2331105
  simp only [CollatzResearch.WordTrace]
  refine ⟨85022384219812180883074769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56681589479874787255383179 85022384219812180883074769)
  ·
    refine ⟨63766788164859135662306077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85022384219812180883074769 63766788164859135662306077)
    ·
      refine ⟨23912545561822175873364779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63766788164859135662306077 23912545561822175873364779)
      ·
        refine ⟨35868818342733263810047169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23912545561822175873364779 35868818342733263810047169)
        ·
          refine ⟨26901613757049947857535377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35868818342733263810047169 26901613757049947857535377)
          ·
            refine ⟨20176210317787460893151533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26901613757049947857535377 20176210317787460893151533)
            ·
              refine ⟨7566078869170297834931825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20176210317787460893151533 7566078869170297834931825)
              ·
                refine ⟨5674559151877723376198869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7566078869170297834931825 5674559151877723376198869)
                ·
                  refine ⟨132997480122134141629661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5674559151877723376198869 132997480122134141629661)
                  ·
                    rfl

theorem cell23_2331105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 7].length) (baseStart_2331105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331105 prefixEnd_2331105 := by exact prefixLift 2331105
  have htrace : WordTrace (prefixWord ++ tailWord_2331105) baseStart_2331105 baseEnd_2331105 := by
    simpa [prefixWord, tailWord_2331105, baseEnd_2331105] using wordTrace_append hprefix tailTrace_2331105
  have hstable : (prefixWord ++ tailWord_2331105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331105).length < 2 ^ (prefixWord ++ tailWord_2331105).sum := by decide
  have hdescent : baseEnd_2331105 < baseStart_2331105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331115 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 3]
def baseStart_2331115 : Nat := 118140960795 + 2331115 * 2 ^ 59
def prefixEnd_2331115 : Nat := 4983230072969 + 3 ^ 40 * 2331115 * 2
def baseEnd_2331115 : Nat := 1196982455905752235541903

theorem tailTrace_2331115 : CollatzResearch.WordTrace tailWord_2331115 prefixEnd_2331115 1196982455905752235541903 := by
  unfold tailWord_2331115
  simp only [CollatzResearch.WordTrace]
  refine ⟨85022748949775952590938799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56681832633183968393959199 85022748949775952590938799)
  ·
    refine ⟨127534123424663928886408199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85022748949775952590938799 127534123424663928886408199)
    ·
      refine ⟨191301185136995893329612299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127534123424663928886408199 191301185136995893329612299)
      ·
        refine ⟨286951777705493839994418449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191301185136995893329612299 286951777705493839994418449)
        ·
          refine ⟨215213833279120379995813837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286951777705493839994418449 215213833279120379995813837)
          ·
            refine ⟨80705187479670142498430189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215213833279120379995813837 80705187479670142498430189)
            ·
              refine ⟨30264445304876303436911321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80705187479670142498430189 30264445304876303436911321)
              ·
                refine ⟨22698333978657227577683491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30264445304876303436911321 22698333978657227577683491)
                ·
                  refine ⟨34047500967985841366525237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22698333978657227577683491 34047500967985841366525237)
                  ·
                    refine ⟨3191953215748672628111741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34047500967985841366525237 3191953215748672628111741)
                    ·
                      refine ⟨1196982455905752235541903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3191953215748672628111741 1196982455905752235541903)
                      ·
                        rfl

theorem cell23_2331115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 3].length) (baseStart_2331115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331115 prefixEnd_2331115 := by exact prefixLift 2331115
  have htrace : WordTrace (prefixWord ++ tailWord_2331115) baseStart_2331115 baseEnd_2331115 := by
    simpa [prefixWord, tailWord_2331115, baseEnd_2331115] using wordTrace_append hprefix tailTrace_2331115
  have hstable : (prefixWord ++ tailWord_2331115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331115).length < 2 ^ (prefixWord ++ tailWord_2331115).sum := by decide
  have hdescent : baseEnd_2331115 < baseStart_2331115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331135 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 4, 5]
def baseStart_2331135 : Nat := 118140960795 + 2331135 * 2 ^ 59
def prefixEnd_2331135 : Nat := 4983230072969 + 3 ^ 40 * 2331135 * 2
def baseEnd_2331135 : Nat := 398997575172947385763937

theorem tailTrace_2331135 : CollatzResearch.WordTrace tailWord_2331135 prefixEnd_2331135 398997575172947385763937 := by
  unfold tailWord_2331135
  simp only [CollatzResearch.WordTrace]
  refine ⟨85023478409703496006666859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56682318939802330671111239 85023478409703496006666859)
  ·
    refine ⟨127535217614555244010000289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85023478409703496006666859 127535217614555244010000289)
    ·
      refine ⟨95651413210916433007500217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127535217614555244010000289 95651413210916433007500217)
      ·
        refine ⟨71738559908187324755625163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95651413210916433007500217 71738559908187324755625163)
        ·
          refine ⟨107607839862280987133437745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71738559908187324755625163 107607839862280987133437745)
          ·
            refine ⟨80705879896710740350078309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107607839862280987133437745 80705879896710740350078309)
            ·
              refine ⟨15132352480633263815639683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80705879896710740350078309 15132352480633263815639683)
              ·
                refine ⟨22698528720949895723459525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15132352480633263815639683 22698528720949895723459525)
                ·
                  refine ⟨4255974135178105448148661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22698528720949895723459525 4255974135178105448148661)
                  ·
                    refine ⟨398997575172947385763937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4255974135178105448148661 398997575172947385763937)
                    ·
                      rfl

theorem cell23_2331135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_2331135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331135 prefixEnd_2331135 := by exact prefixLift 2331135
  have htrace : WordTrace (prefixWord ++ tailWord_2331135) baseStart_2331135 baseEnd_2331135 := by
    simpa [prefixWord, tailWord_2331135, baseEnd_2331135] using wordTrace_append hprefix tailTrace_2331135
  have hstable : (prefixWord ++ tailWord_2331135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331135).length < 2 ^ (prefixWord ++ tailWord_2331135).sum := by decide
  have hdescent : baseEnd_2331135 < baseStart_2331135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331155 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 4]
def baseStart_2331155 : Nat := 118140960795 + 2331155 * 2 ^ 59
def prefixEnd_2331155 : Nat := 4983230072969 + 3 ^ 40 * 2331155 * 2
def baseEnd_2331155 : Nat := 1197002995131932079041719

theorem tailTrace_2331155 : CollatzResearch.WordTrace tailWord_2331155 prefixEnd_2331155 1197002995131932079041719 := by
  unfold tailWord_2331155
  simp only [CollatzResearch.WordTrace]
  refine ⟨85024207869631039422394919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56682805246420692948263279 85024207869631039422394919)
  ·
    refine ⟨127536311804446559133592379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85024207869631039422394919 127536311804446559133592379)
    ·
      refine ⟨191304467706669838700388569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127536311804446559133592379 191304467706669838700388569)
      ·
        refine ⟨143478350780002379025291427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191304467706669838700388569 143478350780002379025291427)
        ·
          refine ⟨215217526170003568537937141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143478350780002379025291427 215217526170003568537937141)
          ·
            refine ⟨20176643078437834550431607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 215217526170003568537937141 20176643078437834550431607)
            ·
              refine ⟨30264964617656751825647411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20176643078437834550431607 30264964617656751825647411)
              ·
                refine ⟨45397446926485127738471117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30264964617656751825647411 45397446926485127738471117)
                ·
                  refine ⟨17024042597431922901926669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45397446926485127738471117 17024042597431922901926669)
                  ·
                    refine ⟨6384015974036971088222501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17024042597431922901926669 6384015974036971088222501)
                    ·
                      refine ⟨1197002995131932079041719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6384015974036971088222501 1197002995131932079041719)
                      ·
                        rfl

theorem cell23_2331155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_2331155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331155 prefixEnd_2331155 := by exact prefixLift 2331155
  have htrace : WordTrace (prefixWord ++ tailWord_2331155) baseStart_2331155 baseEnd_2331155 := by
    simpa [prefixWord, tailWord_2331155, baseEnd_2331155] using wordTrace_append hprefix tailTrace_2331155
  have hstable : (prefixWord ++ tailWord_2331155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331155).length < 2 ^ (prefixWord ++ tailWord_2331155).sum := by decide
  have hdescent : baseEnd_2331155 < baseStart_2331155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331185 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2331185 : Nat := 118140960795 + 2331185 * 2 ^ 59
def prefixEnd_2331185 : Nat := 4983230072969 + 3 ^ 40 * 2331185 * 2
def baseEnd_2331185 : Nat := 1197018399551566961666581

theorem tailTrace_2331185 : CollatzResearch.WordTrace tailWord_2331185 prefixEnd_2331185 1197018399551566961666581 := by
  unfold tailWord_2331185
  simp only [CollatzResearch.WordTrace]
  refine ⟨85025302059522354545987009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56683534706348236363991339 85025302059522354545987009)
  ·
    refine ⟨63768976544641765909490257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85025302059522354545987009 63768976544641765909490257)
    ·
      refine ⟨47826732408481324432117693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63768976544641765909490257 47826732408481324432117693)
      ·
        refine ⟨17935024653180496662044135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47826732408481324432117693 17935024653180496662044135)
        ·
          refine ⟨26902536979770744993066203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17935024653180496662044135 26902536979770744993066203)
          ·
            refine ⟨40353805469656117489599305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26902536979770744993066203 40353805469656117489599305)
            ·
              refine ⟨30265354102242088117199479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40353805469656117489599305 30265354102242088117199479)
              ·
                refine ⟨45398031153363132175799219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30265354102242088117199479 45398031153363132175799219)
                ·
                  refine ⟨68097046730044698263698829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45398031153363132175799219 68097046730044698263698829)
                  ·
                    refine ⟨25536392523766761848887061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68097046730044698263698829 25536392523766761848887061)
                    ·
                      refine ⟨1197018399551566961666581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25536392523766761848887061 1197018399551566961666581)
                      ·
                        rfl

theorem cell23_2331185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2331185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331185 prefixEnd_2331185 := by exact prefixLift 2331185
  have htrace : WordTrace (prefixWord ++ tailWord_2331185) baseStart_2331185 baseEnd_2331185 := by
    simpa [prefixWord, tailWord_2331185, baseEnd_2331185] using wordTrace_append hprefix tailTrace_2331185
  have hstable : (prefixWord ++ tailWord_2331185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331185).length < 2 ^ (prefixWord ++ tailWord_2331185).sum := by decide
  have hdescent : baseEnd_2331185 < baseStart_2331185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331212 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 6]
def baseStart_2331212 : Nat := 118140960795 + 2331212 * 2 ^ 59
def prefixEnd_2331212 : Nat := 4983230072969 + 3 ^ 40 * 2331212 * 2
def baseEnd_2331212 : Nat := 133003584836582039558773

theorem tailTrace_2331212 : CollatzResearch.WordTrace tailWord_2331212 prefixEnd_2331212 133003584836582039558773 := by
  unfold tailWord_2331212
  simp only [CollatzResearch.WordTrace]
  refine ⟨42513143415212269078609945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56684191220283025438146593 42513143415212269078609945)
  ·
    refine ⟨31884857561409201808957459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42513143415212269078609945 31884857561409201808957459)
    ·
      refine ⟨47827286342113802713436189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31884857561409201808957459 47827286342113802713436189)
      ·
        refine ⟨17935232378292676017538571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47827286342113802713436189 17935232378292676017538571)
        ·
          refine ⟨26902848567439014026307857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17935232378292676017538571 26902848567439014026307857)
          ·
            refine ⟨20177136425579260519730893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26902848567439014026307857 20177136425579260519730893)
            ·
              refine ⟨7566426159592222694899085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20177136425579260519730893 7566426159592222694899085)
              ·
                refine ⟨2837409809847083510587157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7566426159592222694899085 2837409809847083510587157)
                ·
                  refine ⟨133003584836582039558773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2837409809847083510587157 133003584836582039558773)
                  ·
                    rfl

theorem cell23_2331212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_2331212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331212 prefixEnd_2331212 := by exact prefixLift 2331212
  have htrace : WordTrace (prefixWord ++ tailWord_2331212) baseStart_2331212 baseEnd_2331212 := by
    simpa [prefixWord, tailWord_2331212, baseEnd_2331212] using wordTrace_append hprefix tailTrace_2331212
  have hstable : (prefixWord ++ tailWord_2331212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331212).length < 2 ^ (prefixWord ++ tailWord_2331212).sum := by decide
  have hdescent : baseEnd_2331212 < baseStart_2331212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331215 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_2331215 : Nat := 118140960795 + 2331215 * 2 ^ 59
def prefixEnd_2331215 : Nat := 4983230072969 + 3 ^ 40 * 2331215 * 2
def baseEnd_2331215 : Nat := 1197033803971201844291443

theorem tailTrace_2331215 : CollatzResearch.WordTrace tailWord_2331215 prefixEnd_2331215 1197033803971201844291443 := by
  unfold tailWord_2331215
  simp only [CollatzResearch.WordTrace]
  refine ⟨85026396249413669669579099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56684264166275779779719399 85026396249413669669579099)
  ·
    refine ⟨127539594374120504504368649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85026396249413669669579099 127539594374120504504368649)
    ·
      refine ⟨95654695780590378378276487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127539594374120504504368649 95654695780590378378276487)
      ·
        refine ⟨143482043670885567567414731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95654695780590378378276487 143482043670885567567414731)
        ·
          refine ⟨215223065506328351351122097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143482043670885567567414731 215223065506328351351122097)
          ·
            refine ⟨161417299129746263513341573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215223065506328351351122097 161417299129746263513341573)
            ·
              refine ⟨30265743586827424408751545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161417299129746263513341573 30265743586827424408751545)
              ·
                refine ⟨22699307690120568306563659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30265743586827424408751545 22699307690120568306563659)
                ·
                  refine ⟨34048961535180852459845489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22699307690120568306563659 34048961535180852459845489)
                  ·
                    refine ⟨25536721151385639344884117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34048961535180852459845489 25536721151385639344884117)
                    ·
                      refine ⟨1197033803971201844291443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25536721151385639344884117 1197033803971201844291443)
                      ·
                        rfl

theorem cell23_2331215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_2331215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331215 prefixEnd_2331215 := by exact prefixLift 2331215
  have htrace : WordTrace (prefixWord ++ tailWord_2331215) baseStart_2331215 baseEnd_2331215 := by
    simpa [prefixWord, tailWord_2331215, baseEnd_2331215] using wordTrace_append hprefix tailTrace_2331215
  have hstable : (prefixWord ++ tailWord_2331215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331215).length < 2 ^ (prefixWord ++ tailWord_2331215).sum := by decide
  have hdescent : baseEnd_2331215 < baseStart_2331215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331250 : List Nat := [3, 2, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_2331250 : Nat := 118140960795 + 2331250 * 2 ^ 59
def prefixEnd_2331250 : Nat := 4983230072969 + 3 ^ 40 * 2331250 * 2
def baseEnd_2331250 : Nat := 399017258598036402451261

theorem tailTrace_2331250 : CollatzResearch.WordTrace tailWord_2331250 prefixEnd_2331250 399017258598036402451261 := by
  unfold tailWord_2331250
  simp only [CollatzResearch.WordTrace]
  refine ⟨21256918201071717661775801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56685115202857913764735469 21256918201071717661775801)
  ·
    refine ⟨15942688650803788246331851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21256918201071717661775801 15942688650803788246331851)
    ·
      refine ⟨23914032976205682369497777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15942688650803788246331851 23914032976205682369497777)
      ·
        refine ⟨17935524732154261777123333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23914032976205682369497777 17935524732154261777123333)
        ·
          refine ⟨3362910887278924083210625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17935524732154261777123333 3362910887278924083210625)
          ·
            refine ⟨2522183165459193062407969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3362910887278924083210625 2522183165459193062407969)
            ·
              refine ⟨1891637374094394796805977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2522183165459193062407969 1891637374094394796805977)
              ·
                refine ⟨1418728030570796097604483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1891637374094394796805977 1418728030570796097604483)
                ·
                  refine ⟨2128092045856194146406725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418728030570796097604483 2128092045856194146406725)
                  ·
                    refine ⟨399017258598036402451261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2128092045856194146406725 399017258598036402451261)
                    ·
                      rfl

theorem cell23_2331250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_2331250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331250 prefixEnd_2331250 := by exact prefixLift 2331250
  have htrace : WordTrace (prefixWord ++ tailWord_2331250) baseStart_2331250 baseEnd_2331250 := by
    simpa [prefixWord, tailWord_2331250, baseEnd_2331250] using wordTrace_append hprefix tailTrace_2331250
  have hstable : (prefixWord ++ tailWord_2331250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331250).length < 2 ^ (prefixWord ++ tailWord_2331250).sum := by decide
  have hdescent : baseEnd_2331250 < baseStart_2331250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331256 : List Nat := [2, 1, 2, 1, 1, 1, 2, 8, 1, 1, 3]
def baseStart_2331256 : Nat := 118140960795 + 2331256 * 2 ^ 59
def prefixEnd_2331256 : Nat := 4983230072969 + 3 ^ 40 * 2331256 * 2
def baseEnd_2331256 : Nat := 1197054856678036183878755

theorem tailTrace_2331256 : CollatzResearch.WordTrace tailWord_2331256 prefixEnd_2331256 1197054856678036183878755 := by
  unfold tailWord_2331256
  simp only [CollatzResearch.WordTrace]
  refine ⟨42513945821132566835910811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56685261094843422447881081 42513945821132566835910811)
  ·
    refine ⟨63770918731698850253866217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42513945821132566835910811 63770918731698850253866217)
    ·
      refine ⟨47828189048774137690399663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63770918731698850253866217 47828189048774137690399663)
      ·
        refine ⟨71742283573161206535599495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47828189048774137690399663 71742283573161206535599495)
        ·
          refine ⟨107613425359741809803399243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71742283573161206535599495 107613425359741809803399243)
          ·
            refine ⟨161420138039612714705098865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107613425359741809803399243 161420138039612714705098865)
            ·
              refine ⟨121065103529709536028824149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161420138039612714705098865 121065103529709536028824149)
              ·
                refine ⟨1418731681988783625337783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 121065103529709536028824149 1418731681988783625337783)
                ·
                  refine ⟨2128097522983175438006675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1418731681988783625337783 2128097522983175438006675)
                  ·
                    refine ⟨3192146284474763157010013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2128097522983175438006675 3192146284474763157010013)
                    ·
                      refine ⟨1197054856678036183878755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3192146284474763157010013 1197054856678036183878755)
                      ·
                        rfl

theorem cell23_2331256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 1, 1, 3].length) (baseStart_2331256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331256 prefixEnd_2331256 := by exact prefixLift 2331256
  have htrace : WordTrace (prefixWord ++ tailWord_2331256) baseStart_2331256 baseEnd_2331256 := by
    simpa [prefixWord, tailWord_2331256, baseEnd_2331256] using wordTrace_append hprefix tailTrace_2331256
  have hstable : (prefixWord ++ tailWord_2331256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331256).length < 2 ^ (prefixWord ++ tailWord_2331256).sum := by decide
  have hdescent : baseEnd_2331256 < baseStart_2331256 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331296 : List Nat := [2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 4]
def baseStart_2331296 : Nat := 118140960795 + 2331296 * 2 ^ 59
def prefixEnd_2331296 : Nat := 4983230072969 + 3 ^ 40 * 2331296 * 2
def baseEnd_2331296 : Nat := 1197075395904216027378571

theorem tailTrace_2331296 : CollatzResearch.WordTrace tailWord_2331296 prefixEnd_2331296 1197075395904216027378571 := by
  unfold tailWord_2331296
  simp only [CollatzResearch.WordTrace]
  refine ⟨42514675281060110251638871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56686233708080147002185161 42514675281060110251638871)
  ·
    refine ⟨63772012921590165377458307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42514675281060110251638871 63772012921590165377458307)
    ·
      refine ⟨95658019382385248066187461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63772012921590165377458307 95658019382385248066187461)
      ·
        refine ⟨17935878634197234012410149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95658019382385248066187461 17935878634197234012410149)
        ·
          refine ⟨3362977243911981377326903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17935878634197234012410149 3362977243911981377326903)
          ·
            refine ⟨5044465865867972065990355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3362977243911981377326903 5044465865867972065990355)
            ·
              refine ⟨7566698798801958098985533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5044465865867972065990355 7566698798801958098985533)
              ·
                refine ⟨2837512049550734287119575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7566698798801958098985533 2837512049550734287119575)
                ·
                  refine ⟨4256268074326101430679363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837512049550734287119575 4256268074326101430679363)
                  ·
                    refine ⟨6384402111489152146019045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4256268074326101430679363 6384402111489152146019045)
                    ·
                      refine ⟨1197075395904216027378571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6384402111489152146019045 1197075395904216027378571)
                      ·
                        rfl

theorem cell23_2331296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_2331296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331296 prefixEnd_2331296 := by exact prefixLift 2331296
  have htrace : WordTrace (prefixWord ++ tailWord_2331296) baseStart_2331296 baseEnd_2331296 := by
    simpa [prefixWord, tailWord_2331296, baseEnd_2331296] using wordTrace_append hprefix tailTrace_2331296
  have hstable : (prefixWord ++ tailWord_2331296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331296).length < 2 ^ (prefixWord ++ tailWord_2331296).sum := by decide
  have hdescent : baseEnd_2331296 < baseStart_2331296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331372 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 5]
def baseStart_2331372 : Nat := 118140960795 + 2331372 * 2 ^ 59
def prefixEnd_2331372 : Nat := 4983230072969 + 3 ^ 40 * 2331372 * 2
def baseEnd_2331372 : Nat := 1197114420433957730028221

theorem tailTrace_2331372 : CollatzResearch.WordTrace tailWord_2331372 prefixEnd_2331372 1197114420433957730028221 := by
  unfold tailWord_2331372
  simp only [CollatzResearch.WordTrace]
  refine ⟨42516061254922442741522185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56688081673229923655362913 42516061254922442741522185)
  ·
    refine ⟨31887045941191832056141639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42516061254922442741522185 31887045941191832056141639)
    ·
      refine ⟨47830568911787748084212459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31887045941191832056141639 47830568911787748084212459)
      ·
        refine ⟨71745853367681622126318689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47830568911787748084212459 71745853367681622126318689)
        ·
          refine ⟨53809390025761216594739017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71745853367681622126318689 53809390025761216594739017)
          ·
            refine ⟨40357042519320912446054263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53809390025761216594739017 40357042519320912446054263)
            ·
              refine ⟨60535563778981368669081395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40357042519320912446054263 60535563778981368669081395)
              ·
                refine ⟨90803345668472053003622093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60535563778981368669081395 90803345668472053003622093)
                ·
                  refine ⟨34051254625677019876358285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90803345668472053003622093 34051254625677019876358285)
                  ·
                    refine ⟨12769220484628882453634357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34051254625677019876358285 12769220484628882453634357)
                    ·
                      refine ⟨1197114420433957730028221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12769220484628882453634357 1197114420433957730028221)
                      ·
                        rfl

theorem cell23_2331372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_2331372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331372 prefixEnd_2331372 := by exact prefixLift 2331372
  have htrace : WordTrace (prefixWord ++ tailWord_2331372) baseStart_2331372 baseEnd_2331372 := by
    simpa [prefixWord, tailWord_2331372, baseEnd_2331372] using wordTrace_append hprefix tailTrace_2331372
  have hstable : (prefixWord ++ tailWord_2331372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331372).length < 2 ^ (prefixWord ++ tailWord_2331372).sum := by decide
  have hdescent : baseEnd_2331372 < baseStart_2331372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331390 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 1, 3, 2]
def baseStart_2331390 : Nat := 118140960795 + 2331390 * 2 ^ 59
def prefixEnd_2331390 : Nat := 4983230072969 + 3 ^ 40 * 2331390 * 2
def baseEnd_2331390 : Nat := 1197123663085738659603139

theorem tailTrace_2331390 : CollatzResearch.WordTrace tailWord_2331390 prefixEnd_2331390 1197123663085738659603139 := by
  unfold tailWord_2331390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10629097377972459319649953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56688519349186449704799749 10629097377972459319649953)
  ·
    refine ⟨7971823033479344489737465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10629097377972459319649953 7971823033479344489737465)
    ·
      refine ⟨5978867275109508367303099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7971823033479344489737465 5978867275109508367303099)
      ·
        refine ⟨8968300912664262550954649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5978867275109508367303099 8968300912664262550954649)
        ·
          refine ⟨6726225684498196913215987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8968300912664262550954649 6726225684498196913215987)
          ·
            refine ⟨10089338526747295369823981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6726225684498196913215987 10089338526747295369823981)
            ·
              refine ⟨3783501947530235763683993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10089338526747295369823981 3783501947530235763683993)
              ·
                refine ⟨2837626460647676822762995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3783501947530235763683993 2837626460647676822762995)
                ·
                  refine ⟨4256439690971515234144493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837626460647676822762995 4256439690971515234144493)
                  ·
                    refine ⟨1596164884114318212804185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4256439690971515234144493 1596164884114318212804185)
                    ·
                      refine ⟨1197123663085738659603139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596164884114318212804185 1197123663085738659603139)
                      ·
                        rfl

theorem cell23_2331390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_2331390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331390 prefixEnd_2331390 := by exact prefixLift 2331390
  have htrace : WordTrace (prefixWord ++ tailWord_2331390) baseStart_2331390 baseEnd_2331390 := by
    simpa [prefixWord, tailWord_2331390, baseEnd_2331390] using wordTrace_append hprefix tailTrace_2331390
  have hstable : (prefixWord ++ tailWord_2331390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331390).length < 2 ^ (prefixWord ++ tailWord_2331390).sum := by decide
  have hdescent : baseEnd_2331390 < baseStart_2331390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331420 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_2331420 : Nat := 118140960795 + 2331420 * 2 ^ 59
def prefixEnd_2331420 : Nat := 4983230072969 + 3 ^ 40 * 2331420 * 2
def baseEnd_2331420 : Nat := 1197139067505373542228001

theorem tailTrace_2331420 : CollatzResearch.WordTrace tailWord_2331420 prefixEnd_2331420 1197139067505373542228001 := by
  unfold tailWord_2331420
  simp only [CollatzResearch.WordTrace]
  refine ⟨42516936606835494840395857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56689248809113993120527809 42516936606835494840395857)
  ·
    refine ⟨31887702455126621130296893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42516936606835494840395857 31887702455126621130296893)
    ·
      refine ⟨11957888420672482923861335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31887702455126621130296893 11957888420672482923861335)
      ·
        refine ⟨17936832631008724385792003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11957888420672482923861335 17936832631008724385792003)
        ·
          refine ⟨26905248946513086578688005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17936832631008724385792003 26905248946513086578688005)
          ·
            refine ⟨5044734177471203733504001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26905248946513086578688005 5044734177471203733504001)
            ·
              refine ⟨3783550633103402800128001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5044734177471203733504001 3783550633103402800128001)
              ·
                refine ⟨2837662974827552100096001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3783550633103402800128001 2837662974827552100096001)
                ·
                  refine ⟨2128247231120664075072001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2837662974827552100096001 2128247231120664075072001)
                  ·
                    refine ⟨1596185423340498056304001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2128247231120664075072001 1596185423340498056304001)
                    ·
                      refine ⟨1197139067505373542228001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596185423340498056304001 1197139067505373542228001)
                      ·
                        rfl

theorem cell23_2331420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_2331420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331420 prefixEnd_2331420 := by exact prefixLift 2331420
  have htrace : WordTrace (prefixWord ++ tailWord_2331420) baseStart_2331420 baseEnd_2331420 := by
    simpa [prefixWord, tailWord_2331420, baseEnd_2331420] using wordTrace_append hprefix tailTrace_2331420
  have hstable : (prefixWord ++ tailWord_2331420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331420).length < 2 ^ (prefixWord ++ tailWord_2331420).sum := by decide
  have hdescent : baseEnd_2331420 < baseStart_2331420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331437 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2331437 : Nat := 118140960795 + 2331437 * 2 ^ 59
def prefixEnd_2331437 : Nat := 4983230072969 + 3 ^ 40 * 2331437 * 2
def baseEnd_2331437 : Nat := 1197147796676499975715423

theorem tailTrace_2331437 : CollatzResearch.WordTrace tailWord_2331437 prefixEnd_2331437 1197147796676499975715423 := by
  unfold tailWord_2331437
  simp only [CollatzResearch.WordTrace]
  refine ⟨85034493254609401584160565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56689662169739601056107043 85034493254609401584160565)
  ·
    refine ⟨7971983742619631398515053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85034493254609401584160565 7971983742619631398515053)
    ·
      refine ⟨2989493903482361774443145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7971983742619631398515053 2989493903482361774443145)
      ·
        refine ⟨2242120427611771330832359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2989493903482361774443145 2242120427611771330832359)
        ·
          refine ⟨3363180641417656996248539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242120427611771330832359 3363180641417656996248539)
          ·
            refine ⟨5044770962126485494372809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363180641417656996248539 5044770962126485494372809)
            ·
              refine ⟨3783578221594864120779607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5044770962126485494372809 3783578221594864120779607)
              ·
                refine ⟨5675367332392296181169411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3783578221594864120779607 5675367332392296181169411)
                ·
                  refine ⟨8513050998588444271754117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5675367332392296181169411 8513050998588444271754117)
                  ·
                    refine ⟨1596197062235333300953897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8513050998588444271754117 1596197062235333300953897)
                    ·
                      refine ⟨1197147796676499975715423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596197062235333300953897 1197147796676499975715423)
                      ·
                        rfl

theorem cell23_2331437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2331437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331437 prefixEnd_2331437 := by exact prefixLift 2331437
  have htrace : WordTrace (prefixWord ++ tailWord_2331437) baseStart_2331437 baseEnd_2331437 := by
    simpa [prefixWord, tailWord_2331437, baseEnd_2331437] using wordTrace_append hprefix tailTrace_2331437
  have hstable : (prefixWord ++ tailWord_2331437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331437).length < 2 ^ (prefixWord ++ tailWord_2331437).sum := by decide
  have hdescent : baseEnd_2331437 < baseStart_2331437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331459 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 4]
def baseStart_2331459 : Nat := 118140960795 + 2331459 * 2 ^ 59
def prefixEnd_2331459 : Nat := 4983230072969 + 3 ^ 40 * 2331459 * 2
def baseEnd_2331459 : Nat := 1197159093250898889640321

theorem tailTrace_2331459 : CollatzResearch.WordTrace tailWord_2331459 prefixEnd_2331459 1197159093250898889640321 := by
  unfold tailWord_2331459
  simp only [CollatzResearch.WordTrace]
  refine ⟨85035295660529699341461431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56690197107019799560974287 85035295660529699341461431)
  ·
    refine ⟨127552943490794549012192147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85035295660529699341461431 127552943490794549012192147)
    ·
      refine ⟨191329415236191823518288221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127552943490794549012192147 191329415236191823518288221)
      ·
        refine ⟨71748530713571933819358083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191329415236191823518288221 71748530713571933819358083)
        ·
          refine ⟨107622796070357900729037125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71748530713571933819358083 107622796070357900729037125)
          ·
            refine ⟨20179274263192106386694461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107622796070357900729037125 20179274263192106386694461)
            ·
              refine ⟨7567227848697039895010423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20179274263192106386694461 7567227848697039895010423)
              ·
                refine ⟨11350841773045559842515635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7567227848697039895010423 11350841773045559842515635)
                ·
                  refine ⟨17026262659568339763773453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11350841773045559842515635 17026262659568339763773453)
                  ·
                    refine ⟨6384848497338127411415045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17026262659568339763773453 6384848497338127411415045)
                    ·
                      refine ⟨1197159093250898889640321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6384848497338127411415045 1197159093250898889640321)
                      ·
                        rfl

theorem cell23_2331459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_2331459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331459 prefixEnd_2331459 := by exact prefixLift 2331459
  have htrace : WordTrace (prefixWord ++ tailWord_2331459) baseStart_2331459 baseEnd_2331459 := by
    simpa [prefixWord, tailWord_2331459, baseEnd_2331459] using wordTrace_append hprefix tailTrace_2331459
  have hstable : (prefixWord ++ tailWord_2331459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331459).length < 2 ^ (prefixWord ++ tailWord_2331459).sum := by decide
  have hdescent : baseEnd_2331459 < baseStart_2331459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331496 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_2331496 : Nat := 118140960795 + 2331496 * 2 ^ 59
def prefixEnd_2331496 : Nat := 4983230072969 + 3 ^ 40 * 2331496 * 2
def baseEnd_2331496 : Nat := 1197178092035115244877651

theorem tailTrace_2331496 : CollatzResearch.WordTrace tailWord_2331496 prefixEnd_2331496 1197178092035115244877651 := by
  unfold tailWord_2331496
  simp only [CollatzResearch.WordTrace]
  refine ⟨42518322580697827330279171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56691096774263769773705561 42518322580697827330279171)
  ·
    refine ⟨63777483871046740995418757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42518322580697827330279171 63777483871046740995418757)
    ·
      refine ⟨11958278225821263936641017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63777483871046740995418757 11958278225821263936641017)
      ·
        refine ⟨8968708669365947952480763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11958278225821263936641017 8968708669365947952480763)
        ·
          refine ⟨13453063004048921928721145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8968708669365947952480763 13453063004048921928721145)
          ·
            refine ⟨10089797253036691446540859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13453063004048921928721145 10089797253036691446540859)
            ·
              refine ⟨15134695879555037169811289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10089797253036691446540859 15134695879555037169811289)
              ·
                refine ⟨11351021909666277877358467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15134695879555037169811289 11351021909666277877358467)
                ·
                  refine ⟨17026532864499416816037701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11351021909666277877358467 17026532864499416816037701)
                  ·
                    refine ⟨3192474912093640653007069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17026532864499416816037701 3192474912093640653007069)
                    ·
                      refine ⟨1197178092035115244877651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3192474912093640653007069 1197178092035115244877651)
                      ·
                        rfl

theorem cell23_2331496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_2331496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331496 prefixEnd_2331496 := by exact prefixLift 2331496
  have htrace : WordTrace (prefixWord ++ tailWord_2331496) baseStart_2331496 baseEnd_2331496 := by
    simpa [prefixWord, tailWord_2331496, baseEnd_2331496] using wordTrace_append hprefix tailTrace_2331496
  have hstable : (prefixWord ++ tailWord_2331496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331496).length < 2 ^ (prefixWord ++ tailWord_2331496).sum := by decide
  have hdescent : baseEnd_2331496 < baseStart_2331496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331499 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 6]
def baseStart_2331499 : Nat := 118140960795 + 2331499 * 2 ^ 59
def prefixEnd_2331499 : Nat := 4983230072969 + 3 ^ 40 * 2331499 * 2
def baseEnd_2331499 : Nat := 133019959164119859237793

theorem tailTrace_2331499 : CollatzResearch.WordTrace tailWord_2331499 prefixEnd_2331499 133019959164119859237793 := by
  unfold tailWord_2331499
  simp only [CollatzResearch.WordTrace]
  refine ⟨85036754580384786172917551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56691169720256524115278367 85036754580384786172917551)
  ·
    refine ⟨127555131870577179259376327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85036754580384786172917551 127555131870577179259376327)
    ·
      refine ⟨191332697805865768889064491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127555131870577179259376327 191332697805865768889064491)
      ·
        refine ⟨286999046708798653333596737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191332697805865768889064491 286999046708798653333596737)
        ·
          refine ⟨215249285031598990000197553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 286999046708798653333596737 215249285031598990000197553)
          ·
            refine ⟨161436963773699242500148165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215249285031598990000197553 161436963773699242500148165)
            ·
              refine ⟨30269430707568607968777781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161436963773699242500148165 30269430707568607968777781)
              ·
                refine ⟨2837759128834556997072917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30269430707568607968777781 2837759128834556997072917)
                ·
                  refine ⟨133019959164119859237793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2837759128834556997072917 133019959164119859237793)
                  ·
                    rfl

theorem cell23_2331499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 6].length) (baseStart_2331499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331499 prefixEnd_2331499 := by exact prefixLift 2331499
  have htrace : WordTrace (prefixWord ++ tailWord_2331499) baseStart_2331499 baseEnd_2331499 := by
    simpa [prefixWord, tailWord_2331499, baseEnd_2331499] using wordTrace_append hprefix tailTrace_2331499
  have hstable : (prefixWord ++ tailWord_2331499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331499).length < 2 ^ (prefixWord ++ tailWord_2331499).sum := by decide
  have hdescent : baseEnd_2331499 < baseStart_2331499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331576 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 1, 6]
def baseStart_2331576 : Nat := 118140960795 + 2331576 * 2 ^ 59
def prefixEnd_2331576 : Nat := 4983230072969 + 3 ^ 40 * 2331576 * 2
def baseEnd_2331576 : Nat := 399073056829158310625761

theorem tailTrace_2331576 : CollatzResearch.WordTrace tailWord_2331576 prefixEnd_2331576 399073056829158310625761 := by
  unfold tailWord_2331576
  simp only [CollatzResearch.WordTrace]
  refine ⟨42519781500552914161735291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56693042000737218882313721 42519781500552914161735291)
  ·
    refine ⟨63779672250829371242602937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42519781500552914161735291 63779672250829371242602937)
    ·
      refine ⟨47834754188122028431952203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63779672250829371242602937 47834754188122028431952203)
      ·
        refine ⟨71752131282183042647928305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47834754188122028431952203 71752131282183042647928305)
        ·
          refine ⟨53814098461637281985946229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71752131282183042647928305 53814098461637281985946229)
          ·
            refine ⟨5045071730778495186182459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53814098461637281985946229 5045071730778495186182459)
            ·
              refine ⟨7567607596167742779273689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045071730778495186182459 7567607596167742779273689)
              ·
                refine ⟨5675705697125807084455267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7567607596167742779273689 5675705697125807084455267)
                ·
                  refine ⟨8513558545688710626682901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5675705697125807084455267 8513558545688710626682901)
                  ·
                    refine ⟨399073056829158310625761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8513558545688710626682901 399073056829158310625761)
                    ·
                      rfl

theorem cell23_2331576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_2331576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331576 prefixEnd_2331576 := by exact prefixLift 2331576
  have htrace : WordTrace (prefixWord ++ tailWord_2331576) baseStart_2331576 baseEnd_2331576 := by
    simpa [prefixWord, tailWord_2331576, baseEnd_2331576] using wordTrace_append hprefix tailTrace_2331576
  have hstable : (prefixWord ++ tailWord_2331576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331576).length < 2 ^ (prefixWord ++ tailWord_2331576).sum := by decide
  have hdescent : baseEnd_2331576 < baseStart_2331576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331579 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 4]
def baseStart_2331579 : Nat := 118140960795 + 2331579 * 2 ^ 59
def prefixEnd_2331579 : Nat := 4983230072969 + 3 ^ 40 * 2331579 * 2
def baseEnd_2331579 : Nat := 1197220710929438420139769

theorem tailTrace_2331579 : CollatzResearch.WordTrace tailWord_2331579 prefixEnd_2331579 1197220710929438420139769 := by
  unfold tailWord_2331579
  simp only [CollatzResearch.WordTrace]
  refine ⟨85039672420094959835829791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56693114946729973223886527 85039672420094959835829791)
  ·
    refine ⟨127559508630142439753744687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85039672420094959835829791 127559508630142439753744687)
    ·
      refine ⟨191339262945213659630617031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127559508630142439753744687 191339262945213659630617031)
      ·
        refine ⟨287008894417820489445925547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191339262945213659630617031 287008894417820489445925547)
        ·
          refine ⟨430513341626730734168888321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287008894417820489445925547 430513341626730734168888321)
          ·
            refine ⟨322885006220048050626666241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430513341626730734168888321 322885006220048050626666241)
            ·
              refine ⟨242163754665036037969999681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322885006220048050626666241 242163754665036037969999681)
              ·
                refine ⟨181622815998777028477499761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242163754665036037969999681 181622815998777028477499761)
                ·
                  refine ⟨136217111999082771358124821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 181622815998777028477499761 136217111999082771358124821)
                  ·
                    refine ⟨6385177124957004907412101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 136217111999082771358124821 6385177124957004907412101)
                    ·
                      refine ⟨1197220710929438420139769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6385177124957004907412101 1197220710929438420139769)
                      ·
                        rfl

theorem cell23_2331579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 4].length) (baseStart_2331579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331579 prefixEnd_2331579 := by exact prefixLift 2331579
  have htrace : WordTrace (prefixWord ++ tailWord_2331579) baseStart_2331579 baseEnd_2331579 := by
    simpa [prefixWord, tailWord_2331579, baseEnd_2331579] using wordTrace_append hprefix tailTrace_2331579
  have hstable : (prefixWord ++ tailWord_2331579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331579).length < 2 ^ (prefixWord ++ tailWord_2331579).sum := by decide
  have hdescent : baseEnd_2331579 < baseStart_2331579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331583 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 7, 2, 2]
def baseStart_2331583 : Nat := 118140960795 + 2331583 * 2 ^ 59
def prefixEnd_2331583 : Nat := 4983230072969 + 3 ^ 40 * 2331583 * 2
def baseEnd_2331583 : Nat := 1197222764852056404489751

theorem tailTrace_2331583 : CollatzResearch.WordTrace tailWord_2331583 prefixEnd_2331583 1197222764852056404489751 := by
  unfold tailWord_2331583
  simp only [CollatzResearch.WordTrace]
  refine ⟨85039818312080468518975403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56693212208053645679316935 85039818312080468518975403)
  ·
    refine ⟨127559727468120702778463105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85039818312080468518975403 127559727468120702778463105)
    ·
      refine ⟨95669795601090527083847329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127559727468120702778463105 95669795601090527083847329)
      ·
        refine ⟨71752346700817895312885497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95669795601090527083847329 71752346700817895312885497)
        ·
          refine ⟨53814260025613421484664123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71752346700817895312885497 53814260025613421484664123)
          ·
            refine ⟨80721390038420132226996185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53814260025613421484664123 80721390038420132226996185)
            ·
              refine ⟨60541042528815099170247139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80721390038420132226996185 60541042528815099170247139)
              ·
                refine ⟨90811563793222648755370709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60541042528815099170247139 90811563793222648755370709)
                ·
                  refine ⟨2128396026403655830204001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 90811563793222648755370709 2128396026403655830204001)
                  ·
                    refine ⟨1596297019802741872653001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2128396026403655830204001 1596297019802741872653001)
                    ·
                      refine ⟨1197222764852056404489751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596297019802741872653001 1197222764852056404489751)
                      ·
                        rfl

theorem cell23_2331583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 2, 2].length) (baseStart_2331583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331583 prefixEnd_2331583 := by exact prefixLift 2331583
  have htrace : WordTrace (prefixWord ++ tailWord_2331583) baseStart_2331583 baseEnd_2331583 := by
    simpa [prefixWord, tailWord_2331583, baseEnd_2331583] using wordTrace_append hprefix tailTrace_2331583
  have hstable : (prefixWord ++ tailWord_2331583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331583).length < 2 ^ (prefixWord ++ tailWord_2331583).sum := by decide
  have hdescent : baseEnd_2331583 < baseStart_2331583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331596 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2331596 : Nat := 118140960795 + 2331596 * 2 ^ 59
def prefixEnd_2331596 : Nat := 4983230072969 + 3 ^ 40 * 2331596 * 2
def baseEnd_2331596 : Nat := 1197229440100564853627191

theorem tailTrace_2331596 : CollatzResearch.WordTrace tailWord_2331596 prefixEnd_2331596 1197229440100564853627191 := by
  unfold tailWord_2331596
  simp only [CollatzResearch.WordTrace]
  refine ⟨42520146230516685869599321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56693528307355581159465761 42520146230516685869599321)
  ·
    refine ⟨31890109672887514402199491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42520146230516685869599321 31890109672887514402199491)
    ·
      refine ⟨47835164509331271603299237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31890109672887514402199491 47835164509331271603299237)
      ·
        refine ⟨8969093345499613425618607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47835164509331271603299237 8969093345499613425618607)
        ·
          refine ⟨13453640018249420138427911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8969093345499613425618607 13453640018249420138427911)
          ·
            refine ⟨20180460027374130207641867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13453640018249420138427911 20180460027374130207641867)
            ·
              refine ⟨30270690041061195311462801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20180460027374130207641867 30270690041061195311462801)
              ·
                refine ⟨22703017530795896483597101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30270690041061195311462801 22703017530795896483597101)
                ·
                  refine ⟨8513631574048461181348913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22703017530795896483597101 8513631574048461181348913)
                  ·
                    refine ⟨6385223680536345886011685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8513631574048461181348913 6385223680536345886011685)
                    ·
                      refine ⟨1197229440100564853627191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6385223680536345886011685 1197229440100564853627191)
                      ·
                        rfl

theorem cell23_2331596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2331596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331596 prefixEnd_2331596 := by exact prefixLift 2331596
  have htrace : WordTrace (prefixWord ++ tailWord_2331596) baseStart_2331596 baseEnd_2331596 := by
    simpa [prefixWord, tailWord_2331596, baseEnd_2331596] using wordTrace_append hprefix tailTrace_2331596
  have hstable : (prefixWord ++ tailWord_2331596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331596).length < 2 ^ (prefixWord ++ tailWord_2331596).sum := by decide
  have hdescent : baseEnd_2331596 < baseStart_2331596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331613 : List Nat := [1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2331613 : Nat := 118140960795 + 2331613 * 2 ^ 59
def prefixEnd_2331613 : Nat := 4983230072969 + 3 ^ 40 * 2331613 * 2
def baseEnd_2331613 : Nat := 1197238169271691287114613

theorem tailTrace_2331613 : CollatzResearch.WordTrace tailWord_2331613 prefixEnd_2331613 1197238169271691287114613 := by
  unfold tailWord_2331613
  simp only [CollatzResearch.WordTrace]
  refine ⟨85040912501971783642567493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56693941667981189095044995 85040912501971783642567493)
  ·
    refine ⟨15945171094119709432981405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85040912501971783642567493 15945171094119709432981405)
    ·
      refine ⟨5979439160294891037368027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15945171094119709432981405 5979439160294891037368027)
      ·
        refine ⟨8969158740442336556052041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5979439160294891037368027 8969158740442336556052041)
        ·
          refine ⟨6726869055331752417039031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8969158740442336556052041 6726869055331752417039031)
          ·
            refine ⟨10090303582997628625558547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6726869055331752417039031 10090303582997628625558547)
            ·
              refine ⟨15135455374496442938337821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10090303582997628625558547 15135455374496442938337821)
              ·
                refine ⟨5675795765436166101876683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15135455374496442938337821 5675795765436166101876683)
                ·
                  refine ⟨8513693648154249152815025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5675795765436166101876683 8513693648154249152815025)
                  ·
                    refine ⟨6385270236115686864611269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8513693648154249152815025 6385270236115686864611269)
                    ·
                      refine ⟨1197238169271691287114613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6385270236115686864611269 1197238169271691287114613)
                      ·
                        rfl

theorem cell23_2331613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2331613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331613 prefixEnd_2331613 := by exact prefixLift 2331613
  have htrace : WordTrace (prefixWord ++ tailWord_2331613) baseStart_2331613 baseEnd_2331613 := by
    simpa [prefixWord, tailWord_2331613, baseEnd_2331613] using wordTrace_append hprefix tailTrace_2331613
  have hstable : (prefixWord ++ tailWord_2331613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331613).length < 2 ^ (prefixWord ++ tailWord_2331613).sum := by decide
  have hdescent : baseEnd_2331613 < baseStart_2331613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331623 : List Nat := [1, 1, 5, 2, 2, 2, 3, 7]
def baseStart_2331623 : Nat := 118140960795 + 2331623 * 2 ^ 59
def prefixEnd_2331623 : Nat := 4983230072969 + 3 ^ 40 * 2331623 * 2
def baseEnd_2331623 : Nat := 44342344595490231407021

theorem tailTrace_2331623 : CollatzResearch.WordTrace tailWord_2331623 prefixEnd_2331623 44342344595490231407021 := by
  unfold tailWord_2331623
  simp only [CollatzResearch.WordTrace]
  refine ⟨85041277231935555350431523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56694184821290370233621015 85041277231935555350431523)
  ·
    refine ⟨127561915847903333025647285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85041277231935555350431523 127561915847903333025647285)
    ·
      refine ⟨11958929610740937471154433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127561915847903333025647285 11958929610740937471154433)
      ·
        refine ⟨8969197208055703103365825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11958929610740937471154433 8969197208055703103365825)
        ·
          refine ⟨6726897906041777327524369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8969197208055703103365825 6726897906041777327524369)
          ·
            refine ⟨5045173429531332995643277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6726897906041777327524369 5045173429531332995643277)
            ·
              refine ⟨1891940036074249873366229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5045173429531332995643277 1891940036074249873366229)
              ·
                refine ⟨44342344595490231407021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1891940036074249873366229 44342344595490231407021)
                ·
                  rfl

theorem cell23_2331623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 7].length) (baseStart_2331623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331623 prefixEnd_2331623 := by exact prefixLift 2331623
  have htrace : WordTrace (prefixWord ++ tailWord_2331623) baseStart_2331623 baseEnd_2331623 := by
    simpa [prefixWord, tailWord_2331623, baseEnd_2331623] using wordTrace_append hprefix tailTrace_2331623
  have hstable : (prefixWord ++ tailWord_2331623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331623).length < 2 ^ (prefixWord ++ tailWord_2331623).sum := by decide
  have hdescent : baseEnd_2331623 < baseStart_2331623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331633 : List Nat := [1, 2, 2, 2, 4, 1, 2, 2, 1, 3, 3]
def baseStart_2331633 : Nat := 118140960795 + 2331633 * 2 ^ 59
def prefixEnd_2331633 : Nat := 4983230072969 + 3 ^ 40 * 2331633 * 2
def baseEnd_2331633 : Nat := 1197248438884781208864521

theorem tailTrace_2331633 : CollatzResearch.WordTrace tailWord_2331633 prefixEnd_2331633 1197248438884781208864521 := by
  unfold tailWord_2331633
  simp only [CollatzResearch.WordTrace]
  refine ⟨85041641961899327058295553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56694427974599551372197035 85041641961899327058295553)
  ·
    refine ⟨63781231471424495293721665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85041641961899327058295553 63781231471424495293721665)
    ·
      refine ⟨47835923603568371470291249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63781231471424495293721665 47835923603568371470291249)
      ·
        refine ⟨35876942702676278602718437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47835923603568371470291249 35876942702676278602718437)
        ·
          refine ⟨6726926756751802238009707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35876942702676278602718437 6726926756751802238009707)
          ·
            refine ⟨10090390135127703357014561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6726926756751802238009707 10090390135127703357014561)
            ·
              refine ⟨7567792601345777517760921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10090390135127703357014561 7567792601345777517760921)
              ·
                refine ⟨5675844451009333138320691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7567792601345777517760921 5675844451009333138320691)
                ·
                  refine ⟨8513766676513999707481037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5675844451009333138320691 8513766676513999707481037)
                  ·
                    refine ⟨3192662503692749890305389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8513766676513999707481037 3192662503692749890305389)
                    ·
                      refine ⟨1197248438884781208864521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3192662503692749890305389 1197248438884781208864521)
                      ·
                        rfl

theorem cell23_2331633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_2331633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331633 prefixEnd_2331633 := by exact prefixLift 2331633
  have htrace : WordTrace (prefixWord ++ tailWord_2331633) baseStart_2331633 baseEnd_2331633 := by
    simpa [prefixWord, tailWord_2331633, baseEnd_2331633] using wordTrace_append hprefix tailTrace_2331633
  have hstable : (prefixWord ++ tailWord_2331633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331633).length < 2 ^ (prefixWord ++ tailWord_2331633).sum := by decide
  have hdescent : baseEnd_2331633 < baseStart_2331633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331634 : List Nat := [3, 2, 1, 5, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2331634 : Nat := 118140960795 + 2331634 * 2 ^ 59
def prefixEnd_2331634 : Nat := 4983230072969 + 3 ^ 40 * 2331634 * 2
def baseEnd_2331634 : Nat := 1197248952365435704952017

theorem tailTrace_2331634 : CollatzResearch.WordTrace tailWord_2331634 prefixEnd_2331634 1197248952365435704952017 := by
  unfold tailWord_2331634
  simp only [CollatzResearch.WordTrace]
  refine ⟨21260419608723926057270489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56694452289930469486054637 21260419608723926057270489)
  ·
    refine ⟨15945314706542944542952867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21260419608723926057270489 15945314706542944542952867)
    ·
      refine ⟨23917972059814416814429301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15945314706542944542952867 23917972059814416814429301)
      ·
        refine ⟨2242309880607601576352747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23917972059814416814429301 2242309880607601576352747)
        ·
          refine ⟨3363464820911402364529121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242309880607601576352747 3363464820911402364529121)
          ·
            refine ⟨2522598615683551773396841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3363464820911402364529121 2522598615683551773396841)
            ·
              refine ⟨1891948961762663830047631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2522598615683551773396841 1891948961762663830047631)
              ·
                refine ⟨2837923442643995745071447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1891948961762663830047631 2837923442643995745071447)
                ·
                  refine ⟨4256885163965993617607171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2837923442643995745071447 4256885163965993617607171)
                  ·
                    refine ⟨6385327745948990426410757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4256885163965993617607171 6385327745948990426410757)
                    ·
                      refine ⟨1197248952365435704952017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6385327745948990426410757 1197248952365435704952017)
                      ·
                        rfl

theorem cell23_2331634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2331634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331634 prefixEnd_2331634 := by exact prefixLift 2331634
  have htrace : WordTrace (prefixWord ++ tailWord_2331634) baseStart_2331634 baseEnd_2331634 := by
    simpa [prefixWord, tailWord_2331634, baseEnd_2331634] using wordTrace_append hprefix tailTrace_2331634
  have hstable : (prefixWord ++ tailWord_2331634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331634).length < 2 ^ (prefixWord ++ tailWord_2331634).sum := by decide
  have hdescent : baseEnd_2331634 < baseStart_2331634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331736 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2331736 : Nat := 118140960795 + 2331736 * 2 ^ 59
def prefixEnd_2331736 : Nat := 4983230072969 + 3 ^ 40 * 2331736 * 2
def baseEnd_2331736 : Nat := 1197301327392194305876547

theorem tailTrace_2331736 : CollatzResearch.WordTrace tailWord_2331736 prefixEnd_2331736 1197301327392194305876547 := by
  unfold tailWord_2331736
  simp only [CollatzResearch.WordTrace]
  refine ⟨42522699340263087824647531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56696932453684117099530041 42522699340263087824647531)
  ·
    refine ⟨63784049010394631736971297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42522699340263087824647531 63784049010394631736971297)
    ·
      refine ⟨47838036757795973802728473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63784049010394631736971297 47838036757795973802728473)
      ·
        refine ⟨35878527568346980352046355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47838036757795973802728473 35878527568346980352046355)
        ·
          refine ⟨53817791352520470528069533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35878527568346980352046355 53817791352520470528069533)
          ·
            refine ⟨20181671757195176448026075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53817791352520470528069533 20181671757195176448026075)
            ·
              refine ⟨30272507635792764672039113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20181671757195176448026075 30272507635792764672039113)
              ·
                refine ⟨22704380726844573504029335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30272507635792764672039113 22704380726844573504029335)
                ·
                  refine ⟨34056571090266860256044003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22704380726844573504029335 34056571090266860256044003)
                  ·
                    refine ⟨51084856635400290384066005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34056571090266860256044003 51084856635400290384066005)
                    ·
                      refine ⟨1197301327392194305876547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51084856635400290384066005 1197301327392194305876547)
                      ·
                        rfl

theorem cell23_2331736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2331736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331736 prefixEnd_2331736 := by exact prefixLift 2331736
  have htrace : WordTrace (prefixWord ++ tailWord_2331736) baseStart_2331736 baseEnd_2331736 := by
    simpa [prefixWord, tailWord_2331736, baseEnd_2331736] using wordTrace_append hprefix tailTrace_2331736
  have hstable : (prefixWord ++ tailWord_2331736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331736).length < 2 ^ (prefixWord ++ tailWord_2331736).sum := by decide
  have hdescent : baseEnd_2331736 < baseStart_2331736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331743 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 2, 5]
def baseStart_2331743 : Nat := 118140960795 + 2331743 * 2 ^ 59
def prefixEnd_2331743 : Nat := 4983230072969 + 3 ^ 40 * 2331743 * 2
def baseEnd_2331743 : Nat := 399101640585591926163005

theorem tailTrace_2331743 : CollatzResearch.WordTrace tailWord_2331743 prefixEnd_2331743 399101640585591926163005 := by
  unfold tailWord_2331743
  simp only [CollatzResearch.WordTrace]
  refine ⟨85045653991500815844799883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56697102661000543896533255 85045653991500815844799883)
  ·
    refine ⟨127568480987251223767199825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85045653991500815844799883 127568480987251223767199825)
    ·
      refine ⟨95676360740438417825399869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127568480987251223767199825 95676360740438417825399869)
      ·
        refine ⟨35878635277664406684524951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95676360740438417825399869 35878635277664406684524951)
        ·
          refine ⟨53817952916496610026787427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35878635277664406684524951 53817952916496610026787427)
          ·
            refine ⟨80726929374744915040181141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53817952916496610026787427 80726929374744915040181141)
            ·
              refine ⟨3784074814441167892508491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80726929374744915040181141 3784074814441167892508491)
              ·
                refine ⟨5676112221661751838762737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784074814441167892508491 5676112221661751838762737)
                ·
                  refine ⟨4257084166246313879072053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5676112221661751838762737 4257084166246313879072053)
                  ·
                    refine ⟨399101640585591926163005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4257084166246313879072053 399101640585591926163005)
                    ·
                      rfl

theorem cell23_2331743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 5].length) (baseStart_2331743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331743 prefixEnd_2331743 := by exact prefixLift 2331743
  have htrace : WordTrace (prefixWord ++ tailWord_2331743) baseStart_2331743 baseEnd_2331743 := by
    simpa [prefixWord, tailWord_2331743, baseEnd_2331743] using wordTrace_append hprefix tailTrace_2331743
  have hstable : (prefixWord ++ tailWord_2331743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331743).length < 2 ^ (prefixWord ++ tailWord_2331743).sum := by decide
  have hdescent : baseEnd_2331743 < baseStart_2331743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331763 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 5, 6, 2]
def baseStart_2331763 : Nat := 118140960795 + 2331763 * 2 ^ 59
def prefixEnd_2331763 : Nat := 4983230072969 + 3 ^ 40 * 2331763 * 2
def baseEnd_2331763 : Nat := 1197315191369865700238923

theorem tailTrace_2331763 : CollatzResearch.WordTrace tailWord_2331763 prefixEnd_2331763 1197315191369865700238923 := by
  unfold tailWord_2331763
  simp only [CollatzResearch.WordTrace]
  refine ⟨85046383451428359260527943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56697588967618906173685295 85046383451428359260527943)
  ·
    refine ⟨127569575177142538890791915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85046383451428359260527943 127569575177142538890791915)
    ·
      refine ⟨191354362765713808336187873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127569575177142538890791915 191354362765713808336187873)
      ·
        refine ⟨143515772074285356252140905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191354362765713808336187873 143515772074285356252140905)
        ·
          refine ⟨107636829055714017189105679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143515772074285356252140905 107636829055714017189105679)
          ·
            refine ⟨161455243583571025783658519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107636829055714017189105679 161455243583571025783658519)
            ·
              refine ⟨242182865375356538675487779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161455243583571025783658519 242182865375356538675487779)
              ·
                refine ⟨363274298063034808013231669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242182865375356538675487779 363274298063034808013231669)
                ·
                  refine ⟨34056965443409513251240469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 363274298063034808013231669 34056965443409513251240469)
                  ·
                    refine ⟨1596420255159820933651897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34056965443409513251240469 1596420255159820933651897)
                    ·
                      refine ⟨1197315191369865700238923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596420255159820933651897 1197315191369865700238923)
                      ·
                        rfl

theorem cell23_2331763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 6, 2].length) (baseStart_2331763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331763 prefixEnd_2331763 := by exact prefixLift 2331763
  have htrace : WordTrace (prefixWord ++ tailWord_2331763) baseStart_2331763 baseEnd_2331763 := by
    simpa [prefixWord, tailWord_2331763, baseEnd_2331763] using wordTrace_append hprefix tailTrace_2331763
  have hstable : (prefixWord ++ tailWord_2331763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331763).length < 2 ^ (prefixWord ++ tailWord_2331763).sum := by decide
  have hdescent : baseEnd_2331763 < baseStart_2331763 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331780 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_2331780 : Nat := 118140960795 + 2331780 * 2 ^ 59
def prefixEnd_2331780 : Nat := 4983230072969 + 3 ^ 40 * 2331780 * 2
def baseEnd_2331780 : Nat := 1197323920540992133726345

theorem tailTrace_2331780 : CollatzResearch.WordTrace tailWord_2331780 prefixEnd_2331780 1197323920540992133726345 := by
  unfold tailWord_2331780
  simp only [CollatzResearch.WordTrace]
  refine ⟨42523501746183385581948397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56698002328244514109264529 42523501746183385581948397)
  ·
    refine ⟨15946313154818769593230649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42523501746183385581948397 15946313154818769593230649)
    ·
      refine ⟨11959734866114077194922987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15946313154818769593230649 11959734866114077194922987)
      ·
        refine ⟨17939602299171115792384481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11959734866114077194922987 17939602299171115792384481)
        ·
          refine ⟨13454701724378336844288361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17939602299171115792384481 13454701724378336844288361)
          ·
            refine ⟨10091026293283752633216271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13454701724378336844288361 10091026293283752633216271)
            ·
              refine ⟨15136539439925628949824407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10091026293283752633216271 15136539439925628949824407)
              ·
                refine ⟨22704809159888443424736611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15136539439925628949824407 22704809159888443424736611)
                ·
                  refine ⟨34057213739832665137104917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22704809159888443424736611 34057213739832665137104917)
                  ·
                    refine ⟨1596431894054656178301793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34057213739832665137104917 1596431894054656178301793)
                    ·
                      refine ⟨1197323920540992133726345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596431894054656178301793 1197323920540992133726345)
                      ·
                        rfl

theorem cell23_2331780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_2331780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331780 prefixEnd_2331780 := by exact prefixLift 2331780
  have htrace : WordTrace (prefixWord ++ tailWord_2331780) baseStart_2331780 baseEnd_2331780 := by
    simpa [prefixWord, tailWord_2331780, baseEnd_2331780] using wordTrace_append hprefix tailTrace_2331780
  have hstable : (prefixWord ++ tailWord_2331780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331780).length < 2 ^ (prefixWord ++ tailWord_2331780).sum := by decide
  have hdescent : baseEnd_2331780 < baseStart_2331780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331783 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 3]
def baseStart_2331783 : Nat := 118140960795 + 2331783 * 2 ^ 59
def prefixEnd_2331783 : Nat := 4983230072969 + 3 ^ 40 * 2331783 * 2
def baseEnd_2331783 : Nat := 1197325460982955621988831

theorem tailTrace_2331783 : CollatzResearch.WordTrace tailWord_2331783 prefixEnd_2331783 1197325460982955621988831 := by
  unfold tailWord_2331783
  simp only [CollatzResearch.WordTrace]
  refine ⟨85047112911355902676256003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56698075274237268450837335 85047112911355902676256003)
  ·
    refine ⟨127570669367033854014384005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85047112911355902676256003 127570669367033854014384005)
    ·
      refine ⟨23919500506318847627697001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127570669367033854014384005 23919500506318847627697001)
      ·
        refine ⟨17939625379739135720772751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23919500506318847627697001 17939625379739135720772751)
        ·
          refine ⟨26909438069608703581159127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17939625379739135720772751 26909438069608703581159127)
          ·
            refine ⟨40364157104413055371738691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26909438069608703581159127 40364157104413055371738691)
            ·
              refine ⟨60546235656619583057608037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40364157104413055371738691 60546235656619583057608037)
              ·
                refine ⟨11352419185616171823301507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60546235656619583057608037 11352419185616171823301507)
                ·
                  refine ⟨17028628778424257734952261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11352419185616171823301507 17028628778424257734952261)
                  ·
                    refine ⟨3192867895954548325303549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17028628778424257734952261 3192867895954548325303549)
                    ·
                      refine ⟨1197325460982955621988831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3192867895954548325303549 1197325460982955621988831)
                      ·
                        rfl

theorem cell23_2331783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_2331783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331783 prefixEnd_2331783 := by exact prefixLift 2331783
  have htrace : WordTrace (prefixWord ++ tailWord_2331783) baseStart_2331783 baseEnd_2331783 := by
    simpa [prefixWord, tailWord_2331783, baseEnd_2331783] using wordTrace_append hprefix tailTrace_2331783
  have hstable : (prefixWord ++ tailWord_2331783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331783).length < 2 ^ (prefixWord ++ tailWord_2331783).sum := by decide
  have hdescent : baseEnd_2331783 < baseStart_2331783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331790 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 5, 4]
def baseStart_2331790 : Nat := 118140960795 + 2331790 * 2 ^ 59
def prefixEnd_2331790 : Nat := 4983230072969 + 3 ^ 40 * 2331790 * 2
def baseEnd_2331790 : Nat := 399109685115845698200433

theorem tailTrace_2331790 : CollatzResearch.WordTrace tailWord_2331790 prefixEnd_2331790 399109685115845698200433 := by
  unfold tailWord_2331790
  simp only [CollatzResearch.WordTrace]
  refine ⟨10630921027791317858970103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56698245481553695247840549 10630921027791317858970103)
  ·
    refine ⟨15946381541686976788455155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10630921027791317858970103 15946381541686976788455155)
    ·
      refine ⟨23919572312530465182682733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15946381541686976788455155 23919572312530465182682733)
      ·
        refine ⟨8969839617198924443506025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23919572312530465182682733 8969839617198924443506025)
        ·
          refine ⟨6727379712899193332629519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8969839617198924443506025 6727379712899193332629519)
          ·
            refine ⟨10091069569348789998944279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727379712899193332629519 10091069569348789998944279)
            ·
              refine ⟨15136604354023184998416419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10091069569348789998944279 15136604354023184998416419)
              ·
                refine ⟨22704906531034777497624629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15136604354023184998416419 22704906531034777497624629)
                ·
                  refine ⟨2128584987284510390402309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22704906531034777497624629 2128584987284510390402309)
                  ·
                    refine ⟨399109685115845698200433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2128584987284510390402309 399109685115845698200433)
                    ·
                      rfl

theorem cell23_2331790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_2331790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331790 prefixEnd_2331790 := by exact prefixLift 2331790
  have htrace : WordTrace (prefixWord ++ tailWord_2331790) baseStart_2331790 baseEnd_2331790 := by
    simpa [prefixWord, tailWord_2331790, baseEnd_2331790] using wordTrace_append hprefix tailTrace_2331790
  have hstable : (prefixWord ++ tailWord_2331790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331790).length < 2 ^ (prefixWord ++ tailWord_2331790).sum := by decide
  have hdescent : baseEnd_2331790 < baseStart_2331790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331800 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2331800 : Nat := 118140960795 + 2331800 * 2 ^ 59
def prefixEnd_2331800 : Nat := 4983230072969 + 3 ^ 40 * 2331800 * 2
def baseEnd_2331800 : Nat := 1197334190154082055476253

theorem tailTrace_2331800 : CollatzResearch.WordTrace tailWord_2331800 prefixEnd_2331800 1197334190154082055476253 := by
  unfold tailWord_2331800
  simp only [CollatzResearch.WordTrace]
  refine ⟨42523866476147157289812427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56698488634862876386416569 42523866476147157289812427)
  ·
    refine ⟨63785799714220735934718641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42523866476147157289812427 63785799714220735934718641)
    ·
      refine ⟨47839349785665551951038981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63785799714220735934718641 47839349785665551951038981)
      ·
        refine ⟨8969878084812290990819809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47839349785665551951038981 8969878084812290990819809)
        ·
          refine ⟨6727408563609218243114857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8969878084812290990819809 6727408563609218243114857)
          ·
            refine ⟨5045556422706913682336143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6727408563609218243114857 5045556422706913682336143)
            ·
              refine ⟨7568334634060370523504215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045556422706913682336143 7568334634060370523504215)
              ·
                refine ⟨11352501951090555785256323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7568334634060370523504215 11352501951090555785256323)
                ·
                  refine ⟨17028752926635833677884485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11352501951090555785256323 17028752926635833677884485)
                  ·
                    refine ⟨3192891173744218814603341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17028752926635833677884485 3192891173744218814603341)
                    ·
                      refine ⟨1197334190154082055476253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3192891173744218814603341 1197334190154082055476253)
                      ·
                        rfl

theorem cell23_2331800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2331800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331800 prefixEnd_2331800 := by exact prefixLift 2331800
  have htrace : WordTrace (prefixWord ++ tailWord_2331800) baseStart_2331800 baseEnd_2331800 := by
    simpa [prefixWord, tailWord_2331800, baseEnd_2331800] using wordTrace_append hprefix tailTrace_2331800
  have hstable : (prefixWord ++ tailWord_2331800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331800).length < 2 ^ (prefixWord ++ tailWord_2331800).sum := by decide
  have hdescent : baseEnd_2331800 < baseStart_2331800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331850 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_2331850 : Nat := 118140960795 + 2331850 * 2 ^ 59
def prefixEnd_2331850 : Nat := 4983230072969 + 3 ^ 40 * 2331850 * 2
def baseEnd_2331850 : Nat := 399119954728935619950341

theorem tailTrace_2331850 : CollatzResearch.WordTrace tailWord_2331850 prefixEnd_2331850 399119954728935619950341 := by
  unfold tailWord_2331850
  simp only [CollatzResearch.WordTrace]
  refine ⟨21262389150528293279736251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56699704401408782079296669 21262389150528293279736251)
  ·
    refine ⟨31893583725792439919604377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21262389150528293279736251 31893583725792439919604377)
    ·
      refine ⟨23920187794344329939703283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31893583725792439919604377 23920187794344329939703283)
      ·
        refine ⟨35880281691516494909554925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23920187794344329939703283 35880281691516494909554925)
        ·
          refine ⟨13455105634318685591083097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35880281691516494909554925 13455105634318685591083097)
          ·
            refine ⟨10091329225739014193312323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13455105634318685591083097 10091329225739014193312323)
            ·
              refine ⟨15136993838608521289968485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10091329225739014193312323 15136993838608521289968485)
              ·
                refine ⟨2838186344739097741869091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15136993838608521289968485 2838186344739097741869091)
                ·
                  refine ⟨4257279517108646612803637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838186344739097741869091 4257279517108646612803637)
                  ·
                    refine ⟨399119954728935619950341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4257279517108646612803637 399119954728935619950341)
                    ·
                      rfl

theorem cell23_2331850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_2331850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331850 prefixEnd_2331850 := by exact prefixLift 2331850
  have htrace : WordTrace (prefixWord ++ tailWord_2331850) baseStart_2331850 baseEnd_2331850 := by
    simpa [prefixWord, tailWord_2331850, baseEnd_2331850] using wordTrace_append hprefix tailTrace_2331850
  have hstable : (prefixWord ++ tailWord_2331850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331850).length < 2 ^ (prefixWord ++ tailWord_2331850).sum := by decide
  have hdescent : baseEnd_2331850 < baseStart_2331850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331863 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 1, 6]
def baseStart_2331863 : Nat := 118140960795 + 2331863 * 2 ^ 59
def prefixEnd_2331863 : Nat := 4983230072969 + 3 ^ 40 * 2331863 * 2
def baseEnd_2331863 : Nat := 399122179811771769662821

theorem tailTrace_2331863 : CollatzResearch.WordTrace tailWord_2331863 prefixEnd_2331863 399122179811771769662821 := by
  unfold tailWord_2331863
  simp only [CollatzResearch.WordTrace]
  refine ⟨85050030751066076339168243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56700020500710717559445495 85050030751066076339168243)
  ·
    refine ⟨127575046126599114508752365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85050030751066076339168243 127575046126599114508752365)
    ·
      refine ⟨47840642297474667940782137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127575046126599114508752365 47840642297474667940782137)
      ·
        refine ⟨35880481723106000955586603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47840642297474667940782137 35880481723106000955586603)
        ·
          refine ⟨53820722584659001433379905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35880481723106000955586603 53820722584659001433379905)
          ·
            refine ⟨40365541938494251075034929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53820722584659001433379905 40365541938494251075034929)
            ·
              refine ⟨30274156453870688306276197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40365541938494251075034929 30274156453870688306276197)
              ·
                refine ⟨5676404335100754057426787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30274156453870688306276197 5676404335100754057426787)
                ·
                  refine ⟨8514606502651131086140181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5676404335100754057426787 8514606502651131086140181)
                  ·
                    refine ⟨399122179811771769662821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8514606502651131086140181 399122179811771769662821)
                    ·
                      rfl

theorem cell23_2331863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_2331863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331863 prefixEnd_2331863 := by exact prefixLift 2331863
  have htrace : WordTrace (prefixWord ++ tailWord_2331863) baseStart_2331863 baseEnd_2331863 := by
    simpa [prefixWord, tailWord_2331863, baseEnd_2331863] using wordTrace_append hprefix tailTrace_2331863
  have hstable : (prefixWord ++ tailWord_2331863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331863).length < 2 ^ (prefixWord ++ tailWord_2331863).sum := by decide
  have hdescent : baseEnd_2331863 < baseStart_2331863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331880 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 4, 4]
def baseStart_2331880 : Nat := 118140960795 + 2331880 * 2 ^ 59
def prefixEnd_2331880 : Nat := 4983230072969 + 3 ^ 40 * 2331880 * 2
def baseEnd_2331880 : Nat := 399125089535480580825295

theorem tailTrace_2331880 : CollatzResearch.WordTrace tailWord_2331880 prefixEnd_2331880 399125089535480580825295 := by
  unfold tailWord_2331880
  simp only [CollatzResearch.WordTrace]
  refine ⟨42525325396002244121268547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56700433861336325495024729 42525325396002244121268547)
  ·
    refine ⟨63787988094003366181902821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42525325396002244121268547 63787988094003366181902821)
    ·
      refine ⟨11960247767625631159106779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63787988094003366181902821 11960247767625631159106779)
      ·
        refine ⟨17940371651438446738660169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11960247767625631159106779 17940371651438446738660169)
        ·
          refine ⟨13455278738578835053995127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17940371651438446738660169 13455278738578835053995127)
          ·
            refine ⟨20182918107868252580992691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13455278738578835053995127 20182918107868252580992691)
            ·
              refine ⟨30274377161802378871489037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20182918107868252580992691 30274377161802378871489037)
              ·
                refine ⟨11352891435675892076808389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30274377161802378871489037 11352891435675892076808389)
                ·
                  refine ⟨2128667144189229764401573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11352891435675892076808389 2128667144189229764401573)
                  ·
                    refine ⟨399125089535480580825295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2128667144189229764401573 399125089535480580825295)
                    ·
                      rfl

theorem cell23_2331880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_2331880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331880 prefixEnd_2331880 := by exact prefixLift 2331880
  have htrace : WordTrace (prefixWord ++ tailWord_2331880) baseStart_2331880 baseEnd_2331880 := by
    simpa [prefixWord, tailWord_2331880, baseEnd_2331880] using wordTrace_append hprefix tailTrace_2331880
  have hstable : (prefixWord ++ tailWord_2331880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331880).length < 2 ^ (prefixWord ++ tailWord_2331880).sum := by decide
  have hdescent : baseEnd_2331880 < baseStart_2331880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331883 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 6]
def baseStart_2331883 : Nat := 118140960795 + 2331883 * 2 ^ 59
def prefixEnd_2331883 : Nat := 4983230072969 + 3 ^ 40 * 2331883 * 2
def baseEnd_2331883 : Nat := 1197376809048405230738371

theorem tailTrace_2331883 : CollatzResearch.WordTrace tailWord_2331883 prefixEnd_2331883 1197376809048405230738371 := by
  unfold tailWord_2331883
  simp only [CollatzResearch.WordTrace]
  refine ⟨85050760210993619754896303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56700506807329079836597535 85050760210993619754896303)
  ·
    refine ⟨127576140316490429632344455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85050760210993619754896303 127576140316490429632344455)
    ·
      refine ⟨191364210474735644448516683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127576140316490429632344455 191364210474735644448516683)
      ·
        refine ⟨287046315712103466672775025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191364210474735644448516683 287046315712103466672775025)
        ·
          refine ⟨215284736784077600004581269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287046315712103466672775025 215284736784077600004581269)
          ·
            refine ⟨10091472036753637500214747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 215284736784077600004581269 10091472036753637500214747)
            ·
              refine ⟨15137208055130456250322121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10091472036753637500214747 15137208055130456250322121)
              ·
                refine ⟨11352906041347842187741591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15137208055130456250322121 11352906041347842187741591)
                ·
                  refine ⟨17029359062021763281612387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11352906041347842187741591 17029359062021763281612387)
                  ·
                    refine ⟨25544038593032644922418581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17029359062021763281612387 25544038593032644922418581)
                    ·
                      refine ⟨1197376809048405230738371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25544038593032644922418581 1197376809048405230738371)
                      ·
                        rfl

theorem cell23_2331883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 6].length) (baseStart_2331883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331883 prefixEnd_2331883 := by exact prefixLift 2331883
  have htrace : WordTrace (prefixWord ++ tailWord_2331883) baseStart_2331883 baseEnd_2331883 := by
    simpa [prefixWord, tailWord_2331883, baseEnd_2331883] using wordTrace_append hprefix tailTrace_2331883
  have hstable : (prefixWord ++ tailWord_2331883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331883).length < 2 ^ (prefixWord ++ tailWord_2331883).sum := by decide
  have hdescent : baseEnd_2331883 < baseStart_2331883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331907 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 1, 2, 3]
def baseStart_2331907 : Nat := 118140960795 + 2331907 * 2 ^ 59
def prefixEnd_2331907 : Nat := 4983230072969 + 3 ^ 40 * 2331907 * 2
def baseEnd_2331907 : Nat := 1197389132584113136838261

theorem tailTrace_2331907 : CollatzResearch.WordTrace tailWord_2331907 prefixEnd_2331907 1197389132584113136838261 := by
  unfold tailWord_2331907
  simp only [CollatzResearch.WordTrace]
  refine ⟨85051635562906671853769975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56701090375271114569179983 85051635562906671853769975)
  ·
    refine ⟨127577453344360007780654963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85051635562906671853769975 127577453344360007780654963)
    ·
      refine ⟨191366180016540011670982445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127577453344360007780654963 191366180016540011670982445)
      ·
        refine ⟨71762317506202504376618417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191366180016540011670982445 71762317506202504376618417)
        ·
          refine ⟨53821738129651878282463813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71762317506202504376618417 53821738129651878282463813)
          ·
            refine ⟨10091575899309727177961965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53821738129651878282463813 10091575899309727177961965)
            ·
              refine ⟨3784340962241147691735737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10091575899309727177961965 3784340962241147691735737)
              ·
                refine ⟨2838255721680860768801803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3784340962241147691735737 2838255721680860768801803)
                ·
                  refine ⟨4257383582521291153202705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838255721680860768801803 4257383582521291153202705)
                  ·
                    refine ⟨3193037686890968364902029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257383582521291153202705 3193037686890968364902029)
                    ·
                      refine ⟨1197389132584113136838261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3193037686890968364902029 1197389132584113136838261)
                      ·
                        rfl

theorem cell23_2331907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_2331907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331907 prefixEnd_2331907 := by exact prefixLift 2331907
  have htrace : WordTrace (prefixWord ++ tailWord_2331907) baseStart_2331907 baseEnd_2331907 := by
    simpa [prefixWord, tailWord_2331907, baseEnd_2331907] using wordTrace_append hprefix tailTrace_2331907
  have hstable : (prefixWord ++ tailWord_2331907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331907).length < 2 ^ (prefixWord ++ tailWord_2331907).sum := by decide
  have hdescent : baseEnd_2331907 < baseStart_2331907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331938 : List Nat := [3, 3, 1, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_2331938 : Nat := 118140960795 + 2331938 * 2 ^ 59
def prefixEnd_2331938 : Nat := 4983230072969 + 3 ^ 40 * 2331938 * 2
def baseEnd_2331938 : Nat := 1197405050484402515550619

theorem tailTrace_2331938 : CollatzResearch.WordTrace tailWord_2331938 prefixEnd_2331938 1197405050484402515550619 := by
  unfold tailWord_2331938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21263191556448591037037117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56701844150529576098765645 21263191556448591037037117)
  ·
    refine ⟨7973696833668221638888919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21263191556448591037037117 7973696833668221638888919)
    ·
      refine ⟨11960545250502332458333379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7973696833668221638888919 11960545250502332458333379)
      ·
        refine ⟨17940817875753498687500069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11960545250502332458333379 17940817875753498687500069)
        ·
          refine ⟨3363903351703781003906263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17940817875753498687500069 3363903351703781003906263)
          ·
            refine ⟨5045855027555671505859395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3363903351703781003906263 5045855027555671505859395)
            ·
              refine ⟨7568782541333507258789093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5045855027555671505859395 7568782541333507258789093)
              ·
                refine ⟨1419146726500032611022955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7568782541333507258789093 1419146726500032611022955)
                ·
                  refine ⟨2128720089750048916534433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419146726500032611022955 2128720089750048916534433)
                  ·
                    refine ⟨1596540067312536687400825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2128720089750048916534433 1596540067312536687400825)
                    ·
                      refine ⟨1197405050484402515550619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596540067312536687400825 1197405050484402515550619)
                      ·
                        rfl

theorem cell23_2331938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_2331938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331938 prefixEnd_2331938 := by exact prefixLift 2331938
  have htrace : WordTrace (prefixWord ++ tailWord_2331938) baseStart_2331938 baseEnd_2331938 := by
    simpa [prefixWord, tailWord_2331938, baseEnd_2331938] using wordTrace_append hprefix tailTrace_2331938
  have hstable : (prefixWord ++ tailWord_2331938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331938).length < 2 ^ (prefixWord ++ tailWord_2331938).sum := by decide
  have hdescent : baseEnd_2331938 < baseStart_2331938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331954 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_2331954 : Nat := 118140960795 + 2331954 * 2 ^ 59
def prefixEnd_2331954 : Nat := 4983230072969 + 3 ^ 40 * 2331954 * 2
def baseEnd_2331954 : Nat := 1197413266174874452950545

theorem tailTrace_2331954 : CollatzResearch.WordTrace tailWord_2331954 prefixEnd_2331954 1197413266174874452950545 := by
  unfold tailWord_2331954
  simp only [CollatzResearch.WordTrace]
  refine ⟨21263337448434099720182729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56702233195824265920487277 21263337448434099720182729)
  ·
    refine ⟨15947503086325574790137047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21263337448434099720182729 15947503086325574790137047)
    ·
      refine ⟨23921254629488362185205571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15947503086325574790137047 23921254629488362185205571)
      ·
        refine ⟨35881881944232543277808357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23921254629488362185205571 35881881944232543277808357)
        ·
          refine ⟨6727852864543601864589067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35881881944232543277808357 6727852864543601864589067)
          ·
            refine ⟨10091779296815402796883601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727852864543601864589067 10091779296815402796883601)
            ·
              refine ⟨7568834472611552097662701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10091779296815402796883601 7568834472611552097662701)
              ·
                refine ⟨2838312927229332036623513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7568834472611552097662701 2838312927229332036623513)
                ·
                  refine ⟨2128734695421999027467635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2838312927229332036623513 2128734695421999027467635)
                  ·
                    refine ⟨3193102043132998541201453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2128734695421999027467635 3193102043132998541201453)
                    ·
                      refine ⟨1197413266174874452950545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3193102043132998541201453 1197413266174874452950545)
                      ·
                        rfl

theorem cell23_2331954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_2331954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331954 prefixEnd_2331954 := by exact prefixLift 2331954
  have htrace : WordTrace (prefixWord ++ tailWord_2331954) baseStart_2331954 baseEnd_2331954 := by
    simpa [prefixWord, tailWord_2331954, baseEnd_2331954] using wordTrace_append hprefix tailTrace_2331954
  have hstable : (prefixWord ++ tailWord_2331954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331954).length < 2 ^ (prefixWord ++ tailWord_2331954).sum := by decide
  have hdescent : baseEnd_2331954 < baseStart_2331954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2331977 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 1, 4, 2]
def baseStart_2331977 : Nat := 118140960795 + 2331977 * 2 ^ 59
def prefixEnd_2331977 : Nat := 4983230072969 + 3 ^ 40 * 2331977 * 2
def baseEnd_2331977 : Nat := 1197425076229927862962939

theorem tailTrace_2331977 : CollatzResearch.WordTrace tailWord_2331977 prefixEnd_2331977 1197425076229927862962939 := by
  unfold tailWord_2331977
  simp only [CollatzResearch.WordTrace]
  refine ⟨85054188672653073808818185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56702792448435382539212123 85054188672653073808818185)
  ·
    refine ⟨63790641504489805356613639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85054188672653073808818185 63790641504489805356613639)
    ·
      refine ⟨95685962256734708034920459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63790641504489805356613639 95685962256734708034920459)
      ·
        refine ⟨143528943385102062052380689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95685962256734708034920459 143528943385102062052380689)
        ·
          refine ⟨107646707538826546539285517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143528943385102062052380689 107646707538826546539285517)
          ·
            refine ⟨40367515327059954952232069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107646707538826546539285517 40367515327059954952232069)
            ·
              refine ⟨7568909123823741553543513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40367515327059954952232069 7568909123823741553543513)
              ·
                refine ⟨5676681842867806165157635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7568909123823741553543513 5676681842867806165157635)
                ·
                  refine ⟨8515022764301709247736453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5676681842867806165157635 8515022764301709247736453)
                  ·
                    refine ⟨1596566768306570483950585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8515022764301709247736453 1596566768306570483950585)
                    ·
                      refine ⟨1197425076229927862962939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596566768306570483950585 1197425076229927862962939)
                      ·
                        rfl

theorem cell23_2331977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 4, 2].length) (baseStart_2331977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2331977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2331977 prefixEnd_2331977 := by exact prefixLift 2331977
  have htrace : WordTrace (prefixWord ++ tailWord_2331977) baseStart_2331977 baseEnd_2331977 := by
    simpa [prefixWord, tailWord_2331977, baseEnd_2331977] using wordTrace_append hprefix tailTrace_2331977
  have hstable : (prefixWord ++ tailWord_2331977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2331977).length < 2 ^ (prefixWord ++ tailWord_2331977).sum := by decide
  have hdescent : baseEnd_2331977 < baseStart_2331977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2331977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332000 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 7]
def baseStart_2332000 : Nat := 118140960795 + 2332000 * 2 ^ 59
def prefixEnd_2332000 : Nat := 4983230072969 + 3 ^ 40 * 2332000 * 2
def baseEnd_2332000 : Nat := 133048542920553474775037

theorem tailTrace_2332000 : CollatzResearch.WordTrace tailWord_2332000 prefixEnd_2332000 133048542920553474775037 := by
  unfold tailWord_2332000
  simp only [CollatzResearch.WordTrace]
  refine ⟨42527513775784874368452727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56703351701046499157936969 42527513775784874368452727)
  ·
    refine ⟨63791270663677311552679091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42527513775784874368452727 63791270663677311552679091)
    ·
      refine ⟨95686905995515967329018637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63791270663677311552679091 95686905995515967329018637)
      ·
        refine ⟨35882589748318487748381989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95686905995515967329018637 35882589748318487748381989)
        ·
          refine ⟨6727985577809716452821623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35882589748318487748381989 6727985577809716452821623)
          ·
            refine ⟨10091978366714574679232435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6727985577809716452821623 10091978366714574679232435)
            ·
              refine ⟨15137967550071862018848653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10091978366714574679232435 15137967550071862018848653)
              ·
                refine ⟨5676737831276948257068245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15137967550071862018848653 5676737831276948257068245)
                ·
                  refine ⟨133048542920553474775037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5676737831276948257068245 133048542920553474775037)
                  ·
                    rfl

theorem cell23_2332000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 7].length) (baseStart_2332000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332000 prefixEnd_2332000 := by exact prefixLift 2332000
  have htrace : WordTrace (prefixWord ++ tailWord_2332000) baseStart_2332000 baseEnd_2332000 := by
    simpa [prefixWord, tailWord_2332000, baseEnd_2332000] using wordTrace_append hprefix tailTrace_2332000
  have hstable : (prefixWord ++ tailWord_2332000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332000).length < 2 ^ (prefixWord ++ tailWord_2332000).sum := by decide
  have hdescent : baseEnd_2332000 < baseStart_2332000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332062 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_2332062 : Nat := 118140960795 + 2332062 * 2 ^ 59
def prefixEnd_2332062 : Nat := 4983230072969 + 3 ^ 40 * 2332062 * 2
def baseEnd_2332062 : Nat := 1197468722085560030400049

theorem tailTrace_2332062 : CollatzResearch.WordTrace tailWord_2332062 prefixEnd_2332062 1197468722085560030400049 := by
  unfold tailWord_2332062
  simp only [CollatzResearch.WordTrace]
  refine ⟨10632161109668141665707805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56704859251563422217108293 10632161109668141665707805)
  ·
    refine ⟨3987060416125553124640427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10632161109668141665707805 3987060416125553124640427)
    ·
      refine ⟨5980590624188329686960641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3987060416125553124640427 5980590624188329686960641)
      ·
        refine ⟨4485442968141247265220481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5980590624188329686960641 4485442968141247265220481)
        ·
          refine ⟨3364082226105935448915361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4485442968141247265220481 3364082226105935448915361)
          ·
            refine ⟨2523061669579451586686521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3364082226105935448915361 2523061669579451586686521)
            ·
              refine ⟨1892296252184588690014891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2523061669579451586686521 1892296252184588690014891)
              ·
                refine ⟨2838444378276883035022337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892296252184588690014891 2838444378276883035022337)
                ·
                  refine ⟨2128833283707662276266753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2838444378276883035022337 2128833283707662276266753)
                  ·
                    refine ⟨1596624962780746707200065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2128833283707662276266753 1596624962780746707200065)
                    ·
                      refine ⟨1197468722085560030400049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596624962780746707200065 1197468722085560030400049)
                      ·
                        rfl

theorem cell23_2332062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_2332062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332062 prefixEnd_2332062 := by exact prefixLift 2332062
  have htrace : WordTrace (prefixWord ++ tailWord_2332062) baseStart_2332062 baseEnd_2332062 := by
    simpa [prefixWord, tailWord_2332062, baseEnd_2332062] using wordTrace_append hprefix tailTrace_2332062
  have hstable : (prefixWord ++ tailWord_2332062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332062).length < 2 ^ (prefixWord ++ tailWord_2332062).sum := by decide
  have hdescent : baseEnd_2332062 < baseStart_2332062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332067 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 1, 6, 2]
def baseStart_2332067 : Nat := 118140960795 + 2332067 * 2 ^ 59
def prefixEnd_2332067 : Nat := 4983230072969 + 3 ^ 40 * 2332067 * 2
def baseEnd_2332067 : Nat := 1197471289488832510837525

theorem tailTrace_2332067 : CollatzResearch.WordTrace tailWord_2332067 prefixEnd_2332067 1197471289488832510837525 := by
  unfold tailWord_2332067
  simp only [CollatzResearch.WordTrace]
  refine ⟨85057471242327019179594455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56704980828218012786396303 85057471242327019179594455)
  ·
    refine ⟨127586206863490528769391683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85057471242327019179594455 127586206863490528769391683)
    ·
      refine ⟨191379310295235793154087525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127586206863490528769391683 191379310295235793154087525)
      ·
        refine ⟨35883620680356711216391411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191379310295235793154087525 35883620680356711216391411)
        ·
          refine ⟨53825431020535066824587117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35883620680356711216391411 53825431020535066824587117)
          ·
            refine ⟨20184536632700650059220169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53825431020535066824587117 20184536632700650059220169)
            ·
              refine ⟨15138402474525487544415127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20184536632700650059220169 15138402474525487544415127)
              ·
                refine ⟨22707603711788231316622691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15138402474525487544415127 22707603711788231316622691)
                ·
                  refine ⟨34061405567682346974934037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22707603711788231316622691 34061405567682346974934037)
                  ·
                    refine ⟨1596628385985110014450033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34061405567682346974934037 1596628385985110014450033)
                    ·
                      refine ⟨1197471289488832510837525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596628385985110014450033 1197471289488832510837525)
                      ·
                        rfl

theorem cell23_2332067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_2332067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332067 prefixEnd_2332067 := by exact prefixLift 2332067
  have htrace : WordTrace (prefixWord ++ tailWord_2332067) baseStart_2332067 baseEnd_2332067 := by
    simpa [prefixWord, tailWord_2332067, baseEnd_2332067] using wordTrace_append hprefix tailTrace_2332067
  have hstable : (prefixWord ++ tailWord_2332067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332067).length < 2 ^ (prefixWord ++ tailWord_2332067).sum := by decide
  have hdescent : baseEnd_2332067 < baseStart_2332067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332111 : List Nat := [1, 1, 2, 1, 1, 4, 6, 2, 1, 4]
def baseStart_2332111 : Nat := 118140960795 + 2332111 * 2 ^ 59
def prefixEnd_2332111 : Nat := 4983230072969 + 3 ^ 40 * 2332111 * 2
def baseEnd_2332111 : Nat := 399164627545876779562441

theorem tailTrace_2332111 : CollatzResearch.WordTrace tailWord_2332111 prefixEnd_2332111 399164627545876779562441 := by
  unfold tailWord_2332111
  simp only [CollatzResearch.WordTrace]
  refine ⟨85059076054167614694196187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56706050702778409796130791 85059076054167614694196187)
  ·
    refine ⟨127588614081251422041294281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85059076054167614694196187 127588614081251422041294281)
    ·
      refine ⟨95691460560938566530970711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127588614081251422041294281 95691460560938566530970711)
      ·
        refine ⟨143537190841407849796456067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95691460560938566530970711 143537190841407849796456067)
        ·
          refine ⟨215305786262111774694684101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143537190841407849796456067 215305786262111774694684101)
          ·
            refine ⟨40369834924145957755253269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215305786262111774694684101 40369834924145957755253269)
            ·
              refine ⟨1892336012069341769777497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40369834924145957755253269 1892336012069341769777497)
              ·
                refine ⟨1419252009052006327333123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1892336012069341769777497 1419252009052006327333123)
                ·
                  refine ⟨2128878013578009490999685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419252009052006327333123 2128878013578009490999685)
                  ·
                    refine ⟨399164627545876779562441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2128878013578009490999685 399164627545876779562441)
                    ·
                      rfl

theorem cell23_2332111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 1, 4].length) (baseStart_2332111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332111 prefixEnd_2332111 := by exact prefixLift 2332111
  have htrace : WordTrace (prefixWord ++ tailWord_2332111) baseStart_2332111 baseEnd_2332111 := by
    simpa [prefixWord, tailWord_2332111, baseEnd_2332111] using wordTrace_append hprefix tailTrace_2332111
  have hstable : (prefixWord ++ tailWord_2332111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332111).length < 2 ^ (prefixWord ++ tailWord_2332111).sum := by decide
  have hdescent : baseEnd_2332111 < baseStart_2332111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332138 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_2332138 : Nat := 118140960795 + 2332138 * 2 ^ 59
def prefixEnd_2332138 : Nat := 4983230072969 + 3 ^ 40 * 2332138 * 2
def baseEnd_2332138 : Nat := 1197507746615301733049699

theorem tailTrace_2332138 : CollatzResearch.WordTrace tailWord_2332138 prefixEnd_2332138 1197507746615301733049699 := by
  unfold tailWord_2332138
  simp only [CollatzResearch.WordTrace]
  refine ⟨21265015206267449576357267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56706707216713198870286045 21265015206267449576357267)
  ·
    refine ⟨31897522809401174364535901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21265015206267449576357267 31897522809401174364535901)
    ·
      refine ⟨11961571053525440386700963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31897522809401174364535901 11961571053525440386700963)
      ·
        refine ⟨17942356580288160580051445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11961571053525440386700963 17942356580288160580051445)
        ·
          refine ⟨1682095929402015054379823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17942356580288160580051445 1682095929402015054379823)
          ·
            refine ⟨2523143894103022581569735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682095929402015054379823 2523143894103022581569735)
            ·
              refine ⟨3784715841154533872354603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523143894103022581569735 3784715841154533872354603)
              ·
                refine ⟨5677073761731800808531905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784715841154533872354603 5677073761731800808531905)
                ·
                  refine ⟨4257805321298850606398929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5677073761731800808531905 4257805321298850606398929)
                  ·
                    refine ⟨3193353990974137954799197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257805321298850606398929 3193353990974137954799197)
                    ·
                      refine ⟨1197507746615301733049699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3193353990974137954799197 1197507746615301733049699)
                      ·
                        rfl

theorem cell23_2332138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_2332138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332138 prefixEnd_2332138 := by exact prefixLift 2332138
  have htrace : WordTrace (prefixWord ++ tailWord_2332138) baseStart_2332138 baseEnd_2332138 := by
    simpa [prefixWord, tailWord_2332138, baseEnd_2332138] using wordTrace_append hprefix tailTrace_2332138
  have hstable : (prefixWord ++ tailWord_2332138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332138).length < 2 ^ (prefixWord ++ tailWord_2332138).sum := by decide
  have hdescent : baseEnd_2332138 < baseStart_2332138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332144 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 1, 5, 2]
def baseStart_2332144 : Nat := 118140960795 + 2332144 * 2 ^ 59
def prefixEnd_2332144 : Nat := 4983230072969 + 3 ^ 40 * 2332144 * 2
def baseEnd_2332144 : Nat := 1197510827499228709574671

theorem tailTrace_2332144 : CollatzResearch.WordTrace tailWord_2332144 prefixEnd_2332144 1197510827499228709574671 := by
  unfold tailWord_2332144
  simp only [CollatzResearch.WordTrace]
  refine ⟨42530139831524030665073743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56706853108698707553431657 42530139831524030665073743)
  ·
    refine ⟨63795209747286045997610615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42530139831524030665073743 63795209747286045997610615)
    ·
      refine ⟨95692814620929068996415923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63795209747286045997610615 95692814620929068996415923)
      ·
        refine ⟨143539221931393603494623885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95692814620929068996415923 143539221931393603494623885)
        ·
          refine ⟨53827208224272601310483957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143539221931393603494623885 53827208224272601310483957)
          ·
            refine ⟨5046300771025556372857871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53827208224272601310483957 5046300771025556372857871)
            ·
              refine ⟨7569451156538334559286807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5046300771025556372857871 7569451156538334559286807)
              ·
                refine ⟨11354176734807501838930211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7569451156538334559286807 11354176734807501838930211)
                ·
                  refine ⟨17031265102211252758395317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11354176734807501838930211 17031265102211252758395317)
                  ·
                    refine ⟨1596681103332304946099561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17031265102211252758395317 1596681103332304946099561)
                    ·
                      refine ⟨1197510827499228709574671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596681103332304946099561 1197510827499228709574671)
                      ·
                        rfl

theorem cell23_2332144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 5, 2].length) (baseStart_2332144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332144 prefixEnd_2332144 := by exact prefixLift 2332144
  have htrace : WordTrace (prefixWord ++ tailWord_2332144) baseStart_2332144 baseEnd_2332144 := by
    simpa [prefixWord, tailWord_2332144, baseEnd_2332144] using wordTrace_append hprefix tailTrace_2332144
  have hstable : (prefixWord ++ tailWord_2332144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332144).length < 2 ^ (prefixWord ++ tailWord_2332144).sum := by decide
  have hdescent : baseEnd_2332144 < baseStart_2332144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332158 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_2332158 : Nat := 118140960795 + 2332158 * 2 ^ 59
def prefixEnd_2332158 : Nat := 4983230072969 + 3 ^ 40 * 2332158 * 2
def baseEnd_2332158 : Nat := 133057557358710183866623

theorem tailTrace_2332158 : CollatzResearch.WordTrace tailWord_2332158 prefixEnd_2332158 133057557358710183866623 := by
  unfold tailWord_2332158
  simp only [CollatzResearch.WordTrace]
  refine ⟨10632598785624667715144641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56707193523331561147438085 10632598785624667715144641)
  ·
    refine ⟨7974449089218500786358481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10632598785624667715144641 7974449089218500786358481)
    ·
      refine ⟨5980836816913875589768861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7974449089218500786358481 5980836816913875589768861)
      ·
        refine ⟨2242813806342703346163323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5980836816913875589768861 2242813806342703346163323)
        ·
          refine ⟨3364220709514055019244985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2242813806342703346163323 3364220709514055019244985)
          ·
            refine ⟨2523165532135541264433739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3364220709514055019244985 2523165532135541264433739)
            ·
              refine ⟨3784748298203311896650609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523165532135541264433739 3784748298203311896650609)
              ·
                refine ⟨2838561223652483922487957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3784748298203311896650609 2838561223652483922487957)
                ·
                  refine ⟨133057557358710183866623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2838561223652483922487957 133057557358710183866623)
                  ·
                    rfl

theorem cell23_2332158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_2332158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332158 prefixEnd_2332158 := by exact prefixLift 2332158
  have htrace : WordTrace (prefixWord ++ tailWord_2332158) baseStart_2332158 baseEnd_2332158 := by
    simpa [prefixWord, tailWord_2332158, baseEnd_2332158] using wordTrace_append hprefix tailTrace_2332158
  have hstable : (prefixWord ++ tailWord_2332158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332158).length < 2 ^ (prefixWord ++ tailWord_2332158).sum := by decide
  have hdescent : baseEnd_2332158 < baseStart_2332158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332177 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 5]
def baseStart_2332177 : Nat := 118140960795 + 2332177 * 2 ^ 59
def prefixEnd_2332177 : Nat := 4983230072969 + 3 ^ 40 * 2332177 * 2
def baseEnd_2332177 : Nat := 1197527772360827080462019

theorem tailTrace_2332177 : CollatzResearch.WordTrace tailWord_2332177 prefixEnd_2332177 1197527772360827080462019 := by
  unfold tailWord_2332177
  simp only [CollatzResearch.WordTrace]
  refine ⟨85061483271928507966098785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56707655514619005310732523 85061483271928507966098785)
  ·
    refine ⟨63796112453946380974574089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85061483271928507966098785 63796112453946380974574089)
    ·
      refine ⟨47847084340459785730930567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63796112453946380974574089 47847084340459785730930567)
      ·
        refine ⟨71770626510689678596395851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47847084340459785730930567 71770626510689678596395851)
        ·
          refine ⟨107655939766034517894593777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71770626510689678596395851 107655939766034517894593777)
          ·
            refine ⟨80741954824525888420945333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107655939766034517894593777 80741954824525888420945333)
            ·
              refine ⟨7569558264799302039463625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80741954824525888420945333 7569558264799302039463625)
              ·
                refine ⟨5677168698599476529597719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7569558264799302039463625 5677168698599476529597719)
                ·
                  refine ⟨8515753047899214794396579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5677168698599476529597719 8515753047899214794396579)
                  ·
                    refine ⟨12773629571848822191594869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8515753047899214794396579 12773629571848822191594869)
                    ·
                      refine ⟨1197527772360827080462019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12773629571848822191594869 1197527772360827080462019)
                      ·
                        rfl

theorem cell23_2332177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_2332177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332177 prefixEnd_2332177 := by exact prefixLift 2332177
  have htrace : WordTrace (prefixWord ++ tailWord_2332177) baseStart_2332177 baseEnd_2332177 := by
    simpa [prefixWord, tailWord_2332177, baseEnd_2332177] using wordTrace_append hprefix tailTrace_2332177
  have hstable : (prefixWord ++ tailWord_2332177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332177).length < 2 ^ (prefixWord ++ tailWord_2332177).sum := by decide
  have hdescent : baseEnd_2332177 < baseStart_2332177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332191 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 3, 2, 2]
def baseStart_2332191 : Nat := 118140960795 + 2332191 * 2 ^ 59
def prefixEnd_2332191 : Nat := 4983230072969 + 3 ^ 40 * 2332191 * 2
def baseEnd_2332191 : Nat := 1197534961089990025686955

theorem tailTrace_2332191 : CollatzResearch.WordTrace tailWord_2332191 prefixEnd_2332191 1197534961089990025686955 := by
  unfold tailWord_2332191
  simp only [CollatzResearch.WordTrace]
  refine ⟨85061993893877788357108427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56707995929251858904738951 85061993893877788357108427)
  ·
    refine ⟨127592990840816682535662641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85061993893877788357108427 127592990840816682535662641)
    ·
      refine ⟨95694743130612511901746981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127592990840816682535662641 95694743130612511901746981)
      ·
        refine ⟨17942764336989845981577559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95694743130612511901746981 17942764336989845981577559)
        ·
          refine ⟨26914146505484768972366339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17942764336989845981577559 26914146505484768972366339)
          ·
            refine ⟨40371219758227153458549509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26914146505484768972366339 40371219758227153458549509)
            ·
              refine ⟨7569603704667591273478033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40371219758227153458549509 7569603704667591273478033)
              ·
                refine ⟨5677202778500693455108525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7569603704667591273478033 5677202778500693455108525)
                ·
                  refine ⟨2128951041937760045665697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5677202778500693455108525 2128951041937760045665697)
                  ·
                    refine ⟨1596713281453320034249273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2128951041937760045665697 1596713281453320034249273)
                    ·
                      refine ⟨1197534961089990025686955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596713281453320034249273 1197534961089990025686955)
                      ·
                        rfl

theorem cell23_2332191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_2332191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332191 prefixEnd_2332191 := by exact prefixLift 2332191
  have htrace : WordTrace (prefixWord ++ tailWord_2332191) baseStart_2332191 baseEnd_2332191 := by
    simpa [prefixWord, tailWord_2332191, baseEnd_2332191] using wordTrace_append hprefix tailTrace_2332191
  have hstable : (prefixWord ++ tailWord_2332191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332191).length < 2 ^ (prefixWord ++ tailWord_2332191).sum := by decide
  have hdescent : baseEnd_2332191 < baseStart_2332191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332194 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_2332194 : Nat := 118140960795 + 2332194 * 2 ^ 59
def prefixEnd_2332194 : Nat := 4983230072969 + 3 ^ 40 * 2332194 * 2
def baseEnd_2332194 : Nat := 1197536501531953513949441

theorem tailTrace_2332194 : CollatzResearch.WordTrace tailWord_2332194 prefixEnd_2332194 1197536501531953513949441 := by
  unfold tailWord_2332194
  simp only [CollatzResearch.WordTrace]
  refine ⟨21265525828216729967366909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56708068875244613246311757 21265525828216729967366909)
  ·
    refine ⟨7974572185581273737762591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21265525828216729967366909 7974572185581273737762591)
    ·
      refine ⟨11961858278371910606643887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7974572185581273737762591 11961858278371910606643887)
      ·
        refine ⟨17942787417557865909965831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11961858278371910606643887 17942787417557865909965831)
        ·
          refine ⟨26914181126336798864948747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17942787417557865909965831 26914181126336798864948747)
          ·
            refine ⟨40371271689505198297423121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26914181126336798864948747 40371271689505198297423121)
            ·
              refine ⟨30278453767128898723067341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40371271689505198297423121 30278453767128898723067341)
              ·
                refine ⟨11354420162673337021150253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30278453767128898723067341 11354420162673337021150253)
                ·
                  refine ⟨4257907561002501382931345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11354420162673337021150253 4257907561002501382931345)
                  ·
                    refine ⟨3193430670751876037198509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4257907561002501382931345 3193430670751876037198509)
                    ·
                      refine ⟨1197536501531953513949441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3193430670751876037198509 1197536501531953513949441)
                      ·
                        rfl

theorem cell23_2332194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_2332194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332194 prefixEnd_2332194 := by exact prefixLift 2332194
  have htrace : WordTrace (prefixWord ++ tailWord_2332194) baseStart_2332194 baseEnd_2332194 := by
    simpa [prefixWord, tailWord_2332194, baseEnd_2332194] using wordTrace_append hprefix tailTrace_2332194
  have hstable : (prefixWord ++ tailWord_2332194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332194).length < 2 ^ (prefixWord ++ tailWord_2332194).sum := by decide
  have hdescent : baseEnd_2332194 < baseStart_2332194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332241 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 2, 1, 3]
def baseStart_2332241 : Nat := 118140960795 + 2332241 * 2 ^ 59
def prefixEnd_2332241 : Nat := 4983230072969 + 3 ^ 40 * 2332241 * 2
def baseEnd_2332241 : Nat := 1197560635122714830061725

theorem tailTrace_2332241 : CollatzResearch.WordTrace tailWord_2332241 prefixEnd_2332241 1197560635122714830061725 := by
  unfold tailWord_2332241
  simp only [CollatzResearch.WordTrace]
  refine ⟨85063817543696646896428577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56709211695797764597619051 85063817543696646896428577)
  ·
    refine ⟨63797863157772485172321433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85063817543696646896428577 63797863157772485172321433)
    ·
      refine ⟨47848397368329363879241075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63797863157772485172321433 47848397368329363879241075)
      ·
        refine ⟨71772596052494045818861613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47848397368329363879241075 71772596052494045818861613)
        ·
          refine ⟨26914723519685267182073105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71772596052494045818861613 26914723519685267182073105)
          ·
            refine ⟨20186042639763950386554829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26914723519685267182073105 20186042639763950386554829)
            ·
              refine ⟨7569765989911481394958061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20186042639763950386554829 7569765989911481394958061)
              ·
                refine ⟨2838662246216805523109273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7569765989911481394958061 2838662246216805523109273)
                ·
                  refine ⟨2128996684662604142331955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2838662246216805523109273 2128996684662604142331955)
                  ·
                    refine ⟨3193495026993906213497933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2128996684662604142331955 3193495026993906213497933)
                    ·
                      refine ⟨1197560635122714830061725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3193495026993906213497933 1197560635122714830061725)
                      ·
                        rfl

theorem cell23_2332241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_2332241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332241 prefixEnd_2332241 := by exact prefixLift 2332241
  have htrace : WordTrace (prefixWord ++ tailWord_2332241) baseStart_2332241 baseEnd_2332241 := by
    simpa [prefixWord, tailWord_2332241, baseEnd_2332241] using wordTrace_append hprefix tailTrace_2332241
  have hstable : (prefixWord ++ tailWord_2332241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332241).length < 2 ^ (prefixWord ++ tailWord_2332241).sum := by decide
  have hdescent : baseEnd_2332241 < baseStart_2332241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332298 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2]
def baseStart_2332298 : Nat := 118140960795 + 2332298 * 2 ^ 59
def prefixEnd_2332298 : Nat := 4983230072969 + 3 ^ 40 * 2332298 * 2
def baseEnd_2332298 : Nat := 1197589903520021107048963

theorem tailTrace_2332298 : CollatzResearch.WordTrace tailWord_2332298 prefixEnd_2332298 1197589903520021107048963 := by
  unfold tailWord_2332298
  simp only [CollatzResearch.WordTrace]
  refine ⟨21266474126122536407813387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56710597669660097087502365 21266474126122536407813387)
  ·
    refine ⟨31899711189183804611720081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21266474126122536407813387 31899711189183804611720081)
    ·
      refine ⟨23924783391887853458790061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31899711189183804611720081 23924783391887853458790061)
      ·
        refine ⟨8971793771957945047046273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23924783391887853458790061 8971793771957945047046273)
        ·
          refine ⟨6728845328968458785284705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8971793771957945047046273 6728845328968458785284705)
          ·
            refine ⟨5046633996726344088963529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6728845328968458785284705 5046633996726344088963529)
            ·
              refine ⟨3784975497544758066722647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5046633996726344088963529 3784975497544758066722647)
              ·
                refine ⟨5677463246317137100083971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3784975497544758066722647 5677463246317137100083971)
                ·
                  refine ⟨8516194869475705650125957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5677463246317137100083971 8516194869475705650125957)
                  ·
                    refine ⟨1596786538026694809398617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8516194869475705650125957 1596786538026694809398617)
                    ·
                      refine ⟨1197589903520021107048963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596786538026694809398617 1197589903520021107048963)
                      ·
                        rfl

theorem cell23_2332298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_2332298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332298 prefixEnd_2332298 := by exact prefixLift 2332298
  have htrace : WordTrace (prefixWord ++ tailWord_2332298) baseStart_2332298 baseEnd_2332298 := by
    simpa [prefixWord, tailWord_2332298, baseEnd_2332298] using wordTrace_append hprefix tailTrace_2332298
  have hstable : (prefixWord ++ tailWord_2332298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332298).length < 2 ^ (prefixWord ++ tailWord_2332298).sum := by decide
  have hdescent : baseEnd_2332298 < baseStart_2332298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332319 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2332319 : Nat := 118140960795 + 2332319 * 2 ^ 59
def prefixEnd_2332319 : Nat := 4983230072969 + 3 ^ 40 * 2332319 * 2
def baseEnd_2332319 : Nat := 1197600686613765524886367

theorem tailTrace_2332319 : CollatzResearch.WordTrace tailWord_2332319 prefixEnd_2332319 1197600686613765524886367 := by
  unfold tailWord_2332319
  simp only [CollatzResearch.WordTrace]
  refine ⟨85066662437414066217768011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56711108291609377478512007 85066662437414066217768011)
  ·
    refine ⟨127599993656121099326652017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85066662437414066217768011 127599993656121099326652017)
    ·
      refine ⟨95699995242090824494989013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127599993656121099326652017 95699995242090824494989013)
      ·
        refine ⟨2242968638486503699101305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 95699995242090824494989013 2242968638486503699101305)
        ·
          refine ⟨1682226478864877774325979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2242968638486503699101305 1682226478864877774325979)
          ·
            refine ⟨2523339718297316661488969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682226478864877774325979 2523339718297316661488969)
            ·
              refine ⟨1892504788722987496116727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2523339718297316661488969 1892504788722987496116727)
              ·
                refine ⟨2838757183084481244175091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892504788722987496116727 2838757183084481244175091)
                ·
                  refine ⟨4258135774626721866262637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838757183084481244175091 4258135774626721866262637)
                  ·
                    refine ⟨1596800915485020699848489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4258135774626721866262637 1596800915485020699848489)
                    ·
                      refine ⟨1197600686613765524886367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596800915485020699848489 1197600686613765524886367)
                      ·
                        rfl

theorem cell23_2332319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2332319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332319 prefixEnd_2332319 := by exact prefixLift 2332319
  have htrace : WordTrace (prefixWord ++ tailWord_2332319) baseStart_2332319 baseEnd_2332319 := by
    simpa [prefixWord, tailWord_2332319, baseEnd_2332319] using wordTrace_append hprefix tailTrace_2332319
  have hstable : (prefixWord ++ tailWord_2332319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332319).length < 2 ^ (prefixWord ++ tailWord_2332319).sum := by decide
  have hdescent : baseEnd_2332319 < baseStart_2332319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332321 : List Nat := [1, 2, 3, 3, 2, 1, 1, 5, 5]
def baseStart_2332321 : Nat := 118140960795 + 2332321 * 2 ^ 59
def prefixEnd_2332321 : Nat := 4983230072969 + 3 ^ 40 * 2332321 * 2
def baseEnd_2332321 : Nat := 133066857063897168562373

theorem tailTrace_2332321 : CollatzResearch.WordTrace tailWord_2332321 prefixEnd_2332321 133066857063897168562373 := by
  unfold tailWord_2332321
  simp only [CollatzResearch.WordTrace]
  refine ⟨85066735383406820559340817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56711156922271213706227211 85066735383406820559340817)
  ·
    refine ⟨63800051537555115419505613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85066735383406820559340817 63800051537555115419505613)
    ·
      refine ⟨23925019326583168282314605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63800051537555115419505613 23925019326583168282314605)
      ·
        refine ⟨8971882247468688105867977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23925019326583168282314605 8971882247468688105867977)
        ·
          refine ⟨6728911685601516079400983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8971882247468688105867977 6728911685601516079400983)
          ·
            refine ⟨10093367528402274119101475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6728911685601516079400983 10093367528402274119101475)
            ·
              refine ⟨15140051292603411178652213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10093367528402274119101475 15140051292603411178652213)
              ·
                refine ⟨1419379808681569797998645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15140051292603411178652213 1419379808681569797998645)
                ·
                  refine ⟨133066857063897168562373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1419379808681569797998645 133066857063897168562373)
                  ·
                    rfl

theorem cell23_2332321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 5].length) (baseStart_2332321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332321 prefixEnd_2332321 := by exact prefixLift 2332321
  have htrace : WordTrace (prefixWord ++ tailWord_2332321) baseStart_2332321 baseEnd_2332321 := by
    simpa [prefixWord, tailWord_2332321, baseEnd_2332321] using wordTrace_append hprefix tailTrace_2332321
  have hstable : (prefixWord ++ tailWord_2332321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332321).length < 2 ^ (prefixWord ++ tailWord_2332321).sum := by decide
  have hdescent : baseEnd_2332321 < baseStart_2332321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332394 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 8]
def baseStart_2332394 : Nat := 118140960795 + 2332394 * 2 ^ 59
def prefixEnd_2332394 : Nat := 4983230072969 + 3 ^ 40 * 2332394 * 2
def baseEnd_2332394 : Nat := 133071021962539192383169

theorem tailTrace_2332394 : CollatzResearch.WordTrace tailWord_2332394 prefixEnd_2332394 133071021962539192383169 := by
  unfold tailWord_2332394
  simp only [CollatzResearch.WordTrace]
  refine ⟨21267349478035588506687059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56712931941428236017832157 21267349478035588506687059)
  ·
    refine ⟨31901024217053382760030589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21267349478035588506687059 31901024217053382760030589)
    ·
      refine ⟨11962884081395018535011471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31901024217053382760030589 11962884081395018535011471)
      ·
        refine ⟨17944326122092527802517207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11962884081395018535011471 17944326122092527802517207)
        ·
          refine ⟨26916489183138791703775811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17944326122092527802517207 26916489183138791703775811)
          ·
            refine ⟨40374733774708187555663717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26916489183138791703775811 40374733774708187555663717)
            ·
              refine ⟨7570262582757785166686947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40374733774708187555663717 7570262582757785166686947)
              ·
                refine ⟨11355393874136677750030421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7570262582757785166686947 11355393874136677750030421)
                ·
                  refine ⟨133071021962539192383169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11355393874136677750030421 133071021962539192383169)
                  ·
                    rfl

theorem cell23_2332394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_2332394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332394 prefixEnd_2332394 := by exact prefixLift 2332394
  have htrace : WordTrace (prefixWord ++ tailWord_2332394) baseStart_2332394 baseEnd_2332394 := by
    simpa [prefixWord, tailWord_2332394, baseEnd_2332394] using wordTrace_append hprefix tailTrace_2332394
  have hstable : (prefixWord ++ tailWord_2332394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332394).length < 2 ^ (prefixWord ++ tailWord_2332394).sum := by decide
  have hdescent : baseEnd_2332394 < baseStart_2332394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332448 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 2, 3, 2]
def baseStart_2332448 : Nat := 118140960795 + 2332448 * 2 ^ 59
def prefixEnd_2332448 : Nat := 4983230072969 + 3 ^ 40 * 2332448 * 2
def baseEnd_2332448 : Nat := 1197666925618195520173273

theorem tailTrace_2332448 : CollatzResearch.WordTrace tailWord_2332448 prefixEnd_2332448 1197666925618195520173273 := by
  unfold tailWord_2332448
  simp only [CollatzResearch.WordTrace]
  refine ⟨42535683726973360624606999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56714244969297814166142665 42535683726973360624606999)
  ·
    refine ⟨63803525590460040936910499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42535683726973360624606999 63803525590460040936910499)
    ·
      refine ⟨95705288385690061405365749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63803525590460040936910499 95705288385690061405365749)
      ·
        refine ⟨8972370786158443256753039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95705288385690061405365749 8972370786158443256753039)
        ·
          refine ⟨13458556179237664885129559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8972370786158443256753039 13458556179237664885129559)
          ·
            refine ⟨20187834268856497327694339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13458556179237664885129559 20187834268856497327694339)
            ·
              refine ⟨30281751403284745991541509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20187834268856497327694339 30281751403284745991541509)
              ·
                refine ⟨5677828388115889873414033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30281751403284745991541509 5677828388115889873414033)
                ·
                  refine ⟨4258371291086917405060525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5677828388115889873414033 4258371291086917405060525)
                  ·
                    refine ⟨1596889234157594026897697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4258371291086917405060525 1596889234157594026897697)
                    ·
                      refine ⟨1197666925618195520173273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596889234157594026897697 1197666925618195520173273)
                      ·
                        rfl

theorem cell23_2332448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_2332448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332448 prefixEnd_2332448 := by exact prefixLift 2332448
  have htrace : WordTrace (prefixWord ++ tailWord_2332448) baseStart_2332448 baseEnd_2332448 := by
    simpa [prefixWord, tailWord_2332448, baseEnd_2332448] using wordTrace_append hprefix tailTrace_2332448
  have hstable : (prefixWord ++ tailWord_2332448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332448).length < 2 ^ (prefixWord ++ tailWord_2332448).sum := by decide
  have hdescent : baseEnd_2332448 < baseStart_2332448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332478 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_2332478 : Nat := 118140960795 + 2332478 * 2 ^ 59
def prefixEnd_2332478 : Nat := 4983230072969 + 3 ^ 40 * 2332478 * 2
def baseEnd_2332478 : Nat := 1197682330037830402798135

theorem tailTrace_2332478 : CollatzResearch.WordTrace tailWord_2332478 prefixEnd_2332478 1197682330037830402798135 := by
  unfold tailWord_2332478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10634057705479754546600761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56714974429225357581870725 10634057705479754546600761)
  ·
    refine ⟨7975543279109815909950571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10634057705479754546600761 7975543279109815909950571)
    ·
      refine ⟨11963314918664723864925857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7975543279109815909950571 11963314918664723864925857)
      ·
        refine ⟨8972486188998542898694393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11963314918664723864925857 8972486188998542898694393)
        ·
          refine ⟨6729364641748907174020795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8972486188998542898694393 6729364641748907174020795)
          ·
            refine ⟨10094046962623360761031193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6729364641748907174020795 10094046962623360761031193)
            ·
              refine ⟨7570535221967520570773395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10094046962623360761031193 7570535221967520570773395)
              ·
                refine ⟨11355802832951280856160093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7570535221967520570773395 11355802832951280856160093)
                ·
                  refine ⟨4258426062356730321060035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11355802832951280856160093 4258426062356730321060035)
                  ·
                    refine ⟨6387639093535095481590053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4258426062356730321060035 6387639093535095481590053)
                    ·
                      refine ⟨1197682330037830402798135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6387639093535095481590053 1197682330037830402798135)
                      ·
                        rfl

theorem cell23_2332478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_2332478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332478 prefixEnd_2332478 := by exact prefixLift 2332478
  have htrace : WordTrace (prefixWord ++ tailWord_2332478) baseStart_2332478 baseEnd_2332478 := by
    simpa [prefixWord, tailWord_2332478, baseEnd_2332478] using wordTrace_append hprefix tailTrace_2332478
  have hstable : (prefixWord ++ tailWord_2332478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332478).length < 2 ^ (prefixWord ++ tailWord_2332478).sum := by decide
  have hdescent : baseEnd_2332478 < baseStart_2332478 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332492 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 1, 5]
def baseStart_2332492 : Nat := 118140960795 + 2332492 * 2 ^ 59
def prefixEnd_2332492 : Nat := 4983230072969 + 3 ^ 40 * 2332492 * 2
def baseEnd_2332492 : Nat := 399229839588997782674357

theorem tailTrace_2332492 : CollatzResearch.WordTrace tailWord_2332492 prefixEnd_2332492 399229839588997782674357 := by
  unfold tailWord_2332492
  simp only [CollatzResearch.WordTrace]
  refine ⟨42536486132893658381907865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56715314843858211175877153 42536486132893658381907865)
  ·
    refine ⟨31902364599670243786430899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42536486132893658381907865 31902364599670243786430899)
    ·
      refine ⟨47853546899505365679646349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31902364599670243786430899 47853546899505365679646349)
      ·
        refine ⟨17945080087314512129867381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47853546899505365679646349 17945080087314512129867381)
        ·
          refine ⟨1682351258185735512175067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17945080087314512129867381 1682351258185735512175067)
          ·
            refine ⟨2523526887278603268262601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682351258185735512175067 2523526887278603268262601)
            ·
              refine ⟨1892645165458952451196951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2523526887278603268262601 1892645165458952451196951)
              ·
                refine ⟨2838967748188428676795427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892645165458952451196951 2838967748188428676795427)
                ·
                  refine ⟨4258451622282643015193141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2838967748188428676795427 4258451622282643015193141)
                  ·
                    refine ⟨399229839588997782674357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4258451622282643015193141 399229839588997782674357)
                    ·
                      rfl

theorem cell23_2332492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_2332492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332492 prefixEnd_2332492 := by exact prefixLift 2332492
  have htrace : WordTrace (prefixWord ++ tailWord_2332492) baseStart_2332492 baseEnd_2332492 := by
    simpa [prefixWord, tailWord_2332492, baseEnd_2332492] using wordTrace_append hprefix tailTrace_2332492
  have hstable : (prefixWord ++ tailWord_2332492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332492).length < 2 ^ (prefixWord ++ tailWord_2332492).sum := by decide
  have hdescent : baseEnd_2332492 < baseStart_2332492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332504 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2332504 : Nat := 118140960795 + 2332504 * 2 ^ 59
def prefixEnd_2332504 : Nat := 4983230072969 + 3 ^ 40 * 2332504 * 2
def baseEnd_2332504 : Nat := 1197695680534847301073015

theorem tailTrace_2332504 : CollatzResearch.WordTrace tailWord_2332504 prefixEnd_2332504 1197695680534847301073015 := by
  unfold tailWord_2332504
  simp only [CollatzResearch.WordTrace]
  refine ⟨42536704970871921406626283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56715606627829228542168377 42536704970871921406626283)
  ·
    refine ⟨63805057456307882109939425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42536704970871921406626283 63805057456307882109939425)
    ·
      refine ⟨47853793092230911582454569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63805057456307882109939425 47853793092230911582454569)
      ·
        refine ⟨35890344819173183686840927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47853793092230911582454569 35890344819173183686840927)
        ·
          refine ⟨53835517228759775530261391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35890344819173183686840927 53835517228759775530261391)
          ·
            refine ⟨80753275843139663295392087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53835517228759775530261391 80753275843139663295392087)
            ·
              refine ⟨121129913764709494943088131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80753275843139663295392087 121129913764709494943088131)
              ·
                refine ⟨181694870647064242414632197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121129913764709494943088131 181694870647064242414632197)
                ·
                  refine ⟨34067788246324545452743537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181694870647064242414632197 34067788246324545452743537)
                  ·
                    refine ⟨25550841184743409089557653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34067788246324545452743537 25550841184743409089557653)
                    ·
                      refine ⟨1197695680534847301073015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25550841184743409089557653 1197695680534847301073015)
                      ·
                        rfl

theorem cell23_2332504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2332504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332504 prefixEnd_2332504 := by exact prefixLift 2332504
  have htrace : WordTrace (prefixWord ++ tailWord_2332504) baseStart_2332504 baseEnd_2332504 := by
    simpa [prefixWord, tailWord_2332504, baseEnd_2332504] using wordTrace_append hprefix tailTrace_2332504
  have hstable : (prefixWord ++ tailWord_2332504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332504).length < 2 ^ (prefixWord ++ tailWord_2332504).sum := by decide
  have hdescent : baseEnd_2332504 < baseStart_2332504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332512 : List Nat := [2, 1, 1, 3, 3, 2, 2, 4, 1, 2, 2]
def baseStart_2332512 : Nat := 118140960795 + 2332512 * 2 ^ 59
def prefixEnd_2332512 : Nat := 4983230072969 + 3 ^ 40 * 2332512 * 2
def baseEnd_2332512 : Nat := 1197699788380083269772979

theorem tailTrace_2332512 : CollatzResearch.WordTrace tailWord_2332512 prefixEnd_2332512 1197699788380083269772979 := by
  unfold tailWord_2332512
  simp only [CollatzResearch.WordTrace]
  refine ⟨42536850862857430089771895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56715801150476573453029193 42536850862857430089771895)
  ·
    refine ⟨63805276294286145134657843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42536850862857430089771895 63805276294286145134657843)
    ·
      refine ⟨95707914441429217701986765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63805276294286145134657843 95707914441429217701986765)
      ·
        refine ⟨35890467915535956638245037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95707914441429217701986765 35890467915535956638245037)
        ·
          refine ⟨13458925468325983739341889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35890467915535956638245037 13458925468325983739341889)
          ·
            refine ⟨10094194101244487804506417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13458925468325983739341889 10094194101244487804506417)
            ·
              refine ⟨7570645575933365853379813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10094194101244487804506417 7570645575933365853379813)
              ·
                refine ⟨1419496045487506097508715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7570645575933365853379813 1419496045487506097508715)
                ·
                  refine ⟨2129244068231259146263073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419496045487506097508715 2129244068231259146263073)
                  ·
                    refine ⟨1596933051173444359697305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2129244068231259146263073 1596933051173444359697305)
                    ·
                      refine ⟨1197699788380083269772979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596933051173444359697305 1197699788380083269772979)
                      ·
                        rfl

theorem cell23_2332512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_2332512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332512 prefixEnd_2332512 := by exact prefixLift 2332512
  have htrace : WordTrace (prefixWord ++ tailWord_2332512) baseStart_2332512 baseEnd_2332512 := by
    simpa [prefixWord, tailWord_2332512, baseEnd_2332512] using wordTrace_append hprefix tailTrace_2332512
  have hstable : (prefixWord ++ tailWord_2332512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332512).length < 2 ^ (prefixWord ++ tailWord_2332512).sum := by decide
  have hdescent : baseEnd_2332512 < baseStart_2332512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332522 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 1, 6]
def baseStart_2332522 : Nat := 118140960795 + 2332522 * 2 ^ 59
def prefixEnd_2332522 : Nat := 4983230072969 + 3 ^ 40 * 2332522 * 2
def baseEnd_2332522 : Nat := 399234974395542743549311

theorem tailTrace_2332522 : CollatzResearch.WordTrace tailWord_2332522 prefixEnd_2332522 399234974395542743549311 := by
  unfold tailWord_2332522
  simp only [CollatzResearch.WordTrace]
  refine ⟨21268516613919657971851955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56716044303785754591605213 21268516613919657971851955)
  ·
    refine ⟨31902774920879486957777933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21268516613919657971851955 31902774920879486957777933)
    ·
      refine ⟨11963540595329807609166725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31902774920879486957777933 11963540595329807609166725)
      ·
        refine ⟨2243163861624338926718761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11963540595329807609166725 2243163861624338926718761)
        ·
          refine ⟨1682372896218254195039071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2243163861624338926718761 1682372896218254195039071)
          ·
            refine ⟨2523559344327381292558607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1682372896218254195039071 2523559344327381292558607)
            ·
              refine ⟨3785339016491071938837911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523559344327381292558607 3785339016491071938837911)
              ·
                refine ⟨5678008524736607908256867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3785339016491071938837911 5678008524736607908256867)
                ·
                  refine ⟨8517012787104911862385301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5678008524736607908256867 8517012787104911862385301)
                  ·
                    refine ⟨399234974395542743549311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8517012787104911862385301 399234974395542743549311)
                    ·
                      rfl

theorem cell23_2332522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_2332522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332522 prefixEnd_2332522 := by exact prefixLift 2332522
  have htrace : WordTrace (prefixWord ++ tailWord_2332522) baseStart_2332522 baseEnd_2332522 := by
    simpa [prefixWord, tailWord_2332522, baseEnd_2332522] using wordTrace_append hprefix tailTrace_2332522
  have hstable : (prefixWord ++ tailWord_2332522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332522).length < 2 ^ (prefixWord ++ tailWord_2332522).sum := by decide
  have hdescent : baseEnd_2332522 < baseStart_2332522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332538 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2]
def baseStart_2332538 : Nat := 118140960795 + 2332538 * 2 ^ 59
def prefixEnd_2332538 : Nat := 4983230072969 + 3 ^ 40 * 2332538 * 2
def baseEnd_2332538 : Nat := 1197713138877100168047859

theorem tailTrace_2332538 : CollatzResearch.WordTrace tailWord_2332538 prefixEnd_2332538 1197713138877100168047859 := by
  unfold tailWord_2332538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21268662505905166654997567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56716433349080444413326845 21268662505905166654997567)
  ·
    refine ⟨31902993758857749982496351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21268662505905166654997567 31902993758857749982496351)
    ·
      refine ⟨47854490638286624973744527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31902993758857749982496351 47854490638286624973744527)
      ·
        refine ⟨71781735957429937460616791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47854490638286624973744527 71781735957429937460616791)
        ·
          refine ⟨107672603936144906190925187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71781735957429937460616791 107672603936144906190925187)
          ·
            refine ⟨161508905904217359286387781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107672603936144906190925187 161508905904217359286387781)
            ·
              refine ⟨30282919857040754866197709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 161508905904217359286387781 30282919857040754866197709)
              ·
                refine ⟨11356094946390283074824141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30282919857040754866197709 11356094946390283074824141)
                ·
                  refine ⟨4258535604896356153059053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11356094946390283074824141 4258535604896356153059053)
                  ·
                    refine ⟨1596950851836133557397145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4258535604896356153059053 1596950851836133557397145)
                    ·
                      refine ⟨1197713138877100168047859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1596950851836133557397145 1197713138877100168047859)
                      ·
                        rfl

theorem cell23_2332538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_2332538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332538 prefixEnd_2332538 := by exact prefixLift 2332538
  have htrace : WordTrace (prefixWord ++ tailWord_2332538) baseStart_2332538 baseEnd_2332538 := by
    simpa [prefixWord, tailWord_2332538, baseEnd_2332538] using wordTrace_append hprefix tailTrace_2332538
  have hstable : (prefixWord ++ tailWord_2332538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332538).length < 2 ^ (prefixWord ++ tailWord_2332538).sum := by decide
  have hdescent : baseEnd_2332538 < baseStart_2332538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332581 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_2332581 : Nat := 118140960795 + 2332581 * 2 ^ 59
def prefixEnd_2332581 : Nat := 4983230072969 + 3 ^ 40 * 2332581 * 2
def baseEnd_2332581 : Nat := 1197735218545243499810161

theorem tailTrace_2332581 : CollatzResearch.WordTrace tailWord_2332581 prefixEnd_2332581 1197735218545243499810161 := by
  unfold tailWord_2332581
  simp only [CollatzResearch.WordTrace]
  refine ⟨85076218362464884963805597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56717478908309923309203731 85076218362464884963805597)
  ·
    refine ⟨31903581885924331861427099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85076218362464884963805597 31903581885924331861427099)
    ·
      refine ⟨47855372828886497792140649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31903581885924331861427099 47855372828886497792140649)
      ·
        refine ⟨35891529621664873344105487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47855372828886497792140649 35891529621664873344105487)
        ·
          refine ⟨53837294432497310016158231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35891529621664873344105487 53837294432497310016158231)
          ·
            refine ⟨80755941648745965024237347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53837294432497310016158231 80755941648745965024237347)
            ·
              refine ⟨121133912473118947536356021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80755941648745965024237347 121133912473118947536356021)
              ·
                refine ⟨11356304294354901331533377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121133912473118947536356021 11356304294354901331533377)
                ·
                  refine ⟨8517228220766175998650033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11356304294354901331533377 8517228220766175998650033)
                  ·
                    refine ⟨6387921165574631998987525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8517228220766175998650033 6387921165574631998987525)
                    ·
                      refine ⟨1197735218545243499810161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6387921165574631998987525 1197735218545243499810161)
                      ·
                        rfl

theorem cell23_2332581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_2332581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332581 prefixEnd_2332581 := by exact prefixLift 2332581
  have htrace : WordTrace (prefixWord ++ tailWord_2332581) baseStart_2332581 baseEnd_2332581 := by
    simpa [prefixWord, tailWord_2332581, baseEnd_2332581] using wordTrace_append hprefix tailTrace_2332581
  have hstable : (prefixWord ++ tailWord_2332581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332581).length < 2 ^ (prefixWord ++ tailWord_2332581).sum := by decide
  have hdescent : baseEnd_2332581 < baseStart_2332581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332608 : List Nat := [2, 1, 1, 2, 3, 2, 2, 5, 5]
def baseStart_2332608 : Nat := 118140960795 + 2332608 * 2 ^ 59
def prefixEnd_2332608 : Nat := 4983230072969 + 3 ^ 40 * 2332608 * 2
def baseEnd_2332608 : Nat := 133083231391434988241393

theorem tailTrace_2332608 : CollatzResearch.WordTrace tailWord_2332608 prefixEnd_2332608 133083231391434988241393 := by
  unfold tailWord_2332608
  simp only [CollatzResearch.WordTrace]
  refine ⟨42538601566683534287519239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56718135422244712383358985 42538601566683534287519239)
  ·
    refine ⟨63807902350025301431278859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42538601566683534287519239 63807902350025301431278859)
    ·
      refine ⟨95711853525037952146918289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63807902350025301431278859 95711853525037952146918289)
      ·
        refine ⟨71783890143778464110188717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95711853525037952146918289 71783890143778464110188717)
        ·
          refine ⟨26918958803916924041320769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71783890143778464110188717 26918958803916924041320769)
          ·
            refine ⟨20189219102937693030990577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26918958803916924041320769 20189219102937693030990577)
            ·
              refine ⟨15141914327203269773242933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20189219102937693030990577 15141914327203269773242933)
              ·
                refine ⟨1419554468175306541241525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15141914327203269773242933 1419554468175306541241525)
                ·
                  refine ⟨133083231391434988241393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1419554468175306541241525 133083231391434988241393)
                  ·
                    rfl

theorem cell23_2332608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 5].length) (baseStart_2332608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332608 prefixEnd_2332608 := by exact prefixLift 2332608
  have htrace : WordTrace (prefixWord ++ tailWord_2332608) baseStart_2332608 baseEnd_2332608 := by
    simpa [prefixWord, tailWord_2332608, baseEnd_2332608] using wordTrace_append hprefix tailTrace_2332608
  have hstable : (prefixWord ++ tailWord_2332608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332608).length < 2 ^ (prefixWord ++ tailWord_2332608).sum := by decide
  have hdescent : baseEnd_2332608 < baseStart_2332608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332631 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_2332631 : Nat := 118140960795 + 2332631 * 2 ^ 59
def prefixEnd_2332631 : Nat := 4983230072969 + 3 ^ 40 * 2332631 * 2
def baseEnd_2332631 : Nat := 1197760892577968304184931

theorem tailTrace_2332631 : CollatzResearch.WordTrace tailWord_2332631 prefixEnd_2332631 1197760892577968304184931 := by
  unfold tailWord_2332631
  simp only [CollatzResearch.WordTrace]
  refine ⟨85078042012283743503125747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56718694674855829002083831 85078042012283743503125747)
  ·
    refine ⟨127617063018425615254688621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85078042012283743503125747 127617063018425615254688621)
    ·
      refine ⟨47856398631909605720508233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127617063018425615254688621 47856398631909605720508233)
      ·
        refine ⟨35892298973932204290381175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47856398631909605720508233 35892298973932204290381175)
        ·
          refine ⟨53838448460898306435571763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35892298973932204290381175 53838448460898306435571763)
          ·
            refine ⟨80757672691347459653357645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53838448460898306435571763 80757672691347459653357645)
            ·
              refine ⟨30284127259255297370009117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80757672691347459653357645 30284127259255297370009117)
              ·
                refine ⟨11356547722220736513753419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30284127259255297370009117 11356547722220736513753419)
                ·
                  refine ⟨17034821583331104770630129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11356547722220736513753419 17034821583331104770630129)
                  ·
                    refine ⟨12776116187498328577972597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17034821583331104770630129 12776116187498328577972597)
                    ·
                      refine ⟨1197760892577968304184931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12776116187498328577972597 1197760892577968304184931)
                      ·
                        rfl

theorem cell23_2332631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_2332631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332631 prefixEnd_2332631 := by exact prefixLift 2332631
  have htrace : WordTrace (prefixWord ++ tailWord_2332631) baseStart_2332631 baseEnd_2332631 := by
    simpa [prefixWord, tailWord_2332631, baseEnd_2332631] using wordTrace_append hprefix tailTrace_2332631
  have hstable : (prefixWord ++ tailWord_2332631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332631).length < 2 ^ (prefixWord ++ tailWord_2332631).sum := by decide
  have hdescent : baseEnd_2332631 < baseStart_2332631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332636 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_2332636 : Nat := 118140960795 + 2332636 * 2 ^ 59
def prefixEnd_2332636 : Nat := 4983230072969 + 3 ^ 40 * 2332636 * 2
def baseEnd_2332636 : Nat := 1197763459981240784622409

theorem tailTrace_2332636 : CollatzResearch.WordTrace tailWord_2332636 prefixEnd_2332636 1197763459981240784622409 := by
  unfold tailWord_2332636
  simp only [CollatzResearch.WordTrace]
  refine ⟨42539112188632814678528881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56718816251510419571371841 42539112188632814678528881)
  ·
    refine ⟨31904334141474611008896661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42539112188632814678528881 31904334141474611008896661)
    ·
      refine ⟨1495515662881622391042031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31904334141474611008896661 1495515662881622391042031)
      ·
        refine ⟨2243273494322433586563047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1495515662881622391042031 2243273494322433586563047)
        ·
          refine ⟨3364910241483650379844571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2243273494322433586563047 3364910241483650379844571)
          ·
            refine ⟨5047365362225475569766857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3364910241483650379844571 5047365362225475569766857)
            ·
              refine ⟨3785524021669106677325143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5047365362225475569766857 3785524021669106677325143)
              ·
                refine ⟨5678286032503660015987715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3785524021669106677325143 5678286032503660015987715)
                ·
                  refine ⟨8517429048755490023981573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5678286032503660015987715 8517429048755490023981573)
                  ·
                    refine ⟨1597017946641654379496545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8517429048755490023981573 1597017946641654379496545)
                    ·
                      refine ⟨1197763459981240784622409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1597017946641654379496545 1197763459981240784622409)
                      ·
                        rfl

theorem cell23_2332636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_2332636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332636 prefixEnd_2332636 := by exact prefixLift 2332636
  have htrace : WordTrace (prefixWord ++ tailWord_2332636) baseStart_2332636 baseEnd_2332636 := by
    simpa [prefixWord, tailWord_2332636, baseEnd_2332636] using wordTrace_append hprefix tailTrace_2332636
  have hstable : (prefixWord ++ tailWord_2332636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332636).length < 2 ^ (prefixWord ++ tailWord_2332636).sum := by decide
  have hdescent : baseEnd_2332636 < baseStart_2332636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332668 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_2332668 : Nat := 118140960795 + 2332668 * 2 ^ 59
def prefixEnd_2332668 : Nat := 4983230072969 + 3 ^ 40 * 2332668 * 2
def baseEnd_2332668 : Nat := 399259963787394886474087

theorem tailTrace_2332668 : CollatzResearch.WordTrace tailWord_2332668 prefixEnd_2332668 399259963787394886474087 := by
  unfold tailWord_2332668
  simp only [CollatzResearch.WordTrace]
  refine ⟨42539695756574849411111329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56719594342099799214815105 42539695756574849411111329)
  ·
    refine ⟨31904771817431137058333497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42539695756574849411111329 31904771817431137058333497)
    ·
      refine ⟨23928578863073352793750123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31904771817431137058333497 23928578863073352793750123)
      ·
        refine ⟨35892868294610029190625185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23928578863073352793750123 35892868294610029190625185)
        ·
          refine ⟨26919651220957521892968889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35892868294610029190625185 26919651220957521892968889)
          ·
            refine ⟨20189738415718141419726667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26919651220957521892968889 20189738415718141419726667)
            ·
              refine ⟨30284607623577212129590001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20189738415718141419726667 30284607623577212129590001)
              ·
                refine ⟨22713455717682909097192501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30284607623577212129590001 22713455717682909097192501)
                ·
                  refine ⟨2129386473532772727861797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22713455717682909097192501 2129386473532772727861797)
                  ·
                    refine ⟨399259963787394886474087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2129386473532772727861797 399259963787394886474087)
                    ·
                      rfl

theorem cell23_2332668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_2332668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332668 prefixEnd_2332668 := by exact prefixLift 2332668
  have htrace : WordTrace (prefixWord ++ tailWord_2332668) baseStart_2332668 baseEnd_2332668 := by
    simpa [prefixWord, tailWord_2332668, baseEnd_2332668] using wordTrace_append hprefix tailTrace_2332668
  have hstable : (prefixWord ++ tailWord_2332668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332668).length < 2 ^ (prefixWord ++ tailWord_2332668).sum := by decide
  have hdescent : baseEnd_2332668 < baseStart_2332668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332671 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 4]
def baseStart_2332671 : Nat := 118140960795 + 2332671 * 2 ^ 59
def prefixEnd_2332671 : Nat := 4983230072969 + 3 ^ 40 * 2332671 * 2
def baseEnd_2332671 : Nat := 1197781431804148147684747

theorem tailTrace_2332671 : CollatzResearch.WordTrace tailWord_2332671 prefixEnd_2332671 1197781431804148147684747 := by
  unfold tailWord_2332671
  simp only [CollatzResearch.WordTrace]
  refine ⟨85079500932138830334581867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56719667288092553556387911 85079500932138830334581867)
  ·
    refine ⟨127619251398208245501872801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85079500932138830334581867 127619251398208245501872801)
    ·
      refine ⟨95714438548656184126404601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127619251398208245501872801 95714438548656184126404601)
      ·
        refine ⟨71785828911492138094803451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95714438548656184126404601 71785828911492138094803451)
        ·
          refine ⟨107678743367238207142205177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71785828911492138094803451 107678743367238207142205177)
          ·
            refine ⟨80759057525428655356653883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107678743367238207142205177 80759057525428655356653883)
            ·
              refine ⟨121138586288142983034980825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80759057525428655356653883 121138586288142983034980825)
              ·
                refine ⟨90853939716107237276235619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121138586288142983034980825 90853939716107237276235619)
                ·
                  refine ⟨136280909574160855914353429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90853939716107237276235619 136280909574160855914353429)
                  ·
                    refine ⟨6388167636288790120985317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 136280909574160855914353429 6388167636288790120985317)
                    ·
                      refine ⟨1197781431804148147684747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6388167636288790120985317 1197781431804148147684747)
                      ·
                        rfl

theorem cell23_2332671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 4].length) (baseStart_2332671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332671 prefixEnd_2332671 := by exact prefixLift 2332671
  have htrace : WordTrace (prefixWord ++ tailWord_2332671) baseStart_2332671 baseEnd_2332671 := by
    simpa [prefixWord, tailWord_2332671, baseEnd_2332671] using wordTrace_append hprefix tailTrace_2332671
  have hstable : (prefixWord ++ tailWord_2332671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332671).length < 2 ^ (prefixWord ++ tailWord_2332671).sum := by decide
  have hdescent : baseEnd_2332671 < baseStart_2332671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332725 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_2332725 : Nat := 118140960795 + 2332725 * 2 ^ 59
def prefixEnd_2332725 : Nat := 4983230072969 + 3 ^ 40 * 2332725 * 2
def baseEnd_2332725 : Nat := 1197809159759490936409499

theorem tailTrace_2332725 : CollatzResearch.WordTrace tailWord_2332725 prefixEnd_2332725 1197809159759490936409499 := by
  unfold tailWord_2332725
  simp only [CollatzResearch.WordTrace]
  refine ⟨85081470473943197557047629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56720980315962131704698419 85081470473943197557047629)
  ·
    refine ⟨31905551427728699083892861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85081470473943197557047629 31905551427728699083892861)
    ·
      refine ⟨11964581785398262156459823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31905551427728699083892861 11964581785398262156459823)
      ·
        refine ⟨17946872678097393234689735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11964581785398262156459823 17946872678097393234689735)
        ·
          refine ⟨26920309017146089852034603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17946872678097393234689735 26920309017146089852034603)
          ·
            refine ⟨40380463525719134778051905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26920309017146089852034603 40380463525719134778051905)
            ·
              refine ⟨30285347644289351083538929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40380463525719134778051905 30285347644289351083538929)
              ·
                refine ⟨22714010733217013312654197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30285347644289351083538929 22714010733217013312654197)
                ·
                  refine ⟨2129438506239094998061331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22714010733217013312654197 2129438506239094998061331)
                  ·
                    refine ⟨3194157759358642497091997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2129438506239094998061331 3194157759358642497091997)
                    ·
                      refine ⟨1197809159759490936409499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3194157759358642497091997 1197809159759490936409499)
                      ·
                        rfl

theorem cell23_2332725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_2332725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332725 prefixEnd_2332725 := by exact prefixLift 2332725
  have htrace : WordTrace (prefixWord ++ tailWord_2332725) baseStart_2332725 baseEnd_2332725 := by
    simpa [prefixWord, tailWord_2332725, baseEnd_2332725] using wordTrace_append hprefix tailTrace_2332725
  have hstable : (prefixWord ++ tailWord_2332725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332725).length < 2 ^ (prefixWord ++ tailWord_2332725).sum := by decide
  have hdescent : baseEnd_2332725 < baseStart_2332725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332735 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 4, 3, 2]
def baseStart_2332735 : Nat := 118140960795 + 2332735 * 2 ^ 59
def prefixEnd_2332735 : Nat := 4983230072969 + 3 ^ 40 * 2332735 * 2
def baseEnd_2332735 : Nat := 1197814294566035897284453

theorem tailTrace_2332735 : CollatzResearch.WordTrace tailWord_2332735 prefixEnd_2332735 1197814294566035897284453 := by
  unfold tailWord_2332735
  simp only [CollatzResearch.WordTrace]
  refine ⟨85081835203906969264911659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56721223469271312843274439 85081835203906969264911659)
  ·
    refine ⟨127622752805860453897367489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85081835203906969264911659 127622752805860453897367489)
    ·
      refine ⟨95717064604395340423025617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127622752805860453897367489 95717064604395340423025617)
      ·
        refine ⟨71787798453296505317269213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95717064604395340423025617 71787798453296505317269213)
        ·
          refine ⟨26920424419986189493975955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71787798453296505317269213 26920424419986189493975955)
          ·
            refine ⟨40380636629979284240963933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26920424419986189493975955 40380636629979284240963933)
            ·
              refine ⟨15142738736242231590361475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40380636629979284240963933 15142738736242231590361475)
              ·
                refine ⟨22714108104363347385542213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15142738736242231590361475 22714108104363347385542213)
                ·
                  refine ⟨4258895269568127634789165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22714108104363347385542213 4258895269568127634789165)
                  ·
                    refine ⟨1597085726088047863045937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4258895269568127634789165 1597085726088047863045937)
                    ·
                      refine ⟨1197814294566035897284453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1597085726088047863045937 1197814294566035897284453)
                      ·
                        rfl

theorem cell23_2332735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 3, 2].length) (baseStart_2332735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332735 prefixEnd_2332735 := by exact prefixLift 2332735
  have htrace : WordTrace (prefixWord ++ tailWord_2332735) baseStart_2332735 baseEnd_2332735 := by
    simpa [prefixWord, tailWord_2332735, baseEnd_2332735] using wordTrace_append hprefix tailTrace_2332735
  have hstable : (prefixWord ++ tailWord_2332735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332735).length < 2 ^ (prefixWord ++ tailWord_2332735).sum := by decide
  have hdescent : baseEnd_2332735 < baseStart_2332735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332805 : List Nat := [1, 3, 1, 1, 5, 3, 1, 8]
def baseStart_2332805 : Nat := 118140960795 + 2332805 * 2 ^ 59
def prefixEnd_2332805 : Nat := 4983230072969 + 3 ^ 40 * 2332805 * 2
def baseEnd_2332805 : Nat := 44364823637475949015153

theorem tailTrace_2332805 : CollatzResearch.WordTrace tailWord_2332805 prefixEnd_2332805 44364823637475949015153 := by
  unfold tailWord_2332805
  simp only [CollatzResearch.WordTrace]
  refine ⟨85084388313653371219959869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56722925542435580813306579 85084388313653371219959869)
  ·
    refine ⟨31906645617620014207484951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85084388313653371219959869 31906645617620014207484951)
    ·
      refine ⟨47859968426430021311227427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31906645617620014207484951 47859968426430021311227427)
      ·
        refine ⟨71789952639645031966841141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47859968426430021311227427 71789952639645031966841141)
        ·
          refine ⟨6730308059966721746891357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71789952639645031966841141 6730308059966721746891357)
          ·
            refine ⟨2523865522487520655084259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6730308059966721746891357 2523865522487520655084259)
            ·
              refine ⟨3785798283731280982626389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2523865522487520655084259 3785798283731280982626389)
              ·
                refine ⟨44364823637475949015153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3785798283731280982626389 44364823637475949015153)
                ·
                  rfl

theorem cell23_2332805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 8].length) (baseStart_2332805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332805 prefixEnd_2332805 := by exact prefixLift 2332805
  have htrace : WordTrace (prefixWord ++ tailWord_2332805) baseStart_2332805 baseEnd_2332805 := by
    simpa [prefixWord, tailWord_2332805, baseEnd_2332805] using wordTrace_append hprefix tailTrace_2332805
  have hstable : (prefixWord ++ tailWord_2332805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332805).length < 2 ^ (prefixWord ++ tailWord_2332805).sum := by decide
  have hdescent : baseEnd_2332805 < baseStart_2332805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332836 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 1, 2, 3]
def baseStart_2332836 : Nat := 118140960795 + 2332836 * 2 ^ 59
def prefixEnd_2332836 : Nat := 4983230072969 + 3 ^ 40 * 2332836 * 2
def baseEnd_2332836 : Nat := 1197866156112140002121489

theorem tailTrace_2332836 : CollatzResearch.WordTrace tailWord_2332836 prefixEnd_2332836 1197866156112140002121489 := by
  unfold tailWord_2332836
  simp only [CollatzResearch.WordTrace]
  refine ⟨42542759488270531757169181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56723679317694042342892241 42542759488270531757169181)
  ·
    refine ⟨15953534808101449408938443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42542759488270531757169181 15953534808101449408938443)
    ·
      refine ⟨23930302212152174113407665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15953534808101449408938443 23930302212152174113407665)
      ·
        refine ⟨17947726659114130585055749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23930302212152174113407665 17947726659114130585055749)
        ·
          refine ⟨3365198748583899484697953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17947726659114130585055749 3365198748583899484697953)
          ·
            refine ⟨2523899061437924613523465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3365198748583899484697953 2523899061437924613523465)
            ·
              refine ⟨1892924296078443460142599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2523899061437924613523465 1892924296078443460142599)
              ·
                refine ⟨2839386444117665190213899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1892924296078443460142599 2839386444117665190213899)
                ·
                  refine ⟨4259079666176497785320849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2839386444117665190213899 4259079666176497785320849)
                  ·
                    refine ⟨3194309749632373338990637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4259079666176497785320849 3194309749632373338990637)
                    ·
                      refine ⟨1197866156112140002121489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3194309749632373338990637 1197866156112140002121489)
                      ·
                        rfl

theorem cell23_2332836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_2332836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332836 prefixEnd_2332836 := by exact prefixLift 2332836
  have htrace : WordTrace (prefixWord ++ tailWord_2332836) baseStart_2332836 baseEnd_2332836 := by
    simpa [prefixWord, tailWord_2332836, baseEnd_2332836] using wordTrace_append hprefix tailTrace_2332836
  have hstable : (prefixWord ++ tailWord_2332836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332836).length < 2 ^ (prefixWord ++ tailWord_2332836).sum := by decide
  have hdescent : baseEnd_2332836 < baseStart_2332836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332849 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2332849 : Nat := 118140960795 + 2332849 * 2 ^ 59
def prefixEnd_2332849 : Nat := 4983230072969 + 3 ^ 40 * 2332849 * 2
def baseEnd_2332849 : Nat := 1197872831360648451258929

theorem tailTrace_2332849 : CollatzResearch.WordTrace tailWord_2332849 prefixEnd_2332849 1197872831360648451258929 := by
  unfold tailWord_2332849
  simp only [CollatzResearch.WordTrace]
  refine ⟨85085993125493966734561601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56723995416995977823041067 85085993125493966734561601)
  ·
    refine ⟨63814494844120475050921201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85085993125493966734561601 63814494844120475050921201)
    ·
      refine ⟨47860871133090356288190901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63814494844120475050921201 47860871133090356288190901)
      ·
        refine ⟨4486956668727220902017897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47860871133090356288190901 4486956668727220902017897)
        ·
          refine ⟨3365217501545415676513423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4486956668727220902017897 3365217501545415676513423)
          ·
            refine ⟨5047826252318123514770135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3365217501545415676513423 5047826252318123514770135)
            ·
              refine ⟨7571739378477185272155203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5047826252318123514770135 7571739378477185272155203)
              ·
                refine ⟨11357609067715777908232805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7571739378477185272155203 11357609067715777908232805)
                ·
                  refine ⟨2129551700196708357793651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11357609067715777908232805 2129551700196708357793651)
                  ·
                    refine ⟨3194327550295062536690477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2129551700196708357793651 3194327550295062536690477)
                    ·
                      refine ⟨1197872831360648451258929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3194327550295062536690477 1197872831360648451258929)
                      ·
                        rfl

theorem cell23_2332849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2332849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332849 prefixEnd_2332849 := by exact prefixLift 2332849
  have htrace : WordTrace (prefixWord ++ tailWord_2332849) baseStart_2332849 baseEnd_2332849 := by
    simpa [prefixWord, tailWord_2332849, baseEnd_2332849] using wordTrace_append hprefix tailTrace_2332849
  have hstable : (prefixWord ++ tailWord_2332849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332849).length < 2 ^ (prefixWord ++ tailWord_2332849).sum := by decide
  have hdescent : baseEnd_2332849 < baseStart_2332849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332866 : List Nat := [3, 5, 1, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2332866 : Nat := 118140960795 + 2332866 * 2 ^ 59
def prefixEnd_2332866 : Nat := 4983230072969 + 3 ^ 40 * 2332866 * 2
def baseEnd_2332866 : Nat := 1197881560531774884746351

theorem tailTrace_2332866 : CollatzResearch.WordTrace tailWord_2332866 prefixEnd_2332866 1197881560531774884746351 := by
  unfold tailWord_2332866
  simp only [CollatzResearch.WordTrace]
  refine ⟨21271653291608094659482613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56724408777621585758620301 21271653291608094659482613)
  ·
    refine ⟨1994217496088258874326495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21271653291608094659482613 1994217496088258874326495)
    ·
      refine ⟨2991326244132388311489743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1994217496088258874326495 2991326244132388311489743)
      ·
        refine ⟨4486989366198582467234615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2991326244132388311489743 4486989366198582467234615)
        ·
          refine ⟨6730484049297873700851923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4486989366198582467234615 6730484049297873700851923)
          ·
            refine ⟨10095726073946810551277885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6730484049297873700851923 10095726073946810551277885)
            ·
              refine ⟨3785897277730053956729207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10095726073946810551277885 3785897277730053956729207)
              ·
                refine ⟨5678845916595080935093811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3785897277730053956729207 5678845916595080935093811)
                ·
                  refine ⟨8518268874892621402640717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5678845916595080935093811 8518268874892621402640717)
                  ·
                    refine ⟨3194350828084733025990269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8518268874892621402640717 3194350828084733025990269)
                    ·
                      refine ⟨1197881560531774884746351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3194350828084733025990269 1197881560531774884746351)
                      ·
                        rfl

theorem cell23_2332866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2332866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332866 prefixEnd_2332866 := by exact prefixLift 2332866
  have htrace : WordTrace (prefixWord ++ tailWord_2332866) baseStart_2332866 baseEnd_2332866 := by
    simpa [prefixWord, tailWord_2332866, baseEnd_2332866] using wordTrace_append hprefix tailTrace_2332866
  have hstable : (prefixWord ++ tailWord_2332866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332866).length < 2 ^ (prefixWord ++ tailWord_2332866).sum := by decide
  have hdescent : baseEnd_2332866 < baseStart_2332866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2332942 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 2, 5]
def baseStart_2332942 : Nat := 118140960795 + 2332942 * 2 ^ 59
def prefixEnd_2332942 : Nat := 4983230072969 + 3 ^ 40 * 2332942 * 2
def baseEnd_2332942 : Nat := 399306861687172195798667

theorem tailTrace_2332942 : CollatzResearch.WordTrace tailWord_2332942 prefixEnd_2332942 399306861687172195798667 := by
  unfold tailWord_2332942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10636173139269630452212135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56726256742771362411798053 10636173139269630452212135)
  ·
    refine ⟨15954259708904445678318203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10636173139269630452212135 15954259708904445678318203)
    ·
      refine ⟨23931389563356668517477305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15954259708904445678318203 23931389563356668517477305)
      ·
        refine ⟨17948542172517501388107979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23931389563356668517477305 17948542172517501388107979)
        ·
          refine ⟨26922813258776252082161969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17948542172517501388107979 26922813258776252082161969)
          ·
            refine ⟨20192109944082189061621477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26922813258776252082161969 20192109944082189061621477)
            ·
              refine ⟨3786020614515410449054027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20192109944082189061621477 3786020614515410449054027)
              ·
                refine ⟨5679030921773115673581041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3786020614515410449054027 5679030921773115673581041)
                ·
                  refine ⟨4259273191329836755185781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5679030921773115673581041 4259273191329836755185781)
                  ·
                    refine ⟨399306861687172195798667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4259273191329836755185781 399306861687172195798667)
                    ·
                      rfl

theorem cell23_2332942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_2332942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2332942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2332942 prefixEnd_2332942 := by exact prefixLift 2332942
  have htrace : WordTrace (prefixWord ++ tailWord_2332942) baseStart_2332942 baseEnd_2332942 := by
    simpa [prefixWord, tailWord_2332942, baseEnd_2332942] using wordTrace_append hprefix tailTrace_2332942
  have hstable : (prefixWord ++ tailWord_2332942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2332942).length < 2 ^ (prefixWord ++ tailWord_2332942).sum := by decide
  have hdescent : baseEnd_2332942 < baseStart_2332942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2332942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333029 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 3]
def baseStart_2333029 : Nat := 118140960795 + 2333029 * 2 ^ 59
def prefixEnd_2333029 : Nat := 4983230072969 + 3 ^ 40 * 2333029 * 2
def baseEnd_2333029 : Nat := 1197965257878457747008101

theorem tailTrace_2333029 : CollatzResearch.WordTrace tailWord_2333029 prefixEnd_2333029 1197965257878457747008101 := by
  unfold tailWord_2333029
  simp only [CollatzResearch.WordTrace]
  refine ⟨85092558264841857476114141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56728372176561238317409427 85092558264841857476114141)
  ·
    refine ⟨31909709349315696553542803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85092558264841857476114141 31909709349315696553542803)
    ·
      refine ⟨47864564023973544830314205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31909709349315696553542803 47864564023973544830314205)
      ·
        refine ⟨17949211508990079311367827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47864564023973544830314205 17949211508990079311367827)
        ·
          refine ⟨26923817263485118967051741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17949211508990079311367827 26923817263485118967051741)
          ·
            refine ⟨10096431473806919612644403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26923817263485118967051741 10096431473806919612644403)
            ·
              refine ⟨15144647210710379418966605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10096431473806919612644403 15144647210710379418966605)
              ·
                refine ⟨5679242704016392282112477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15144647210710379418966605 5679242704016392282112477)
                ·
                  refine ⟨2129716014006147105792179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5679242704016392282112477 2129716014006147105792179)
                  ·
                    refine ⟨3194574021009220658688269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2129716014006147105792179 3194574021009220658688269)
                    ·
                      refine ⟨1197965257878457747008101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3194574021009220658688269 1197965257878457747008101)
                      ·
                        rfl

theorem cell23_2333029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_2333029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333029 prefixEnd_2333029 := by exact prefixLift 2333029
  have htrace : WordTrace (prefixWord ++ tailWord_2333029) baseStart_2333029 baseEnd_2333029 := by
    simpa [prefixWord, tailWord_2333029, baseEnd_2333029] using wordTrace_append hprefix tailTrace_2333029
  have hstable : (prefixWord ++ tailWord_2333029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333029).length < 2 ^ (prefixWord ++ tailWord_2333029).sum := by decide
  have hdescent : baseEnd_2333029 < baseStart_2333029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333080 : List Nat := [2, 1, 2, 5, 1, 2, 3, 2, 1, 1, 3]
def baseStart_2333080 : Nat := 118140960795 + 2333080 * 2 ^ 59
def prefixEnd_2333080 : Nat := 4983230072969 + 3 ^ 40 * 2333080 * 2
def baseEnd_2333080 : Nat := 1197991445391837047470367

theorem tailTrace_2333080 : CollatzResearch.WordTrace tailWord_2333080 prefixEnd_2333080 1197991445391837047470367 := by
  unfold tailWord_2333080
  simp only [CollatzResearch.WordTrace]
  refine ⟨42547209193828546593110347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56729612258438062124147129 42547209193828546593110347)
  ·
    refine ⟨63820813790742819889665521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42547209193828546593110347 63820813790742819889665521)
    ·
      refine ⟨47865610343057114917249141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63820813790742819889665521 47865610343057114917249141)
      ·
        refine ⟨4487400969661604523492107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47865610343057114917249141 4487400969661604523492107)
        ·
          refine ⟨6731101454492406785238161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4487400969661604523492107 6731101454492406785238161)
          ·
            refine ⟨5048326090869305088928621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6731101454492406785238161 5048326090869305088928621)
            ·
              refine ⟨1893122284075989408348233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5048326090869305088928621 1893122284075989408348233)
              ·
                refine ⟨1419841713056992056261175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1893122284075989408348233 1419841713056992056261175)
                ·
                  refine ⟨2129762569585488084391763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1419841713056992056261175 2129762569585488084391763)
                  ·
                    refine ⟨3194643854378232126587645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2129762569585488084391763 3194643854378232126587645)
                    ·
                      refine ⟨1197991445391837047470367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3194643854378232126587645 1197991445391837047470367)
                      ·
                        rfl

theorem cell23_2333080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_2333080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333080 prefixEnd_2333080 := by exact prefixLift 2333080
  have htrace : WordTrace (prefixWord ++ tailWord_2333080) baseStart_2333080 baseEnd_2333080 := by
    simpa [prefixWord, tailWord_2333080, baseEnd_2333080] using wordTrace_append hprefix tailTrace_2333080
  have hstable : (prefixWord ++ tailWord_2333080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333080).length < 2 ^ (prefixWord ++ tailWord_2333080).sum := by decide
  have hdescent : baseEnd_2333080 < baseStart_2333080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333082 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2333082 : Nat := 118140960795 + 2333082 * 2 ^ 59
def prefixEnd_2333082 : Nat := 4983230072969 + 3 ^ 40 * 2333082 * 2
def baseEnd_2333082 : Nat := 1197992472353146039645357

theorem tailTrace_2333082 : CollatzResearch.WordTrace tailWord_2333082 prefixEnd_2333082 1197992472353146039645357 := by
  unfold tailWord_2333082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21273622833412461881948375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56729660889099898351862333 21273622833412461881948375)
  ·
    refine ⟨31910434250118692822922563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21273622833412461881948375 31910434250118692822922563)
    ·
      refine ⟨47865651375178039234383845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31910434250118692822922563 47865651375178039234383845)
      ·
        refine ⟨8974809632845882356446971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47865651375178039234383845 8974809632845882356446971)
        ·
          refine ⟨13462214449268823534670457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8974809632845882356446971 13462214449268823534670457)
          ·
            refine ⟨10096660836951617651002843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13462214449268823534670457 10096660836951617651002843)
            ·
              refine ⟨15144991255427426476504265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10096660836951617651002843 15144991255427426476504265)
              ·
                refine ⟨11358743441570569857378199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15144991255427426476504265 11358743441570569857378199)
                ·
                  refine ⟨17038115162355854786067299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11358743441570569857378199 17038115162355854786067299)
                  ·
                    refine ⟨25557172743533782179100949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17038115162355854786067299 25557172743533782179100949)
                    ·
                      refine ⟨1197992472353146039645357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25557172743533782179100949 1197992472353146039645357)
                      ·
                        rfl

theorem cell23_2333082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2333082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333082 prefixEnd_2333082 := by exact prefixLift 2333082
  have htrace : WordTrace (prefixWord ++ tailWord_2333082) baseStart_2333082 baseEnd_2333082 := by
    simpa [prefixWord, tailWord_2333082, baseEnd_2333082] using wordTrace_append hprefix tailTrace_2333082
  have hstable : (prefixWord ++ tailWord_2333082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333082).length < 2 ^ (prefixWord ++ tailWord_2333082).sum := by decide
  have hdescent : baseEnd_2333082 < baseStart_2333082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333152 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 2, 6]
def baseStart_2333152 : Nat := 118140960795 + 2333152 * 2 ^ 59
def prefixEnd_2333152 : Nat := 4983230072969 + 3 ^ 40 * 2333152 * 2
def baseEnd_2333152 : Nat := 399342805332986921923345

theorem tailTrace_2333152 : CollatzResearch.WordTrace tailWord_2333152 prefixEnd_2333152 399342805332986921923345 := by
  unfold tailWord_2333152
  simp only [CollatzResearch.WordTrace]
  refine ⟨42548522221698124741420855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56731362962264166321894473 42548522221698124741420855)
  ·
    refine ⟨63822783332547187112131283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42548522221698124741420855 63822783332547187112131283)
    ·
      refine ⟨95734174998820780668196925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63822783332547187112131283 95734174998820780668196925)
      ·
        refine ⟨35900315624557792750573847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95734174998820780668196925 35900315624557792750573847)
        ·
          refine ⟨53850473436836689125860771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35900315624557792750573847 53850473436836689125860771)
          ·
            refine ⟨80775710155255033688791157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53850473436836689125860771 80775710155255033688791157)
            ·
              refine ⟨7572722827055159408324171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80775710155255033688791157 7572722827055159408324171)
              ·
                refine ⟨11359084240582739112486257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7572722827055159408324171 11359084240582739112486257)
                ·
                  refine ⟨8519313180437054334364693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11359084240582739112486257 8519313180437054334364693)
                  ·
                    refine ⟨399342805332986921923345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8519313180437054334364693 399342805332986921923345)
                    ·
                      rfl

theorem cell23_2333152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_2333152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333152 prefixEnd_2333152 := by exact prefixLift 2333152
  have htrace : WordTrace (prefixWord ++ tailWord_2333152) baseStart_2333152 baseEnd_2333152 := by
    simpa [prefixWord, tailWord_2333152, baseEnd_2333152] using wordTrace_append hprefix tailTrace_2333152
  have hstable : (prefixWord ++ tailWord_2333152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333152).length < 2 ^ (prefixWord ++ tailWord_2333152).sum := by decide
  have hdescent : baseEnd_2333152 < baseStart_2333152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333176 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 4, 2, 2]
def baseStart_2333176 : Nat := 118140960795 + 2333176 * 2 ^ 59
def prefixEnd_2333176 : Nat := 4983230072969 + 3 ^ 40 * 2333176 * 2
def baseEnd_2333176 : Nat := 1198040739534668671869925

theorem tailTrace_2333176 : CollatzResearch.WordTrace tailWord_2333176 prefixEnd_2333176 1198040739534668671869925 := by
  unfold tailWord_2333176
  simp only [CollatzResearch.WordTrace]
  refine ⟨42548959897654650790857691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56731946530206201054476921 42548959897654650790857691)
  ·
    refine ⟨63823439846481976186286537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42548959897654650790857691 63823439846481976186286537)
    ·
      refine ⟨47867579884861482139714903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63823439846481976186286537 47867579884861482139714903)
      ·
        refine ⟨71801369827292223209572355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47867579884861482139714903 71801369827292223209572355)
        ·
          refine ⟨107702054740938334814358533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71801369827292223209572355 107702054740938334814358533)
          ·
            refine ⟨20194135263925937777692225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 107702054740938334814358533 20194135263925937777692225)
            ·
              refine ⟨15145601447944453333269169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20194135263925937777692225 15145601447944453333269169)
              ·
                refine ⟨11359201085958339999951877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15145601447944453333269169 11359201085958339999951877)
                ·
                  refine ⟨2129850203617188749990977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11359201085958339999951877 2129850203617188749990977)
                  ·
                    refine ⟨1597387652712891562493233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2129850203617188749990977 1597387652712891562493233)
                    ·
                      refine ⟨1198040739534668671869925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1597387652712891562493233 1198040739534668671869925)
                      ·
                        rfl

theorem cell23_2333176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_2333176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333176 prefixEnd_2333176 := by exact prefixLift 2333176
  have htrace : WordTrace (prefixWord ++ tailWord_2333176) baseStart_2333176 baseEnd_2333176 := by
    simpa [prefixWord, tailWord_2333176, baseEnd_2333176] using wordTrace_append hprefix tailTrace_2333176
  have hstable : (prefixWord ++ tailWord_2333176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333176).length < 2 ^ (prefixWord ++ tailWord_2333176).sum := by decide
  have hdescent : baseEnd_2333176 < baseStart_2333176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333266 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_2333266 : Nat := 118140960795 + 2333266 * 2 ^ 59
def prefixEnd_2333266 : Nat := 4983230072969 + 3 ^ 40 * 2333266 * 2
def baseEnd_2333266 : Nat := 1198086952793573319744511

theorem tailTrace_2333266 : CollatzResearch.WordTrace tailWord_2333266 prefixEnd_2333266 1198086952793573319744511 := by
  unfold tailWord_2333266
  simp only [CollatzResearch.WordTrace]
  refine ⟨21275300591245811738122913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56734134909988831301661101 21275300591245811738122913)
  ·
    refine ⟨15956475443434358803592185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21275300591245811738122913 15956475443434358803592185)
    ·
      refine ⟨11967356582575769102694139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15956475443434358803592185 11967356582575769102694139)
      ·
        refine ⟨17951034873863653654041209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11967356582575769102694139 17951034873863653654041209)
        ·
          refine ⟨13463276155397740240530907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17951034873863653654041209 13463276155397740240530907)
          ·
            refine ⟨20194914233096610360796361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13463276155397740240530907 20194914233096610360796361)
            ·
              refine ⟨15146185674822457770597271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20194914233096610360796361 15146185674822457770597271)
              ·
                refine ⟨22719278512233686655895907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15146185674822457770597271 22719278512233686655895907)
                ·
                  refine ⟨34078917768350529983843861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22719278512233686655895907 34078917768350529983843861)
                  ·
                    refine ⟨1597449270391431092992681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34078917768350529983843861 1597449270391431092992681)
                    ·
                      refine ⟨1198086952793573319744511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1597449270391431092992681 1198086952793573319744511)
                      ·
                        rfl

theorem cell23_2333266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_2333266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333266 prefixEnd_2333266 := by exact prefixLift 2333266
  have htrace : WordTrace (prefixWord ++ tailWord_2333266) baseStart_2333266 baseEnd_2333266 := by
    simpa [prefixWord, tailWord_2333266, baseEnd_2333266] using wordTrace_append hprefix tailTrace_2333266
  have hstable : (prefixWord ++ tailWord_2333266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333266).length < 2 ^ (prefixWord ++ tailWord_2333266).sum := by decide
  have hdescent : baseEnd_2333266 < baseStart_2333266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333269 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_2333269 : Nat := 118140960795 + 2333269 * 2 ^ 59
def prefixEnd_2333269 : Nat := 4983230072969 + 3 ^ 40 * 2333269 * 2
def baseEnd_2333269 : Nat := 1198088493235536808006997

theorem tailTrace_2333269 : CollatzResearch.WordTrace tailWord_2333269 prefixEnd_2333269 1198088493235536808006997 := by
  unfold tailWord_2333269
  simp only [CollatzResearch.WordTrace]
  refine ⟨85101311783972378464850861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56734207855981585643233907 85101311783972378464850861)
  ·
    refine ⟨31912991918989641924319073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85101311783972378464850861 31912991918989641924319073)
    ·
      refine ⟨23934743939242231443239305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31912991918989641924319073 23934743939242231443239305)
      ·
        refine ⟨17951057954431673582429479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23934743939242231443239305 17951057954431673582429479)
        ·
          refine ⟨26926586931647510373644219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17951057954431673582429479 26926586931647510373644219)
          ·
            refine ⟨40389880397471265560466329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26926586931647510373644219 40389880397471265560466329)
            ·
              refine ⟨30292410298103449170349747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40389880397471265560466329 30292410298103449170349747)
              ·
                refine ⟨45438615447155173755524621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30292410298103449170349747 45438615447155173755524621)
                ·
                  refine ⟨17039480792683190158321733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45438615447155173755524621 17039480792683190158321733)
                  ·
                    refine ⟨3194902648628098154685325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17039480792683190158321733 3194902648628098154685325)
                    ·
                      refine ⟨1198088493235536808006997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3194902648628098154685325 1198088493235536808006997)
                      ·
                        rfl

theorem cell23_2333269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_2333269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333269 prefixEnd_2333269 := by exact prefixLift 2333269
  have htrace : WordTrace (prefixWord ++ tailWord_2333269) baseStart_2333269 baseEnd_2333269 := by
    simpa [prefixWord, tailWord_2333269, baseEnd_2333269] using wordTrace_append hprefix tailTrace_2333269
  have hstable : (prefixWord ++ tailWord_2333269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333269).length < 2 ^ (prefixWord ++ tailWord_2333269).sum := by decide
  have hdescent : baseEnd_2333269 < baseStart_2333269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333319 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 5, 5]
def baseStart_2333319 : Nat := 118140960795 + 2333319 * 2 ^ 59
def prefixEnd_2333319 : Nat := 4983230072969 + 3 ^ 40 * 2333319 * 2
def baseEnd_2333319 : Nat := 399371389089420537460589

theorem tailTrace_2333319 : CollatzResearch.WordTrace tailWord_2333319 prefixEnd_2333319 399371389089420537460589 := by
  unfold tailWord_2333319
  simp only [CollatzResearch.WordTrace]
  refine ⟨85103135433791237004171011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56735423622527491336114007 85103135433791237004171011)
  ·
    refine ⟨127654703150686855506256517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85103135433791237004171011 127654703150686855506256517)
    ·
      refine ⟨23935256840753785407423097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127654703150686855506256517 23935256840753785407423097)
      ·
        refine ⟨17951442630565339055567323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23935256840753785407423097 17951442630565339055567323)
        ·
          refine ⟨26927163945848008583350985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17951442630565339055567323 26927163945848008583350985)
          ·
            refine ⟨20195372959386006437513239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26927163945848008583350985 20195372959386006437513239)
            ·
              refine ⟨30293059439079009656269859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20195372959386006437513239 30293059439079009656269859)
              ·
                refine ⟨45439589158618514484404789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30293059439079009656269859 45439589158618514484404789)
                ·
                  refine ⟨4259961483620485732912949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45439589158618514484404789 4259961483620485732912949)
                  ·
                    refine ⟨399371389089420537460589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4259961483620485732912949 399371389089420537460589)
                    ·
                      rfl

theorem cell23_2333319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_2333319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333319 prefixEnd_2333319 := by exact prefixLift 2333319
  have htrace : WordTrace (prefixWord ++ tailWord_2333319) baseStart_2333319 baseEnd_2333319 := by
    simpa [prefixWord, tailWord_2333319, baseEnd_2333319] using wordTrace_append hprefix tailTrace_2333319
  have hstable : (prefixWord ++ tailWord_2333319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333319).length < 2 ^ (prefixWord ++ tailWord_2333319).sum := by decide
  have hdescent : baseEnd_2333319 < baseStart_2333319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333336 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 1, 5]
def baseStart_2333336 : Nat := 118140960795 + 2333336 * 2 ^ 59
def prefixEnd_2333336 : Nat := 4983230072969 + 3 ^ 40 * 2333336 * 2
def baseEnd_2333336 : Nat := 399374298813129348623063

theorem tailTrace_2333336 : CollatzResearch.WordTrace tailWord_2333336 prefixEnd_2333336 399374298813129348623063 := by
  unfold tailWord_2333336
  simp only [CollatzResearch.WordTrace]
  refine ⟨42551877737364824453769931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56735836983153099271693241 42551877737364824453769931)
  ·
    refine ⟨63827816606047236680654897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42551877737364824453769931 63827816606047236680654897)
    ·
      refine ⟨47870862454535427510491173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63827816606047236680654897 47870862454535427510491173)
      ·
        refine ⟨8975786710225392658217095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47870862454535427510491173 8975786710225392658217095)
        ·
          refine ⟨13463680065338088987325643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8975786710225392658217095 13463680065338088987325643)
          ·
            refine ⟨20195520098007133480988465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13463680065338088987325643 20195520098007133480988465)
            ·
              refine ⟨15146640073505350110741349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20195520098007133480988465 15146640073505350110741349)
              ·
                refine ⟨2839995013782253145764003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15146640073505350110741349 2839995013782253145764003)
                ·
                  refine ⟨4259992520673379718646005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2839995013782253145764003 4259992520673379718646005)
                  ·
                    refine ⟨399374298813129348623063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4259992520673379718646005 399374298813129348623063)
                    ·
                      rfl

theorem cell23_2333336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_2333336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333336 prefixEnd_2333336 := by exact prefixLift 2333336
  have htrace : WordTrace (prefixWord ++ tailWord_2333336) baseStart_2333336 baseEnd_2333336 := by
    simpa [prefixWord, tailWord_2333336, baseEnd_2333336] using wordTrace_append hprefix tailTrace_2333336
  have hstable : (prefixWord ++ tailWord_2333336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333336).length < 2 ^ (prefixWord ++ tailWord_2333336).sum := by decide
  have hdescent : baseEnd_2333336 < baseStart_2333336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333369 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2333369 : Nat := 118140960795 + 2333369 * 2 ^ 59
def prefixEnd_2333369 : Nat := 4983230072969 + 3 ^ 40 * 2333369 * 2
def baseEnd_2333369 : Nat := 1198139841300986416756537

theorem tailTrace_2333369 : CollatzResearch.WordTrace tailWord_2333369 prefixEnd_2333369 1198139841300986416756537 := by
  unfold tailWord_2333369
  simp only [CollatzResearch.WordTrace]
  refine ⟨85104959083610095543491161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56736639389073397028994107 85104959083610095543491161)
  ·
    refine ⟨63828719312707571657618371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85104959083610095543491161 63828719312707571657618371)
    ·
      refine ⟨95743078969061357486427557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63828719312707571657618371 95743078969061357486427557)
      ·
        refine ⟨17951827306699004528705167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95743078969061357486427557 17951827306699004528705167)
        ·
          refine ⟨26927740960048506793057751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17951827306699004528705167 26927740960048506793057751)
          ·
            refine ⟨40391611440072760189586627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26927740960048506793057751 40391611440072760189586627)
            ·
              refine ⟨60587417160109140284379941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40391611440072760189586627 60587417160109140284379941)
              ·
                refine ⟨11360140717520463803321239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60587417160109140284379941 11360140717520463803321239)
                ·
                  refine ⟨17040211076280695704981859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11360140717520463803321239 17040211076280695704981859)
                  ·
                    refine ⟨25560316614421043557472789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17040211076280695704981859 25560316614421043557472789)
                    ·
                      refine ⟨1198139841300986416756537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25560316614421043557472789 1198139841300986416756537)
                      ·
                        rfl

theorem cell23_2333369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2333369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333369 prefixEnd_2333369 := by exact prefixLift 2333369
  have htrace : WordTrace (prefixWord ++ tailWord_2333369) baseStart_2333369 baseEnd_2333369 := by
    simpa [prefixWord, tailWord_2333369, baseEnd_2333369] using wordTrace_append hprefix tailTrace_2333369
  have hstable : (prefixWord ++ tailWord_2333369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333369).length < 2 ^ (prefixWord ++ tailWord_2333369).sum := by decide
  have hdescent : baseEnd_2333369 < baseStart_2333369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333376 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 5]
def baseStart_2333376 : Nat := 118140960795 + 2333376 * 2 ^ 59
def prefixEnd_2333376 : Nat := 4983230072969 + 3 ^ 40 * 2333376 * 2
def baseEnd_2333376 : Nat := 1198143435665567889369005

theorem tailTrace_2333376 : CollatzResearch.WordTrace tailWord_2333376 prefixEnd_2333376 1198143435665567889369005 := by
  unfold tailWord_2333376
  simp only [CollatzResearch.WordTrace]
  refine ⟨42552607197292367869497991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56736809596389823825997321 42552607197292367869497991)
  ·
    refine ⟨63828910795938551804246987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42552607197292367869497991 63828910795938551804246987)
    ·
      refine ⟨95743366193907827706370481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63828910795938551804246987 95743366193907827706370481)
      ·
        refine ⟨71807524645430870779777861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95743366193907827706370481 71807524645430870779777861)
        ·
          refine ⟨13463910871018288271208349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71807524645430870779777861 13463910871018288271208349)
          ·
            refine ⟨5048966576631858101703131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13463910871018288271208349 5048966576631858101703131)
            ·
              refine ⟨7573449864947787152554697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5048966576631858101703131 7573449864947787152554697)
              ·
                refine ⟨5680087398710840364416023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7573449864947787152554697 5680087398710840364416023)
                ·
                  refine ⟨8520131098066260546624035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5680087398710840364416023 8520131098066260546624035)
                  ·
                    refine ⟨12780196647099390819936053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8520131098066260546624035 12780196647099390819936053)
                    ·
                      refine ⟨1198143435665567889369005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12780196647099390819936053 1198143435665567889369005)
                      ·
                        rfl

theorem cell23_2333376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_2333376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333376 prefixEnd_2333376 := by exact prefixLift 2333376
  have htrace : WordTrace (prefixWord ++ tailWord_2333376) baseStart_2333376 baseEnd_2333376 := by
    simpa [prefixWord, tailWord_2333376, baseEnd_2333376] using wordTrace_append hprefix tailTrace_2333376
  have hstable : (prefixWord ++ tailWord_2333376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333376).length < 2 ^ (prefixWord ++ tailWord_2333376).sum := by decide
  have hdescent : baseEnd_2333376 < baseStart_2333376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333386 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_2333386 : Nat := 118140960795 + 2333386 * 2 ^ 59
def prefixEnd_2333386 : Nat := 4983230072969 + 3 ^ 40 * 2333386 * 2
def baseEnd_2333386 : Nat := 1198148570472112850243959

theorem tailTrace_2333386 : CollatzResearch.WordTrace tailWord_2333386 prefixEnd_2333386 1198148570472112850243959 := by
  unfold tailWord_2333386
  simp only [CollatzResearch.WordTrace]
  refine ⟨21276394781137126861715003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56737052749699004964573341 21276394781137126861715003)
  ·
    refine ⟨31914592171705690292572505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21276394781137126861715003 31914592171705690292572505)
    ·
      refine ⟨23935944128779267719429379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31914592171705690292572505 23935944128779267719429379)
      ·
        refine ⟨35903916193168901579144069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23935944128779267719429379 35903916193168901579144069)
        ·
          refine ⟨6731984286219169046089513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35903916193168901579144069 6731984286219169046089513)
          ·
            refine ⟨5048988214664376784567135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6731984286219169046089513 5048988214664376784567135)
            ·
              refine ⟨7573482321996565176850703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5048988214664376784567135 7573482321996565176850703)
              ·
                refine ⟨11360223482994847765276055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7573482321996565176850703 11360223482994847765276055)
                ·
                  refine ⟨17040335224492271647914083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11360223482994847765276055 17040335224492271647914083)
                  ·
                    refine ⟨25560502836738407471871125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17040335224492271647914083 25560502836738407471871125)
                    ·
                      refine ⟨1198148570472112850243959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25560502836738407471871125 1198148570472112850243959)
                      ·
                        rfl

theorem cell23_2333386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_2333386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333386 prefixEnd_2333386 := by exact prefixLift 2333386
  have htrace : WordTrace (prefixWord ++ tailWord_2333386) baseStart_2333386 baseEnd_2333386 := by
    simpa [prefixWord, tailWord_2333386, baseEnd_2333386] using wordTrace_append hprefix tailTrace_2333386
  have hstable : (prefixWord ++ tailWord_2333386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333386).length < 2 ^ (prefixWord ++ tailWord_2333386).sum := by decide
  have hdescent : baseEnd_2333386 < baseStart_2333386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333390 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2]
def baseStart_2333390 : Nat := 118140960795 + 2333390 * 2 ^ 59
def prefixEnd_2333390 : Nat := 4983230072969 + 3 ^ 40 * 2333390 * 2
def baseEnd_2333390 : Nat := 1198150624394730834593941

theorem tailTrace_2333390 : CollatzResearch.WordTrace tailWord_2333390 prefixEnd_2333390 1198150624394730834593941 := by
  unfold tailWord_2333390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10638215627066752016250703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56737150011022677420003749 10638215627066752016250703)
  ·
    refine ⟨15957323440600128024376055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10638215627066752016250703 15957323440600128024376055)
    ·
      refine ⟨23935985160900192036564083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15957323440600128024376055 23935985160900192036564083)
      ·
        refine ⟨35903977741350288054846125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23935985160900192036564083 35903977741350288054846125)
        ·
          refine ⟨13463991653006358020567297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35903977741350288054846125 13463991653006358020567297)
          ·
            refine ⟨10097993739754768515425473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13463991653006358020567297 10097993739754768515425473)
            ·
              refine ⟨7573495304816076386569105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10097993739754768515425473 7573495304816076386569105)
              ·
                refine ⟨5680121478612057289926829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7573495304816076386569105 5680121478612057289926829)
                ·
                  refine ⟨2130045554479521483722561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5680121478612057289926829 2130045554479521483722561)
                  ·
                    refine ⟨1597534165859641112791921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2130045554479521483722561 1597534165859641112791921)
                    ·
                      refine ⟨1198150624394730834593941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1597534165859641112791921 1198150624394730834593941)
                      ·
                        rfl

theorem cell23_2333390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_2333390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333390 prefixEnd_2333390 := by exact prefixLift 2333390
  have htrace : WordTrace (prefixWord ++ tailWord_2333390) baseStart_2333390 baseEnd_2333390 := by
    simpa [prefixWord, tailWord_2333390, baseEnd_2333390] using wordTrace_append hprefix tailTrace_2333390
  have hstable : (prefixWord ++ tailWord_2333390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333390).length < 2 ^ (prefixWord ++ tailWord_2333390).sum := by decide
  have hdescent : baseEnd_2333390 < baseStart_2333390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333393 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 1, 2, 3]
def baseStart_2333393 : Nat := 118140960795 + 2333393 * 2 ^ 59
def prefixEnd_2333393 : Nat := 4983230072969 + 3 ^ 40 * 2333393 * 2
def baseEnd_2333393 : Nat := 1198152164836694322856427

theorem tailTrace_2333393 : CollatzResearch.WordTrace tailWord_2333393 prefixEnd_2333393 1198152164836694322856427 := by
  unfold tailWord_2333393
  simp only [CollatzResearch.WordTrace]
  refine ⟨85105834435523147642364833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56737222957015431761576555 85105834435523147642364833)
  ·
    refine ⟨63829375826642360731773625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85105834435523147642364833 63829375826642360731773625)
    ·
      refine ⟨47872031869981770548830219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63829375826642360731773625 47872031869981770548830219)
      ·
        refine ⟨71808047804972655823245329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47872031869981770548830219 71808047804972655823245329)
        ·
          refine ⟨53856035853729491867433997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71808047804972655823245329 53856035853729491867433997)
          ·
            refine ⟨20196013445148559450287749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53856035853729491867433997 20196013445148559450287749)
            ·
              refine ⟨3786752520965354896928953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20196013445148559450287749 3786752520965354896928953)
              ·
                refine ⟨2840064390724016172696715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3786752520965354896928953 2840064390724016172696715)
                ·
                  refine ⟨4260096586086024259045073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840064390724016172696715 4260096586086024259045073)
                  ·
                    refine ⟨3195072439564518194283805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4260096586086024259045073 3195072439564518194283805)
                    ·
                      refine ⟨1198152164836694322856427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3195072439564518194283805 1198152164836694322856427)
                      ·
                        rfl

theorem cell23_2333393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_2333393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333393 prefixEnd_2333393 := by exact prefixLift 2333393
  have htrace : WordTrace (prefixWord ++ tailWord_2333393) baseStart_2333393 baseEnd_2333393 := by
    simpa [prefixWord, tailWord_2333393, baseEnd_2333393] using wordTrace_append hprefix tailTrace_2333393
  have hstable : (prefixWord ++ tailWord_2333393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333393).length < 2 ^ (prefixWord ++ tailWord_2333393).sum := by decide
  have hdescent : baseEnd_2333393 < baseStart_2333393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333407 : List Nat := [1, 1, 2, 3, 2, 3, 3, 3, 1, 2, 2]
def baseStart_2333407 : Nat := 118140960795 + 2333407 * 2 ^ 59
def prefixEnd_2333407 : Nat := 4983230072969 + 3 ^ 40 * 2333407 * 2
def baseEnd_2333407 : Nat := 1198159353565857268081363

theorem tailTrace_2333407 : CollatzResearch.WordTrace tailWord_2333407 prefixEnd_2333407 1198159353565857268081363 := by
  unfold tailWord_2333407
  simp only [CollatzResearch.WordTrace]
  refine ⟨85106345057472428033374475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56737563371648285355582983 85106345057472428033374475)
  ·
    refine ⟨127659517586208642050061713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85106345057472428033374475 127659517586208642050061713)
    ·
      refine ⟨95744638189656481537546285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127659517586208642050061713 95744638189656481537546285)
      ·
        refine ⟨35904239321121180576579857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95744638189656481537546285 35904239321121180576579857)
        ·
          refine ⟨26928179490840885432434893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35904239321121180576579857 26928179490840885432434893)
          ·
            refine ⟨10098067309065332037163085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26928179490840885432434893 10098067309065332037163085)
            ·
              refine ⟨3786775240899499513936157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10098067309065332037163085 3786775240899499513936157)
              ·
                refine ⟨1420040715337312317726059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3786775240899499513936157 1420040715337312317726059)
                ·
                  refine ⟨2130061073005968476589089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420040715337312317726059 2130061073005968476589089)
                  ·
                    refine ⟨1597545804754476357441817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2130061073005968476589089 1597545804754476357441817)
                    ·
                      refine ⟨1198159353565857268081363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1597545804754476357441817 1198159353565857268081363)
                      ·
                        rfl

theorem cell23_2333407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 1, 2, 2].length) (baseStart_2333407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333407 prefixEnd_2333407 := by exact prefixLift 2333407
  have htrace : WordTrace (prefixWord ++ tailWord_2333407) baseStart_2333407 baseEnd_2333407 := by
    simpa [prefixWord, tailWord_2333407, baseEnd_2333407] using wordTrace_append hprefix tailTrace_2333407
  have hstable : (prefixWord ++ tailWord_2333407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333407).length < 2 ^ (prefixWord ++ tailWord_2333407).sum := by decide
  have hdescent : baseEnd_2333407 < baseStart_2333407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333419 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 5]
def baseStart_2333419 : Nat := 118140960795 + 2333419 * 2 ^ 59
def prefixEnd_2333419 : Nat := 4983230072969 + 3 ^ 40 * 2333419 * 2
def baseEnd_2333419 : Nat := 1198165515333711221131307

theorem tailTrace_2333419 : CollatzResearch.WordTrace tailWord_2333419 prefixEnd_2333419 1198165515333711221131307 := by
  unfold tailWord_2333419
  simp only [CollatzResearch.WordTrace]
  refine ⟨85106782733428954082811311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56737855155619302721874207 85106782733428954082811311)
  ·
    refine ⟨127660174100143431124216967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85106782733428954082811311 127660174100143431124216967)
    ·
      refine ⟨191490261150215146686325451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127660174100143431124216967 191490261150215146686325451)
      ·
        refine ⟨287235391725322720029488177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191490261150215146686325451 287235391725322720029488177)
        ·
          refine ⟨215426543793992040022116133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287235391725322720029488177 215426543793992040022116133)
          ·
            refine ⟨40392476961373507504146775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 215426543793992040022116133 40392476961373507504146775)
            ·
              refine ⟨60588715442060261256220163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40392476961373507504146775 60588715442060261256220163)
              ·
                refine ⟨90883073163090391884330245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60588715442060261256220163 90883073163090391884330245)
                ·
                  refine ⟨17040576218079448478311921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90883073163090391884330245 17040576218079448478311921)
                  ·
                    refine ⟨12780432163559586358733941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17040576218079448478311921 12780432163559586358733941)
                    ·
                      refine ⟨1198165515333711221131307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12780432163559586358733941 1198165515333711221131307)
                      ·
                        rfl

theorem cell23_2333419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 5].length) (baseStart_2333419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333419 prefixEnd_2333419 := by exact prefixLift 2333419
  have htrace : WordTrace (prefixWord ++ tailWord_2333419) baseStart_2333419 baseEnd_2333419 := by
    simpa [prefixWord, tailWord_2333419, baseEnd_2333419] using wordTrace_append hprefix tailTrace_2333419
  have hstable : (prefixWord ++ tailWord_2333419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333419).length < 2 ^ (prefixWord ++ tailWord_2333419).sum := by decide
  have hdescent : baseEnd_2333419 < baseStart_2333419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333423 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 4, 1, 3]
def baseStart_2333423 : Nat := 118140960795 + 2333423 * 2 ^ 59
def prefixEnd_2333423 : Nat := 4983230072969 + 3 ^ 40 * 2333423 * 2
def baseEnd_2333423 : Nat := 1198167569256329205481289

theorem tailTrace_2333423 : CollatzResearch.WordTrace tailWord_2333423 prefixEnd_2333423 1198167569256329205481289 := by
  unfold tailWord_2333423
  simp only [CollatzResearch.WordTrace]
  refine ⟨85106928625414462765956923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56737952416942975177304615 85106928625414462765956923)
  ·
    refine ⟨127660392938121694148935385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85106928625414462765956923 127660392938121694148935385)
    ·
      refine ⟨95745294703591270611701539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127660392938121694148935385 95745294703591270611701539)
      ·
        refine ⟨143617942055386905917552309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95745294703591270611701539 143617942055386905917552309)
        ·
          refine ⟨13464182067692522429770529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 143617942055386905917552309 13464182067692522429770529)
          ·
            refine ⟨10098136550769391822327897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13464182067692522429770529 10098136550769391822327897)
            ·
              refine ⟨7573602413077043866745923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10098136550769391822327897 7573602413077043866745923)
              ·
                refine ⟨11360403619615565800118885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7573602413077043866745923 11360403619615565800118885)
                ·
                  refine ⟨2130075678677918587522291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11360403619615565800118885 2130075678677918587522291)
                  ·
                    refine ⟨3195113518016877881283437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2130075678677918587522291 3195113518016877881283437)
                    ·
                      refine ⟨1198167569256329205481289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3195113518016877881283437 1198167569256329205481289)
                      ·
                        rfl

theorem cell23_2333423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 1, 3].length) (baseStart_2333423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333423 prefixEnd_2333423 := by exact prefixLift 2333423
  have htrace : WordTrace (prefixWord ++ tailWord_2333423) baseStart_2333423 baseEnd_2333423 := by
    simpa [prefixWord, tailWord_2333423, baseEnd_2333423] using wordTrace_append hprefix tailTrace_2333423
  have hstable : (prefixWord ++ tailWord_2333423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333423).length < 2 ^ (prefixWord ++ tailWord_2333423).sum := by decide
  have hdescent : baseEnd_2333423 < baseStart_2333423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333439 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 1, 8]
def baseStart_2333439 : Nat := 118140960795 + 2333439 * 2 ^ 59
def prefixEnd_2333439 : Nat := 4983230072969 + 3 ^ 40 * 2333439 * 2
def baseEnd_2333439 : Nat := 399391928315600380960405

theorem tailTrace_2333439 : CollatzResearch.WordTrace tailWord_2333439 prefixEnd_2333439 399391928315600380960405 := by
  unfold tailWord_2333439
  simp only [CollatzResearch.WordTrace]
  refine ⟨85107512193356497498539371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56738341462237664999026247 85107512193356497498539371)
  ·
    refine ⟨127661268290034746247809057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85107512193356497498539371 127661268290034746247809057)
    ·
      refine ⟨95745951217526059685856793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127661268290034746247809057 95745951217526059685856793)
      ·
        refine ⟨71809463413144544764392595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95745951217526059685856793 71809463413144544764392595)
        ·
          refine ⟨107714195119716817146588893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71809463413144544764392595 107714195119716817146588893)
          ·
            refine ⟨40392823169893806429970835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107714195119716817146588893 40392823169893806429970835)
            ·
              refine ⟨60589234754840709644956253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40392823169893806429970835 60589234754840709644956253)
              ·
                refine ⟨22720963033065266116858595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60589234754840709644956253 22720963033065266116858595)
                ·
                  refine ⟨34081444549597899175287893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22720963033065266116858595 34081444549597899175287893)
                  ·
                    refine ⟨399391928315600380960405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34081444549597899175287893 399391928315600380960405)
                    ·
                      rfl

theorem cell23_2333439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 8].length) (baseStart_2333439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333439 prefixEnd_2333439 := by exact prefixLift 2333439
  have htrace : WordTrace (prefixWord ++ tailWord_2333439) baseStart_2333439 baseEnd_2333439 := by
    simpa [prefixWord, tailWord_2333439, baseEnd_2333439] using wordTrace_append hprefix tailTrace_2333439
  have hstable : (prefixWord ++ tailWord_2333439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333439).length < 2 ^ (prefixWord ++ tailWord_2333439).sum := by decide
  have hdescent : baseEnd_2333439 < baseStart_2333439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333466 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_2333466 : Nat := 118140960795 + 2333466 * 2 ^ 59
def prefixEnd_2333466 : Nat := 4983230072969 + 3 ^ 40 * 2333466 * 2
def baseEnd_2333466 : Nat := 1198189648924472537243591

theorem tailTrace_2333466 : CollatzResearch.WordTrace tailWord_2333466 prefixEnd_2333466 1198189648924472537243591 := by
  unfold tailWord_2333466
  simp only [CollatzResearch.WordTrace]
  refine ⟨21277124241064670277443063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56738997976172454073181501 21277124241064670277443063)
  ·
    refine ⟨31915686361597005416164595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21277124241064670277443063 31915686361597005416164595)
    ·
      refine ⟨47873529542395508124246893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31915686361597005416164595 47873529542395508124246893)
      ·
        refine ⟨17952573578398315546592585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47873529542395508124246893 17952573578398315546592585)
        ·
          refine ⟨13464430183798736659944439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17952573578398315546592585 13464430183798736659944439)
          ·
            refine ⟨20196645275698104989916659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13464430183798736659944439 20196645275698104989916659)
            ·
              refine ⟨30294967913547157484874989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20196645275698104989916659 30294967913547157484874989)
              ·
                refine ⟨11360612967580184056828121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30294967913547157484874989 11360612967580184056828121)
                ·
                  refine ⟨8520459725685138042621091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11360612967580184056828121 8520459725685138042621091)
                  ·
                    refine ⟨12780689588527707063931637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8520459725685138042621091 12780689588527707063931637)
                    ·
                      refine ⟨1198189648924472537243591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12780689588527707063931637 1198189648924472537243591)
                      ·
                        rfl

theorem cell23_2333466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_2333466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333466 prefixEnd_2333466 := by exact prefixLift 2333466
  have htrace : WordTrace (prefixWord ++ tailWord_2333466) baseStart_2333466 baseEnd_2333466 := by
    simpa [prefixWord, tailWord_2333466, baseEnd_2333466] using wordTrace_append hprefix tailTrace_2333466
  have hstable : (prefixWord ++ tailWord_2333466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333466).length < 2 ^ (prefixWord ++ tailWord_2333466).sum := by decide
  have hdescent : baseEnd_2333466 < baseStart_2333466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333493 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_2333493 : Nat := 118140960795 + 2333493 * 2 ^ 59
def prefixEnd_2333493 : Nat := 4983230072969 + 3 ^ 40 * 2333493 * 2
def baseEnd_2333493 : Nat := 1198203512902143931605967

theorem tailTrace_2333493 : CollatzResearch.WordTrace tailWord_2333493 prefixEnd_2333493 1198203512902143931605967 := by
  unfold tailWord_2333493
  simp only [CollatzResearch.WordTrace]
  refine ⟨85109481735160864721005133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56739654490107243147336755 85109481735160864721005133)
  ·
    refine ⟨31916055650685324270376925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85109481735160864721005133 31916055650685324270376925)
    ·
      refine ⟨11968520869006996601391347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31916055650685324270376925 11968520869006996601391347)
      ·
        refine ⟨17952781303510494902087021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11968520869006996601391347 17952781303510494902087021)
        ·
          refine ⟨6732292988816435588282633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17952781303510494902087021 6732292988816435588282633)
          ·
            refine ⟨5049219741612326691211975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6732292988816435588282633 5049219741612326691211975)
            ·
              refine ⟨7573829612418490036817963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049219741612326691211975 7573829612418490036817963)
              ·
                refine ⟨11360744418627735055226945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7573829612418490036817963 11360744418627735055226945)
                ·
                  refine ⟨8520558313970801291420209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11360744418627735055226945 8520558313970801291420209)
                  ·
                    refine ⟨6390418735478100968565157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8520558313970801291420209 6390418735478100968565157)
                    ·
                      refine ⟨1198203512902143931605967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6390418735478100968565157 1198203512902143931605967)
                      ·
                        rfl

theorem cell23_2333493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_2333493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333493 prefixEnd_2333493 := by exact prefixLift 2333493
  have htrace : WordTrace (prefixWord ++ tailWord_2333493) baseStart_2333493 baseEnd_2333493 := by
    simpa [prefixWord, tailWord_2333493, baseEnd_2333493] using wordTrace_append hprefix tailTrace_2333493
  have hstable : (prefixWord ++ tailWord_2333493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333493).length < 2 ^ (prefixWord ++ tailWord_2333493).sum := by decide
  have hdescent : baseEnd_2333493 < baseStart_2333493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333563 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 3, 4]
def baseStart_2333563 : Nat := 118140960795 + 2333563 * 2 ^ 59
def prefixEnd_2333563 : Nat := 4983230072969 + 3 ^ 40 * 2333563 * 2
def baseEnd_2333563 : Nat := 399413152182652885910215

theorem tailTrace_2333563 : CollatzResearch.WordTrace tailWord_2333563 prefixEnd_2333563 399413152182652885910215 := by
  unfold tailWord_2333563
  simp only [CollatzResearch.WordTrace]
  refine ⟨85112034844907266676053343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56741356563271511117368895 85112034844907266676053343)
  ·
    refine ⟨127668052267360900014080015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85112034844907266676053343 127668052267360900014080015)
    ·
      refine ⟨191502078401041350021120023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127668052267360900014080015 191502078401041350021120023)
      ·
        refine ⟨287253117601562025031680035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191502078401041350021120023 287253117601562025031680035)
        ·
          refine ⟨430879676402343037547520053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287253117601562025031680035 430879676402343037547520053)
          ·
            refine ⟨40394969662719659770080005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 430879676402343037547520053 40394969662719659770080005)
            ·
              refine ⟨7574056811759936206890001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40394969662719659770080005 7574056811759936206890001)
              ·
                refine ⟨5680542608819952155167501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7574056811759936206890001 5680542608819952155167501)
                ·
                  refine ⟨2130203478307482058187813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5680542608819952155167501 2130203478307482058187813)
                  ·
                    refine ⟨399413152182652885910215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2130203478307482058187813 399413152182652885910215)
                    ·
                      rfl

theorem cell23_2333563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 3, 4].length) (baseStart_2333563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333563 prefixEnd_2333563 := by exact prefixLift 2333563
  have htrace : WordTrace (prefixWord ++ tailWord_2333563) baseStart_2333563 baseEnd_2333563 := by
    simpa [prefixWord, tailWord_2333563, baseEnd_2333563] using wordTrace_append hprefix tailTrace_2333563
  have hstable : (prefixWord ++ tailWord_2333563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333563).length < 2 ^ (prefixWord ++ tailWord_2333563).sum := by decide
  have hdescent : baseEnd_2333563 < baseStart_2333563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333573 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 1, 4, 3]
def baseStart_2333573 : Nat := 118140960795 + 2333573 * 2 ^ 59
def prefixEnd_2333573 : Nat := 4983230072969 + 3 ^ 40 * 2333573 * 2
def baseEnd_2333573 : Nat := 1198244591354503618605599

theorem tailTrace_2333573 : CollatzResearch.WordTrace tailWord_2333573 prefixEnd_2333573 1198244591354503618605599 := by
  unfold tailWord_2333573
  simp only [CollatzResearch.WordTrace]
  refine ⟨85112399574871038383917373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56741599716580692255944915 85112399574871038383917373)
  ·
    refine ⟨31917149840576639393969015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85112399574871038383917373 31917149840576639393969015)
    ·
      refine ⟨47875724760864959090953523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31917149840576639393969015 47875724760864959090953523)
      ·
        refine ⟨71813587141297438636430285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47875724760864959090953523 71813587141297438636430285)
        ·
          refine ⟨26930095177986539488661357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71813587141297438636430285 26930095177986539488661357)
          ·
            refine ⟨10098785691744952308248009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26930095177986539488661357 10098785691744952308248009)
            ·
              refine ⟨7574089268808714231186007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10098785691744952308248009 7574089268808714231186007)
              ·
                refine ⟨11361133903213071346779011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7574089268808714231186007 11361133903213071346779011)
                ·
                  refine ⟨17041700854819607020168517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11361133903213071346779011 17041700854819607020168517)
                  ·
                    refine ⟨3195318910278676316281597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17041700854819607020168517 3195318910278676316281597)
                    ·
                      refine ⟨1198244591354503618605599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3195318910278676316281597 1198244591354503618605599)
                      ·
                        rfl

theorem cell23_2333573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_2333573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333573 prefixEnd_2333573 := by exact prefixLift 2333573
  have htrace : WordTrace (prefixWord ++ tailWord_2333573) baseStart_2333573 baseEnd_2333573 := by
    simpa [prefixWord, tailWord_2333573, baseEnd_2333573] using wordTrace_append hprefix tailTrace_2333573
  have hstable : (prefixWord ++ tailWord_2333573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333573).length < 2 ^ (prefixWord ++ tailWord_2333573).sum := by decide
  have hdescent : baseEnd_2333573 < baseStart_2333573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333680 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 3]
def baseStart_2333680 : Nat := 118140960795 + 2333680 * 2 ^ 59
def prefixEnd_2333680 : Nat := 4983230072969 + 3 ^ 40 * 2333680 * 2
def baseEnd_2333680 : Nat := 1198299533784534699967607

theorem tailTrace_2333680 : CollatzResearch.WordTrace tailWord_2333680 prefixEnd_2333680 1198299533784534699967607 := by
  unfold tailWord_2333680
  simp only [CollatzResearch.WordTrace]
  refine ⟨42558151092741697829031247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56744201456988930438708329 42558151092741697829031247)
  ·
    refine ⟨63837226639112546743546871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42558151092741697829031247 63837226639112546743546871)
    ·
      refine ⟨95755839958668820115320307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63837226639112546743546871 95755839958668820115320307)
      ·
        refine ⟨143633759938003230172980461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95755839958668820115320307 143633759938003230172980461)
        ·
          refine ⟨53862659976751211314867673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143633759938003230172980461 53862659976751211314867673)
          ·
            refine ⟨40396994982563408486150755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53862659976751211314867673 40396994982563408486150755)
            ·
              refine ⟨60595492473845112729226133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40396994982563408486150755 60595492473845112729226133)
              ·
                refine ⟨2840413709711489659182475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60595492473845112729226133 2840413709711489659182475)
                ·
                  refine ⟨4260620564567234488773713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840413709711489659182475 4260620564567234488773713)
                  ·
                    refine ⟨3195465423425425866580285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4260620564567234488773713 3195465423425425866580285)
                    ·
                      refine ⟨1198299533784534699967607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3195465423425425866580285 1198299533784534699967607)
                      ·
                        rfl

theorem cell23_2333680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 3].length) (baseStart_2333680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333680 prefixEnd_2333680 := by exact prefixLift 2333680
  have htrace : WordTrace (prefixWord ++ tailWord_2333680) baseStart_2333680 baseEnd_2333680 := by
    simpa [prefixWord, tailWord_2333680, baseEnd_2333680] using wordTrace_append hprefix tailTrace_2333680
  have hstable : (prefixWord ++ tailWord_2333680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333680).length < 2 ^ (prefixWord ++ tailWord_2333680).sum := by decide
  have hdescent : baseEnd_2333680 < baseStart_2333680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333694 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2333694 : Nat := 118140960795 + 2333694 * 2 ^ 59
def prefixEnd_2333694 : Nat := 4983230072969 + 3 ^ 40 * 2333694 * 2
def baseEnd_2333694 : Nat := 1198306722513697645192543

theorem tailTrace_2333694 : CollatzResearch.WordTrace tailWord_2333694 prefixEnd_2333694 1198306722513697645192543 := by
  unfold tailWord_2333694
  simp only [CollatzResearch.WordTrace]
  refine ⟨10639601600929084506134017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56744541871621784032714757 10639601600929084506134017)
  ·
    refine ⟨7979701200696813379600513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10639601600929084506134017 7979701200696813379600513)
    ·
      refine ⟨5984775900522610034700385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7979701200696813379600513 5984775900522610034700385)
      ·
        refine ⟨4488581925391957526025289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5984775900522610034700385 4488581925391957526025289)
        ·
          refine ⟨3366436444043968144518967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4488581925391957526025289 3366436444043968144518967)
          ·
            refine ⟨5049654666065952216778451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3366436444043968144518967 5049654666065952216778451)
            ·
              refine ⟨7574481999098928325167677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049654666065952216778451 7574481999098928325167677)
              ·
                refine ⟨2840430749662098121937879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7574481999098928325167677 2840430749662098121937879)
                ·
                  refine ⟨4260646124493147182906819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840430749662098121937879 4260646124493147182906819)
                  ·
                    refine ⟨6390969186739720774360229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4260646124493147182906819 6390969186739720774360229)
                    ·
                      refine ⟨1198306722513697645192543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6390969186739720774360229 1198306722513697645192543)
                      ·
                        rfl

theorem cell23_2333694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2333694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333694 prefixEnd_2333694 := by exact prefixLift 2333694
  have htrace : WordTrace (prefixWord ++ tailWord_2333694) baseStart_2333694 baseEnd_2333694 := by
    simpa [prefixWord, tailWord_2333694, baseEnd_2333694] using wordTrace_append hprefix tailTrace_2333694
  have hstable : (prefixWord ++ tailWord_2333694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333694).length < 2 ^ (prefixWord ++ tailWord_2333694).sum := by decide
  have hdescent : baseEnd_2333694 < baseStart_2333694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333697 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_2333697 : Nat := 118140960795 + 2333697 * 2 ^ 59
def prefixEnd_2333697 : Nat := 4983230072969 + 3 ^ 40 * 2333697 * 2
def baseEnd_2333697 : Nat := 1198308262955661133455029

theorem tailTrace_2333697 : CollatzResearch.WordTrace tailWord_2333697 prefixEnd_2333697 1198308262955661133455029 := by
  unfold tailWord_2333697
  simp only [CollatzResearch.WordTrace]
  refine ⟨85116922226421807561431345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56744614817614538374287563 85116922226421807561431345)
  ·
    refine ⟨63837691669816355671073509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85116922226421807561431345 63837691669816355671073509)
    ·
      refine ⟨11969567188090566688326283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63837691669816355671073509 11969567188090566688326283)
      ·
        refine ⟨17954350782135850032489425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11969567188090566688326283 17954350782135850032489425)
        ·
          refine ⟨13465763086601887524367069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17954350782135850032489425 13465763086601887524367069)
          ·
            refine ⟨5049661157475707821637651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13465763086601887524367069 5049661157475707821637651)
            ·
              refine ⟨7574491736213561732456477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5049661157475707821637651 7574491736213561732456477)
              ·
                refine ⟨2840434401080085649671179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7574491736213561732456477 2840434401080085649671179)
                ·
                  refine ⟨4260651601620128474506769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840434401080085649671179 4260651601620128474506769)
                  ·
                    refine ⟨3195488701215096355880077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4260651601620128474506769 3195488701215096355880077)
                    ·
                      refine ⟨1198308262955661133455029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3195488701215096355880077 1198308262955661133455029)
                      ·
                        rfl

theorem cell23_2333697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_2333697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333697 prefixEnd_2333697 := by exact prefixLift 2333697
  have htrace : WordTrace (prefixWord ++ tailWord_2333697) baseStart_2333697 baseEnd_2333697 := by
    simpa [prefixWord, tailWord_2333697, baseEnd_2333697] using wordTrace_append hprefix tailTrace_2333697
  have hstable : (prefixWord ++ tailWord_2333697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333697).length < 2 ^ (prefixWord ++ tailWord_2333697).sum := by decide
  have hdescent : baseEnd_2333697 < baseStart_2333697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333724 : List Nat := [2, 2, 3, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_2333724 : Nat := 118140960795 + 2333724 * 2 ^ 59
def prefixEnd_2333724 : Nat := 4983230072969 + 3 ^ 40 * 2333724 * 2
def baseEnd_2333724 : Nat := 1198322126933332527817405

theorem tailTrace_2333724 : CollatzResearch.WordTrace tailWord_2333724 prefixEnd_2333724 1198322126933332527817405 := by
  unfold tailWord_2333724
  simp only [CollatzResearch.WordTrace]
  refine ⟨42558953498661995586332113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56745271331549327448442817 42558953498661995586332113)
  ·
    refine ⟨31919215123996496689749085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42558953498661995586332113 31919215123996496689749085)
    ·
      refine ⟨11969705671498686258655907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31919215123996496689749085 11969705671498686258655907)
      ·
        refine ⟨17954558507248029387983861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11969705671498686258655907 17954558507248029387983861)
        ·
          refine ⟨1683239860054502755123487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17954558507248029387983861 1683239860054502755123487)
          ·
            refine ⟨2524859790081754132685231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1683239860054502755123487 2524859790081754132685231)
            ·
              refine ⟨3787289685122631199027847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2524859790081754132685231 3787289685122631199027847)
              ·
                refine ⟨5680934527683946798541771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787289685122631199027847 5680934527683946798541771)
                ·
                  refine ⟨8521401791525920197812657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5680934527683946798541771 8521401791525920197812657)
                  ·
                    refine ⟨6391051343644440148359493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8521401791525920197812657 6391051343644440148359493)
                    ·
                      refine ⟨1198322126933332527817405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6391051343644440148359493 1198322126933332527817405)
                      ·
                        rfl

theorem cell23_2333724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_2333724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333724 prefixEnd_2333724 := by exact prefixLift 2333724
  have htrace : WordTrace (prefixWord ++ tailWord_2333724) baseStart_2333724 baseEnd_2333724 := by
    simpa [prefixWord, tailWord_2333724, baseEnd_2333724] using wordTrace_append hprefix tailTrace_2333724
  have hstable : (prefixWord ++ tailWord_2333724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333724).length < 2 ^ (prefixWord ++ tailWord_2333724).sum := by decide
  have hdescent : baseEnd_2333724 < baseStart_2333724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333727 : List Nat := [1, 1, 2, 4, 1, 5, 1, 1, 1, 3, 3]
def baseStart_2333727 : Nat := 118140960795 + 2333727 * 2 ^ 59
def prefixEnd_2333727 : Nat := 4983230072969 + 3 ^ 40 * 2333727 * 2
def baseEnd_2333727 : Nat := 1198323667375296016079891

theorem tailTrace_2333727 : CollatzResearch.WordTrace tailWord_2333727 prefixEnd_2333727 1198323667375296016079891 := by
  unfold tailWord_2333727
  simp only [CollatzResearch.WordTrace]
  refine ⟨85118016416313122685023435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56745344277542081790015623 85118016416313122685023435)
  ·
    refine ⟨127677024624469684027535153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85118016416313122685023435 127677024624469684027535153)
    ·
      refine ⟨95757768468352263020651365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127677024624469684027535153 95757768468352263020651365)
      ·
        refine ⟨17954581587816049316372131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95757768468352263020651365 17954581587816049316372131)
        ·
          refine ⟨26931872381724073974558197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17954581587816049316372131 26931872381724073974558197)
          ·
            refine ⟨2524863035786631935114831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26931872381724073974558197 2524863035786631935114831)
            ·
              refine ⟨3787294553679947902672247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2524863035786631935114831 3787294553679947902672247)
              ·
                refine ⟨5680941830519921854008371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787294553679947902672247 5680941830519921854008371)
                ·
                  refine ⟨8521412745779882781012557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5680941830519921854008371 8521412745779882781012557)
                  ·
                    refine ⟨3195529779667456042879709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8521412745779882781012557 3195529779667456042879709)
                    ·
                      refine ⟨1198323667375296016079891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3195529779667456042879709 1198323667375296016079891)
                      ·
                        rfl

theorem cell23_2333727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_2333727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333727 prefixEnd_2333727 := by exact prefixLift 2333727
  have htrace : WordTrace (prefixWord ++ tailWord_2333727) baseStart_2333727 baseEnd_2333727 := by
    simpa [prefixWord, tailWord_2333727, baseEnd_2333727] using wordTrace_append hprefix tailTrace_2333727
  have hstable : (prefixWord ++ tailWord_2333727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333727).length < 2 ^ (prefixWord ++ tailWord_2333727).sum := by decide
  have hdescent : baseEnd_2333727 < baseStart_2333727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333780 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_2333780 : Nat := 118140960795 + 2333780 * 2 ^ 59
def prefixEnd_2333780 : Nat := 4983230072969 + 3 ^ 40 * 2333780 * 2
def baseEnd_2333780 : Nat := 1198350881849984308717147

theorem tailTrace_2333780 : CollatzResearch.WordTrace tailWord_2333780 prefixEnd_2333780 1198350881849984308717147 := by
  unfold tailWord_2333780
  simp only [CollatzResearch.WordTrace]
  refine ⟨42559974742560556368351397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56746632990080741824468529 42559974742560556368351397)
  ·
    refine ⟨7979995264230104319065887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42559974742560556368351397 7979995264230104319065887)
    ·
      refine ⟨11969992896345156478598831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7979995264230104319065887 11969992896345156478598831)
      ·
        refine ⟨17954989344517734717898247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11969992896345156478598831 17954989344517734717898247)
        ·
          refine ⟨26932484016776602076847371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17954989344517734717898247 26932484016776602076847371)
          ·
            refine ⟨40398726025164903115271057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26932484016776602076847371 40398726025164903115271057)
            ·
              refine ⟨30299044518873677336453293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40398726025164903115271057 30299044518873677336453293)
              ·
                refine ⟨11362141694577629001169985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30299044518873677336453293 11362141694577629001169985)
                ·
                  refine ⟨8521606270933221750877489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11362141694577629001169985 8521606270933221750877489)
                  ·
                    refine ⟨6391204703199916313158117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8521606270933221750877489 6391204703199916313158117)
                    ·
                      refine ⟨1198350881849984308717147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6391204703199916313158117 1198350881849984308717147)
                      ·
                        rfl

theorem cell23_2333780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_2333780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333780 prefixEnd_2333780 := by exact prefixLift 2333780
  have htrace : WordTrace (prefixWord ++ tailWord_2333780) baseStart_2333780 baseEnd_2333780 := by
    simpa [prefixWord, tailWord_2333780, baseEnd_2333780] using wordTrace_append hprefix tailTrace_2333780
  have hstable : (prefixWord ++ tailWord_2333780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333780).length < 2 ^ (prefixWord ++ tailWord_2333780).sum := by decide
  have hdescent : baseEnd_2333780 < baseStart_2333780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333784 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 2, 2, 2]
def baseStart_2333784 : Nat := 118140960795 + 2333784 * 2 ^ 59
def prefixEnd_2333784 : Nat := 4983230072969 + 3 ^ 40 * 2333784 * 2
def baseEnd_2333784 : Nat := 1198352935772602293067129

theorem tailTrace_2333784 : CollatzResearch.WordTrace tailWord_2333784 prefixEnd_2333784 1198352935772602293067129 := by
  unfold tailWord_2333784
  simp only [CollatzResearch.WordTrace]
  refine ⟨42560047688553310709924203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56746730251404414279898937 42560047688553310709924203)
  ·
    refine ⟨63840071532829966064886305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42560047688553310709924203 63840071532829966064886305)
    ·
      refine ⟨47880053649622474548664729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63840071532829966064886305 47880053649622474548664729)
      ·
        refine ⟨35910040237216855911498547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47880053649622474548664729 35910040237216855911498547)
        ·
          refine ⟨53865060355825283867247821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35910040237216855911498547 53865060355825283867247821)
          ·
            refine ⟨20199397633434481450217933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53865060355825283867247821 20199397633434481450217933)
            ·
              refine ⟨7574774112537930543831725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20199397633434481450217933 7574774112537930543831725)
              ·
                refine ⟨2840540292201723953936897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7574774112537930543831725 2840540292201723953936897)
                ·
                  refine ⟨2130405219151292965452673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2840540292201723953936897 2130405219151292965452673)
                  ·
                    refine ⟨1597803914363469724089505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2130405219151292965452673 1597803914363469724089505)
                    ·
                      refine ⟨1198352935772602293067129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1597803914363469724089505 1198352935772602293067129)
                      ·
                        rfl

theorem cell23_2333784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_2333784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333784 prefixEnd_2333784 := by exact prefixLift 2333784
  have htrace : WordTrace (prefixWord ++ tailWord_2333784) baseStart_2333784 baseEnd_2333784 := by
    simpa [prefixWord, tailWord_2333784, baseEnd_2333784] using wordTrace_append hprefix tailTrace_2333784
  have hstable : (prefixWord ++ tailWord_2333784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333784).length < 2 ^ (prefixWord ++ tailWord_2333784).sum := by decide
  have hdescent : baseEnd_2333784 < baseStart_2333784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333820 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_2333820 : Nat := 118140960795 + 2333820 * 2 ^ 59
def prefixEnd_2333820 : Nat := 4983230072969 + 3 ^ 40 * 2333820 * 2
def baseEnd_2333820 : Nat := 399457140358721384072321

theorem tailTrace_2333820 : CollatzResearch.WordTrace tailWord_2333820 prefixEnd_2333820 399457140358721384072321 := by
  unfold tailWord_2333820
  simp only [CollatzResearch.WordTrace]
  refine ⟨42560704202488099784079457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56747605603317466378772609 42560704202488099784079457)
  ·
    refine ⟨31920528151866074838059593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42560704202488099784079457 31920528151866074838059593)
    ·
      refine ⟨23940396113899556128544695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31920528151866074838059593 23940396113899556128544695)
      ·
        refine ⟨35910594170849334192817043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23940396113899556128544695 35910594170849334192817043)
        ·
          refine ⟨53865891256274001289225565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35910594170849334192817043 53865891256274001289225565)
          ·
            refine ⟨20199709221102750483459587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53865891256274001289225565 20199709221102750483459587)
            ·
              refine ⟨30299563831654125725189381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20199709221102750483459587 30299563831654125725189381)
              ·
                refine ⟨5681168218435148573473009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30299563831654125725189381 5681168218435148573473009)
                ·
                  refine ⟨4260876163826361430104757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5681168218435148573473009 4260876163826361430104757)
                  ·
                    refine ⟨399457140358721384072321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4260876163826361430104757 399457140358721384072321)
                    ·
                      rfl

theorem cell23_2333820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_2333820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333820 prefixEnd_2333820 := by exact prefixLift 2333820
  have htrace : WordTrace (prefixWord ++ tailWord_2333820) baseStart_2333820 baseEnd_2333820 := by
    simpa [prefixWord, tailWord_2333820, baseEnd_2333820] using wordTrace_append hprefix tailTrace_2333820
  have hstable : (prefixWord ++ tailWord_2333820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333820).length < 2 ^ (prefixWord ++ tailWord_2333820).sum := by decide
  have hdescent : baseEnd_2333820 < baseStart_2333820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333854 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2333854 : Nat := 118140960795 + 2333854 * 2 ^ 59
def prefixEnd_2333854 : Nat := 4983230072969 + 3 ^ 40 * 2333854 * 2
def baseEnd_2333854 : Nat := 399462959806139006397269

theorem tailTrace_2333854 : CollatzResearch.WordTrace tailWord_2333854 prefixEnd_2333854 399462959806139006397269 := by
  unfold tailWord_2333854
  simp only [CollatzResearch.WordTrace]
  refine ⟨10640331060856627921862077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56748432324568682249931077 10640331060856627921862077)
  ·
    refine ⟨3990124147821235470698279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10640331060856627921862077 3990124147821235470698279)
    ·
      refine ⟨5985186221731853206047419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3990124147821235470698279 5985186221731853206047419)
      ·
        refine ⟨8977779332597779809071129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5985186221731853206047419 8977779332597779809071129)
        ·
          refine ⟨6733334499448334856803347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8977779332597779809071129 6733334499448334856803347)
          ·
            refine ⟨10100001749172502285205021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6733334499448334856803347 10100001749172502285205021)
            ·
              refine ⟨3787500655939688356951883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10100001749172502285205021 3787500655939688356951883)
              ·
                refine ⟨5681250983909532535427825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787500655939688356951883 5681250983909532535427825)
                ·
                  refine ⟨4260938237932149401570869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5681250983909532535427825 4260938237932149401570869)
                  ·
                    refine ⟨399462959806139006397269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4260938237932149401570869 399462959806139006397269)
                    ·
                      rfl

theorem cell23_2333854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2333854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333854 prefixEnd_2333854 := by exact prefixLift 2333854
  have htrace : WordTrace (prefixWord ++ tailWord_2333854) baseStart_2333854 baseEnd_2333854 := by
    simpa [prefixWord, tailWord_2333854, baseEnd_2333854] using wordTrace_append hprefix tailTrace_2333854
  have hstable : (prefixWord ++ tailWord_2333854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333854).length < 2 ^ (prefixWord ++ tailWord_2333854).sum := by decide
  have hdescent : baseEnd_2333854 < baseStart_2333854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333857 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 1, 6, 2]
def baseStart_2333857 : Nat := 118140960795 + 2333857 * 2 ^ 59
def prefixEnd_2333857 : Nat := 4983230072969 + 3 ^ 40 * 2333857 * 2
def baseEnd_2333857 : Nat := 1198390419860380507454293

theorem tailTrace_2333857 : CollatzResearch.WordTrace tailWord_2333857 prefixEnd_2333857 1198390419860380507454293 := by
  unfold tailWord_2333857
  simp only [CollatzResearch.WordTrace]
  refine ⟨85122757905842154887255825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56748505270561436591503883 85122757905842154887255825)
  ·
    refine ⟨63842068429381616165441869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85122757905842154887255825 63842068429381616165441869)
    ·
      refine ⟨23940775661018106062040701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63842068429381616165441869 23940775661018106062040701)
      ·
        refine ⟨8977790872881789773265263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23940775661018106062040701 8977790872881789773265263)
        ·
          refine ⟨13466686309322684659897895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8977790872881789773265263 13466686309322684659897895)
          ·
            refine ⟨20200029463984026989846843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13466686309322684659897895 20200029463984026989846843)
            ·
              refine ⟨30300044195976040484770265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20200029463984026989846843 30300044195976040484770265)
              ·
                refine ⟨22725033146982030363577699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30300044195976040484770265 22725033146982030363577699)
                ·
                  refine ⟨34087549720473045545366549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22725033146982030363577699 34087549720473045545366549)
                  ·
                    refine ⟨1597853893147174009939057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34087549720473045545366549 1597853893147174009939057)
                    ·
                      refine ⟨1198390419860380507454293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1597853893147174009939057 1198390419860380507454293)
                      ·
                        rfl

theorem cell23_2333857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_2333857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333857 prefixEnd_2333857 := by exact prefixLift 2333857
  have htrace : WordTrace (prefixWord ++ tailWord_2333857) baseStart_2333857 baseEnd_2333857 := by
    simpa [prefixWord, tailWord_2333857, baseEnd_2333857] using wordTrace_append hprefix tailTrace_2333857
  have hstable : (prefixWord ++ tailWord_2333857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333857).length < 2 ^ (prefixWord ++ tailWord_2333857).sum := by decide
  have hdescent : baseEnd_2333857 < baseStart_2333857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333880 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 6]
def baseStart_2333880 : Nat := 118140960795 + 2333880 * 2 ^ 59
def prefixEnd_2333880 : Nat := 4983230072969 + 3 ^ 40 * 2333880 * 2
def baseEnd_2333880 : Nat := 133155803323937101940743

theorem tailTrace_2333880 : CollatzResearch.WordTrace tailWord_2333880 prefixEnd_2333880 133155803323937101940743 := by
  unfold tailWord_2333880
  simp only [CollatzResearch.WordTrace]
  refine ⟨42561798392379414907671547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56749064523172553210228729 42561798392379414907671547)
  ·
    refine ⟨63842697588569122361507321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42561798392379414907671547 63842697588569122361507321)
    ·
      refine ⟨47882023191426841771130491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63842697588569122361507321 47882023191426841771130491)
      ·
        refine ⟨71823034787140262656695737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47882023191426841771130491 71823034787140262656695737)
        ·
          refine ⟨53867276090355196992521803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71823034787140262656695737 53867276090355196992521803)
          ·
            refine ⟨80800914135532795488782705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53867276090355196992521803 80800914135532795488782705)
            ·
              refine ⟨60600685601649596616587029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80800914135532795488782705 60600685601649596616587029)
              ·
                refine ⟨2840657137577324841402517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60600685601649596616587029 2840657137577324841402517)
                ·
                  refine ⟨133155803323937101940743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2840657137577324841402517 133155803323937101940743)
                  ·
                    rfl

theorem cell23_2333880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 6].length) (baseStart_2333880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333880 prefixEnd_2333880 := by exact prefixLift 2333880
  have htrace : WordTrace (prefixWord ++ tailWord_2333880) baseStart_2333880 baseEnd_2333880 := by
    simpa [prefixWord, tailWord_2333880, baseEnd_2333880] using wordTrace_append hprefix tailTrace_2333880
  have hstable : (prefixWord ++ tailWord_2333880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333880).length < 2 ^ (prefixWord ++ tailWord_2333880).sum := by decide
  have hdescent : baseEnd_2333880 < baseStart_2333880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333884 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_2333884 : Nat := 118140960795 + 2333884 * 2 ^ 59
def prefixEnd_2333884 : Nat := 4983230072969 + 3 ^ 40 * 2333884 * 2
def baseEnd_2333884 : Nat := 399468094612683967272223

theorem tailTrace_2333884 : CollatzResearch.WordTrace tailWord_2333884 prefixEnd_2333884 399468094612683967272223 := by
  unfold tailWord_2333884
  simp only [CollatzResearch.WordTrace]
  refine ⟨42561871338372169249244353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56749161784496225665659137 42561871338372169249244353)
  ·
    refine ⟨31921403503779126936933265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42561871338372169249244353 31921403503779126936933265)
    ·
      refine ⟨23941052627834345202699949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31921403503779126936933265 23941052627834345202699949)
      ·
        refine ⟨8977894735437879451012481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23941052627834345202699949 8977894735437879451012481)
        ·
          refine ⟨6733421051578409588259361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8977894735437879451012481 6733421051578409588259361)
          ·
            refine ⟨5050065788683807191194521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6733421051578409588259361 5050065788683807191194521)
            ·
              refine ⟨3787549341512855393395891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5050065788683807191194521 3787549341512855393395891)
              ·
                refine ⟨5681324012269283090093837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3787549341512855393395891 5681324012269283090093837)
                ·
                  refine ⟨2130496504600981158785189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5681324012269283090093837 2130496504600981158785189)
                  ·
                    refine ⟨399468094612683967272223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2130496504600981158785189 399468094612683967272223)
                    ·
                      rfl

theorem cell23_2333884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_2333884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333884 prefixEnd_2333884 := by exact prefixLift 2333884
  have htrace : WordTrace (prefixWord ++ tailWord_2333884) baseStart_2333884 baseEnd_2333884 := by
    simpa [prefixWord, tailWord_2333884, baseEnd_2333884] using wordTrace_append hprefix tailTrace_2333884
  have hstable : (prefixWord ++ tailWord_2333884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333884).length < 2 ^ (prefixWord ++ tailWord_2333884).sum := by decide
  have hdescent : baseEnd_2333884 < baseStart_2333884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333934 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_2333934 : Nat := 118140960795 + 2333934 * 2 ^ 59
def prefixEnd_2333934 : Nat := 4983230072969 + 3 ^ 40 * 2333934 * 2
def baseEnd_2333934 : Nat := 1198429957870776706191439

theorem tailTrace_2333934 : CollatzResearch.WordTrace tailWord_2333934 prefixEnd_2333934 1198429957870776706191439 := by
  unfold tailWord_2333934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10640695790820399629726107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56750377551042131358539237 10640695790820399629726107)
  ·
    refine ⟨15961043686230599444589161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10640695790820399629726107 15961043686230599444589161)
    ·
      refine ⟨11970782764672949583441871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15961043686230599444589161 11970782764672949583441871)
      ·
        refine ⟨17956174147009424375162807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11970782764672949583441871 17956174147009424375162807)
        ·
          refine ⟨26934261220514136562744211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17956174147009424375162807 26934261220514136562744211)
          ·
            refine ⟨40401391830771204844116317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26934261220514136562744211 40401391830771204844116317)
            ·
              refine ⟨15150521936539201816543619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40401391830771204844116317 15150521936539201816543619)
              ·
                refine ⟨22725782904808802724815429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15150521936539201816543619 22725782904808802724815429)
                ·
                  refine ⟨4261084294651650510902893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22725782904808802724815429 4261084294651650510902893)
                  ·
                    refine ⟨1597906610494368941588585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4261084294651650510902893 1597906610494368941588585)
                    ·
                      refine ⟨1198429957870776706191439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1597906610494368941588585 1198429957870776706191439)
                      ·
                        rfl

theorem cell23_2333934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_2333934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333934 prefixEnd_2333934 := by exact prefixLift 2333934
  have htrace : WordTrace (prefixWord ++ tailWord_2333934) baseStart_2333934 baseEnd_2333934 := by
    simpa [prefixWord, tailWord_2333934, baseEnd_2333934] using wordTrace_append hprefix tailTrace_2333934
  have hstable : (prefixWord ++ tailWord_2333934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333934).length < 2 ^ (prefixWord ++ tailWord_2333934).sum := by decide
  have hdescent : baseEnd_2333934 < baseStart_2333934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2333964 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 1, 1, 4]
def baseStart_2333964 : Nat := 118140960795 + 2333964 * 2 ^ 59
def prefixEnd_2333964 : Nat := 4983230072969 + 3 ^ 40 * 2333964 * 2
def baseEnd_2333964 : Nat := 1198445362290411588816301

theorem tailTrace_2333964 : CollatzResearch.WordTrace tailWord_2333964 prefixEnd_2333964 1198445362290411588816301 := by
  unfold tailWord_2333964
  simp only [CollatzResearch.WordTrace]
  refine ⟨42563330258227256080700473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56751107010969674774267297 42563330258227256080700473)
  ·
    refine ⟨31922497693670442060525355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42563330258227256080700473 31922497693670442060525355)
    ·
      refine ⟨47883746540505663090788033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31922497693670442060525355 47883746540505663090788033)
      ·
        refine ⟨35912809905379247318091025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47883746540505663090788033 35912809905379247318091025)
        ·
          refine ⟨26934607429034435488568269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35912809905379247318091025 26934607429034435488568269)
          ·
            refine ⟨10100477785887913308213101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26934607429034435488568269 10100477785887913308213101)
            ·
              refine ⟨3787679169707967490579913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10100477785887913308213101 3787679169707967490579913)
              ·
                refine ⟨2840759377280975617934935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3787679169707967490579913 2840759377280975617934935)
                ·
                  refine ⟨4261139065921463426902403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2840759377280975617934935 4261139065921463426902403)
                  ·
                    refine ⟨6391708598882195140353605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4261139065921463426902403 6391708598882195140353605)
                    ·
                      refine ⟨1198445362290411588816301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6391708598882195140353605 1198445362290411588816301)
                      ·
                        rfl

theorem cell23_2333964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_2333964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2333964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2333964 prefixEnd_2333964 := by exact prefixLift 2333964
  have htrace : WordTrace (prefixWord ++ tailWord_2333964) baseStart_2333964 baseEnd_2333964 := by
    simpa [prefixWord, tailWord_2333964, baseEnd_2333964] using wordTrace_append hprefix tailTrace_2333964
  have hstable : (prefixWord ++ tailWord_2333964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2333964).length < 2 ^ (prefixWord ++ tailWord_2333964).sum := by decide
  have hdescent : baseEnd_2333964 < baseStart_2333964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2333964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334000 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 1, 9]
def baseStart_2334000 : Nat := 118140960795 + 2334000 * 2 ^ 59
def prefixEnd_2334000 : Nat := 4983230072969 + 3 ^ 40 * 2334000 * 2
def baseEnd_2334000 : Nat := 399487949197991149322045

theorem tailTrace_2334000 : CollatzResearch.WordTrace tailWord_2334000 prefixEnd_2334000 399487949197991149322045 := by
  unfold tailWord_2334000
  simp only [CollatzResearch.WordTrace]
  refine ⟨42563986772162045154855727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56751982362882726873140969 42563986772162045154855727)
  ·
    refine ⟨63845980158243067732283591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42563986772162045154855727 63845980158243067732283591)
    ·
      refine ⟨95768970237364601598425387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63845980158243067732283591 95768970237364601598425387)
      ·
        refine ⟨143653455356046902397638081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95768970237364601598425387 143653455356046902397638081)
        ·
          refine ⟨107740091517035176798228561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143653455356046902397638081 107740091517035176798228561)
          ·
            refine ⟨80805068637776382598671421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107740091517035176798228561 80805068637776382598671421)
            ·
              refine ⟨30301900739166143474501783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80805068637776382598671421 30301900739166143474501783)
              ·
                refine ⟨45452851108749215211752675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30301900739166143474501783 45452851108749215211752675)
                ·
                  refine ⟨68179276663123822817629013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45452851108749215211752675 68179276663123822817629013)
                  ·
                    refine ⟨399487949197991149322045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 68179276663123822817629013 399487949197991149322045)
                    ·
                      rfl

theorem cell23_2334000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_2334000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334000 prefixEnd_2334000 := by exact prefixLift 2334000
  have htrace : WordTrace (prefixWord ++ tailWord_2334000) baseStart_2334000 baseEnd_2334000 := by
    simpa [prefixWord, tailWord_2334000, baseEnd_2334000] using wordTrace_append hprefix tailTrace_2334000
  have hstable : (prefixWord ++ tailWord_2334000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334000).length < 2 ^ (prefixWord ++ tailWord_2334000).sum := by decide
  have hdescent : baseEnd_2334000 < baseStart_2334000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334038 : List Nat := [5, 2, 3, 1, 1, 1, 10]
def baseStart_2334038 : Nat := 118140960795 + 2334038 * 2 ^ 59
def prefixEnd_2334038 : Nat := 4983230072969 + 3 ^ 40 * 2334038 * 2
def baseEnd_2334038 : Nat := 14796090862454867892481

theorem tailTrace_2334038 : CollatzResearch.WordTrace tailWord_2334038 prefixEnd_2334038 14796090862454867892481 := by
  unfold tailWord_2334038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5320584969886651424974673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56752906345457615199729845 5320584969886651424974673)
  ·
    refine ⟨3990438727414988568731005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5320584969886651424974673 3990438727414988568731005)
    ·
      refine ⟨1496414522780620713274127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3990438727414988568731005 1496414522780620713274127)
      ·
        refine ⟨2244621784170931069911191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496414522780620713274127 2244621784170931069911191)
        ·
          refine ⟨3366932676256396604866787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2244621784170931069911191 3366932676256396604866787)
          ·
            refine ⟨5050399014384594907300181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3366932676256396604866787 5050399014384594907300181)
            ·
              refine ⟨14796090862454867892481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5050399014384594907300181 14796090862454867892481)
              ·
                rfl

theorem cell23_2334038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 10].length) (baseStart_2334038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334038 prefixEnd_2334038 := by exact prefixLift 2334038
  have htrace : WordTrace (prefixWord ++ tailWord_2334038) baseStart_2334038 baseEnd_2334038 := by
    simpa [prefixWord, tailWord_2334038, baseEnd_2334038] using wordTrace_append hprefix tailTrace_2334038
  have hstable : (prefixWord ++ tailWord_2334038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334038).length < 2 ^ (prefixWord ++ tailWord_2334038).sum := by decide
  have hdescent : baseEnd_2334038 < baseStart_2334038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334048 : List Nat := [2, 1, 1, 3, 4, 3, 1, 2, 2, 1, 3]
def baseStart_2334048 : Nat := 118140960795 + 2334048 * 2 ^ 59
def prefixEnd_2334048 : Nat := 4983230072969 + 3 ^ 40 * 2334048 * 2
def baseEnd_2334048 : Nat := 1198488494665389260165915

theorem tailTrace_2334048 : CollatzResearch.WordTrace tailWord_2334048 prefixEnd_2334048 1198488494665389260165915 := by
  unfold tailWord_2334048
  simp only [CollatzResearch.WordTrace]
  refine ⟨42564862124075097253729399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56753149498766796338305865 42564862124075097253729399)
  ·
    refine ⟨63847293186112645880594099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42564862124075097253729399 63847293186112645880594099)
    ·
      refine ⟨95770939779168968820891149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63847293186112645880594099 95770939779168968820891149)
      ·
        refine ⟨35914102417188363307834181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95770939779168968820891149 35914102417188363307834181)
        ·
          refine ⟨6733894203222818120218909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35914102417188363307834181 6733894203222818120218909)
          ·
            refine ⟨2525210326208556795082091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6733894203222818120218909 2525210326208556795082091)
            ·
              refine ⟨3787815489312835192623137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2525210326208556795082091 3787815489312835192623137)
              ·
                refine ⟨2840861616984626394467353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3787815489312835192623137 2840861616984626394467353)
                ·
                  refine ⟨2130646212738469795850515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2840861616984626394467353 2130646212738469795850515)
                  ·
                    refine ⟨3195969319107704693775773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2130646212738469795850515 3195969319107704693775773)
                    ·
                      refine ⟨1198488494665389260165915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3195969319107704693775773 1198488494665389260165915)
                      ·
                        rfl

theorem cell23_2334048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_2334048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334048 prefixEnd_2334048 := by exact prefixLift 2334048
  have htrace : WordTrace (prefixWord ++ tailWord_2334048) baseStart_2334048 baseEnd_2334048 := by
    simpa [prefixWord, tailWord_2334048, baseEnd_2334048] using wordTrace_append hprefix tailTrace_2334048
  have hstable : (prefixWord ++ tailWord_2334048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334048).length < 2 ^ (prefixWord ++ tailWord_2334048).sum := by decide
  have hdescent : baseEnd_2334048 < baseStart_2334048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334057 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 2, 4, 3]
def baseStart_2334057 : Nat := 118140960795 + 2334057 * 2 ^ 59
def prefixEnd_2334057 : Nat := 4983230072969 + 3 ^ 40 * 2334057 * 2
def baseEnd_2334057 : Nat := 1198493115991279724953373

theorem tailTrace_2334057 : CollatzResearch.WordTrace tailWord_2334057 prefixEnd_2334057 1198493115991279724953373 := by
  unfold tailWord_2334057
  simp only [CollatzResearch.WordTrace]
  refine ⟨85130052505117589044536425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56753368336745059363024283 85130052505117589044536425)
  ·
    refine ⟨63847539378838191783402319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85130052505117589044536425 63847539378838191783402319)
    ·
      refine ⟨95771309068257287675103479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63847539378838191783402319 95771309068257287675103479)
      ·
        refine ⟨143656963602385931512655219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95771309068257287675103479 143656963602385931512655219)
        ·
          refine ⟨215485445403578897268982829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143656963602385931512655219 215485445403578897268982829)
          ·
            refine ⟨80807042026342086475868561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215485445403578897268982829 80807042026342086475868561)
            ·
              refine ⟨60605281519756564856901421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80807042026342086475868561 60605281519756564856901421)
              ·
                refine ⟨22726980569908711821338033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60605281519756564856901421 22726980569908711821338033)
                ·
                  refine ⟨17045235427431533866003525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22726980569908711821338033 17045235427431533866003525)
                  ·
                    refine ⟨3195981642643412599875661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17045235427431533866003525 3195981642643412599875661)
                    ·
                      refine ⟨1198493115991279724953373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3195981642643412599875661 1198493115991279724953373)
                      ·
                        rfl

theorem cell23_2334057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4, 3].length) (baseStart_2334057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334057 prefixEnd_2334057 := by exact prefixLift 2334057
  have htrace : WordTrace (prefixWord ++ tailWord_2334057) baseStart_2334057 baseEnd_2334057 := by
    simpa [prefixWord, tailWord_2334057, baseEnd_2334057] using wordTrace_append hprefix tailTrace_2334057
  have hstable : (prefixWord ++ tailWord_2334057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334057).length < 2 ^ (prefixWord ++ tailWord_2334057).sum := by decide
  have hdescent : baseEnd_2334057 < baseStart_2334057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334077 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 7]
def baseStart_2334077 : Nat := 118140960795 + 2334077 * 2 ^ 59
def prefixEnd_2334077 : Nat := 4983230072969 + 3 ^ 40 * 2334077 * 2
def baseEnd_2334077 : Nat := 133167042844929960744809

theorem tailTrace_2334077 : CollatzResearch.WordTrace tailWord_2334077 prefixEnd_2334077 133167042844929960744809 := by
  unfold tailWord_2334077
  simp only [CollatzResearch.WordTrace]
  refine ⟨85130781965045132460264485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56753854643363421640176323 85130781965045132460264485)
  ·
    refine ⟨15962021618445962336299591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85130781965045132460264485 15962021618445962336299591)
    ·
      refine ⟨23943032427668943504449387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15962021618445962336299591 23943032427668943504449387)
      ·
        refine ⟨35914548641503415256674081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23943032427668943504449387 35914548641503415256674081)
        ·
          refine ⟨26935911481127561442505561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35914548641503415256674081 26935911481127561442505561)
          ·
            refine ⟨20201933610845671081879171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26935911481127561442505561 20201933610845671081879171)
            ·
              refine ⟨30302900416268506622818757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20201933610845671081879171 30302900416268506622818757)
              ·
                refine ⟨5681793828050344991778517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30302900416268506622818757 5681793828050344991778517)
                ·
                  refine ⟨133167042844929960744809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5681793828050344991778517 133167042844929960744809)
                  ·
                    rfl

theorem cell23_2334077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_2334077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334077 prefixEnd_2334077 := by exact prefixLift 2334077
  have htrace : WordTrace (prefixWord ++ tailWord_2334077) baseStart_2334077 baseEnd_2334077 := by
    simpa [prefixWord, tailWord_2334077, baseEnd_2334077] using wordTrace_append hprefix tailTrace_2334077
  have hstable : (prefixWord ++ tailWord_2334077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334077).length < 2 ^ (prefixWord ++ tailWord_2334077).sum := by decide
  have hdescent : baseEnd_2334077 < baseStart_2334077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334127 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 4]
def baseStart_2334127 : Nat := 118140960795 + 2334127 * 2 ^ 59
def prefixEnd_2334127 : Nat := 4983230072969 + 3 ^ 40 * 2334127 * 2
def baseEnd_2334127 : Nat := 1198529059637094451078051

theorem tailTrace_2334127 : CollatzResearch.WordTrace tailWord_2334127 prefixEnd_2334127 1198529059637094451078051 := by
  unfold tailWord_2334127
  simp only [CollatzResearch.WordTrace]
  refine ⟨85132605614863990999584635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56755070409909327333056423 85132605614863990999584635)
  ·
    refine ⟨127698908422295986499376953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85132605614863990999584635 127698908422295986499376953)
    ·
      refine ⟨95774181316721989874532715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127698908422295986499376953 95774181316721989874532715)
      ·
        refine ⟨143661271975082984811799073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95774181316721989874532715 143661271975082984811799073)
        ·
          refine ⟨107745953981312238608849305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143661271975082984811799073 107745953981312238608849305)
          ·
            refine ⟨80809465485984178956636979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107745953981312238608849305 80809465485984178956636979)
            ·
              refine ⟨121214198228976268434955469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80809465485984178956636979 121214198228976268434955469)
              ·
                refine ⟨45455324335866100663108301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 121214198228976268434955469 45455324335866100663108301)
                ·
                  refine ⟨17045746625949787748665613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45455324335866100663108301 17045746625949787748665613)
                  ·
                    refine ⟨6392154984731170405749605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17045746625949787748665613 6392154984731170405749605)
                    ·
                      refine ⟨1198529059637094451078051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6392154984731170405749605 1198529059637094451078051)
                      ·
                        rfl

theorem cell23_2334127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 4].length) (baseStart_2334127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334127 prefixEnd_2334127 := by exact prefixLift 2334127
  have htrace : WordTrace (prefixWord ++ tailWord_2334127) baseStart_2334127 baseEnd_2334127 := by
    simpa [prefixWord, tailWord_2334127, baseEnd_2334127] using wordTrace_append hprefix tailTrace_2334127
  have hstable : (prefixWord ++ tailWord_2334127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334127).length < 2 ^ (prefixWord ++ tailWord_2334127).sum := by decide
  have hdescent : baseEnd_2334127 < baseStart_2334127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334144 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 4]
def baseStart_2334144 : Nat := 118140960795 + 2334144 * 2 ^ 59
def prefixEnd_2334144 : Nat := 4983230072969 + 3 ^ 40 * 2334144 * 2
def baseEnd_2334144 : Nat := 1198537788808220884565473

theorem tailTrace_2334144 : CollatzResearch.WordTrace tailWord_2334144 prefixEnd_2334144 1198537788808220884565473 := by
  unfold tailWord_2334144
  simp only [CollatzResearch.WordTrace]
  refine ⟨42566612827901201451476743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56755483770534935268635657 42566612827901201451476743)
  ·
    refine ⟨63849919241851802177215115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42566612827901201451476743 63849919241851802177215115)
    ·
      refine ⟨95774878862777703265822673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63849919241851802177215115 95774878862777703265822673)
      ·
        refine ⟨71831159147083277449367005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95774878862777703265822673 71831159147083277449367005)
        ·
          refine ⟨26936684680156229043512627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71831159147083277449367005 26936684680156229043512627)
          ·
            refine ⟨40405027020234343565268941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26936684680156229043512627 40405027020234343565268941)
            ·
              refine ⟨15151885132587878836975853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40405027020234343565268941 15151885132587878836975853)
              ·
                refine ⟨5681956924720454563865945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15151885132587878836975853 5681956924720454563865945)
                ·
                  refine ⟨4261467693540340922899459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5681956924720454563865945 4261467693540340922899459)
                  ·
                    refine ⟨6392201540310511384349189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4261467693540340922899459 6392201540310511384349189)
                    ·
                      refine ⟨1198537788808220884565473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6392201540310511384349189 1198537788808220884565473)
                      ·
                        rfl

theorem cell23_2334144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_2334144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334144 prefixEnd_2334144 := by exact prefixLift 2334144
  have htrace : WordTrace (prefixWord ++ tailWord_2334144) baseStart_2334144 baseEnd_2334144 := by
    simpa [prefixWord, tailWord_2334144, baseEnd_2334144] using wordTrace_append hprefix tailTrace_2334144
  have hstable : (prefixWord ++ tailWord_2334144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334144).length < 2 ^ (prefixWord ++ tailWord_2334144).sum := by decide
  have hdescent : baseEnd_2334144 < baseStart_2334144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334167 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 8]
def baseStart_2334167 : Nat := 118140960795 + 2334167 * 2 ^ 59
def prefixEnd_2334167 : Nat := 4983230072969 + 3 ^ 40 * 2334167 * 2
def baseEnd_2334167 : Nat := 133172177651474921619763

theorem tailTrace_2334167 : CollatzResearch.WordTrace tailWord_2334167 prefixEnd_2334167 133172177651474921619763 := by
  unfold tailWord_2334167
  simp only [CollatzResearch.WordTrace]
  refine ⟨85134064534719077831040755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56756043023146051887360503 85134064534719077831040755)
  ·
    refine ⟨127701096802078616746561133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85134064534719077831040755 127701096802078616746561133)
    ·
      refine ⟨47887911300779481279960425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127701096802078616746561133 47887911300779481279960425)
      ·
        refine ⟨35915933475584610959970319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47887911300779481279960425 35915933475584610959970319)
        ·
          refine ⟨53873900213376916439955479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35915933475584610959970319 53873900213376916439955479)
          ·
            refine ⟨80810850320065374659933219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53873900213376916439955479 80810850320065374659933219)
            ·
              refine ⟨121216275480098061989899829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80810850320065374659933219 121216275480098061989899829)
              ·
                refine ⟨11364025826259193311553109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 121216275480098061989899829 11364025826259193311553109)
                ·
                  refine ⟨133172177651474921619763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11364025826259193311553109 133172177651474921619763)
                  ·
                    rfl

theorem cell23_2334167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 8].length) (baseStart_2334167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334167 prefixEnd_2334167 := by exact prefixLift 2334167
  have htrace : WordTrace (prefixWord ++ tailWord_2334167) baseStart_2334167 baseEnd_2334167 := by
    simpa [prefixWord, tailWord_2334167, baseEnd_2334167] using wordTrace_append hprefix tailTrace_2334167
  have hstable : (prefixWord ++ tailWord_2334167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334167).length < 2 ^ (prefixWord ++ tailWord_2334167).sum := by decide
  have hdescent : baseEnd_2334167 < baseStart_2334167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334184 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 6]
def baseStart_2334184 : Nat := 118140960795 + 2334184 * 2 ^ 59
def prefixEnd_2334184 : Nat := 4983230072969 + 3 ^ 40 * 2334184 * 2
def baseEnd_2334184 : Nat := 133173147559377858673921

theorem tailTrace_2334184 : CollatzResearch.WordTrace tailWord_2334184 prefixEnd_2334184 133173147559377858673921 := by
  unfold tailWord_2334184
  simp only [CollatzResearch.WordTrace]
  refine ⟨42567342287828744867204803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56756456383771659822939737 42567342287828744867204803)
  ·
    refine ⟨63851013431743117300807205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42567342287828744867204803 63851013431743117300807205)
    ·
      refine ⟨11972065018451834493901351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63851013431743117300807205 11972065018451834493901351)
      ·
        refine ⟨17958097527677751740852027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11972065018451834493901351 17958097527677751740852027)
        ·
          refine ⟨26937146291516627611278041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17958097527677751740852027 26937146291516627611278041)
          ·
            refine ⟨20202859718637470708458531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26937146291516627611278041 20202859718637470708458531)
            ·
              refine ⟨30304289577956206062687797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20202859718637470708458531 30304289577956206062687797)
              ·
                refine ⟨2841027147933394318376981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30304289577956206062687797 2841027147933394318376981)
                ·
                  refine ⟨133173147559377858673921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2841027147933394318376981 133173147559377858673921)
                  ·
                    rfl

theorem cell23_2334184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 6].length) (baseStart_2334184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334184 prefixEnd_2334184 := by exact prefixLift 2334184
  have htrace : WordTrace (prefixWord ++ tailWord_2334184) baseStart_2334184 baseEnd_2334184 := by
    simpa [prefixWord, tailWord_2334184, baseEnd_2334184] using wordTrace_append hprefix tailTrace_2334184
  have hstable : (prefixWord ++ tailWord_2334184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334184).length < 2 ^ (prefixWord ++ tailWord_2334184).sum := by decide
  have hdescent : baseEnd_2334184 < baseStart_2334184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334187 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 6]
def baseStart_2334187 : Nat := 118140960795 + 2334187 * 2 ^ 59
def prefixEnd_2334187 : Nat := 4983230072969 + 3 ^ 40 * 2334187 * 2
def baseEnd_2334187 : Nat := 1198559868476364216327775

theorem tailTrace_2334187 : CollatzResearch.WordTrace tailWord_2334187 prefixEnd_2334187 1198559868476364216327775 := by
  unfold tailWord_2334187
  simp only [CollatzResearch.WordTrace]
  refine ⟨85134793994646621246768815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56756529329764414164512543 85134793994646621246768815)
  ·
    refine ⟨127702190991969931870153223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85134793994646621246768815 127702190991969931870153223)
    ·
      refine ⟨191553286487954897805229835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127702190991969931870153223 191553286487954897805229835)
      ·
        refine ⟨287329929731932346707844753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191553286487954897805229835 287329929731932346707844753)
        ·
          refine ⟨215497447298949260030883565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287329929731932346707844753 215497447298949260030883565)
          ·
            refine ⟨80811542737105972511581337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 215497447298949260030883565 80811542737105972511581337)
            ·
              refine ⟨60608657052829479383686003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80811542737105972511581337 60608657052829479383686003)
              ·
                refine ⟨90912985579244219075529005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60608657052829479383686003 90912985579244219075529005)
                ·
                  refine ⟨34092369592216582153323377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90912985579244219075529005 34092369592216582153323377)
                  ·
                    refine ⟨25569277194162436614992533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34092369592216582153323377 25569277194162436614992533)
                    ·
                      refine ⟨1198559868476364216327775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25569277194162436614992533 1198559868476364216327775)
                      ·
                        rfl

theorem cell23_2334187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 6].length) (baseStart_2334187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334187 prefixEnd_2334187 := by exact prefixLift 2334187
  have htrace : WordTrace (prefixWord ++ tailWord_2334187) baseStart_2334187 baseEnd_2334187 := by
    simpa [prefixWord, tailWord_2334187, baseEnd_2334187] using wordTrace_append hprefix tailTrace_2334187
  have hstable : (prefixWord ++ tailWord_2334187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334187).length < 2 ^ (prefixWord ++ tailWord_2334187).sum := by decide
  have hdescent : baseEnd_2334187 < baseStart_2334187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334198 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_2334198 : Nat := 118140960795 + 2334198 * 2 ^ 59
def prefixEnd_2334198 : Nat := 4983230072969 + 3 ^ 40 * 2334198 * 2
def baseEnd_2334198 : Nat := 1198565516763563673290225

theorem tailTrace_2334198 : CollatzResearch.WordTrace tailWord_2334198 prefixEnd_2334198 1198565516763563673290225 := by
  unfold tailWord_2334198
  simp only [CollatzResearch.WordTrace]
  refine ⟨5320949699850423132838703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56756796798404513416946165 5320949699850423132838703)
  ·
    refine ⟨7981424549775634699258055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5320949699850423132838703 7981424549775634699258055)
    ·
      refine ⟨11972136824663452048887083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7981424549775634699258055 11972136824663452048887083)
      ·
        refine ⟨17958205236995178073330625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11972136824663452048887083 17958205236995178073330625)
        ·
          refine ⟨13468653927746383554997969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17958205236995178073330625 13468653927746383554997969)
          ·
            refine ⟨10101490445809787666248477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13468653927746383554997969 10101490445809787666248477)
            ·
              refine ⟨3788058917178670374843179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10101490445809787666248477 3788058917178670374843179)
              ·
                refine ⟨5682088375768005562264769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788058917178670374843179 5682088375768005562264769)
                ·
                  refine ⟨4261566281826004171698577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5682088375768005562264769 4261566281826004171698577)
                  ·
                    refine ⟨3196174711369503128773933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4261566281826004171698577 3196174711369503128773933)
                    ·
                      refine ⟨1198565516763563673290225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3196174711369503128773933 1198565516763563673290225)
                      ·
                        rfl

theorem cell23_2334198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_2334198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334198 prefixEnd_2334198 := by exact prefixLift 2334198
  have htrace : WordTrace (prefixWord ++ tailWord_2334198) baseStart_2334198 baseEnd_2334198 := by
    simpa [prefixWord, tailWord_2334198, baseEnd_2334198] using wordTrace_append hprefix tailTrace_2334198
  have hstable : (prefixWord ++ tailWord_2334198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334198).length < 2 ^ (prefixWord ++ tailWord_2334198).sum := by decide
  have hdescent : baseEnd_2334198 < baseStart_2334198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334261 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2334261 : Nat := 118140960795 + 2334261 * 2 ^ 59
def prefixEnd_2334261 : Nat := 4983230072969 + 3 ^ 40 * 2334261 * 2
def baseEnd_2334261 : Nat := 399532622014932308934145

theorem tailTrace_2334261 : CollatzResearch.WordTrace tailWord_2334261 prefixEnd_2334261 399532622014932308934145 := by
  unfold tailWord_2334261
  simp only [CollatzResearch.WordTrace]
  refine ⟨85137492996378531884962637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56758328664252354589975091 85137492996378531884962637)
  ·
    refine ⟨31926559873641949456860989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85137492996378531884962637 31926559873641949456860989)
    ·
      refine ⟨11972459952615731046322871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31926559873641949456860989 11972459952615731046322871)
      ·
        refine ⟨17958689928923596569484307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11972459952615731046322871 17958689928923596569484307)
        ·
          refine ⟨26938034893385394854226461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17958689928923596569484307 26938034893385394854226461)
          ·
            refine ⟨10101763085019523070334923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26938034893385394854226461 10101763085019523070334923)
            ·
              refine ⟨15152644627529284605502385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10101763085019523070334923 15152644627529284605502385)
              ·
                refine ⟨11364483470646963454126789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15152644627529284605502385 11364483470646963454126789)
                ·
                  refine ⟨2130840650746305647648773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11364483470646963454126789 2130840650746305647648773)
                  ·
                    refine ⟨399532622014932308934145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2130840650746305647648773 399532622014932308934145)
                    ·
                      rfl

theorem cell23_2334261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2334261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334261 prefixEnd_2334261 := by exact prefixLift 2334261
  have htrace : WordTrace (prefixWord ++ tailWord_2334261) baseStart_2334261 baseEnd_2334261 := by
    simpa [prefixWord, tailWord_2334261, baseEnd_2334261] using wordTrace_append hprefix tailTrace_2334261
  have hstable : (prefixWord ++ tailWord_2334261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334261).length < 2 ^ (prefixWord ++ tailWord_2334261).sum := by decide
  have hdescent : baseEnd_2334261 < baseStart_2334261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334271 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 5]
def baseStart_2334271 : Nat := 118140960795 + 2334271 * 2 ^ 59
def prefixEnd_2334271 : Nat := 4983230072969 + 3 ^ 40 * 2334271 * 2
def baseEnd_2334271 : Nat := 1198603000851341887677389

theorem tailTrace_2334271 : CollatzResearch.WordTrace tailWord_2334271 prefixEnd_2334271 1198603000851341887677389 := by
  unfold tailWord_2334271
  simp only [CollatzResearch.WordTrace]
  refine ⟨85137857726342303592826667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56758571817561535728551111 85137857726342303592826667)
  ·
    refine ⟨127706786589513455389240001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85137857726342303592826667 127706786589513455389240001)
    ·
      refine ⟨95780089942135091541930001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127706786589513455389240001 95780089942135091541930001)
      ·
        refine ⟨71835067456601318656447501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95780089942135091541930001 71835067456601318656447501)
        ·
          refine ⟨26938150296225494496167813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71835067456601318656447501 26938150296225494496167813)
          ·
            refine ⟨5050903180542280218031465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26938150296225494496167813 5050903180542280218031465)
            ·
              refine ⟨3788177385406710163523599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5050903180542280218031465 3788177385406710163523599)
              ·
                refine ⟨5682266078110065245285399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788177385406710163523599 5682266078110065245285399)
                ·
                  refine ⟨8523399117165097867928099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5682266078110065245285399 8523399117165097867928099)
                  ·
                    refine ⟨12785098675747646801892149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8523399117165097867928099 12785098675747646801892149)
                    ·
                      refine ⟨1198603000851341887677389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12785098675747646801892149 1198603000851341887677389)
                      ·
                        rfl

theorem cell23_2334271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_2334271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334271 prefixEnd_2334271 := by exact prefixLift 2334271
  have htrace : WordTrace (prefixWord ++ tailWord_2334271) baseStart_2334271 baseEnd_2334271 := by
    simpa [prefixWord, tailWord_2334271, baseEnd_2334271] using wordTrace_append hprefix tailTrace_2334271
  have hstable : (prefixWord ++ tailWord_2334271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334271).length < 2 ^ (prefixWord ++ tailWord_2334271).sum := by decide
  have hdescent : baseEnd_2334271 < baseStart_2334271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334295 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 2, 4]
def baseStart_2334295 : Nat := 118140960795 + 2334295 * 2 ^ 59
def prefixEnd_2334295 : Nat := 4983230072969 + 3 ^ 40 * 2334295 * 2
def baseEnd_2334295 : Nat := 399538441462349931259093

theorem tailTrace_2334295 : CollatzResearch.WordTrace tailWord_2334295 prefixEnd_2334295 399538441462349931259093 := by
  unfold tailWord_2334295
  simp only [CollatzResearch.WordTrace]
  refine ⟨85138733078255355691700339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56759155385503570461133559 85138733078255355691700339)
  ·
    refine ⟨127708099617383033537550509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85138733078255355691700339 127708099617383033537550509)
    ·
      refine ⟨47890537356518637576581441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127708099617383033537550509 47890537356518637576581441)
      ·
        refine ⟨35917903017388978182436081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47890537356518637576581441 35917903017388978182436081)
        ·
          refine ⟨26938427263041733636827061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35917903017388978182436081 26938427263041733636827061)
          ·
            refine ⟨2525477555910162528452537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26938427263041733636827061 2525477555910162528452537)
            ·
              refine ⟨1894108166932621896339403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2525477555910162528452537 1894108166932621896339403)
              ·
                refine ⟨2841162250398932844509105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894108166932621896339403 2841162250398932844509105)
                ·
                  refine ⟨2130871687799199633381829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2841162250398932844509105 2130871687799199633381829)
                  ·
                    refine ⟨399538441462349931259093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2130871687799199633381829 399538441462349931259093)
                    ·
                      rfl

theorem cell23_2334295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_2334295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334295 prefixEnd_2334295 := by exact prefixLift 2334295
  have htrace : WordTrace (prefixWord ++ tailWord_2334295) baseStart_2334295 baseEnd_2334295 := by
    simpa [prefixWord, tailWord_2334295, baseEnd_2334295] using wordTrace_append hprefix tailTrace_2334295
  have hstable : (prefixWord ++ tailWord_2334295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334295).length < 2 ^ (prefixWord ++ tailWord_2334295).sum := by decide
  have hdescent : baseEnd_2334295 < baseStart_2334295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334381 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 9]
def baseStart_2334381 : Nat := 118140960795 + 2334381 * 2 ^ 59
def prefixEnd_2334381 : Nat := 4983230072969 + 3 ^ 40 * 2334381 * 2
def baseEnd_2334381 : Nat := 133184387080370717477987

theorem tailTrace_2334381 : CollatzResearch.WordTrace tailWord_2334381 prefixEnd_2334381 133184387080370717477987 := by
  unfold tailWord_2334381
  simp only [CollatzResearch.WordTrace]
  refine ⟨85141869755943792379330997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56761246503962528252887331 85141869755943792379330997)
  ·
    refine ⟨7982050289619730535562281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85141869755943792379330997 7982050289619730535562281)
    ·
      refine ⟨5986537717214797901671711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7982050289619730535562281 5986537717214797901671711)
      ·
        refine ⟨8979806575822196852507567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5986537717214797901671711 8979806575822196852507567)
        ·
          refine ⟨13469709863733295278761351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8979806575822196852507567 13469709863733295278761351)
          ·
            refine ⟨20204564795599942918142027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13469709863733295278761351 20204564795599942918142027)
            ·
              refine ⟨30306847193399914377213041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20204564795599942918142027 30306847193399914377213041)
              ·
                refine ⟨22730135395049935782909781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30306847193399914377213041 22730135395049935782909781)
                ·
                  refine ⟨133184387080370717477987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22730135395049935782909781 133184387080370717477987)
                  ·
                    rfl

theorem cell23_2334381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_2334381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334381 prefixEnd_2334381 := by exact prefixLift 2334381
  have htrace : WordTrace (prefixWord ++ tailWord_2334381) baseStart_2334381 baseEnd_2334381 := by
    simpa [prefixWord, tailWord_2334381, baseEnd_2334381] using wordTrace_append hprefix tailTrace_2334381
  have hstable : (prefixWord ++ tailWord_2334381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334381).length < 2 ^ (prefixWord ++ tailWord_2334381).sum := by decide
  have hdescent : baseEnd_2334381 < baseStart_2334381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334398 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_2334398 : Nat := 118140960795 + 2334398 * 2 ^ 59
def prefixEnd_2334398 : Nat := 4983230072969 + 3 ^ 40 * 2334398 * 2
def baseEnd_2334398 : Nat := 133185356988273654532145

theorem tailTrace_2334398 : CollatzResearch.WordTrace tailWord_2334398 prefixEnd_2334398 133185356988273654532145 := by
  unfold tailWord_2334398
  simp only [CollatzResearch.WordTrace]
  refine ⟨10642811224610275535337481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56761659864588136188466565 10642811224610275535337481)
  ·
    refine ⟨7982108418457706651503111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10642811224610275535337481 7982108418457706651503111)
    ·
      refine ⟨11973162627686559977254667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7982108418457706651503111 11973162627686559977254667)
      ·
        refine ⟨17959743941529839965882001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11973162627686559977254667 17959743941529839965882001)
        ·
          refine ⟨13469807956147379974411501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17959743941529839965882001 13469807956147379974411501)
          ·
            refine ⟨5051177983555267490404313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13469807956147379974411501 5051177983555267490404313)
            ·
              refine ⟨3788383487666450617803235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5051177983555267490404313 3788383487666450617803235)
              ·
                refine ⟨5682575231499675926704853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788383487666450617803235 5682575231499675926704853)
                ·
                  refine ⟨133185356988273654532145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5682575231499675926704853 133185356988273654532145)
                  ·
                    rfl

theorem cell23_2334398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_2334398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334398 prefixEnd_2334398 := by exact prefixLift 2334398
  have htrace : WordTrace (prefixWord ++ tailWord_2334398) baseStart_2334398 baseEnd_2334398 := by
    simpa [prefixWord, tailWord_2334398, baseEnd_2334398] using wordTrace_append hprefix tailTrace_2334398
  have hstable : (prefixWord ++ tailWord_2334398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334398).length < 2 ^ (prefixWord ++ tailWord_2334398).sum := by decide
  have hdescent : baseEnd_2334398 < baseStart_2334398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334431 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 4]
def baseStart_2334431 : Nat := 118140960795 + 2334431 * 2 ^ 59
def prefixEnd_2334431 : Nat := 4983230072969 + 3 ^ 40 * 2334431 * 2
def baseEnd_2334431 : Nat := 1198685157756061261676653

theorem tailTrace_2334431 : CollatzResearch.WordTrace tailWord_2334431 prefixEnd_2334431 1198685157756061261676653 := by
  unfold tailWord_2334431
  simp only [CollatzResearch.WordTrace]
  refine ⟨85143693405762650918651147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56762462270508433945767431 85143693405762650918651147)
  ·
    refine ⟨127715540108643976377976721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85143693405762650918651147 127715540108643976377976721)
    ·
      refine ⟨95786655081482982283482541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127715540108643976377976721 95786655081482982283482541)
      ·
        refine ⟨35919995655556118356305953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95786655081482982283482541 35919995655556118356305953)
        ·
          refine ⟨26939996741667088767229465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35919995655556118356305953 26939996741667088767229465)
          ·
            refine ⟨20204997556250316575422099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26939996741667088767229465 20204997556250316575422099)
            ·
              refine ⟨30307496334375474863133149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20204997556250316575422099 30307496334375474863133149)
              ·
                refine ⟨11365311125390803073674931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30307496334375474863133149 11365311125390803073674931)
                ·
                  refine ⟨17047966688086204610512397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11365311125390803073674931 17047966688086204610512397)
                  ·
                    refine ⟨6392987508032326728942149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17047966688086204610512397 6392987508032326728942149)
                    ·
                      refine ⟨1198685157756061261676653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6392987508032326728942149 1198685157756061261676653)
                      ·
                        rfl

theorem cell23_2334431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_2334431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334431 prefixEnd_2334431 := by exact prefixLift 2334431
  have htrace : WordTrace (prefixWord ++ tailWord_2334431) baseStart_2334431 baseEnd_2334431 := by
    simpa [prefixWord, tailWord_2334431, baseEnd_2334431] using wordTrace_append hprefix tailTrace_2334431
  have hstable : (prefixWord ++ tailWord_2334431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334431).length < 2 ^ (prefixWord ++ tailWord_2334431).sum := by decide
  have hdescent : baseEnd_2334431 < baseStart_2334431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334448 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 2, 4, 2]
def baseStart_2334448 : Nat := 118140960795 + 2334448 * 2 ^ 59
def prefixEnd_2334448 : Nat := 4983230072969 + 3 ^ 40 * 2334448 * 2
def baseEnd_2334448 : Nat := 1198693886927187695164075

theorem tailTrace_2334448 : CollatzResearch.WordTrace tailWord_2334448 prefixEnd_2334448 1198693886927187695164075 := by
  unfold tailWord_2334448
  simp only [CollatzResearch.WordTrace]
  refine ⟨42572156723350531411009999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56762875631134041881346665 42572156723350531411009999)
  ·
    refine ⟨63858235085025797116514999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42572156723350531411009999 63858235085025797116514999)
    ·
      refine ⟨95787352627538695674772499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63858235085025797116514999 95787352627538695674772499)
      ·
        refine ⟨143681028941308043512158749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95787352627538695674772499 143681028941308043512158749)
        ·
          refine ⟨53880385852990516317059531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143681028941308043512158749 53880385852990516317059531)
          ·
            refine ⟨80820578779485774475589297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53880385852990516317059531 80820578779485774475589297)
            ·
              refine ⟨60615434084614330856691973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80820578779485774475589297 60615434084614330856691973)
              ·
                refine ⟨11365393890865187035629745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60615434084614330856691973 11365393890865187035629745)
                ·
                  refine ⟨8524045418148890276722309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11365393890865187035629745 8524045418148890276722309)
                  ·
                    refine ⟨1598258515902916926885433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8524045418148890276722309 1598258515902916926885433)
                    ·
                      refine ⟨1198693886927187695164075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1598258515902916926885433 1198693886927187695164075)
                      ·
                        rfl

theorem cell23_2334448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 4, 2].length) (baseStart_2334448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334448 prefixEnd_2334448 := by exact prefixLift 2334448
  have htrace : WordTrace (prefixWord ++ tailWord_2334448) baseStart_2334448 baseEnd_2334448 := by
    simpa [prefixWord, tailWord_2334448, baseEnd_2334448] using wordTrace_append hprefix tailTrace_2334448
  have hstable : (prefixWord ++ tailWord_2334448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334448).length < 2 ^ (prefixWord ++ tailWord_2334448).sum := by decide
  have hdescent : baseEnd_2334448 < baseStart_2334448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334461 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 4]
def baseStart_2334461 : Nat := 118140960795 + 2334461 * 2 ^ 59
def prefixEnd_2334461 : Nat := 4983230072969 + 3 ^ 40 * 2334461 * 2
def baseEnd_2334461 : Nat := 1198700562175696144301515

theorem tailTrace_2334461 : CollatzResearch.WordTrace tailWord_2334461 prefixEnd_2334461 1198700562175696144301515 := by
  unfold tailWord_2334461
  simp only [CollatzResearch.WordTrace]
  refine ⟨85144787595653966042243237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56763191730435977361495491 85144787595653966042243237)
  ·
    refine ⟨15964647674185118632920607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85144787595653966042243237 15964647674185118632920607)
    ·
      refine ⟨23946971511277677949380911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15964647674185118632920607 23946971511277677949380911)
      ·
        refine ⟨35920457266916516924071367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23946971511277677949380911 35920457266916516924071367)
        ·
          refine ⟨53880685900374775386107051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35920457266916516924071367 53880685900374775386107051)
          ·
            refine ⟨80821028850562163079160577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53880685900374775386107051 80821028850562163079160577)
            ·
              refine ⟨60615771637921622309370433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80821028850562163079160577 60615771637921622309370433)
              ·
                refine ⟨45461828728441216732027825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60615771637921622309370433 45461828728441216732027825)
                ·
                  refine ⟨34096371546330912549020869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45461828728441216732027825 34096371546330912549020869)
                  ·
                    refine ⟨6393069664937046102941413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34096371546330912549020869 6393069664937046102941413)
                    ·
                      refine ⟨1198700562175696144301515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6393069664937046102941413 1198700562175696144301515)
                      ·
                        rfl

theorem cell23_2334461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_2334461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334461 prefixEnd_2334461 := by exact prefixLift 2334461
  have htrace : WordTrace (prefixWord ++ tailWord_2334461) baseStart_2334461 baseEnd_2334461 := by
    simpa [prefixWord, tailWord_2334461, baseEnd_2334461] using wordTrace_append hprefix tailTrace_2334461
  have hstable : (prefixWord ++ tailWord_2334461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334461).length < 2 ^ (prefixWord ++ tailWord_2334461).sum := by decide
  have hdescent : baseEnd_2334461 < baseStart_2334461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334482 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2334482 : Nat := 118140960795 + 2334482 * 2 ^ 59
def prefixEnd_2334482 : Nat := 4983230072969 + 3 ^ 40 * 2334482 * 2
def baseEnd_2334482 : Nat := 1198711345269440562138919

theorem tailTrace_2334482 : CollatzResearch.WordTrace tailWord_2334482 prefixEnd_2334482 1198711345269440562138919 := by
  unfold tailWord_2334482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21286388382144471657189425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56763702352385257752505133 21286388382144471657189425)
  ·
    refine ⟨15964791286608353742892069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21286388382144471657189425 15964791286608353742892069)
    ·
      refine ⟨2993398366239066326792263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15964791286608353742892069 2993398366239066326792263)
      ·
        refine ⟨4490097549358599490188395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2993398366239066326792263 4490097549358599490188395)
        ·
          refine ⟨6735146324037899235282593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4490097549358599490188395 6735146324037899235282593)
          ·
            refine ⟨5051359743028424426461945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6735146324037899235282593 5051359743028424426461945)
            ·
              refine ⟨3788519807271318319846459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5051359743028424426461945 3788519807271318319846459)
              ·
                refine ⟨5682779710906977479769689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788519807271318319846459 5682779710906977479769689)
                ·
                  refine ⟨4262084783180233109827267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5682779710906977479769689 4262084783180233109827267)
                  ·
                    refine ⟨6393127174770349664740901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4262084783180233109827267 6393127174770349664740901)
                    ·
                      refine ⟨1198711345269440562138919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6393127174770349664740901 1198711345269440562138919)
                      ·
                        rfl

theorem cell23_2334482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2334482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334482 prefixEnd_2334482 := by exact prefixLift 2334482
  have htrace : WordTrace (prefixWord ++ tailWord_2334482) baseStart_2334482 baseEnd_2334482 := by
    simpa [prefixWord, tailWord_2334482, baseEnd_2334482] using wordTrace_append hprefix tailTrace_2334482
  have hstable : (prefixWord ++ tailWord_2334482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334482).length < 2 ^ (prefixWord ++ tailWord_2334482).sum := by decide
  have hdescent : baseEnd_2334482 < baseStart_2334482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334485 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_2334485 : Nat := 118140960795 + 2334485 * 2 ^ 59
def prefixEnd_2334485 : Nat := 4983230072969 + 3 ^ 40 * 2334485 * 2
def baseEnd_2334485 : Nat := 1198712885711404050401405

theorem tailTrace_2334485 : CollatzResearch.WordTrace tailWord_2334485 prefixEnd_2334485 1198712885711404050401405 := by
  unfold tailWord_2334485
  simp only [CollatzResearch.WordTrace]
  refine ⟨85145662947567018141116909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56763775298378012094077939 85145662947567018141116909)
  ·
    refine ⟨31929623605337631802918841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85145662947567018141116909 31929623605337631802918841)
    ·
      refine ⟨23947217704003223852189131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31929623605337631802918841 23947217704003223852189131)
      ·
        refine ⟨35920826556004835778283697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23947217704003223852189131 35920826556004835778283697)
        ·
          refine ⟨26940619917003626833712773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35920826556004835778283697 26940619917003626833712773)
          ·
            refine ⟨5051366234438180031321145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26940619917003626833712773 5051366234438180031321145)
            ·
              refine ⟨3788524675828635023490859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5051366234438180031321145 3788524675828635023490859)
              ·
                refine ⟨5682787013742952535236289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788524675828635023490859 5682787013742952535236289)
                ·
                  refine ⟨4262090260307214401427217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5682787013742952535236289 4262090260307214401427217)
                  ·
                    refine ⟨3196567695230410801070413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4262090260307214401427217 3196567695230410801070413)
                    ·
                      refine ⟨1198712885711404050401405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3196567695230410801070413 1198712885711404050401405)
                      ·
                        rfl

theorem cell23_2334485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_2334485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334485 prefixEnd_2334485 := by exact prefixLift 2334485
  have htrace : WordTrace (prefixWord ++ tailWord_2334485) baseStart_2334485 baseEnd_2334485 := by
    simpa [prefixWord, tailWord_2334485, baseEnd_2334485] using wordTrace_append hprefix tailTrace_2334485
  have hstable : (prefixWord ++ tailWord_2334485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334485).length < 2 ^ (prefixWord ++ tailWord_2334485).sum := by decide
  have hdescent : baseEnd_2334485 < baseStart_2334485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334538 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_2334538 : Nat := 118140960795 + 2334538 * 2 ^ 59
def prefixEnd_2334538 : Nat := 4983230072969 + 3 ^ 40 * 2334538 * 2
def baseEnd_2334538 : Nat := 1198740100186092343038661

theorem tailTrace_2334538 : CollatzResearch.WordTrace tailWord_2334538 prefixEnd_2334538 1198740100186092343038661 := by
  unfold tailWord_2334538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21286899004093752048199067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56765064010916672128530845 21286899004093752048199067)
  ·
    refine ⟨31930348506140628072298601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21286899004093752048199067 31930348506140628072298601)
    ·
      refine ⟨23947761379605471054223951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31930348506140628072298601 23947761379605471054223951)
      ·
        refine ⟨35921642069408206581335927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23947761379605471054223951 35921642069408206581335927)
        ·
          refine ⟨53882463104112309872003891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35921642069408206581335927 53882463104112309872003891)
          ·
            refine ⟨80823694656168464808005837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53882463104112309872003891 80823694656168464808005837)
            ·
              refine ⟨30308885496063174303002189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80823694656168464808005837 30308885496063174303002189)
              ·
                refine ⟨11365832061023690363625821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30308885496063174303002189 11365832061023690363625821)
                ·
                  refine ⟨4262187022883883886359683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11365832061023690363625821 4262187022883883886359683)
                  ·
                    refine ⟨6393280534325825829539525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4262187022883883886359683 6393280534325825829539525)
                    ·
                      refine ⟨1198740100186092343038661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6393280534325825829539525 1198740100186092343038661)
                      ·
                        rfl

theorem cell23_2334538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_2334538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334538 prefixEnd_2334538 := by exact prefixLift 2334538
  have htrace : WordTrace (prefixWord ++ tailWord_2334538) baseStart_2334538 baseEnd_2334538 := by
    simpa [prefixWord, tailWord_2334538, baseEnd_2334538] using wordTrace_append hprefix tailTrace_2334538
  have hstable : (prefixWord ++ tailWord_2334538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334538).length < 2 ^ (prefixWord ++ tailWord_2334538).sum := by decide
  have hdescent : baseEnd_2334538 < baseStart_2334538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334549 : List Nat := [1, 3, 2, 2, 2, 3, 2, 3, 1, 1, 3]
def baseStart_2334549 : Nat := 118140960795 + 2334549 * 2 ^ 59
def prefixEnd_2334549 : Nat := 4983230072969 + 3 ^ 40 * 2334549 * 2
def baseEnd_2334549 : Nat := 1198745748473291800001111

theorem tailTrace_2334549 : CollatzResearch.WordTrace tailWord_2334549 prefixEnd_2334549 1198745748473291800001111 := by
  unfold tailWord_2334549
  simp only [CollatzResearch.WordTrace]
  refine ⟨85147997219335157071446701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56765331479556771380964467 85147997219335157071446701)
  ·
    refine ⟨31930498957250683901792513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85147997219335157071446701 31930498957250683901792513)
    ·
      refine ⟨23947874217938012926344385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31930498957250683901792513 23947874217938012926344385)
      ·
        refine ⟨17960905663453509694758289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23947874217938012926344385 17960905663453509694758289)
        ·
          refine ⟨13470679247590132271068717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17960905663453509694758289 13470679247590132271068717)
          ·
            refine ⟨5051504717846299601650769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13470679247590132271068717 5051504717846299601650769)
            ·
              refine ⟨3788628538384724701238077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5051504717846299601650769 3788628538384724701238077)
              ·
                refine ⟨1420735701894271762964279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3788628538384724701238077 1420735701894271762964279)
                ·
                  refine ⟨2131103552841407644446419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420735701894271762964279 2131103552841407644446419)
                  ·
                    refine ⟨3196655329262111466669629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2131103552841407644446419 3196655329262111466669629)
                    ·
                      refine ⟨1198745748473291800001111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3196655329262111466669629 1198745748473291800001111)
                      ·
                        rfl

theorem cell23_2334549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_2334549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334549 prefixEnd_2334549 := by exact prefixLift 2334549
  have htrace : WordTrace (prefixWord ++ tailWord_2334549) baseStart_2334549 baseEnd_2334549 := by
    simpa [prefixWord, tailWord_2334549, baseEnd_2334549] using wordTrace_append hprefix tailTrace_2334549
  have hstable : (prefixWord ++ tailWord_2334549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334549).length < 2 ^ (prefixWord ++ tailWord_2334549).sum := by decide
  have hdescent : baseEnd_2334549 < baseStart_2334549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334561 : List Nat := [1, 2, 3, 1, 1, 1, 14]
def baseStart_2334561 : Nat := 118140960795 + 2334561 * 2 ^ 59
def prefixEnd_2334561 : Nat := 4983230072969 + 3 ^ 40 * 2334561 * 2
def baseEnd_2334561 : Nat := 14799406299273404358655

theorem tailTrace_2334561 : CollatzResearch.WordTrace tailWord_2334561 prefixEnd_2334561 14799406299273404358655 := by
  unfold tailWord_2334561
  simp only [CollatzResearch.WordTrace]
  refine ⟨85148434895291683120883537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56765623263527788747255691 85148434895291683120883537)
  ·
    refine ⟨63861326171468762340662653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 85148434895291683120883537 63861326171468762340662653)
    ·
      refine ⟨23947997314300785877748495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63861326171468762340662653 23947997314300785877748495)
      ·
        refine ⟨35921995971451178816622743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23947997314300785877748495 35921995971451178816622743)
        ·
          refine ⟨53882993957176768224934115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35921995971451178816622743 53882993957176768224934115)
          ·
            refine ⟨80824490935765152337401173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53882993957176768224934115 80824490935765152337401173)
            ·
              refine ⟨14799406299273404358655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 80824490935765152337401173 14799406299273404358655)
              ·
                rfl

theorem cell23_2334561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 14].length) (baseStart_2334561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334561 prefixEnd_2334561 := by exact prefixLift 2334561
  have htrace : WordTrace (prefixWord ++ tailWord_2334561) baseStart_2334561 baseEnd_2334561 := by
    simpa [prefixWord, tailWord_2334561, baseEnd_2334561] using wordTrace_append hprefix tailTrace_2334561
  have hstable : (prefixWord ++ tailWord_2334561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334561).length < 2 ^ (prefixWord ++ tailWord_2334561).sum := by decide
  have hdescent : baseEnd_2334561 < baseStart_2334561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334568 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2334568 : Nat := 118140960795 + 2334568 * 2 ^ 59
def prefixEnd_2334568 : Nat := 4983230072969 + 3 ^ 40 * 2334568 * 2
def baseEnd_2334568 : Nat := 1198755504605727225663523

theorem tailTrace_2334568 : CollatzResearch.WordTrace tailWord_2334568 prefixEnd_2334568 1198755504605727225663523 := by
  unfold tailWord_2334568
  simp only [CollatzResearch.WordTrace]
  refine ⟨42574345103133161658194179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56765793470844215544258905 42574345103133161658194179)
  ·
    refine ⟨63861517654699742487291269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42574345103133161658194179 63861517654699742487291269)
    ·
      refine ⟨11974034560256201716367113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63861517654699742487291269 11974034560256201716367113)
      ·
        refine ⟨8980525920192151287275335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11974034560256201716367113 8980525920192151287275335)
        ·
          refine ⟨13470788880288226930913003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8980525920192151287275335 13470788880288226930913003)
          ·
            refine ⟨20206183320432340396369505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13470788880288226930913003 20206183320432340396369505)
            ·
              refine ⟨15154637490324255297277129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20206183320432340396369505 15154637490324255297277129)
              ·
                refine ⟨11365978117743191472957847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15154637490324255297277129 11365978117743191472957847)
                ·
                  refine ⟨17048967176614787209436771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11365978117743191472957847 17048967176614787209436771)
                  ·
                    refine ⟨25573450764922180814155157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17048967176614787209436771 25573450764922180814155157)
                    ·
                      refine ⟨1198755504605727225663523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25573450764922180814155157 1198755504605727225663523)
                      ·
                        rfl

theorem cell23_2334568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2334568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334568 prefixEnd_2334568 := by exact prefixLift 2334568
  have htrace : WordTrace (prefixWord ++ tailWord_2334568) baseStart_2334568 baseEnd_2334568 := by
    simpa [prefixWord, tailWord_2334568, baseEnd_2334568] using wordTrace_append hprefix tailTrace_2334568
  have hstable : (prefixWord ++ tailWord_2334568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334568).length < 2 ^ (prefixWord ++ tailWord_2334568).sum := by decide
  have hdescent : baseEnd_2334568 < baseStart_2334568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334571 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 7]
def baseStart_2334571 : Nat := 118140960795 + 2334571 * 2 ^ 59
def prefixEnd_2334571 : Nat := 4983230072969 + 3 ^ 40 * 2334571 * 2
def baseEnd_2334571 : Nat := 1198757045047690713926009

theorem tailTrace_2334571 : CollatzResearch.WordTrace tailWord_2334571 prefixEnd_2334571 1198757045047690713926009 := by
  unfold tailWord_2334571
  simp only [CollatzResearch.WordTrace]
  refine ⟨85148799625255454828747567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56765866416836969885831711 85148799625255454828747567)
  ·
    refine ⟨127723199437883182243121351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85148799625255454828747567 127723199437883182243121351)
    ·
      refine ⟨191584799156824773364682027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127723199437883182243121351 191584799156824773364682027)
      ·
        refine ⟨287377198735237160047023041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191584799156824773364682027 287377198735237160047023041)
        ·
          refine ⟨215532899051427870035267281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287377198735237160047023041 215532899051427870035267281)
          ·
            refine ⟨161649674288570902526450461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215532899051427870035267281 161649674288570902526450461)
            ·
              refine ⟨60618627858214088447418923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 161649674288570902526450461 60618627858214088447418923)
              ·
                refine ⟨90927941787321132671128385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60618627858214088447418923 90927941787321132671128385)
                ·
                  refine ⟨68195956340490849503346289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90927941787321132671128385 68195956340490849503346289)
                  ·
                    refine ⟨51146967255368137127509717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 68195956340490849503346289 51146967255368137127509717)
                    ·
                      refine ⟨1198757045047690713926009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51146967255368137127509717 1198757045047690713926009)
                      ·
                        rfl

theorem cell23_2334571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 7].length) (baseStart_2334571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334571 prefixEnd_2334571 := by exact prefixLift 2334571
  have htrace : WordTrace (prefixWord ++ tailWord_2334571) baseStart_2334571 baseEnd_2334571 := by
    simpa [prefixWord, tailWord_2334571, baseEnd_2334571] using wordTrace_append hprefix tailTrace_2334571
  have hstable : (prefixWord ++ tailWord_2334571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334571).length < 2 ^ (prefixWord ++ tailWord_2334571).sum := by decide
  have hdescent : baseEnd_2334571 < baseStart_2334571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334572 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 3, 2, 2]
def baseStart_2334572 : Nat := 118140960795 + 2334572 * 2 ^ 59
def prefixEnd_2334572 : Nat := 4983230072969 + 3 ^ 40 * 2334572 * 2
def baseEnd_2334572 : Nat := 1198757558528345210013505

theorem tailTrace_2334572 : CollatzResearch.WordTrace tailWord_2334572 prefixEnd_2334572 1198757558528345210013505 := by
  unfold tailWord_2334572
  simp only [CollatzResearch.WordTrace]
  refine ⟨42574418049125915999766985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56765890732167887999689313 42574418049125915999766985)
  ·
    refine ⟨31930813536844436999825239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42574418049125915999766985 31930813536844436999825239)
    ·
      refine ⟨47896220305266655499737859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31930813536844436999825239 47896220305266655499737859)
      ·
        refine ⟨71844330457899983249606789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47896220305266655499737859 71844330457899983249606789)
        ·
          refine ⟨13470811960856246859301273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71844330457899983249606789 13470811960856246859301273)
          ·
            refine ⟨10103108970642185144475955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13470811960856246859301273 10103108970642185144475955)
            ·
              refine ⟨15154663455963277716713933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10103108970642185144475955 15154663455963277716713933)
              ·
                refine ⟨5682998795986229143767725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15154663455963277716713933 5682998795986229143767725)
                ·
                  refine ⟨2131124548494835928912897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5682998795986229143767725 2131124548494835928912897)
                  ·
                    refine ⟨1598343411371126946684673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2131124548494835928912897 1598343411371126946684673)
                    ·
                      refine ⟨1198757558528345210013505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1598343411371126946684673 1198757558528345210013505)
                      ·
                        rfl

theorem cell23_2334572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_2334572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334572 prefixEnd_2334572 := by exact prefixLift 2334572
  have htrace : WordTrace (prefixWord ++ tailWord_2334572) baseStart_2334572 baseEnd_2334572 := by
    simpa [prefixWord, tailWord_2334572, baseEnd_2334572] using wordTrace_append hprefix tailTrace_2334572
  have hstable : (prefixWord ++ tailWord_2334572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334572).length < 2 ^ (prefixWord ++ tailWord_2334572).sum := by decide
  have hdescent : baseEnd_2334572 < baseStart_2334572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334595 : List Nat := [1, 1, 1, 3, 4, 4, 2, 7]
def baseStart_2334595 : Nat := 118140960795 + 2334595 * 2 ^ 59
def prefixEnd_2334595 : Nat := 4983230072969 + 3 ^ 40 * 2334595 * 2
def baseEnd_2334595 : Nat := 44398865503088837778737

theorem tailTrace_2334595 : CollatzResearch.WordTrace tailWord_2334595 prefixEnd_2334595 44398865503088837778737 := by
  unfold tailWord_2334595
  simp only [CollatzResearch.WordTrace]
  refine ⟨85149674977168506927621239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56766449984779004618414159 85149674977168506927621239)
  ·
    refine ⟨127724512465752760391431859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85149674977168506927621239 127724512465752760391431859)
    ·
      refine ⟨191586768698629140587147789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127724512465752760391431859 191586768698629140587147789)
      ·
        refine ⟨71845038261985927720180421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191586768698629140587147789 71845038261985927720180421)
        ·
          refine ⟨13470944674122361447533829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71845038261985927720180421 13470944674122361447533829)
          ·
            refine ⟨2525802126397942771412593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13470944674122361447533829 2525802126397942771412593)
            ·
              refine ⟨1894351594798457078559445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2525802126397942771412593 1894351594798457078559445)
              ·
                refine ⟨44398865503088837778737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1894351594798457078559445 44398865503088837778737)
                ·
                  rfl

theorem cell23_2334595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 7].length) (baseStart_2334595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334595 prefixEnd_2334595 := by exact prefixLift 2334595
  have htrace : WordTrace (prefixWord ++ tailWord_2334595) baseStart_2334595 baseEnd_2334595 := by
    simpa [prefixWord, tailWord_2334595, baseEnd_2334595] using wordTrace_append hprefix tailTrace_2334595
  have hstable : (prefixWord ++ tailWord_2334595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334595).length < 2 ^ (prefixWord ++ tailWord_2334595).sum := by decide
  have hdescent : baseEnd_2334595 < baseStart_2334595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334623 : List Nat := [1, 1, 2, 5, 3, 1, 3, 2, 1, 2, 2]
def baseStart_2334623 : Nat := 118140960795 + 2334623 * 2 ^ 59
def prefixEnd_2334623 : Nat := 4983230072969 + 3 ^ 40 * 2334623 * 2
def baseEnd_2334623 : Nat := 1198783746041724510475771

theorem tailTrace_2334623 : CollatzResearch.WordTrace tailWord_2334623 prefixEnd_2334623 1198783746041724510475771 := by
  unfold tailWord_2334623
  simp only [CollatzResearch.WordTrace]
  refine ⟨85150696221067067709640523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56767130814044711806427015 85150696221067067709640523)
  ·
    refine ⟨127726044331600601564460785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85150696221067067709640523 127726044331600601564460785)
    ·
      refine ⟨95794533248700451173345589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127726044331600601564460785 95794533248700451173345589)
      ·
        refine ⟨8980737492065667297501149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95794533248700451173345589 8980737492065667297501149)
        ·
          refine ⟨3367776559524625236562931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8980737492065667297501149 3367776559524625236562931)
          ·
            refine ⟨5051664839286937854844397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3367776559524625236562931 5051664839286937854844397)
            ·
              refine ⟨1894374314732601695566649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5051664839286937854844397 1894374314732601695566649)
              ·
                refine ⟨1420780736049451271674987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894374314732601695566649 1420780736049451271674987)
                ·
                  refine ⟨2131171104074176907512481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420780736049451271674987 2131171104074176907512481)
                  ·
                    refine ⟨1598378328055632680634361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2131171104074176907512481 1598378328055632680634361)
                    ·
                      refine ⟨1198783746041724510475771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1598378328055632680634361 1198783746041724510475771)
                      ·
                        rfl

theorem cell23_2334623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_2334623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334623 prefixEnd_2334623 := by exact prefixLift 2334623
  have htrace : WordTrace (prefixWord ++ tailWord_2334623) baseStart_2334623 baseEnd_2334623 := by
    simpa [prefixWord, tailWord_2334623, baseEnd_2334623] using wordTrace_append hprefix tailTrace_2334623
  have hstable : (prefixWord ++ tailWord_2334623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334623).length < 2 ^ (prefixWord ++ tailWord_2334623).sum := by decide
  have hdescent : baseEnd_2334623 < baseStart_2334623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334648 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_2334648 : Nat := 118140960795 + 2334648 * 2 ^ 59
def prefixEnd_2334648 : Nat := 4983230072969 + 3 ^ 40 * 2334648 * 2
def baseEnd_2334648 : Nat := 1198796583058086912663155

theorem tailTrace_2334648 : CollatzResearch.WordTrace tailWord_2334648 prefixEnd_2334648 1198796583058086912663155 := by
  unfold tailWord_2334648
  simp only [CollatzResearch.WordTrace]
  refine ⟨42575804022988248489650299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56767738697317664652867065 42575804022988248489650299)
  ·
    refine ⟨63863706034482372734475449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42575804022988248489650299 63863706034482372734475449)
    ·
      refine ⟨47897779525861779550856587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63863706034482372734475449 47897779525861779550856587)
      ·
        refine ⟨71846669288792669326284881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47897779525861779550856587 71846669288792669326284881)
        ·
          refine ⟨53885001966594501994713661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71846669288792669326284881 53885001966594501994713661)
          ·
            refine ⟨20206875737472938248017623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53885001966594501994713661 20206875737472938248017623)
            ·
              refine ⟨30310313606209407372026435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20206875737472938248017623 30310313606209407372026435)
              ·
                refine ⟨45465470409314111058039653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30310313606209407372026435 45465470409314111058039653)
                ·
                  refine ⟨8524775701746395823382435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45465470409314111058039653 8524775701746395823382435)
                  ·
                    refine ⟨12787163552619593735073653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8524775701746395823382435 12787163552619593735073653)
                    ·
                      refine ⟨1198796583058086912663155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12787163552619593735073653 1198796583058086912663155)
                      ·
                        rfl

theorem cell23_2334648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_2334648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334648 prefixEnd_2334648 := by exact prefixLift 2334648
  have htrace : WordTrace (prefixWord ++ tailWord_2334648) baseStart_2334648 baseEnd_2334648 := by
    simpa [prefixWord, tailWord_2334648, baseEnd_2334648] using wordTrace_append hprefix tailTrace_2334648
  have hstable : (prefixWord ++ tailWord_2334648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334648).length < 2 ^ (prefixWord ++ tailWord_2334648).sum := by decide
  have hdescent : baseEnd_2334648 < baseStart_2334648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334679 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 2, 2, 2]
def baseStart_2334679 : Nat := 118140960795 + 2334679 * 2 ^ 59
def prefixEnd_2334679 : Nat := 4983230072969 + 3 ^ 40 * 2334679 * 2
def baseEnd_2334679 : Nat := 1198812500958376291375513

theorem tailTrace_2334679 : CollatzResearch.WordTrace tailWord_2334679 prefixEnd_2334679 1198812500958376291375513 := by
  unfold tailWord_2334679
  simp only [CollatzResearch.WordTrace]
  refine ⟨85152738708864189273679091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56768492472576126182452727 85152738708864189273679091)
  ·
    refine ⟨127729108063296283910518637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85152738708864189273679091 127729108063296283910518637)
    ·
      refine ⟨47898415523736106466444489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127729108063296283910518637 47898415523736106466444489)
      ·
        refine ⟨35923811642802079849833367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47898415523736106466444489 35923811642802079849833367)
        ·
          refine ⟨53885717464203119774750051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35923811642802079849833367 53885717464203119774750051)
          ·
            refine ⟨80828576196304679662125077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53885717464203119774750051 80828576196304679662125077)
            ·
              refine ⟨3788839509201781859162113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80828576196304679662125077 3788839509201781859162113)
              ·
                refine ⟨2841629631901336394371585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3788839509201781859162113 2841629631901336394371585)
                ·
                  refine ⟨2131222223926002295778689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2841629631901336394371585 2131222223926002295778689)
                  ·
                    refine ⟨1598416667944501721834017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2131222223926002295778689 1598416667944501721834017)
                    ·
                      refine ⟨1198812500958376291375513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1598416667944501721834017 1198812500958376291375513)
                      ·
                        rfl

theorem cell23_2334679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_2334679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334679 prefixEnd_2334679 := by exact prefixLift 2334679
  have htrace : WordTrace (prefixWord ++ tailWord_2334679) baseStart_2334679 baseEnd_2334679 := by
    simpa [prefixWord, tailWord_2334679, baseEnd_2334679] using wordTrace_append hprefix tailTrace_2334679
  have hstable : (prefixWord ++ tailWord_2334679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334679).length < 2 ^ (prefixWord ++ tailWord_2334679).sum := by decide
  have hdescent : baseEnd_2334679 < baseStart_2334679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334715 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 2, 5]
def baseStart_2334715 : Nat := 118140960795 + 2334715 * 2 ^ 59
def prefixEnd_2334715 : Nat := 4983230072969 + 3 ^ 40 * 2334715 * 2
def baseEnd_2334715 : Nat := 399610328753979383508449

theorem tailTrace_2334715 : CollatzResearch.WordTrace tailWord_2334715 prefixEnd_2334715 399610328753979383508449 := by
  unfold tailWord_2334715
  simp only [CollatzResearch.WordTrace]
  refine ⟨85154051736733767421989599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56769367824489178281326399 85154051736733767421989599)
  ·
    refine ⟨127731077605100651132984399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85154051736733767421989599 127731077605100651132984399)
    ·
      refine ⟨191596616407650976699476599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127731077605100651132984399 191596616407650976699476599)
      ·
        refine ⟨287394924611476465049214899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191596616407650976699476599 287394924611476465049214899)
        ·
          refine ⟨431092386917214697573822349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287394924611476465049214899 431092386917214697573822349)
          ·
            refine ⟨161659645093955511590183381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 431092386917214697573822349 161659645093955511590183381)
            ·
              refine ⟨3788897931889582302894923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 161659645093955511590183381 3788897931889582302894923)
              ·
                refine ⟨5683346897834373454342385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3788897931889582302894923 5683346897834373454342385)
                ·
                  refine ⟨4262510173375780090756789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5683346897834373454342385 4262510173375780090756789)
                  ·
                    refine ⟨399610328753979383508449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4262510173375780090756789 399610328753979383508449)
                    ·
                      rfl

theorem cell23_2334715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 2, 5].length) (baseStart_2334715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334715 prefixEnd_2334715 := by exact prefixLift 2334715
  have htrace : WordTrace (prefixWord ++ tailWord_2334715) baseStart_2334715 baseEnd_2334715 := by
    simpa [prefixWord, tailWord_2334715, baseEnd_2334715] using wordTrace_append hprefix tailTrace_2334715
  have hstable : (prefixWord ++ tailWord_2334715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334715).length < 2 ^ (prefixWord ++ tailWord_2334715).sum := by decide
  have hdescent : baseEnd_2334715 < baseStart_2334715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334755 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 3]
def baseStart_2334755 : Nat := 118140960795 + 2334755 * 2 ^ 59
def prefixEnd_2334755 : Nat := 4983230072969 + 3 ^ 40 * 2334755 * 2
def baseEnd_2334755 : Nat := 1198851525488117994025163

theorem tailTrace_2334755 : CollatzResearch.WordTrace tailWord_2334755 prefixEnd_2334755 1198851525488117994025163 := by
  unfold tailWord_2334755
  simp only [CollatzResearch.WordTrace]
  refine ⟨85155510656588854253445719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56770340437725902835630479 85155510656588854253445719)
  ·
    refine ⟨127733265984883281380168579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85155510656588854253445719 127733265984883281380168579)
    ·
      refine ⟨191599898977324922070252869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127733265984883281380168579 191599898977324922070252869)
      ·
        refine ⟨35924981058248422888172413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 191599898977324922070252869 35924981058248422888172413)
        ·
          refine ⟨13471867896843158583064655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35924981058248422888172413 13471867896843158583064655)
          ·
            refine ⟨20207801845264737874596983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13471867896843158583064655 20207801845264737874596983)
            ·
              refine ⟨30311702767897106811895475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20207801845264737874596983 30311702767897106811895475)
              ·
                refine ⟨45467554151845660217843213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30311702767897106811895475 45467554151845660217843213)
                ·
                  refine ⟨17050332806942122581691205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45467554151845660217843213 17050332806942122581691205)
                  ·
                    refine ⟨3196937401301647984067101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17050332806942122581691205 3196937401301647984067101)
                    ·
                      refine ⟨1198851525488117994025163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3196937401301647984067101 1198851525488117994025163)
                      ·
                        rfl

theorem cell23_2334755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_2334755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334755 prefixEnd_2334755 := by exact prefixLift 2334755
  have htrace : WordTrace (prefixWord ++ tailWord_2334755) baseStart_2334755 baseEnd_2334755 := by
    simpa [prefixWord, tailWord_2334755, baseEnd_2334755] using wordTrace_append hprefix tailTrace_2334755
  have hstable : (prefixWord ++ tailWord_2334755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334755).length < 2 ^ (prefixWord ++ tailWord_2334755).sum := by decide
  have hdescent : baseEnd_2334755 < baseStart_2334755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334839 : List Nat := [1, 1, 3, 1, 1, 6, 3, 1, 1, 5]
def baseStart_2334839 : Nat := 118140960795 + 2334839 * 2 ^ 59
def prefixEnd_2334839 : Nat := 4983230072969 + 3 ^ 40 * 2334839 * 2
def baseEnd_2334839 : Nat := 399631552621031888458259

theorem tailTrace_2334839 : CollatzResearch.WordTrace tailWord_2334839 prefixEnd_2334839 399631552621031888458259 := by
  unfold tailWord_2334839
  simp only [CollatzResearch.WordTrace]
  refine ⟨85158574388284536599503571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56772382925523024399669047 85158574388284536599503571)
  ·
    refine ⟨127737861582426804899255357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85158574388284536599503571 127737861582426804899255357)
    ·
      refine ⟨47901698093410051837220759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127737861582426804899255357 47901698093410051837220759)
      ·
        refine ⟨71852547140115077755831139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47901698093410051837220759 71852547140115077755831139)
        ·
          refine ⟨107778820710172616633746709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71852547140115077755831139 107778820710172616633746709)
          ·
            refine ⟨5052132220789341404706877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 107778820710172616633746709 5052132220789341404706877)
            ·
              refine ⟨1894549582796003026765079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5052132220789341404706877 1894549582796003026765079)
              ·
                refine ⟨2841824374194004540147619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894549582796003026765079 2841824374194004540147619)
                ·
                  refine ⟨4262736561291006810221429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841824374194004540147619 4262736561291006810221429)
                  ·
                    refine ⟨399631552621031888458259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4262736561291006810221429 399631552621031888458259)
                    ·
                      rfl

theorem cell23_2334839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_2334839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334839 prefixEnd_2334839 := by exact prefixLift 2334839
  have htrace : WordTrace (prefixWord ++ tailWord_2334839) baseStart_2334839 baseEnd_2334839 := by
    simpa [prefixWord, tailWord_2334839, baseEnd_2334839] using wordTrace_append hprefix tailTrace_2334839
  have hstable : (prefixWord ++ tailWord_2334839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334839).length < 2 ^ (prefixWord ++ tailWord_2334839).sum := by decide
  have hdescent : baseEnd_2334839 < baseStart_2334839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334853 : List Nat := [1, 3, 1, 1, 5, 1, 4, 2, 1, 1, 3]
def baseStart_2334853 : Nat := 118140960795 + 2334853 * 2 ^ 59
def prefixEnd_2334853 : Nat := 4983230072969 + 3 ^ 40 * 2334853 * 2
def baseEnd_2334853 : Nat := 1198901846592258610599713

theorem tailTrace_2334853 : CollatzResearch.WordTrace tailWord_2334853 prefixEnd_2334853 1198901846592258610599713 := by
  unfold tailWord_2334853
  simp only [CollatzResearch.WordTrace]
  refine ⟨85159085010233816990513213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56772723340155877993675475 85159085010233816990513213)
  ·
    refine ⟨31934656878837681371442455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 85159085010233816990513213 31934656878837681371442455)
    ·
      refine ⟨47901985318256522057163683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31934656878837681371442455 47901985318256522057163683)
      ·
        refine ⟨71852977977384783085745525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47901985318256522057163683 71852977977384783085745525)
        ·
          refine ⟨6736216685379823414288643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71852977977384783085745525 6736216685379823414288643)
          ·
            refine ⟨10104325028069735121432965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736216685379823414288643 10104325028069735121432965)
            ·
              refine ⟨1894560942763075335268681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10104325028069735121432965 1894560942763075335268681)
              ·
                refine ⟨1420920707072306501451511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1894560942763075335268681 1420920707072306501451511)
                ·
                  refine ⟨2131381060608459752177267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1420920707072306501451511 2131381060608459752177267)
                  ·
                    refine ⟨3197071590912689628265901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2131381060608459752177267 3197071590912689628265901)
                    ·
                      refine ⟨1198901846592258610599713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3197071590912689628265901 1198901846592258610599713)
                      ·
                        rfl

theorem cell23_2334853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 2, 1, 1, 3].length) (baseStart_2334853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334853 prefixEnd_2334853 := by exact prefixLift 2334853
  have htrace : WordTrace (prefixWord ++ tailWord_2334853) baseStart_2334853 baseEnd_2334853 := by
    simpa [prefixWord, tailWord_2334853, baseEnd_2334853] using wordTrace_append hprefix tailTrace_2334853
  have hstable : (prefixWord ++ tailWord_2334853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334853).length < 2 ^ (prefixWord ++ tailWord_2334853).sum := by decide
  have hdescent : baseEnd_2334853 < baseStart_2334853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334855 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 6]
def baseStart_2334855 : Nat := 118140960795 + 2334855 * 2 ^ 59
def prefixEnd_2334855 : Nat := 4983230072969 + 3 ^ 40 * 2334855 * 2
def baseEnd_2334855 : Nat := 1198902873553567602774703

theorem tailTrace_2334855 : CollatzResearch.WordTrace tailWord_2334855 prefixEnd_2334855 1198902873553567602774703 := by
  unfold tailWord_2334855
  simp only [CollatzResearch.WordTrace]
  refine ⟨85159157956226571332086019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56772771970817714221390679 85159157956226571332086019)
  ·
    refine ⟨127738736934339856998129029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85159157956226571332086019 127738736934339856998129029)
    ·
      refine ⟨23951013175188723187149193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 127738736934339856998129029 23951013175188723187149193)
      ·
        refine ⟨17963259881391542390361895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23951013175188723187149193 17963259881391542390361895)
        ·
          refine ⟨26944889822087313585542843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17963259881391542390361895 26944889822087313585542843)
          ·
            refine ⟨40417334733130970378314265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26944889822087313585542843 40417334733130970378314265)
            ·
              refine ⟨30313001049848227783735699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40417334733130970378314265 30313001049848227783735699)
              ·
                refine ⟨45469501574772341675603549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30313001049848227783735699 45469501574772341675603549)
                ·
                  refine ⟨17051063090539628128351331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45469501574772341675603549 17051063090539628128351331)
                  ·
                    refine ⟨25576594635809442192526997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17051063090539628128351331 25576594635809442192526997)
                    ·
                      refine ⟨1198902873553567602774703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25576594635809442192526997 1198902873553567602774703)
                      ·
                        rfl

theorem cell23_2334855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_2334855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334855 prefixEnd_2334855 := by exact prefixLift 2334855
  have htrace : WordTrace (prefixWord ++ tailWord_2334855) baseStart_2334855 baseEnd_2334855 := by
    simpa [prefixWord, tailWord_2334855, baseEnd_2334855] using wordTrace_append hprefix tailTrace_2334855
  have hstable : (prefixWord ++ tailWord_2334855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334855).length < 2 ^ (prefixWord ++ tailWord_2334855).sum := by decide
  have hdescent : baseEnd_2334855 < baseStart_2334855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334876 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 3, 2, 2]
def baseStart_2334876 : Nat := 118140960795 + 2334876 * 2 ^ 59
def prefixEnd_2334876 : Nat := 4983230072969 + 3 ^ 40 * 2334876 * 2
def baseEnd_2334876 : Nat := 1198913656647312020612107

theorem tailTrace_2334876 : CollatzResearch.WordTrace tailWord_2334876 prefixEnd_2334876 1198913656647312020612107 := by
  unfold tailWord_2334876
  simp only [CollatzResearch.WordTrace]
  refine ⟨42579961944575245959300241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56773282592766994612400321 42579961944575245959300241)
  ·
    refine ⟨31934971458431434469475181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42579961944575245959300241 31934971458431434469475181)
    ·
      refine ⟨11975614296911787926053193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31934971458431434469475181 11975614296911787926053193)
      ·
        refine ⟨8981710722683840944539895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11975614296911787926053193 8981710722683840944539895)
        ·
          refine ⟨13472566084025761416809843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8981710722683840944539895 13472566084025761416809843)
          ·
            refine ⟨20208849126038642125214765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13472566084025761416809843 20208849126038642125214765)
            ·
              refine ⟨7578318422264490796955537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20208849126038642125214765 7578318422264490796955537)
              ·
                refine ⟨5683738816698368097716653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7578318422264490796955537 5683738816698368097716653)
                ·
                  refine ⟨2131402056261888036643745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5683738816698368097716653 2131402056261888036643745)
                  ·
                    refine ⟨1598551542196416027482809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2131402056261888036643745 1598551542196416027482809)
                    ·
                      refine ⟨1198913656647312020612107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1598551542196416027482809 1198913656647312020612107)
                      ·
                        rfl

theorem cell23_2334876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_2334876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334876 prefixEnd_2334876 := by exact prefixLift 2334876
  have htrace : WordTrace (prefixWord ++ tailWord_2334876) baseStart_2334876 baseEnd_2334876 := by
    simpa [prefixWord, tailWord_2334876, baseEnd_2334876] using wordTrace_append hprefix tailTrace_2334876
  have hstable : (prefixWord ++ tailWord_2334876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334876).length < 2 ^ (prefixWord ++ tailWord_2334876).sum := by decide
  have hdescent : baseEnd_2334876 < baseStart_2334876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334879 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2334879 : Nat := 118140960795 + 2334879 * 2 ^ 59
def prefixEnd_2334879 : Nat := 4983230072969 + 3 ^ 40 * 2334879 * 2
def baseEnd_2334879 : Nat := 1198915197089275508874593

theorem tailTrace_2334879 : CollatzResearch.WordTrace tailWord_2334879 prefixEnd_2334879 1198915197089275508874593 := by
  unfold tailWord_2334879
  simp only [CollatzResearch.WordTrace]
  refine ⟨85160033308139623430959691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56773355538759748953973127 85160033308139623430959691)
  ·
    refine ⟨127740049962209435146439537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85160033308139623430959691 127740049962209435146439537)
    ·
      refine ⟨95805037471657076359829653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127740049962209435146439537 95805037471657076359829653)
      ·
        refine ⟨4490861131483925454367015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 95805037471657076359829653 4490861131483925454367015)
        ·
          refine ⟨6736291697225888181550523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4490861131483925454367015 6736291697225888181550523)
          ·
            refine ⟨10104437545838832272325785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736291697225888181550523 10104437545838832272325785)
            ·
              refine ⟨7578328159379124204244339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10104437545838832272325785 7578328159379124204244339)
              ·
                refine ⟨11367492239068686306366509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7578328159379124204244339 11367492239068686306366509)
                ·
                  refine ⟨4262809589650757364887441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11367492239068686306366509 4262809589650757364887441)
                  ·
                    refine ⟨3197107192238068023665581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4262809589650757364887441 3197107192238068023665581)
                    ·
                      refine ⟨1198915197089275508874593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3197107192238068023665581 1198915197089275508874593)
                      ·
                        rfl

theorem cell23_2334879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2334879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334879 prefixEnd_2334879 := by exact prefixLift 2334879
  have htrace : WordTrace (prefixWord ++ tailWord_2334879) baseStart_2334879 baseEnd_2334879 := by
    simpa [prefixWord, tailWord_2334879, baseEnd_2334879] using wordTrace_append hprefix tailTrace_2334879
  have hstable : (prefixWord ++ tailWord_2334879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334879).length < 2 ^ (prefixWord ++ tailWord_2334879).sum := by decide
  have hdescent : baseEnd_2334879 < baseStart_2334879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334890 : List Nat := [3, 1, 5, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2334890 : Nat := 118140960795 + 2334890 * 2 ^ 59
def prefixEnd_2334890 : Nat := 4983230072969 + 3 ^ 40 * 2334890 * 2
def baseEnd_2334890 : Nat := 399640281792158321945681

theorem tailTrace_2334890 : CollatzResearch.WordTrace tailWord_2334890 prefixEnd_2334890 399640281792158321945681 := by
  unfold tailWord_2334890
  simp only [CollatzResearch.WordTrace]
  refine ⟨21290108627774943077402531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56773623007399848206406749 21290108627774943077402531)
  ·
    refine ⟨31935162941662414616103797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21290108627774943077402531 31935162941662414616103797)
    ·
      refine ⟨2993921525780851370259731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31935162941662414616103797 2993921525780851370259731)
      ·
        refine ⟨4490882288671277055389597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2993921525780851370259731 4490882288671277055389597)
        ·
          refine ⟨1684080858251728895771099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4490882288671277055389597 1684080858251728895771099)
          ·
            refine ⟨2526121287377593343656649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684080858251728895771099 2526121287377593343656649)
            ·
              refine ⟨1894590965533195007742487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2526121287377593343656649 1894590965533195007742487)
              ·
                refine ⟨2841886448299792511613731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894590965533195007742487 2841886448299792511613731)
                ·
                  refine ⟨4262829672449688767420597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841886448299792511613731 4262829672449688767420597)
                  ·
                    refine ⟨399640281792158321945681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4262829672449688767420597 399640281792158321945681)
                    ·
                      rfl

theorem cell23_2334890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2334890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334890 prefixEnd_2334890 := by exact prefixLift 2334890
  have htrace : WordTrace (prefixWord ++ tailWord_2334890) baseStart_2334890 baseEnd_2334890 := by
    simpa [prefixWord, tailWord_2334890, baseEnd_2334890] using wordTrace_append hprefix tailTrace_2334890
  have hstable : (prefixWord ++ tailWord_2334890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334890).length < 2 ^ (prefixWord ++ tailWord_2334890).sum := by decide
  have hdescent : baseEnd_2334890 < baseStart_2334890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334893 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 1, 1, 4]
def baseStart_2334893 : Nat := 118140960795 + 2334893 * 2 ^ 59
def prefixEnd_2334893 : Nat := 4983230072969 + 3 ^ 40 * 2334893 * 2
def baseEnd_2334893 : Nat := 1198922385818438454099529

theorem tailTrace_2334893 : CollatzResearch.WordTrace tailWord_2334893 prefixEnd_2334893 1198922385818438454099529 := by
  unfold tailWord_2334893
  simp only [CollatzResearch.WordTrace]
  refine ⟨85160543930088903821969333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56773695953392602547979555 85160543930088903821969333)
  ·
    refine ⟨7983800993445834733309625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85160543930088903821969333 7983800993445834733309625)
    ·
      refine ⟨5987850745084376049982219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7983800993445834733309625 5987850745084376049982219)
      ·
        refine ⟨8981776117626564074973329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5987850745084376049982219 8981776117626564074973329)
        ·
          refine ⟨6736332088219923056229997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8981776117626564074973329 6736332088219923056229997)
          ·
            refine ⟨2526124533082471146086249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6736332088219923056229997 2526124533082471146086249)
            ·
              refine ⟨1894593399811853359564687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2526124533082471146086249 1894593399811853359564687)
              ·
                refine ⟨2841890099717780039347031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894593399811853359564687 2841890099717780039347031)
                ·
                  refine ⟨4262835149576670059020547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841890099717780039347031 4262835149576670059020547)
                  ·
                    refine ⟨6394252724365005088530821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4262835149576670059020547 6394252724365005088530821)
                    ·
                      refine ⟨1198922385818438454099529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6394252724365005088530821 1198922385818438454099529)
                      ·
                        rfl

theorem cell23_2334893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_2334893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334893 prefixEnd_2334893 := by exact prefixLift 2334893
  have htrace : WordTrace (prefixWord ++ tailWord_2334893) baseStart_2334893 baseEnd_2334893 := by
    simpa [prefixWord, tailWord_2334893, baseEnd_2334893] using wordTrace_append hprefix tailTrace_2334893
  have hstable : (prefixWord ++ tailWord_2334893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334893).length < 2 ^ (prefixWord ++ tailWord_2334893).sum := by decide
  have hdescent : baseEnd_2334893 < baseStart_2334893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334926 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_2334926 : Nat := 118140960795 + 2334926 * 2 ^ 59
def prefixEnd_2334926 : Nat := 4983230072969 + 3 ^ 40 * 2334926 * 2
def baseEnd_2334926 : Nat := 1198939330680036824986877

theorem tailTrace_2334926 : CollatzResearch.WordTrace tailWord_2334926 prefixEnd_2334926 1198939330680036824986877 := by
  unfold tailWord_2334926
  simp only [CollatzResearch.WordTrace]
  refine ⟨10645218442371168807240079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56774498359312900305280421 10645218442371168807240079)
  ·
    refine ⟨15967827663556753210860119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10645218442371168807240079 15967827663556753210860119)
    ·
      refine ⟨23951741495335129816290179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15967827663556753210860119 23951741495335129816290179)
      ·
        refine ⟨35927612243002694724435269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23951741495335129816290179 35927612243002694724435269)
        ·
          refine ⟨6736427295563005260831613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35927612243002694724435269 6736427295563005260831613)
          ·
            refine ⟨2526160235836126972811855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6736427295563005260831613 2526160235836126972811855)
            ·
              refine ⟨3789240353754190459217783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526160235836126972811855 3789240353754190459217783)
              ·
                refine ⟨5683860530631285688826675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3789240353754190459217783 5683860530631285688826675)
                ·
                  refine ⟨8525790795946928533240013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5683860530631285688826675 8525790795946928533240013)
                  ·
                    refine ⟨3197171548480098199965005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8525790795946928533240013 3197171548480098199965005)
                    ·
                      refine ⟨1198939330680036824986877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3197171548480098199965005 1198939330680036824986877)
                      ·
                        rfl

theorem cell23_2334926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_2334926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334926 prefixEnd_2334926 := by exact prefixLift 2334926
  have htrace : WordTrace (prefixWord ++ tailWord_2334926) baseStart_2334926 baseEnd_2334926 := by
    simpa [prefixWord, tailWord_2334926, baseEnd_2334926] using wordTrace_append hprefix tailTrace_2334926
  have hstable : (prefixWord ++ tailWord_2334926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334926).length < 2 ^ (prefixWord ++ tailWord_2334926).sum := by decide
  have hdescent : baseEnd_2334926 < baseStart_2334926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334936 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 1, 3, 2]
def baseStart_2334936 : Nat := 118140960795 + 2334936 * 2 ^ 59
def prefixEnd_2334936 : Nat := 4983230072969 + 3 ^ 40 * 2334936 * 2
def baseEnd_2334936 : Nat := 1198944465486581785861831

theorem tailTrace_2334936 : CollatzResearch.WordTrace tailWord_2334936 prefixEnd_2334936 1198944465486581785861831 := by
  unfold tailWord_2334936
  simp only [CollatzResearch.WordTrace]
  refine ⟨42581056134466561082892331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56774741512622081443856441 42581056134466561082892331)
  ·
    refine ⟨63871584201699841624338497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42581056134466561082892331 63871584201699841624338497)
    ·
      refine ⟨47903688151274881218253873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63871584201699841624338497 47903688151274881218253873)
      ·
        refine ⟨35927766113456160913690405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47903688151274881218253873 35927766113456160913690405)
        ·
          refine ⟨6736456146273030171316951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35927766113456160913690405 6736456146273030171316951)
          ·
            refine ⟨10104684219409545256975427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6736456146273030171316951 10104684219409545256975427)
            ·
              refine ⟨15157026329114317885463141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10104684219409545256975427 15157026329114317885463141)
              ·
                refine ⟨2841942436708934603524339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15157026329114317885463141 2841942436708934603524339)
                ·
                  refine ⟨4262913655063401905286509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2841942436708934603524339 4262913655063401905286509)
                  ·
                    refine ⟨1598592620648775714482441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4262913655063401905286509 1598592620648775714482441)
                    ·
                      refine ⟨1198944465486581785861831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1598592620648775714482441 1198944465486581785861831)
                      ·
                        rfl

theorem cell23_2334936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_2334936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334936 prefixEnd_2334936 := by exact prefixLift 2334936
  have htrace : WordTrace (prefixWord ++ tailWord_2334936) baseStart_2334936 baseEnd_2334936 := by
    simpa [prefixWord, tailWord_2334936, baseEnd_2334936] using wordTrace_append hprefix tailTrace_2334936
  have hstable : (prefixWord ++ tailWord_2334936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334936).length < 2 ^ (prefixWord ++ tailWord_2334936).sum := by decide
  have hdescent : baseEnd_2334936 < baseStart_2334936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2334952 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_2334952 : Nat := 118140960795 + 2334952 * 2 ^ 59
def prefixEnd_2334952 : Nat := 4983230072969 + 3 ^ 40 * 2334952 * 2
def baseEnd_2334952 : Nat := 1198952681177053723261757

theorem tailTrace_2334952 : CollatzResearch.WordTrace tailWord_2334952 prefixEnd_2334952 1198952681177053723261757 := by
  unfold tailWord_2334952
  simp only [CollatzResearch.WordTrace]
  refine ⟨42581347918437578449183555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56775130557916771265578073 42581347918437578449183555)
  ·
    refine ⟨63872021877656367673775333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42581347918437578449183555 63872021877656367673775333)
    ·
      refine ⟨11976004102060568938832875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63872021877656367673775333 11976004102060568938832875)
      ·
        refine ⟨17964006153090853408249313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11976004102060568938832875 17964006153090853408249313)
        ·
          refine ⟨13473004614818140056186985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17964006153090853408249313 13473004614818140056186985)
          ·
            refine ⟨10104753461113605042140239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13473004614818140056186985 10104753461113605042140239)
            ·
              refine ⟨15157130191670407563210359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10104753461113605042140239 15157130191670407563210359)
              ·
                refine ⟨22735695287505611344815539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15157130191670407563210359 22735695287505611344815539)
                ·
                  refine ⟨34103542931258417017223309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22735695287505611344815539 34103542931258417017223309)
                  ·
                    refine ⟨12788828599221906381458741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34103542931258417017223309 12788828599221906381458741)
                    ·
                      refine ⟨1198952681177053723261757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12788828599221906381458741 1198952681177053723261757)
                      ·
                        rfl

theorem cell23_2334952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_2334952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2334952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2334952 prefixEnd_2334952 := by exact prefixLift 2334952
  have htrace : WordTrace (prefixWord ++ tailWord_2334952) baseStart_2334952 baseEnd_2334952 := by
    simpa [prefixWord, tailWord_2334952, baseEnd_2334952] using wordTrace_append hprefix tailTrace_2334952
  have hstable : (prefixWord ++ tailWord_2334952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2334952).length < 2 ^ (prefixWord ++ tailWord_2334952).sum := by decide
  have hdescent : baseEnd_2334952 < baseStart_2334952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2334952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335056 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 4]
def baseStart_2335056 : Nat := 118140960795 + 2335056 * 2 ^ 59
def prefixEnd_2335056 : Nat := 4983230072969 + 3 ^ 40 * 2335056 * 2
def baseEnd_2335056 : Nat := 1199006083165121316361279

theorem tailTrace_2335056 : CollatzResearch.WordTrace tailWord_2335056 prefixEnd_2335056 1199006083165121316361279 := by
  unfold tailWord_2335056
  simp only [CollatzResearch.WordTrace]
  refine ⟨42583244514249191330076511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56777659352332255106768681 42583244514249191330076511)
  ·
    refine ⟨63874866771373786995114767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42583244514249191330076511 63874866771373786995114767)
    ·
      refine ⟨95812300157060680492672151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63874866771373786995114767 95812300157060680492672151)
      ·
        refine ⟨143718450235591020739008227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95812300157060680492672151 143718450235591020739008227)
        ·
          refine ⟨215577675353386531108512341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143718450235591020739008227 215577675353386531108512341)
          ·
            refine ⟨2526300883047498411427879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 215577675353386531108512341 2526300883047498411427879)
            ·
              refine ⟨3789451324571247617141819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526300883047498411427879 3789451324571247617141819)
              ·
                refine ⟨5684176986856871425712729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3789451324571247617141819 5684176986856871425712729)
                ·
                  refine ⟨4263132740142653569284547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5684176986856871425712729 4263132740142653569284547)
                  ·
                    refine ⟨6394699110213980353926821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4263132740142653569284547 6394699110213980353926821)
                    ·
                      refine ⟨1199006083165121316361279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6394699110213980353926821 1199006083165121316361279)
                      ·
                        rfl

theorem cell23_2335056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 4].length) (baseStart_2335056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335056 prefixEnd_2335056 := by exact prefixLift 2335056
  have htrace : WordTrace (prefixWord ++ tailWord_2335056) baseStart_2335056 baseEnd_2335056 := by
    simpa [prefixWord, tailWord_2335056, baseEnd_2335056] using wordTrace_append hprefix tailTrace_2335056
  have hstable : (prefixWord ++ tailWord_2335056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335056).length < 2 ^ (prefixWord ++ tailWord_2335056).sum := by decide
  have hdescent : baseEnd_2335056 < baseStart_2335056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335059 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 3]
def baseStart_2335059 : Nat := 118140960795 + 2335059 * 2 ^ 59
def prefixEnd_2335059 : Nat := 4983230072969 + 3 ^ 40 * 2335059 * 2
def baseEnd_2335059 : Nat := 1199007623607084804623765

theorem tailTrace_2335059 : CollatzResearch.WordTrace tailWord_2335059 prefixEnd_2335059 1199007623607084804623765 := by
  unfold tailWord_2335059
  simp only [CollatzResearch.WordTrace]
  refine ⟨85166598447487514172512231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56777732298325009448341487 85166598447487514172512231)
  ·
    refine ⟨127749897671231271258768347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85166598447487514172512231 127749897671231271258768347)
    ·
      refine ⟨191624846506846906888152521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127749897671231271258768347 191624846506846906888152521)
      ·
        refine ⟨143718634880135180166114391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191624846506846906888152521 143718634880135180166114391)
        ·
          refine ⟨215577952320202770249171587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143718634880135180166114391 215577952320202770249171587)
          ·
            refine ⟨323366928480304155373757381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215577952320202770249171587 323366928480304155373757381)
            ·
              refine ⟨60631299090057029132579509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 323366928480304155373757381 60631299090057029132579509)
              ·
                refine ⟨5684184289692846481179329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60631299090057029132579509 5684184289692846481179329)
                ·
                  refine ⟨4263138217269634860884497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5684184289692846481179329 4263138217269634860884497)
                  ·
                    refine ⟨3197353662952226145663373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4263138217269634860884497 3197353662952226145663373)
                    ·
                      refine ⟨1199007623607084804623765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3197353662952226145663373 1199007623607084804623765)
                      ·
                        rfl

theorem cell23_2335059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 3].length) (baseStart_2335059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335059 prefixEnd_2335059 := by exact prefixLift 2335059
  have htrace : WordTrace (prefixWord ++ tailWord_2335059) baseStart_2335059 baseEnd_2335059 := by
    simpa [prefixWord, tailWord_2335059, baseEnd_2335059] using wordTrace_append hprefix tailTrace_2335059
  have hstable : (prefixWord ++ tailWord_2335059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335059).length < 2 ^ (prefixWord ++ tailWord_2335059).sum := by decide
  have hdescent : baseEnd_2335059 < baseStart_2335059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335079 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 8]
def baseStart_2335079 : Nat := 118140960795 + 2335079 * 2 ^ 59
def prefixEnd_2335079 : Nat := 4983230072969 + 3 ^ 40 * 2335079 * 2
def baseEnd_2335079 : Nat := 133224210357797191819297

theorem tailTrace_2335079 : CollatzResearch.WordTrace tailWord_2335079 prefixEnd_2335079 133224210357797191819297 := by
  unfold tailWord_2335079
  simp only [CollatzResearch.WordTrace]
  refine ⟨85167327907415057588240291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56778218604943371725493527 85167327907415057588240291)
  ·
    refine ⟨127750991861122586382360437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85167327907415057588240291 127750991861122586382360437)
    ·
      refine ⟨11976655486980242473346291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 127750991861122586382360437 11976655486980242473346291)
      ·
        refine ⟨17964983230470363710019437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11976655486980242473346291 17964983230470363710019437)
        ·
          refine ⟨6736868711426386391257289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17964983230470363710019437 6736868711426386391257289)
          ·
            refine ⟨5052651533569789793442967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6736868711426386391257289 5052651533569789793442967)
            ·
              refine ⟨7578977300354684690164451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5052651533569789793442967 7578977300354684690164451)
              ·
                refine ⟨11368465950532027035246677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7578977300354684690164451 11368465950532027035246677)
                ·
                  refine ⟨133224210357797191819297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11368465950532027035246677 133224210357797191819297)
                  ·
                    rfl

theorem cell23_2335079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 8].length) (baseStart_2335079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335079 prefixEnd_2335079 := by exact prefixLift 2335079
  have htrace : WordTrace (prefixWord ++ tailWord_2335079) baseStart_2335079 baseEnd_2335079 := by
    simpa [prefixWord, tailWord_2335079, baseEnd_2335079] using wordTrace_append hprefix tailTrace_2335079
  have hstable : (prefixWord ++ tailWord_2335079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335079).length < 2 ^ (prefixWord ++ tailWord_2335079).sum := by decide
  have hdescent : baseEnd_2335079 < baseStart_2335079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335116 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 1, 5, 2]
def baseStart_2335116 : Nat := 118140960795 + 2335116 * 2 ^ 59
def prefixEnd_2335116 : Nat := 4983230072969 + 3 ^ 40 * 2335116 * 2
def baseEnd_2335116 : Nat := 1199036892004391081611003

theorem tailTrace_2335116 : CollatzResearch.WordTrace tailWord_2335116 prefixEnd_2335116 1199036892004391081611003 := by
  unfold tailWord_2335116
  simp only [CollatzResearch.WordTrace]
  refine ⟨42584338704140506453668601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56779118272187341938224801 42584338704140506453668601)
  ·
    refine ⟨31938254028105379840251451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42584338704140506453668601 31938254028105379840251451)
    ·
      refine ⟨47907381042158069760377177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31938254028105379840251451 47907381042158069760377177)
      ·
        refine ⟨35930535781618552320282883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47907381042158069760377177 35930535781618552320282883)
        ·
          refine ⟨53895803672427828480424325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35930535781618552320282883 53895803672427828480424325)
          ·
            refine ⟨10105463188580217840079561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53895803672427828480424325 10105463188580217840079561)
            ·
              refine ⟨7579097391435163380059671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10105463188580217840079561 7579097391435163380059671)
              ·
                refine ⟨11368646087152745070089507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7579097391435163380059671 11368646087152745070089507)
                ·
                  refine ⟨17052969130729117605134261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11368646087152745070089507 17052969130729117605134261)
                  ·
                    refine ⟨1598715856005854775481337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17052969130729117605134261 1598715856005854775481337)
                    ·
                      refine ⟨1199036892004391081611003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1598715856005854775481337 1199036892004391081611003)
                      ·
                        rfl

theorem cell23_2335116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_2335116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335116 prefixEnd_2335116 := by exact prefixLift 2335116
  have htrace : WordTrace (prefixWord ++ tailWord_2335116) baseStart_2335116 baseEnd_2335116 := by
    simpa [prefixWord, tailWord_2335116, baseEnd_2335116] using wordTrace_append hprefix tailTrace_2335116
  have hstable : (prefixWord ++ tailWord_2335116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335116).length < 2 ^ (prefixWord ++ tailWord_2335116).sum := by decide
  have hdescent : baseEnd_2335116 < baseStart_2335116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335159 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 6]
def baseStart_2335159 : Nat := 118140960795 + 2335159 * 2 ^ 59
def prefixEnd_2335159 : Nat := 4983230072969 + 3 ^ 40 * 2335159 * 2
def baseEnd_2335159 : Nat := 1199058971672534413373305

theorem tailTrace_2335159 : CollatzResearch.WordTrace tailWord_2335159 prefixEnd_2335159 1199058971672534413373305 := by
  unfold tailWord_2335159
  simp only [CollatzResearch.WordTrace]
  refine ⟨85170245747125231251152531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56780163831416820834101687 85170245747125231251152531)
  ·
    refine ⟨127755368620687846876728797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85170245747125231251152531 127755368620687846876728797)
    ·
      refine ⟨47908263232757942578773299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 127755368620687846876728797 47908263232757942578773299)
      ·
        refine ⟨71862394849136913868159949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47908263232757942578773299 71862394849136913868159949)
        ·
          refine ⟨26948398068426342700559981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71862394849136913868159949 26948398068426342700559981)
          ·
            refine ⟨10105649275659878512709993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26948398068426342700559981 10105649275659878512709993)
            ·
              refine ⟨7579236956744908884532495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10105649275659878512709993 7579236956744908884532495)
              ·
                refine ⟨11368855435117363326798743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7579236956744908884532495 11368855435117363326798743)
                ·
                  refine ⟨17053283152676044990198115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11368855435117363326798743 17053283152676044990198115)
                  ·
                    refine ⟨25579924729014067485297173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17053283152676044990198115 25579924729014067485297173)
                    ·
                      refine ⟨1199058971672534413373305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25579924729014067485297173 1199058971672534413373305)
                      ·
                        rfl

theorem cell23_2335159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_2335159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335159 prefixEnd_2335159 := by exact prefixLift 2335159
  have htrace : WordTrace (prefixWord ++ tailWord_2335159) baseStart_2335159 baseEnd_2335159 := by
    simpa [prefixWord, tailWord_2335159, baseEnd_2335159] using wordTrace_append hprefix tailTrace_2335159
  have hstable : (prefixWord ++ tailWord_2335159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335159).length < 2 ^ (prefixWord ++ tailWord_2335159).sum := by decide
  have hdescent : baseEnd_2335159 < baseStart_2335159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335176 : List Nat := [2, 1, 3, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_2335176 : Nat := 118140960795 + 2335176 * 2 ^ 59
def prefixEnd_2335176 : Nat := 4983230072969 + 3 ^ 40 * 2335176 * 2
def baseEnd_2335176 : Nat := 1199067700843660846860727

theorem tailTrace_2335176 : CollatzResearch.WordTrace tailWord_2335176 prefixEnd_2335176 1199067700843660846860727 := by
  unfold tailWord_2335176
  simp only [CollatzResearch.WordTrace]
  refine ⟨42585432894031821577260691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56780577192042428769680921 42585432894031821577260691)
  ·
    refine ⟨63878149341047732365891037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42585432894031821577260691 63878149341047732365891037)
    ·
      refine ⟨23954306002892899637209139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63878149341047732365891037 23954306002892899637209139)
      ·
        refine ⟨35931459004339349455813709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23954306002892899637209139 35931459004339349455813709)
        ·
          refine ⟨13474297126627256045930141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35931459004339349455813709 13474297126627256045930141)
          ·
            refine ⟨5052861422485221017223803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13474297126627256045930141 5052861422485221017223803)
            ·
              refine ⟨7579292133727831525835705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5052861422485221017223803 7579292133727831525835705)
              ·
                refine ⟨5684469100295873644376779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7579292133727831525835705 5684469100295873644376779)
                ·
                  refine ⟨8526703650443810466565169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5684469100295873644376779 8526703650443810466565169)
                  ·
                    refine ⟨6395027737832857849923877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8526703650443810466565169 6395027737832857849923877)
                    ·
                      refine ⟨1199067700843660846860727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6395027737832857849923877 1199067700843660846860727)
                      ·
                        rfl

theorem cell23_2335176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_2335176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335176 prefixEnd_2335176 := by exact prefixLift 2335176
  have htrace : WordTrace (prefixWord ++ tailWord_2335176) baseStart_2335176 baseEnd_2335176 := by
    simpa [prefixWord, tailWord_2335176, baseEnd_2335176] using wordTrace_append hprefix tailTrace_2335176
  have hstable : (prefixWord ++ tailWord_2335176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335176).length < 2 ^ (prefixWord ++ tailWord_2335176).sum := by decide
  have hdescent : baseEnd_2335176 < baseStart_2335176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335180 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 1, 1, 4]
def baseStart_2335180 : Nat := 118140960795 + 2335180 * 2 ^ 59
def prefixEnd_2335180 : Nat := 4983230072969 + 3 ^ 40 * 2335180 * 2
def baseEnd_2335180 : Nat := 1199069754766278831210709

theorem tailTrace_2335180 : CollatzResearch.WordTrace tailWord_2335180 prefixEnd_2335180 1199069754766278831210709 := by
  unfold tailWord_2335180
  simp only [CollatzResearch.WordTrace]
  refine ⟨42585505840024575918833497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56780674453366101225111329 42585505840024575918833497)
  ·
    refine ⟨31939129380018431939125123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42585505840024575918833497 31939129380018431939125123)
    ·
      refine ⟨47908694070027647908687685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31939129380018431939125123 47908694070027647908687685)
      ·
        refine ⟨8982880138130183982878941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47908694070027647908687685 8982880138130183982878941)
        ·
          refine ⟨3368580051798818993579603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8982880138130183982878941 3368580051798818993579603)
          ·
            refine ⟨5052870077698228490369405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3368580051798818993579603 5052870077698228490369405)
            ·
              refine ⟨1894826279136835683888527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5052870077698228490369405 1894826279136835683888527)
              ·
                refine ⟨2842239418705253525832791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894826279136835683888527 2842239418705253525832791)
                ·
                  refine ⟨4263359128057880288749187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842239418705253525832791 4263359128057880288749187)
                  ·
                    refine ⟨6395038692086820433123781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4263359128057880288749187 6395038692086820433123781)
                    ·
                      refine ⟨1199069754766278831210709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6395038692086820433123781 1199069754766278831210709)
                      ·
                        rfl

theorem cell23_2335180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_2335180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335180 prefixEnd_2335180 := by exact prefixLift 2335180
  have htrace : WordTrace (prefixWord ++ tailWord_2335180) baseStart_2335180 baseEnd_2335180 := by
    simpa [prefixWord, tailWord_2335180, baseEnd_2335180] using wordTrace_append hprefix tailTrace_2335180
  have hstable : (prefixWord ++ tailWord_2335180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335180).length < 2 ^ (prefixWord ++ tailWord_2335180).sum := by decide
  have hdescent : baseEnd_2335180 < baseStart_2335180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335186 : List Nat := [3, 2, 2, 4, 1, 11]
def baseStart_2335186 : Nat := 118140960795 + 2335186 * 2 ^ 59
def prefixEnd_2335186 : Nat := 4983230072969 + 3 ^ 40 * 2335186 * 2
def baseEnd_2335186 : Nat := 4934456113786855175867

theorem tailTrace_2335186 : CollatzResearch.WordTrace tailWord_2335186 prefixEnd_2335186 4934456113786855175867 := by
  unfold tailWord_2335186
  simp only [CollatzResearch.WordTrace]
  refine ⟨21292807629506853715596353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56780820345351609908256941 21292807629506853715596353)
  ·
    refine ⟨15969605722130140286697265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21292807629506853715596353 15969605722130140286697265)
    ·
      refine ⟨11977204291597605215022949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15969605722130140286697265 11977204291597605215022949)
      ·
        refine ⟨2245725804674550977816803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11977204291597605215022949 2245725804674550977816803)
        ·
          refine ⟨3368588707011826466725205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2245725804674550977816803 3368588707011826466725205)
          ·
            refine ⟨4934456113786855175867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3368588707011826466725205 4934456113786855175867)
            ·
              rfl

theorem cell23_2335186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 11].length) (baseStart_2335186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335186 prefixEnd_2335186 := by exact prefixLift 2335186
  have htrace : WordTrace (prefixWord ++ tailWord_2335186) baseStart_2335186 baseEnd_2335186 := by
    simpa [prefixWord, tailWord_2335186, baseEnd_2335186] using wordTrace_append hprefix tailTrace_2335186
  have hstable : (prefixWord ++ tailWord_2335186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335186).length < 2 ^ (prefixWord ++ tailWord_2335186).sum := by decide
  have hdescent : baseEnd_2335186 < baseStart_2335186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335190 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_2335190 : Nat := 118140960795 + 2335190 * 2 ^ 59
def prefixEnd_2335190 : Nat := 4983230072969 + 3 ^ 40 * 2335190 * 2
def baseEnd_2335190 : Nat := 399691629857607930695221

theorem tailTrace_2335190 : CollatzResearch.WordTrace tailWord_2335190 prefixEnd_2335190 399691629857607930695221 := by
  unfold tailWord_2335190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5323211025625807721595689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 56780917606675282363687349 5323211025625807721595689)
  ·
    refine ⟨3992408269219355791196767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5323211025625807721595689 3992408269219355791196767)
    ·
      refine ⟨5988612403829033686795151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3992408269219355791196767 5988612403829033686795151)
      ·
        refine ⟨8982918605743550530192727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5988612403829033686795151 8982918605743550530192727)
        ·
          refine ⟨13474377908615325795289091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8982918605743550530192727 13474377908615325795289091)
          ·
            refine ⟨20211566862922988692933637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13474377908615325795289091 20211566862922988692933637)
            ·
              refine ⟨3789668786798060379925057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20211566862922988692933637 3789668786798060379925057)
              ·
                refine ⟨2842251590098545284943793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3789668786798060379925057 2842251590098545284943793)
                ·
                  refine ⟨2131688692573908963707845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2842251590098545284943793 2131688692573908963707845)
                  ·
                    refine ⟨399691629857607930695221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2131688692573908963707845 399691629857607930695221)
                    ·
                      rfl

theorem cell23_2335190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_2335190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335190 prefixEnd_2335190 := by exact prefixLift 2335190
  have htrace : WordTrace (prefixWord ++ tailWord_2335190) baseStart_2335190 baseEnd_2335190 := by
    simpa [prefixWord, tailWord_2335190, baseEnd_2335190] using wordTrace_append hprefix tailTrace_2335190
  have hstable : (prefixWord ++ tailWord_2335190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335190).length < 2 ^ (prefixWord ++ tailWord_2335190).sum := by decide
  have hdescent : baseEnd_2335190 < baseStart_2335190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335197 : List Nat := [1, 4, 3, 1, 1, 1, 3, 4, 1, 2, 2]
def baseStart_2335197 : Nat := 118140960795 + 2335197 * 2 ^ 59
def prefixEnd_2335197 : Nat := 4983230072969 + 3 ^ 40 * 2335197 * 2
def baseEnd_2335197 : Nat := 1199078483937405264698131

theorem tailTrace_2335197 : CollatzResearch.WordTrace tailWord_2335197 prefixEnd_2335197 1199078483937405264698131 := by
  unfold tailWord_2335197
  simp only [CollatzResearch.WordTrace]
  refine ⟨85171631720987563741035845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56781087813991709160690563 85171631720987563741035845)
  ·
    refine ⟨15969680947685168201444221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85171631720987563741035845 15969680947685168201444221)
    ·
      refine ⟨5988630355381938075541583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15969680947685168201444221 5988630355381938075541583)
      ·
        refine ⟨8982945533072907113312375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5988630355381938075541583 8982945533072907113312375)
        ·
          refine ⟨13474418299609360669968563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8982945533072907113312375 13474418299609360669968563)
          ·
            refine ⟨20211627449414041004952845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13474418299609360669968563 20211627449414041004952845)
            ·
              refine ⟨7579360293530265376857317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20211627449414041004952845 7579360293530265376857317)
              ·
                refine ⟨1421130055036924758160747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7579360293530265376857317 1421130055036924758160747)
                ·
                  refine ⟨2131695082555387137241121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1421130055036924758160747 2131695082555387137241121)
                  ·
                    refine ⟨1598771311916540352930841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2131695082555387137241121 1598771311916540352930841)
                    ·
                      refine ⟨1199078483937405264698131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1598771311916540352930841 1199078483937405264698131)
                      ·
                        rfl

theorem cell23_2335197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_2335197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335197 prefixEnd_2335197 := by exact prefixLift 2335197
  have htrace : WordTrace (prefixWord ++ tailWord_2335197) baseStart_2335197 baseEnd_2335197 := by
    simpa [prefixWord, tailWord_2335197, baseEnd_2335197] using wordTrace_append hprefix tailTrace_2335197
  have hstable : (prefixWord ++ tailWord_2335197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335197).length < 2 ^ (prefixWord ++ tailWord_2335197).sum := by decide
  have hdescent : baseEnd_2335197 < baseStart_2335197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335199 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 2, 7]
def baseStart_2335199 : Nat := 118140960795 + 2335199 * 2 ^ 59
def prefixEnd_2335199 : Nat := 4983230072969 + 3 ^ 40 * 2335199 * 2
def baseEnd_2335199 : Nat := 399693170299571418957707

theorem tailTrace_2335199 : CollatzResearch.WordTrace tailWord_2335199 prefixEnd_2335199 399693170299571418957707 := by
  unfold tailWord_2335199
  simp only [CollatzResearch.WordTrace]
  refine ⟨85171704666980318082608651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56781136444653545388405767 85171704666980318082608651)
  ·
    refine ⟨127757557000470477123912977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85171704666980318082608651 127757557000470477123912977)
    ·
      refine ⟨95818167750352857842934733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 127757557000470477123912977 95818167750352857842934733)
      ·
        refine ⟨35931812906382321691100525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95818167750352857842934733 35931812906382321691100525)
        ·
          refine ⟨13474429839893370634162697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35931812906382321691100525 13474429839893370634162697)
          ·
            refine ⟨10105822379920027975622023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13474429839893370634162697 10105822379920027975622023)
            ·
              refine ⟨15158733569880041963433035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10105822379920027975622023 15158733569880041963433035)
              ·
                refine ⟨22738100354820062945149553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15158733569880041963433035 22738100354820062945149553)
                ·
                  refine ⟨17053575266115047208862165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22738100354820062945149553 17053575266115047208862165)
                  ·
                    refine ⟨399693170299571418957707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17053575266115047208862165 399693170299571418957707)
                    ·
                      rfl

theorem cell23_2335199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_2335199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335199 prefixEnd_2335199 := by exact prefixLift 2335199
  have htrace : WordTrace (prefixWord ++ tailWord_2335199) baseStart_2335199 baseEnd_2335199 := by
    simpa [prefixWord, tailWord_2335199, baseEnd_2335199] using wordTrace_append hprefix tailTrace_2335199
  have hstable : (prefixWord ++ tailWord_2335199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335199).length < 2 ^ (prefixWord ++ tailWord_2335199).sum := by decide
  have hdescent : baseEnd_2335199 < baseStart_2335199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335203 : List Nat := [1, 1, 1, 6, 4, 1, 1, 8]
def baseStart_2335203 : Nat := 118140960795 + 2335203 * 2 ^ 59
def prefixEnd_2335203 : Nat := 4983230072969 + 3 ^ 40 * 2335203 * 2
def baseEnd_2335203 : Nat := 44410428326716008934189

theorem tailTrace_2335203 : CollatzResearch.WordTrace tailWord_2335203 prefixEnd_2335203 44410428326716008934189 := by
  unfold tailWord_2335203
  simp only [CollatzResearch.WordTrace]
  refine ⟨85171850558965826765754263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56781233705977217843836175 85171850558965826765754263)
  ·
    refine ⟨127757775838448740148631395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85171850558965826765754263 127757775838448740148631395)
    ·
      refine ⟨191636663757673110222947093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127757775838448740148631395 191636663757673110222947093)
      ·
        refine ⟨8982968613640927041700645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 191636663757673110222947093 8982968613640927041700645)
        ·
          refine ⟨1684306615057673820318871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8982968613640927041700645 1684306615057673820318871)
          ·
            refine ⟨2526459922586510730478307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1684306615057673820318871 2526459922586510730478307)
            ·
              refine ⟨3789689883879766095717461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2526459922586510730478307 3789689883879766095717461)
              ·
                refine ⟨44410428326716008934189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3789689883879766095717461 44410428326716008934189)
                ·
                  rfl

theorem cell23_2335203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 8].length) (baseStart_2335203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335203 prefixEnd_2335203 := by exact prefixLift 2335203
  have htrace : WordTrace (prefixWord ++ tailWord_2335203) baseStart_2335203 baseEnd_2335203 := by
    simpa [prefixWord, tailWord_2335203, baseEnd_2335203] using wordTrace_append hprefix tailTrace_2335203
  have hstable : (prefixWord ++ tailWord_2335203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335203).length < 2 ^ (prefixWord ++ tailWord_2335203).sum := by decide
  have hdescent : baseEnd_2335203 < baseStart_2335203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335213 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2335213 : Nat := 118140960795 + 2335213 * 2 ^ 59
def prefixEnd_2335213 : Nat := 4983230072969 + 3 ^ 40 * 2335213 * 2
def baseEnd_2335213 : Nat := 1199086699627877202098057

theorem tailTrace_2335213 : CollatzResearch.WordTrace tailWord_2335213 prefixEnd_2335213 1199086699627877202098057 := by
  unfold tailWord_2335213
  simp only [CollatzResearch.WordTrace]
  refine ⟨85172215288929598473618293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56781476859286398982412195 85172215288929598473618293)
  ·
    refine ⟨7984895183337149856901715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 85172215288929598473618293 7984895183337149856901715)
    ·
      refine ⟨11977342775005724785352573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7984895183337149856901715 11977342775005724785352573)
      ·
        refine ⟨4491503540627146794507215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11977342775005724785352573 4491503540627146794507215)
        ·
          refine ⟨6737255310940720191760823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4491503540627146794507215 6737255310940720191760823)
          ·
            refine ⟨10105882966411080287641235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6737255310940720191760823 10105882966411080287641235)
            ·
              refine ⟨15158824449616620431461853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10105882966411080287641235 15158824449616620431461853)
              ·
                refine ⟨5684559168606232661798195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15158824449616620431461853 5684559168606232661798195)
                ·
                  refine ⟨8526838752909348992697293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5684559168606232661798195 8526838752909348992697293)
                  ·
                    refine ⟨3197564532341005872261485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8526838752909348992697293 3197564532341005872261485)
                    ·
                      refine ⟨1199086699627877202098057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3197564532341005872261485 1199086699627877202098057)
                      ·
                        rfl

theorem cell23_2335213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2335213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335213 prefixEnd_2335213 := by exact prefixLift 2335213
  have htrace : WordTrace (prefixWord ++ tailWord_2335213) baseStart_2335213 baseEnd_2335213 := by
    simpa [prefixWord, tailWord_2335213, baseEnd_2335213] using wordTrace_append hprefix tailTrace_2335213
  have hstable : (prefixWord ++ tailWord_2335213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335213).length < 2 ^ (prefixWord ++ tailWord_2335213).sum := by decide
  have hdescent : baseEnd_2335213 < baseStart_2335213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335219 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 4]
def baseStart_2335219 : Nat := 118140960795 + 2335219 * 2 ^ 59
def prefixEnd_2335219 : Nat := 4983230072969 + 3 ^ 40 * 2335219 * 2
def baseEnd_2335219 : Nat := 1199089780511804178623029

theorem tailTrace_2335219 : CollatzResearch.WordTrace tailWord_2335219 prefixEnd_2335219 1199089780511804178623029 := by
  unfold tailWord_2335219
  simp only [CollatzResearch.WordTrace]
  refine ⟨85172434126907861498336711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56781622751271907665557807 85172434126907861498336711)
  ·
    refine ⟨127758651190361792247505067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85172434126907861498336711 127758651190361792247505067)
    ·
      refine ⟨191637976785542688371257601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127758651190361792247505067 191637976785542688371257601)
      ·
        refine ⟨143728482589157016278443201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 191637976785542688371257601 143728482589157016278443201)
        ·
          refine ⟨107796361941867762208832401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143728482589157016278443201 107796361941867762208832401)
          ·
            refine ⟨80847271456400821656624301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107796361941867762208832401 80847271456400821656624301)
            ·
              refine ⟨30317726796150308121234113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80847271456400821656624301 30317726796150308121234113)
              ·
                refine ⟨22738295097112731090925585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30317726796150308121234113 22738295097112731090925585)
                ·
                  refine ⟨17053721322834548318194189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22738295097112731090925585 17053721322834548318194189)
                  ·
                    refine ⟨6395145496062955619322821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17053721322834548318194189 6395145496062955619322821)
                    ·
                      refine ⟨1199089780511804178623029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6395145496062955619322821 1199089780511804178623029)
                      ·
                        rfl

theorem cell23_2335219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_2335219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335219 prefixEnd_2335219 := by exact prefixLift 2335219
  have htrace : WordTrace (prefixWord ++ tailWord_2335219) baseStart_2335219 baseEnd_2335219 := by
    simpa [prefixWord, tailWord_2335219, baseEnd_2335219] using wordTrace_append hprefix tailTrace_2335219
  have hstable : (prefixWord ++ tailWord_2335219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335219).length < 2 ^ (prefixWord ++ tailWord_2335219).sum := by decide
  have hdescent : baseEnd_2335219 < baseStart_2335219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335229 : List Nat := [1, 4, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_2335229 : Nat := 118140960795 + 2335229 * 2 ^ 59
def prefixEnd_2335229 : Nat := 4983230072969 + 3 ^ 40 * 2335229 * 2
def baseEnd_2335229 : Nat := 399698305106116379832661

theorem tailTrace_2335229 : CollatzResearch.WordTrace tailWord_2335229 prefixEnd_2335229 399698305106116379832661 := by
  unfold tailWord_2335229
  simp only [CollatzResearch.WordTrace]
  refine ⟨85172798856871633206200741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56781865904581088804133827 85172798856871633206200741)
  ·
    refine ⟨15969899785663431226162639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 85172798856871633206200741 15969899785663431226162639)
    ·
      refine ⟨23954849678495146839243959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15969899785663431226162639 23954849678495146839243959)
      ·
        refine ⟨35932274517742720258865939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23954849678495146839243959 35932274517742720258865939)
        ·
          refine ⟨53898411776614080388298909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35932274517742720258865939 53898411776614080388298909)
          ·
            refine ⟨20211904416230280145612091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53898411776614080388298909 20211904416230280145612091)
            ·
              refine ⟨30317856624345420218418137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20211904416230280145612091 30317856624345420218418137)
              ·
                refine ⟨22738392468259065163813603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30317856624345420218418137 22738392468259065163813603)
                ·
                  refine ⟨34107588702388597745720405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22738392468259065163813603 34107588702388597745720405)
                  ·
                    refine ⟨399698305106116379832661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34107588702388597745720405 399698305106116379832661)
                    ·
                      rfl

theorem cell23_2335229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_2335229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335229 prefixEnd_2335229 := by exact prefixLift 2335229
  have htrace : WordTrace (prefixWord ++ tailWord_2335229) baseStart_2335229 baseEnd_2335229 := by
    simpa [prefixWord, tailWord_2335229, baseEnd_2335229] using wordTrace_append hprefix tailTrace_2335229
  have hstable : (prefixWord ++ tailWord_2335229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335229).length < 2 ^ (prefixWord ++ tailWord_2335229).sum := by decide
  have hdescent : baseEnd_2335229 < baseStart_2335229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335234 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_2335234 : Nat := 118140960795 + 2335234 * 2 ^ 59
def prefixEnd_2335234 : Nat := 4983230072969 + 3 ^ 40 * 2335234 * 2
def baseEnd_2335234 : Nat := 1199097482721621619935461

theorem tailTrace_2335234 : CollatzResearch.WordTrace tailWord_2335234 prefixEnd_2335234 1199097482721621619935461 := by
  unfold tailWord_2335234
  simp only [CollatzResearch.WordTrace]
  refine ⟨21293245305463379765033189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56781987481235679373421837 21293245305463379765033189)
  ·
    refine ⟨3992483494774383705943723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21293245305463379765033189 3992483494774383705943723)
    ·
      refine ⟨5988725242161575558915585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3992483494774383705943723 5988725242161575558915585)
      ·
        refine ⟨4491543931621181669186689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5988725242161575558915585 4491543931621181669186689)
        ·
          refine ⟨3368657948715886251890017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4491543931621181669186689 3368657948715886251890017)
          ·
            refine ⟨2526493461536914688917513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3368657948715886251890017 2526493461536914688917513)
            ·
              refine ⟨1894870096152686016688135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2526493461536914688917513 1894870096152686016688135)
              ·
                refine ⟨2842305144229029025032203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894870096152686016688135 2842305144229029025032203)
                ·
                  refine ⟨4263457716343543537548305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2842305144229029025032203 4263457716343543537548305)
                  ·
                    refine ⟨3197593287257657653161229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4263457716343543537548305 3197593287257657653161229)
                    ·
                      refine ⟨1199097482721621619935461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3197593287257657653161229 1199097482721621619935461)
                      ·
                        rfl

theorem cell23_2335234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_2335234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335234 prefixEnd_2335234 := by exact prefixLift 2335234
  have htrace : WordTrace (prefixWord ++ tailWord_2335234) baseStart_2335234 baseEnd_2335234 := by
    simpa [prefixWord, tailWord_2335234, baseEnd_2335234] using wordTrace_append hprefix tailTrace_2335234
  have hstable : (prefixWord ++ tailWord_2335234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335234).length < 2 ^ (prefixWord ++ tailWord_2335234).sum := by decide
  have hdescent : baseEnd_2335234 < baseStart_2335234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335246 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 2, 6]
def baseStart_2335246 : Nat := 118140960795 + 2335246 * 2 ^ 59
def prefixEnd_2335246 : Nat := 4983230072969 + 3 ^ 40 * 2335246 * 2
def baseEnd_2335246 : Nat := 399701214829825190995135

theorem tailTrace_2335246 : CollatzResearch.WordTrace tailWord_2335246 prefixEnd_2335246 399701214829825190995135 := by
  unfold tailWord_2335246
  simp only [CollatzResearch.WordTrace]
  refine ⟨10646677362226255638696199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 56782279265206696739713061 10646677362226255638696199)
  ·
    refine ⟨15970016043339383458044299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10646677362226255638696199 15970016043339383458044299)
    ·
      refine ⟨23955024065009075187066449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15970016043339383458044299 23955024065009075187066449)
      ·
        refine ⟨17966268048756806390299837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23955024065009075187066449 17966268048756806390299837)
        ·
          refine ⟨6737350518283802396362439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17966268048756806390299837 6737350518283802396362439)
          ·
            refine ⟨10106025777425703594543659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6737350518283802396362439 10106025777425703594543659)
            ·
              refine ⟨15159038666138555391815489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10106025777425703594543659 15159038666138555391815489)
              ·
                refine ⟨11369278999603916543861617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15159038666138555391815489 11369278999603916543861617)
                ·
                  refine ⟨8526959249702937407896213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11369278999603916543861617 8526959249702937407896213)
                  ·
                    refine ⟨399701214829825190995135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8526959249702937407896213 399701214829825190995135)
                    ·
                      rfl

theorem cell23_2335246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_2335246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335246 prefixEnd_2335246 := by exact prefixLift 2335246
  have htrace : WordTrace (prefixWord ++ tailWord_2335246) baseStart_2335246 baseEnd_2335246 := by
    simpa [prefixWord, tailWord_2335246, baseEnd_2335246] using wordTrace_append hprefix tailTrace_2335246
  have hstable : (prefixWord ++ tailWord_2335246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335246).length < 2 ^ (prefixWord ++ tailWord_2335246).sum := by decide
  have hdescent : baseEnd_2335246 < baseStart_2335246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335299 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 7]
def baseStart_2335299 : Nat := 118140960795 + 2335299 * 2 ^ 59
def prefixEnd_2335299 : Nat := 4983230072969 + 3 ^ 40 * 2335299 * 2
def baseEnd_2335299 : Nat := 1199130858964163865622661

theorem tailTrace_2335299 : CollatzResearch.WordTrace tailWord_2335299 prefixEnd_2335299 1199130858964163865622661 := by
  unfold tailWord_2335299
  simp only [CollatzResearch.WordTrace]
  refine ⟨85175351966618035161248951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56783567977745356774165967 85175351966618035161248951)
  ·
    refine ⟨127763027949927052741873427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85175351966618035161248951 127763027949927052741873427)
    ·
      refine ⟨191644541924890579112810141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127763027949927052741873427 191644541924890579112810141)
      ·
        refine ⟨71866703221833967167303803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191644541924890579112810141 71866703221833967167303803)
        ·
          refine ⟨107800054832750950750955705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71866703221833967167303803 107800054832750950750955705)
          ·
            refine ⟨80850041124563213063216779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107800054832750950750955705 80850041124563213063216779)
            ·
              refine ⟨121275061686844819594825169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80850041124563213063216779 121275061686844819594825169)
              ·
                refine ⟨90956296265133614696118877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 121275061686844819594825169 90956296265133614696118877)
                ·
                  refine ⟨34108611099425105511044579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90956296265133614696118877 34108611099425105511044579)
                  ·
                    refine ⟨51162916649137658266566869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34108611099425105511044579 51162916649137658266566869)
                    ·
                      refine ⟨1199130858964163865622661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51162916649137658266566869 1199130858964163865622661)
                      ·
                        rfl

theorem cell23_2335299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_2335299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335299 prefixEnd_2335299 := by exact prefixLift 2335299
  have htrace : WordTrace (prefixWord ++ tailWord_2335299) baseStart_2335299 baseEnd_2335299 := by
    simpa [prefixWord, tailWord_2335299, baseEnd_2335299] using wordTrace_append hprefix tailTrace_2335299
  have hstable : (prefixWord ++ tailWord_2335299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335299).length < 2 ^ (prefixWord ++ tailWord_2335299).sum := by decide
  have hdescent : baseEnd_2335299 < baseStart_2335299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335306 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_2335306 : Nat := 118140960795 + 2335306 * 2 ^ 59
def prefixEnd_2335306 : Nat := 4983230072969 + 3 ^ 40 * 2335306 * 2
def baseEnd_2335306 : Nat := 399711484442915112745043

theorem tailTrace_2335306 : CollatzResearch.WordTrace tailWord_2335306 prefixEnd_2335306 399711484442915112745043 := by
  unfold tailWord_2335306
  simp only [CollatzResearch.WordTrace]
  refine ⟨21293901819398168839188443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 56783738185061783571169181 21293901819398168839188443)
  ·
    refine ⟨31940852729097253258782665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21293901819398168839188443 31940852729097253258782665)
    ·
      refine ⟨23955639546822939944086999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31940852729097253258782665 23955639546822939944086999)
      ·
        refine ⟨35933459320234409916130499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23955639546822939944086999 35933459320234409916130499)
        ·
          refine ⟨53900188980351614874195749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35933459320234409916130499 53900188980351614874195749)
          ·
            refine ⟨10106285433815927788911703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53900188980351614874195749 10106285433815927788911703)
            ·
              refine ⟨15159428150723891683367555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10106285433815927788911703 15159428150723891683367555)
              ·
                refine ⟨22739142226085837525051333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15159428150723891683367555 22739142226085837525051333)
                ·
                  refine ⟨4263589167391094535947125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22739142226085837525051333 4263589167391094535947125)
                  ·
                    refine ⟨399711484442915112745043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4263589167391094535947125 399711484442915112745043)
                    ·
                      rfl

theorem cell23_2335306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_2335306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335306 prefixEnd_2335306 := by exact prefixLift 2335306
  have htrace : WordTrace (prefixWord ++ tailWord_2335306) baseStart_2335306 baseEnd_2335306 := by
    simpa [prefixWord, tailWord_2335306, baseEnd_2335306] using wordTrace_append hprefix tailTrace_2335306
  have hstable : (prefixWord ++ tailWord_2335306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335306).length < 2 ^ (prefixWord ++ tailWord_2335306).sum := by decide
  have hdescent : baseEnd_2335306 < baseStart_2335306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335316 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_2335316 : Nat := 118140960795 + 2335316 * 2 ^ 59
def prefixEnd_2335316 : Nat := 4983230072969 + 3 ^ 40 * 2335316 * 2
def baseEnd_2335316 : Nat := 1199139588135290299110083

theorem tailTrace_2335316 : CollatzResearch.WordTrace tailWord_2335316 prefixEnd_2335316 1199139588135290299110083 := by
  unfold tailWord_2335316
  simp only [CollatzResearch.WordTrace]
  refine ⟨42587986003778223532308901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 56783981338370964709745201 42587986003778223532308901)
  ·
    refine ⟨7985247375708416912307919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42587986003778223532308901 7985247375708416912307919)
    ·
      refine ⟨11977871063562625368461879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7985247375708416912307919 11977871063562625368461879)
      ·
        refine ⟨17966806595343938052692819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11977871063562625368461879 17966806595343938052692819)
        ·
          refine ⟨26950209893015907079039229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17966806595343938052692819 26950209893015907079039229)
          ·
            refine ⟨10106328709880965154639711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26950209893015907079039229 10106328709880965154639711)
            ·
              refine ⟨15159493064821447731959567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10106328709880965154639711 15159493064821447731959567)
              ·
                refine ⟨22739239597232171597939351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15159493064821447731959567 22739239597232171597939351)
                ·
                  refine ⟨34108859395848257396909027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22739239597232171597939351 34108859395848257396909027)
                  ·
                    refine ⟨51163289093772386095363541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34108859395848257396909027 51163289093772386095363541)
                    ·
                      refine ⟨1199139588135290299110083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51163289093772386095363541 1199139588135290299110083)
                      ·
                        rfl

theorem cell23_2335316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_2335316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335316 prefixEnd_2335316 := by exact prefixLift 2335316
  have htrace : WordTrace (prefixWord ++ tailWord_2335316) baseStart_2335316 baseEnd_2335316 := by
    simpa [prefixWord, tailWord_2335316, baseEnd_2335316] using wordTrace_append hprefix tailTrace_2335316
  have hstable : (prefixWord ++ tailWord_2335316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335316).length < 2 ^ (prefixWord ++ tailWord_2335316).sum := by decide
  have hdescent : baseEnd_2335316 < baseStart_2335316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2335363 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 3]
def baseStart_2335363 : Nat := 118140960795 + 2335363 * 2 ^ 59
def prefixEnd_2335363 : Nat := 4983230072969 + 3 ^ 40 * 2335363 * 2
def baseEnd_2335363 : Nat := 1199163721726051615222367

theorem tailTrace_2335363 : CollatzResearch.WordTrace tailWord_2335363 prefixEnd_2335363 1199163721726051615222367 := by
  unfold tailWord_2335363
  simp only [CollatzResearch.WordTrace]
  refine ⟨85177686238386174091578743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 56785124158924116061052495 85177686238386174091578743)
  ·
    refine ⟨127766529357579261137368115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 85177686238386174091578743 127766529357579261137368115)
    ·
      refine ⟨191649794036368891706052173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127766529357579261137368115 191649794036368891706052173)
      ·
        refine ⟨71868672763638334389769565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 191649794036368891706052173 71868672763638334389769565)
        ·
          refine ⟨26950752286364375396163587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71868672763638334389769565 26950752286364375396163587)
          ·
            refine ⟨40426128429546563094245381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26950752286364375396163587 40426128429546563094245381)
            ·
              refine ⟨7579899080539980580171009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40426128429546563094245381 7579899080539980580171009)
              ·
                refine ⟨5684924310404985435128257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7579899080539980580171009 5684924310404985435128257)
                ·
                  refine ⟨4263693232803739076346193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5684924310404985435128257 4263693232803739076346193)
                  ·
                    refine ⟨3197769924602804307259645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4263693232803739076346193 3197769924602804307259645)
                    ·
                      refine ⟨1199163721726051615222367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3197769924602804307259645 1199163721726051615222367)
                      ·
                        rfl

theorem cell23_2335363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_2335363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2335363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2335363 prefixEnd_2335363 := by exact prefixLift 2335363
  have htrace : WordTrace (prefixWord ++ tailWord_2335363) baseStart_2335363 baseEnd_2335363 := by
    simpa [prefixWord, tailWord_2335363, baseEnd_2335363] using wordTrace_append hprefix tailTrace_2335363
  have hstable : (prefixWord ++ tailWord_2335363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2335363).length < 2 ^ (prefixWord ++ tailWord_2335363).sum := by decide
  have hdescent : baseEnd_2335363 < baseStart_2335363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2335363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
