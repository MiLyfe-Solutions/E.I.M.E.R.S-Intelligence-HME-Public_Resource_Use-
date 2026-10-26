import V185TrunkScan22Chunk078

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_710781 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 7]
def baseStart_710781 : Nat := 118140960795 + 710781 * 2 ^ 59
def prefixEnd_710781 : Nat := 4983230072969 + 3 ^ 40 * 710781 * 2
def baseEnd_710781 : Nat := 81104954018553066615263

theorem tailTrace_710781 : CollatzResearch.WordTrace tailWord_710781 prefixEnd_710781 81104954018553066615263 := by
  unfold tailWord_710781
  simp only [CollatzResearch.WordTrace]
  refine ⟨25924312837969303575420197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17282875225312869050280131 25924312837969303575420197)
  ·
    refine ⟨4860808657119244420391287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25924312837969303575420197 4860808657119244420391287)
    ·
      refine ⟨7291212985678866630586931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4860808657119244420391287 7291212985678866630586931)
      ·
        refine ⟨10936819478518299945880397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7291212985678866630586931 10936819478518299945880397)
        ·
          refine ⟨4101307304444362479705149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10936819478518299945880397 4101307304444362479705149)
          ·
            refine ⟨1537990239166635929889431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4101307304444362479705149 1537990239166635929889431)
            ·
              refine ⟨2306985358749953894834147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537990239166635929889431 2306985358749953894834147)
              ·
                refine ⟨3460478038124930842251221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2306985358749953894834147 3460478038124930842251221)
                ·
                  refine ⟨81104954018553066615263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3460478038124930842251221 81104954018553066615263)
                  ·
                    rfl

theorem cell22_710781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_710781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710781 prefixEnd_710781 := by exact prefixLift 710781
  have htrace : WordTrace (prefixWord ++ tailWord_710781) baseStart_710781 baseEnd_710781 := by
    simpa [prefixWord, tailWord_710781, baseEnd_710781] using wordTrace_append hprefix tailTrace_710781
  have hstable : (prefixWord ++ tailWord_710781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710781).length < 2 ^ (prefixWord ++ tailWord_710781).sum := by decide
  have hdescent : baseEnd_710781 < baseStart_710781 := by decide
  rcases family_descends (prefixWord ++ tailWord_710781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710785 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 3, 3]
def baseStart_710785 : Nat := 118140960795 + 710785 * 2 ^ 59
def prefixEnd_710785 : Nat := 4983230072969 + 3 ^ 40 * 710785 * 2
def baseEnd_710785 : Nat := 243316231337404522745777

theorem tailTrace_710785 : CollatzResearch.WordTrace tailWord_710785 prefixEnd_710785 243316231337404522745777 := by
  unfold tailWord_710785
  simp only [CollatzResearch.WordTrace]
  refine ⟨25924458729954812258565809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17282972486636541505710539 25924458729954812258565809)
  ·
    refine ⟨19443344047466109193924357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25924458729954812258565809 19443344047466109193924357)
    ·
      refine ⟨3645627008899895473860817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19443344047466109193924357 3645627008899895473860817)
      ·
        refine ⟨2734220256674921605395613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3645627008899895473860817 2734220256674921605395613)
        ·
          refine ⟨1025332596253095602023355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2734220256674921605395613 1025332596253095602023355)
          ·
            refine ⟨1537998894379643403035033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025332596253095602023355 1537998894379643403035033)
            ·
              refine ⟨1153499170784732552276275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1537998894379643403035033 1153499170784732552276275)
              ·
                refine ⟨1730248756177098828414413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153499170784732552276275 1730248756177098828414413)
                ·
                  refine ⟨648843283566412060655405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1730248756177098828414413 648843283566412060655405)
                  ·
                    refine ⟨243316231337404522745777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648843283566412060655405 243316231337404522745777)
                    ·
                      rfl

theorem cell22_710785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_710785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710785 prefixEnd_710785 := by exact prefixLift 710785
  have htrace : WordTrace (prefixWord ++ tailWord_710785) baseStart_710785 baseEnd_710785 := by
    simpa [prefixWord, tailWord_710785, baseEnd_710785] using wordTrace_append hprefix tailTrace_710785
  have hstable : (prefixWord ++ tailWord_710785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710785).length < 2 ^ (prefixWord ++ tailWord_710785).sum := by decide
  have hdescent : baseEnd_710785 < baseStart_710785 := by decide
  rcases family_descends (prefixWord ++ tailWord_710785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710836 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_710836 : Nat := 118140960795 + 710836 * 2 ^ 59
def prefixEnd_710836 : Nat := 4983230072969 + 3 ^ 40 * 710836 * 2
def baseEnd_710836 : Nat := 243333689679657389720621

theorem tailTrace_710836 : CollatzResearch.WordTrace tailWord_710836 prefixEnd_710836 243333689679657389720621 := by
  unfold tailWord_710836
  simp only [CollatzResearch.WordTrace]
  refine ⟨12963159426385023984336181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17284212568513365312448241 12963159426385023984336181)
  ·
    refine ⟨1215296196223595998531517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12963159426385023984336181 1215296196223595998531517)
    ·
      refine ⟨455736073583848499449319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1215296196223595998531517 455736073583848499449319)
      ·
        refine ⟨683604110375772749173979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455736073583848499449319 683604110375772749173979)
        ·
          refine ⟨1025406165563659123760969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683604110375772749173979 1025406165563659123760969)
          ·
            refine ⟨769054624172744342820727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1025406165563659123760969 769054624172744342820727)
            ·
              refine ⟨1153581936259116514231091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769054624172744342820727 1153581936259116514231091)
              ·
                refine ⟨1730372904388674771346637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1153581936259116514231091 1730372904388674771346637)
                ·
                  refine ⟨648889839145753039254989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1730372904388674771346637 648889839145753039254989)
                  ·
                    refine ⟨243333689679657389720621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648889839145753039254989 243333689679657389720621)
                    ·
                      rfl

theorem cell22_710836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_710836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710836 prefixEnd_710836 := by exact prefixLift 710836
  have htrace : WordTrace (prefixWord ++ tailWord_710836) baseStart_710836 baseEnd_710836 := by
    simpa [prefixWord, tailWord_710836, baseEnd_710836] using wordTrace_append hprefix tailTrace_710836
  have hstable : (prefixWord ++ tailWord_710836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710836).length < 2 ^ (prefixWord ++ tailWord_710836).sum := by decide
  have hdescent : baseEnd_710836 < baseStart_710836 := by decide
  rcases family_descends (prefixWord ++ tailWord_710836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710849 : List Nat := [1, 2, 6, 1, 3, 1, 2, 1, 5]
def baseStart_710849 : Nat := 118140960795 + 710849 * 2 ^ 59
def prefixEnd_710849 : Nat := 4983230072969 + 3 ^ 40 * 710849 * 2
def baseEnd_710849 : Nat := 81112713281776563048527

theorem tailTrace_710849 : CollatzResearch.WordTrace tailWord_710849 prefixEnd_710849 81112713281776563048527 := by
  unfold tailWord_710849
  simp only [CollatzResearch.WordTrace]
  refine ⟨25926793001722951188895601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17284528667815300792597067 25926793001722951188895601)
  ·
    refine ⟨19445094751292213391671701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25926793001722951188895601 19445094751292213391671701)
    ·
      refine ⟨911488816466822502734611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19445094751292213391671701 911488816466822502734611)
      ·
        refine ⟨1367233224700233754101917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911488816466822502734611 1367233224700233754101917)
        ·
          refine ⟨512712459262587657788219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1367233224700233754101917 512712459262587657788219)
          ·
            refine ⟨769068688893881486682329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512712459262587657788219 769068688893881486682329)
            ·
              refine ⟨576801516670411115011747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769068688893881486682329 576801516670411115011747)
              ·
                refine ⟨865202275005616672517621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576801516670411115011747 865202275005616672517621)
                ·
                  refine ⟨81112713281776563048527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 865202275005616672517621 81112713281776563048527)
                  ·
                    rfl

theorem cell22_710849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 5].length) (baseStart_710849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710849 prefixEnd_710849 := by exact prefixLift 710849
  have htrace : WordTrace (prefixWord ++ tailWord_710849) baseStart_710849 baseEnd_710849 := by
    simpa [prefixWord, tailWord_710849, baseEnd_710849] using wordTrace_append hprefix tailTrace_710849
  have hstable : (prefixWord ++ tailWord_710849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710849).length < 2 ^ (prefixWord ++ tailWord_710849).sum := by decide
  have hdescent : baseEnd_710849 < baseStart_710849 := by decide
  rcases family_descends (prefixWord ++ tailWord_710849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710856 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_710856 : Nat := 118140960795 + 710856 * 2 ^ 59
def prefixEnd_710856 : Nat := 4983230072969 + 3 ^ 40 * 710856 * 2
def baseEnd_710856 : Nat := 243340536088384004220559

theorem tailTrace_710856 : CollatzResearch.WordTrace tailWord_710856 prefixEnd_710856 243340536088384004220559 := by
  unfold tailWord_710856
  simp only [CollatzResearch.WordTrace]
  refine ⟨12963524156348795692200211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17284698875131727589600281 12963524156348795692200211)
  ·
    refine ⟨19445286234523193538300317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12963524156348795692200211 19445286234523193538300317)
    ·
      refine ⟨7291982337946197576862619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19445286234523193538300317 7291982337946197576862619)
      ·
        refine ⟨10937973506919296365293929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7291982337946197576862619 10937973506919296365293929)
        ·
          refine ⟨8203480130189472273970447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10937973506919296365293929 8203480130189472273970447)
          ·
            refine ⟨12305220195284208410955671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8203480130189472273970447 12305220195284208410955671)
            ·
              refine ⟨18457830292926312616433507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12305220195284208410955671 18457830292926312616433507)
              ·
                refine ⟨27686745439389468924650261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18457830292926312616433507 27686745439389468924650261)
                ·
                  refine ⟨1297816192471381355842981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27686745439389468924650261 1297816192471381355842981)
                  ·
                    refine ⟨243340536088384004220559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1297816192471381355842981 243340536088384004220559)
                    ·
                      rfl

theorem cell22_710856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_710856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710856 prefixEnd_710856 := by exact prefixLift 710856
  have htrace : WordTrace (prefixWord ++ tailWord_710856) baseStart_710856 baseEnd_710856 := by
    simpa [prefixWord, tailWord_710856, baseEnd_710856] using wordTrace_append hprefix tailTrace_710856
  have hstable : (prefixWord ++ tailWord_710856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710856).length < 2 ^ (prefixWord ++ tailWord_710856).sum := by decide
  have hdescent : baseEnd_710856 < baseStart_710856 := by decide
  rcases family_descends (prefixWord ++ tailWord_710856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710920 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 3, 3]
def baseStart_710920 : Nat := 118140960795 + 710920 * 2 ^ 59
def prefixEnd_710920 : Nat := 4983230072969 + 3 ^ 40 * 710920 * 2
def baseEnd_710920 : Nat := 243362444596309170620363

theorem tailTrace_710920 : CollatzResearch.WordTrace tailWord_710920 prefixEnd_710920 243362444596309170620363 := by
  unfold tailWord_710920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12964691292232865157365107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17286255056310486876486809 12964691292232865157365107)
  ·
    refine ⟨19447036938349297736047661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12964691292232865157365107 19447036938349297736047661)
    ·
      refine ⟨7292638851880986651017873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19447036938349297736047661 7292638851880986651017873)
      ·
        refine ⟨5469479138910739988263405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7292638851880986651017873 5469479138910739988263405)
        ·
          refine ⟨2051054677091527495598777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5469479138910739988263405 2051054677091527495598777)
          ·
            refine ⟨1538291007818645621699083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2051054677091527495598777 1538291007818645621699083)
            ·
              refine ⟨2307436511727968432548625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1538291007818645621699083 2307436511727968432548625)
              ·
                refine ⟨1730577383795976324411469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2307436511727968432548625 1730577383795976324411469)
                ·
                  refine ⟨648966518923491121654301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1730577383795976324411469 648966518923491121654301)
                  ·
                    refine ⟨243362444596309170620363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648966518923491121654301 243362444596309170620363)
                    ·
                      rfl

theorem cell22_710920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_710920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710920 prefixEnd_710920 := by exact prefixLift 710920
  have htrace : WordTrace (prefixWord ++ tailWord_710920) baseStart_710920 baseEnd_710920 := by
    simpa [prefixWord, tailWord_710920, baseEnd_710920] using wordTrace_append hprefix tailTrace_710920
  have hstable : (prefixWord ++ tailWord_710920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710920).length < 2 ^ (prefixWord ++ tailWord_710920).sum := by decide
  have hdescent : baseEnd_710920 < baseStart_710920 := by decide
  rcases family_descends (prefixWord ++ tailWord_710920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_710948 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_710948 : Nat := 118140960795 + 710948 * 2 ^ 59
def prefixEnd_710948 : Nat := 4983230072969 + 3 ^ 40 * 710948 * 2
def baseEnd_710948 : Nat := 243372029568526430920277

theorem tailTrace_710948 : CollatzResearch.WordTrace tailWord_710948 prefixEnd_710948 243372029568526430920277 := by
  unfold tailWord_710948
  simp only [CollatzResearch.WordTrace]
  refine ⟨12965201914182145548374749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17286935885576194064499665 12965201914182145548374749)
  ·
    refine ⟨4861950717818304580640531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12965201914182145548374749 4861950717818304580640531)
    ·
      refine ⟨7292926076727456870960797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4861950717818304580640531 7292926076727456870960797)
      ·
        refine ⟨2734847278772796326610299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7292926076727456870960797 2734847278772796326610299)
        ·
          refine ⟨4102270918159194489915449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2734847278772796326610299 4102270918159194489915449)
          ·
            refine ⟨3076703188619395867436587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4102270918159194489915449 3076703188619395867436587)
            ·
              refine ⟨4615054782929093801154881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3076703188619395867436587 4615054782929093801154881)
              ·
                refine ⟨3461291087196820350866161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4615054782929093801154881 3461291087196820350866161)
                ·
                  refine ⟨2595968315397615263149621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3461291087196820350866161 2595968315397615263149621)
                  ·
                    refine ⟨243372029568526430920277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2595968315397615263149621 243372029568526430920277)
                    ·
                      rfl

theorem cell22_710948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_710948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_710948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_710948 prefixEnd_710948 := by exact prefixLift 710948
  have htrace : WordTrace (prefixWord ++ tailWord_710948) baseStart_710948 baseEnd_710948 := by
    simpa [prefixWord, tailWord_710948, baseEnd_710948] using wordTrace_append hprefix tailTrace_710948
  have hstable : (prefixWord ++ tailWord_710948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_710948).length < 2 ^ (prefixWord ++ tailWord_710948).sum := by decide
  have hdescent : baseEnd_710948 < baseStart_710948 := by decide
  rcases family_descends (prefixWord ++ tailWord_710948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711012 : List Nat := [2, 3, 1, 1, 3, 1, 5, 2, 4]
def baseStart_711012 : Nat := 118140960795 + 711012 * 2 ^ 59
def prefixEnd_711012 : Nat := 4983230072969 + 3 ^ 40 * 711012 * 2
def baseEnd_711012 : Nat := 81131312692150532440027

theorem tailTrace_711012 : CollatzResearch.WordTrace tailWord_711012 prefixEnd_711012 81131312692150532440027 := by
  unfold tailWord_711012
  simp only [CollatzResearch.WordTrace]
  refine ⟨12966369050066215013539645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17288492066754953351386193 12966369050066215013539645)
  ·
    refine ⟨4862388393774830630077367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12966369050066215013539645 4862388393774830630077367)
    ·
      refine ⟨7293582590662245945116051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4862388393774830630077367 7293582590662245945116051)
      ·
        refine ⟨10940373885993368917674077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7293582590662245945116051 10940373885993368917674077)
        ·
          refine ⟨4102640207247513344127779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10940373885993368917674077 4102640207247513344127779)
          ·
            refine ⟨6153960310871270016191669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4102640207247513344127779 6153960310871270016191669)
            ·
              refine ⟨576933779144181564017969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6153960310871270016191669 576933779144181564017969)
              ·
                refine ⟨432700334358136173013477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 576933779144181564017969 432700334358136173013477)
                ·
                  refine ⟨81131312692150532440027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432700334358136173013477 81131312692150532440027)
                  ·
                    rfl

theorem cell22_711012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_711012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711012 prefixEnd_711012 := by exact prefixLift 711012
  have htrace : WordTrace (prefixWord ++ tailWord_711012) baseStart_711012 baseEnd_711012 := by
    simpa [prefixWord, tailWord_711012, baseEnd_711012] using wordTrace_append hprefix tailTrace_711012
  have hstable : (prefixWord ++ tailWord_711012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711012).length < 2 ^ (prefixWord ++ tailWord_711012).sum := by decide
  have hdescent : baseEnd_711012 < baseStart_711012 := by decide
  rcases family_descends (prefixWord ++ tailWord_711012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711130 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_711130 : Nat := 118140960795 + 711130 * 2 ^ 59
def prefixEnd_711130 : Nat := 4983230072969 + 3 ^ 40 * 711130 * 2
def baseEnd_711130 : Nat := 81144777295979540956573

theorem tailTrace_711130 : CollatzResearch.WordTrace tailWord_711130 prefixEnd_711130 81144777295979540956573 := by
  unfold tailWord_711130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6484260478426234044968711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17291361275803290786583229 6484260478426234044968711)
  ·
    refine ⟨9726390717639351067453067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6484260478426234044968711 9726390717639351067453067)
    ·
      refine ⟨14589586076459026601179601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9726390717639351067453067 14589586076459026601179601)
      ·
        refine ⟨10942189557344269950884701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14589586076459026601179601 10942189557344269950884701)
        ·
          refine ⟨4103321084004101231581763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10942189557344269950884701 4103321084004101231581763)
          ·
            refine ⟨6154981626006151847372645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103321084004101231581763 6154981626006151847372645)
            ·
              refine ⟨1154059054876153471382371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6154981626006151847372645 1154059054876153471382371)
              ·
                refine ⟨1731088582314230207073557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154059054876153471382371 1731088582314230207073557)
                ·
                  refine ⟨81144777295979540956573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1731088582314230207073557 81144777295979540956573)
                  ·
                    rfl

theorem cell22_711130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_711130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711130 prefixEnd_711130 := by exact prefixLift 711130
  have htrace : WordTrace (prefixWord ++ tailWord_711130) baseStart_711130 baseEnd_711130 := by
    simpa [prefixWord, tailWord_711130, baseEnd_711130] using wordTrace_append hprefix tailTrace_711130
  have hstable : (prefixWord ++ tailWord_711130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711130).length < 2 ^ (prefixWord ++ tailWord_711130).sum := by decide
  have hdescent : baseEnd_711130 < baseStart_711130 := by decide
  rcases family_descends (prefixWord ++ tailWord_711130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711149 : List Nat := [1, 5, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_711149 : Nat := 118140960795 + 711149 * 2 ^ 59
def prefixEnd_711149 : Nat := 4983230072969 + 3 ^ 40 * 711149 * 2
def baseEnd_711149 : Nat := 243440835976228906644661

theorem tailTrace_711149 : CollatzResearch.WordTrace tailWord_711149 prefixEnd_711149 243440835976228906644661 := by
  unfold tailWord_711149
  simp only [CollatzResearch.WordTrace]
  refine ⟨25937734900636102424816501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17291823267090734949877667 25937734900636102424816501)
  ·
    refine ⟨2431662646934634602326547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25937734900636102424816501 2431662646934634602326547)
    ·
      refine ⟨3647493970401951903489821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2431662646934634602326547 3647493970401951903489821)
      ·
        refine ⟨1367810238900731963808683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3647493970401951903489821 1367810238900731963808683)
        ·
          refine ⟨2051715358351097945713025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367810238900731963808683 2051715358351097945713025)
          ·
            refine ⟨1538786518763323459284769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2051715358351097945713025 1538786518763323459284769)
            ·
              refine ⟨1154089889072492594463577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538786518763323459284769 1154089889072492594463577)
              ·
                refine ⟨865567416804369445847683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154089889072492594463577 865567416804369445847683)
                ·
                  refine ⟨1298351125206554168771525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865567416804369445847683 1298351125206554168771525)
                  ·
                    refine ⟨243440835976228906644661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1298351125206554168771525 243440835976228906644661)
                    ·
                      rfl

theorem cell22_711149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_711149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711149 prefixEnd_711149 := by exact prefixLift 711149
  have htrace : WordTrace (prefixWord ++ tailWord_711149) baseStart_711149 baseEnd_711149 := by
    simpa [prefixWord, tailWord_711149, baseEnd_711149] using wordTrace_append hprefix tailTrace_711149
  have hstable : (prefixWord ++ tailWord_711149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711149).length < 2 ^ (prefixWord ++ tailWord_711149).sum := by decide
  have hdescent : baseEnd_711149 < baseStart_711149 := by decide
  rcases family_descends (prefixWord ++ tailWord_711149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711160 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_711160 : Nat := 118140960795 + 711160 * 2 ^ 59
def prefixEnd_711160 : Nat := 4983230072969 + 3 ^ 40 * 711160 * 2
def baseEnd_711160 : Nat := 243444601501028544619627

theorem tailTrace_711160 : CollatzResearch.WordTrace tailWord_711160 prefixEnd_711160 243444601501028544619627 := by
  unfold tailWord_711160
  simp only [CollatzResearch.WordTrace]
  refine ⟨12969068051798125651733467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17292090735730834202311289 12969068051798125651733467)
  ·
    refine ⟨19453602077697188477600201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12969068051798125651733467 19453602077697188477600201)
    ·
      refine ⟨14590201558272891358200151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19453602077697188477600201 14590201558272891358200151)
      ·
        refine ⟨21885302337409337037300227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14590201558272891358200151 21885302337409337037300227)
        ·
          refine ⟨32827953506114005555950341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21885302337409337037300227 32827953506114005555950341)
          ·
            refine ⟨6155241282396376041740689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32827953506114005555950341 6155241282396376041740689)
            ·
              refine ⟨4616430961797282031305517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6155241282396376041740689 4616430961797282031305517)
              ·
                refine ⟨1731161610673980761739569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4616430961797282031305517 1731161610673980761739569)
                ·
                  refine ⟨1298371208005485571304677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1731161610673980761739569 1298371208005485571304677)
                  ·
                    refine ⟨243444601501028544619627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1298371208005485571304677 243444601501028544619627)
                    ·
                      rfl

theorem cell22_711160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_711160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711160 prefixEnd_711160 := by exact prefixLift 711160
  have htrace : WordTrace (prefixWord ++ tailWord_711160) baseStart_711160 baseEnd_711160 := by
    simpa [prefixWord, tailWord_711160, baseEnd_711160] using wordTrace_append hprefix tailTrace_711160
  have hstable : (prefixWord ++ tailWord_711160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711160).length < 2 ^ (prefixWord ++ tailWord_711160).sum := by decide
  have hdescent : baseEnd_711160 < baseStart_711160 := by decide
  rcases family_descends (prefixWord ++ tailWord_711160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711181 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 6]
def baseStart_711181 : Nat := 118140960795 + 711181 * 2 ^ 59
def prefixEnd_711181 : Nat := 4983230072969 + 3 ^ 40 * 711181 * 2
def baseEnd_711181 : Nat := 81150596743397163281521

theorem tailTrace_711181 : CollatzResearch.WordTrace tailWord_711181 prefixEnd_711181 81150596743397163281521 := by
  unfold tailWord_711181
  simp only [CollatzResearch.WordTrace]
  refine ⟨25938902036520171889981397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17292601357680114593320931 25938902036520171889981397)
  ·
    refine ⟨607943016480941528671439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 25938902036520171889981397 607943016480941528671439)
    ·
      refine ⟨911914524721412293007159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607943016480941528671439 911914524721412293007159)
      ·
        refine ⟨1367871787082118439510739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 911914524721412293007159 1367871787082118439510739)
        ·
          refine ⟨2051807680623177659266109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1367871787082118439510739 2051807680623177659266109)
          ·
            refine ⟨769427880233691622224791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2051807680623177659266109 769427880233691622224791)
            ·
              refine ⟨1154141820350537433337187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769427880233691622224791 1154141820350537433337187)
              ·
                refine ⟨1731212730525806150005781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154141820350537433337187 1731212730525806150005781)
                ·
                  refine ⟨81150596743397163281521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1731212730525806150005781 81150596743397163281521)
                  ·
                    rfl

theorem cell22_711181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_711181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711181 prefixEnd_711181 := by exact prefixLift 711181
  have htrace : WordTrace (prefixWord ++ tailWord_711181) baseStart_711181 baseEnd_711181 := by
    simpa [prefixWord, tailWord_711181, baseEnd_711181] using wordTrace_append hprefix tailTrace_711181
  have hstable : (prefixWord ++ tailWord_711181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711181).length < 2 ^ (prefixWord ++ tailWord_711181).sum := by decide
  have hdescent : baseEnd_711181 < baseStart_711181 := by decide
  rcases family_descends (prefixWord ++ tailWord_711181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711196 : List Nat := [2, 2, 3, 1, 2, 4, 2, 1, 2, 3]
def baseStart_711196 : Nat := 118140960795 + 711196 * 2 ^ 59
def prefixEnd_711196 : Nat := 4983230072969 + 3 ^ 40 * 711196 * 2
def baseEnd_711196 : Nat := 243456925036736450719517

theorem tailTrace_711196 : CollatzResearch.WordTrace tailWord_711196 prefixEnd_711196 243456925036736450719517 := by
  unfold tailWord_711196
  simp only [CollatzResearch.WordTrace]
  refine ⟨12969724565732914725888721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17292966087643886301184961 12969724565732914725888721)
  ·
    refine ⟨9727293424299686044416541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12969724565732914725888721 9727293424299686044416541)
    ·
      refine ⟨3647735034112382266656203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9727293424299686044416541 3647735034112382266656203)
      ·
        refine ⟨5471602551168573399984305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647735034112382266656203 5471602551168573399984305)
        ·
          refine ⟨4103701913376430049988229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5471602551168573399984305 4103701913376430049988229)
          ·
            refine ⟨769444108758080634372793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4103701913376430049988229 769444108758080634372793)
            ·
              refine ⟨577083081568560475779595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769444108758080634372793 577083081568560475779595)
              ·
                refine ⟨865624622352840713669393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577083081568560475779595 865624622352840713669393)
                ·
                  refine ⟨649218466764630535252045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 865624622352840713669393 649218466764630535252045)
                  ·
                    refine ⟨243456925036736450719517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 649218466764630535252045 243456925036736450719517)
                    ·
                      rfl

theorem cell22_711196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_711196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711196 prefixEnd_711196 := by exact prefixLift 711196
  have htrace : WordTrace (prefixWord ++ tailWord_711196) baseStart_711196 baseEnd_711196 := by
    simpa [prefixWord, tailWord_711196, baseEnd_711196] using wordTrace_append hprefix tailTrace_711196
  have hstable : (prefixWord ++ tailWord_711196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711196).length < 2 ^ (prefixWord ++ tailWord_711196).sum := by decide
  have hdescent : baseEnd_711196 < baseStart_711196 := by decide
  rcases family_descends (prefixWord ++ tailWord_711196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711224 : List Nat := [2, 1, 2, 1, 4, 1, 2, 5, 1, 3]
def baseStart_711224 : Nat := 118140960795 + 711224 * 2 ^ 59
def prefixEnd_711224 : Nat := 4983230072969 + 3 ^ 40 * 711224 * 2
def baseEnd_711224 : Nat := 243466510008953711019431

theorem tailTrace_711224 : CollatzResearch.WordTrace tailWord_711224 prefixEnd_711224 243466510008953711019431 := by
  unfold tailWord_711224
  simp only [CollatzResearch.WordTrace]
  refine ⟨12970235187682195116898363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17293646916909593489197817 12970235187682195116898363)
  ·
    refine ⟨19455352781523292675347545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12970235187682195116898363 19455352781523292675347545)
    ·
      refine ⟨14591514586142469506510659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19455352781523292675347545 14591514586142469506510659)
      ·
        refine ⟨21887271879213704259765989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14591514586142469506510659 21887271879213704259765989)
        ·
          refine ⟨4103863477352569548706123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21887271879213704259765989 4103863477352569548706123)
          ·
            refine ⟨6155795216028854323059185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103863477352569548706123 6155795216028854323059185)
            ·
              refine ⟨4616846412021640742294389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6155795216028854323059185 4616846412021640742294389)
              ·
                refine ⟨432829351127028819590099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4616846412021640742294389 432829351127028819590099)
                ·
                  refine ⟨649244026690543229385149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432829351127028819590099 649244026690543229385149)
                  ·
                    refine ⟨243466510008953711019431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 649244026690543229385149 243466510008953711019431)
                    ·
                      rfl

theorem cell22_711224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_711224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711224 prefixEnd_711224 := by exact prefixLift 711224
  have htrace : WordTrace (prefixWord ++ tailWord_711224) baseStart_711224 baseEnd_711224 := by
    simpa [prefixWord, tailWord_711224, baseEnd_711224] using wordTrace_append hprefix tailTrace_711224
  have hstable : (prefixWord ++ tailWord_711224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711224).length < 2 ^ (prefixWord ++ tailWord_711224).sum := by decide
  have hdescent : baseEnd_711224 < baseStart_711224 := by decide
  rcases family_descends (prefixWord ++ tailWord_711224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711237 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 5]
def baseStart_711237 : Nat := 118140960795 + 711237 * 2 ^ 59
def prefixEnd_711237 : Nat := 4983230072969 + 3 ^ 40 * 711237 * 2
def baseEnd_711237 : Nat := 81156986724875336814797

theorem tailTrace_711237 : CollatzResearch.WordTrace tailWord_711237 prefixEnd_711237 81156986724875336814797 := by
  unfold tailWord_711237
  simp only [CollatzResearch.WordTrace]
  refine ⟨25940944524317293454019965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17293963016211528969346643 25940944524317293454019965)
  ·
    refine ⟨9727854196618985045257487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25940944524317293454019965 9727854196618985045257487)
    ·
      refine ⟨14591781294928477567886231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9727854196618985045257487 14591781294928477567886231)
      ·
        refine ⟨21887671942392716351829347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14591781294928477567886231 21887671942392716351829347)
        ·
          refine ⟨32831507913589074527744021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21887671942392716351829347 32831507913589074527744021)
          ·
            refine ⟨1538976933449487868488001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32831507913589074527744021 1538976933449487868488001)
            ·
              refine ⟨1154232700087115901366001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1538976933449487868488001 1154232700087115901366001)
              ·
                refine ⟨865674525065336926024501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154232700087115901366001 865674525065336926024501)
                ·
                  refine ⟨81156986724875336814797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 865674525065336926024501 81156986724875336814797)
                  ·
                    rfl

theorem cell22_711237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_711237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711237 prefixEnd_711237 := by exact prefixLift 711237
  have htrace : WordTrace (prefixWord ++ tailWord_711237) baseStart_711237 baseEnd_711237 := by
    simpa [prefixWord, tailWord_711237, baseEnd_711237] using wordTrace_append hprefix tailTrace_711237
  have hstable : (prefixWord ++ tailWord_711237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711237).length < 2 ^ (prefixWord ++ tailWord_711237).sum := by decide
  have hdescent : baseEnd_711237 < baseStart_711237 := by decide
  rcases family_descends (prefixWord ++ tailWord_711237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711252 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_711252 : Nat := 118140960795 + 711252 * 2 ^ 59
def prefixEnd_711252 : Nat := 4983230072969 + 3 ^ 40 * 711252 * 2
def baseEnd_711252 : Nat := 243476094981170971319345

theorem tailTrace_711252 : CollatzResearch.WordTrace tailWord_711252 prefixEnd_711252 243476094981170971319345 := by
  unfold tailWord_711252
  simp only [CollatzResearch.WordTrace]
  refine ⟨12970745809631475507908005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17294327746175300677210673 12970745809631475507908005)
  ·
    refine ⟨2432014839305901657732751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12970745809631475507908005 2432014839305901657732751)
    ·
      refine ⟨3648022258958852486599127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2432014839305901657732751 3648022258958852486599127)
      ·
        refine ⟨5472033388438278729898691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3648022258958852486599127 5472033388438278729898691)
        ·
          refine ⟨8208050082657418094848037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5472033388438278729898691 8208050082657418094848037)
          ·
            refine ⟨1539009390498265892784007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8208050082657418094848037 1539009390498265892784007)
            ·
              refine ⟨2308514085747398839176011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539009390498265892784007 2308514085747398839176011)
              ·
                refine ⟨3462771128621098258764017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2308514085747398839176011 3462771128621098258764017)
                ·
                  refine ⟨2597078346465823694073013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3462771128621098258764017 2597078346465823694073013)
                  ·
                    refine ⟨243476094981170971319345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2597078346465823694073013 243476094981170971319345)
                    ·
                      rfl

theorem cell22_711252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_711252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711252 prefixEnd_711252 := by exact prefixLift 711252
  have htrace : WordTrace (prefixWord ++ tailWord_711252) baseStart_711252 baseEnd_711252 := by
    simpa [prefixWord, tailWord_711252, baseEnd_711252] using wordTrace_append hprefix tailTrace_711252
  have hstable : (prefixWord ++ tailWord_711252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711252).length < 2 ^ (prefixWord ++ tailWord_711252).sum := by decide
  have hdescent : baseEnd_711252 < baseStart_711252 := by decide
  rcases family_descends (prefixWord ++ tailWord_711252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711265 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 8]
def baseStart_711265 : Nat := 118140960795 + 711265 * 2 ^ 59
def prefixEnd_711265 : Nat := 4983230072969 + 3 ^ 40 * 711265 * 2
def baseEnd_711265 : Nat := 81160181715614423581435

theorem tailTrace_711265 : CollatzResearch.WordTrace tailWord_711265 prefixEnd_711265 81160181715614423581435 := by
  unfold tailWord_711265
  simp only [CollatzResearch.WordTrace]
  refine ⟨25941965768215854236039249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17294643845477236157359499 25941965768215854236039249)
  ·
    refine ⟨19456474326161890677029437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25941965768215854236039249 19456474326161890677029437)
    ·
      refine ⟨7296177872310709003886039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19456474326161890677029437 7296177872310709003886039)
      ·
        refine ⟨10944266808466063505829059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7296177872310709003886039 10944266808466063505829059)
        ·
          refine ⟨16416400212699095258743589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10944266808466063505829059 16416400212699095258743589)
          ·
            refine ⟨3078075039881080361014423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16416400212699095258743589 3078075039881080361014423)
            ·
              refine ⟨4617112559821620541521635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3078075039881080361014423 4617112559821620541521635)
              ·
                refine ⟨6925668839732430812282453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4617112559821620541521635 6925668839732430812282453)
                ·
                  refine ⟨81160181715614423581435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6925668839732430812282453 81160181715614423581435)
                  ·
                    rfl

theorem cell22_711265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_711265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711265 prefixEnd_711265 := by exact prefixLift 711265
  have htrace : WordTrace (prefixWord ++ tailWord_711265) baseStart_711265 baseEnd_711265 := by
    simpa [prefixWord, tailWord_711265, baseEnd_711265] using wordTrace_append hprefix tailTrace_711265
  have hstable : (prefixWord ++ tailWord_711265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711265).length < 2 ^ (prefixWord ++ tailWord_711265).sum := by decide
  have hdescent : baseEnd_711265 < baseStart_711265 := by decide
  rcases family_descends (prefixWord ++ tailWord_711265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711267 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 1, 4]
def baseStart_711267 : Nat := 118140960795 + 711267 * 2 ^ 59
def prefixEnd_711267 : Nat := 4983230072969 + 3 ^ 40 * 711267 * 2
def baseEnd_711267 : Nat := 243481229787715932194299

theorem tailTrace_711267 : CollatzResearch.WordTrace tailWord_711267 prefixEnd_711267 243481229787715932194299 := by
  unfold tailWord_711267
  simp only [CollatzResearch.WordTrace]
  refine ⟨25942038714208608577612055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17294692476139072385074703 25942038714208608577612055)
  ·
    refine ⟨38913058071312912866418083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25942038714208608577612055 38913058071312912866418083)
    ·
      refine ⟨58369587106969369299627125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38913058071312912866418083 58369587106969369299627125)
      ·
        refine ⟨5472148791278378371840043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58369587106969369299627125 5472148791278378371840043)
        ·
          refine ⟨8208223186917567557760065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5472148791278378371840043 8208223186917567557760065)
          ·
            refine ⟨6156167390188175668320049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8208223186917567557760065 6156167390188175668320049)
            ·
              refine ⟨4617125542641131751240037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6156167390188175668320049 4617125542641131751240037)
              ·
                refine ⟨865711039245212203357507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4617125542641131751240037 865711039245212203357507)
                ·
                  refine ⟨1298566558867818305036261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865711039245212203357507 1298566558867818305036261)
                  ·
                    refine ⟨243481229787715932194299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1298566558867818305036261 243481229787715932194299)
                    ·
                      rfl

theorem cell22_711267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 4].length) (baseStart_711267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711267 prefixEnd_711267 := by exact prefixLift 711267
  have htrace : WordTrace (prefixWord ++ tailWord_711267) baseStart_711267 baseEnd_711267 := by
    simpa [prefixWord, tailWord_711267, baseEnd_711267] using wordTrace_append hprefix tailTrace_711267
  have hstable : (prefixWord ++ tailWord_711267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711267).length < 2 ^ (prefixWord ++ tailWord_711267).sum := by decide
  have hdescent : baseEnd_711267 < baseStart_711267 := by decide
  rcases family_descends (prefixWord ++ tailWord_711267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711314 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 1, 5]
def baseStart_711314 : Nat := 118140960795 + 711314 * 2 ^ 59
def prefixEnd_711314 : Nat := 4983230072969 + 3 ^ 40 * 711314 * 2
def baseEnd_711314 : Nat := 243497318848223476269155

theorem tailTrace_711314 : CollatzResearch.WordTrace tailWord_711314 prefixEnd_711314 243497318848223476269155 := by
  unfold tailWord_711314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6485938236259583901143249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17295835296692223736381997 6485938236259583901143249)
  ·
    refine ⟨4864453677194687925857437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6485938236259583901143249 4864453677194687925857437)
    ·
      refine ⟨1824170128948007972196539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4864453677194687925857437 1824170128948007972196539)
      ·
        refine ⟨2736255193422011958294809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824170128948007972196539 2736255193422011958294809)
        ·
          refine ⟨2052191395066508968721107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2736255193422011958294809 2052191395066508968721107)
          ·
            refine ⟨3078287092599763453081661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2052191395066508968721107 3078287092599763453081661)
            ·
              refine ⟨1154357659724911294905623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3078287092599763453081661 1154357659724911294905623)
              ·
                refine ⟨1731536489587366942358435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154357659724911294905623 1731536489587366942358435)
                ·
                  refine ⟨2597304734381050413537653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1731536489587366942358435 2597304734381050413537653)
                  ·
                    refine ⟨243497318848223476269155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2597304734381050413537653 243497318848223476269155)
                    ·
                      rfl

theorem cell22_711314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_711314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711314 prefixEnd_711314 := by exact prefixLift 711314
  have htrace : WordTrace (prefixWord ++ tailWord_711314) baseStart_711314 baseEnd_711314 := by
    simpa [prefixWord, tailWord_711314, baseEnd_711314] using wordTrace_append hprefix tailTrace_711314
  have hstable : (prefixWord ++ tailWord_711314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711314).length < 2 ^ (prefixWord ++ tailWord_711314).sum := by decide
  have hdescent : baseEnd_711314 < baseStart_711314 := by decide
  rcases family_descends (prefixWord ++ tailWord_711314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711350 : List Nat := [5, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_711350 : Nat := 118140960795 + 711350 * 2 ^ 59
def prefixEnd_711350 : Nat := 4983230072969 + 3 ^ 40 * 711350 * 2
def baseEnd_711350 : Nat := 81169880794643794123015

theorem tailTrace_711350 : CollatzResearch.WordTrace tailWord_711350 prefixEnd_711350 81169880794643794123015 := by
  unfold tailWord_711350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621566623306744609555219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17296710648605275835255669 1621566623306744609555219)
  ·
    refine ⟨2432349934960116914332829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1621566623306744609555219 2432349934960116914332829)
    ·
      refine ⟨912131225610043842874811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2432349934960116914332829 912131225610043842874811)
      ·
        refine ⟨1368196838415065764312217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 912131225610043842874811 1368196838415065764312217)
        ·
          refine ⟨1026147628811299323234163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1368196838415065764312217 1026147628811299323234163)
          ·
            refine ⟨1539221443216948984851245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026147628811299323234163 1539221443216948984851245)
            ·
              refine ⟨577208041206355869319217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1539221443216948984851245 577208041206355869319217)
              ·
                refine ⟨432906030904766901989413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577208041206355869319217 432906030904766901989413)
                ·
                  refine ⟨81169880794643794123015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432906030904766901989413 81169880794643794123015)
                  ·
                    rfl

theorem cell22_711350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_711350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711350 prefixEnd_711350 := by exact prefixLift 711350
  have htrace : WordTrace (prefixWord ++ tailWord_711350) baseStart_711350 baseEnd_711350 := by
    simpa [prefixWord, tailWord_711350, baseEnd_711350] using wordTrace_append hprefix tailTrace_711350
  have hstable : (prefixWord ++ tailWord_711350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711350).length < 2 ^ (prefixWord ++ tailWord_711350).sum := by decide
  have hdescent : baseEnd_711350 < baseStart_711350 := by decide
  rcases family_descends (prefixWord ++ tailWord_711350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711359 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 3, 3]
def baseStart_711359 : Nat := 118140960795 + 711359 * 2 ^ 59
def prefixEnd_711359 : Nat := 4983230072969 + 3 ^ 40 * 711359 * 2
def baseEnd_711359 : Nat := 243512723267858358894017

theorem tailTrace_711359 : CollatzResearch.WordTrace tailWord_711359 prefixEnd_711359 243512723267858358894017 := by
  unfold tailWord_711359
  simp only [CollatzResearch.WordTrace]
  refine ⟨25945394229875308289961131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17296929486583538859974087 25945394229875308289961131)
  ·
    refine ⟨38918091344812962434941697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25945394229875308289961131 38918091344812962434941697)
    ·
      refine ⟨29188568508609721826206273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38918091344812962434941697 29188568508609721826206273)
      ·
        refine ⟨21891426381457291369654705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29188568508609721826206273 21891426381457291369654705)
        ·
          refine ⟨16418569786092968527241029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21891426381457291369654705 16418569786092968527241029)
          ·
            refine ⟨3078481834892431598857693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16418569786092968527241029 3078481834892431598857693)
            ·
              refine ⟨1154430688084661849571635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3078481834892431598857693 1154430688084661849571635)
              ·
                refine ⟨1731646032126992774357453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154430688084661849571635 1731646032126992774357453)
                ·
                  refine ⟨649367262047622290384045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1731646032126992774357453 649367262047622290384045)
                  ·
                    refine ⟨243512723267858358894017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 649367262047622290384045 243512723267858358894017)
                    ·
                      rfl

theorem cell22_711359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 3].length) (baseStart_711359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711359 prefixEnd_711359 := by exact prefixLift 711359
  have htrace : WordTrace (prefixWord ++ tailWord_711359) baseStart_711359 baseEnd_711359 := by
    simpa [prefixWord, tailWord_711359, baseEnd_711359] using wordTrace_append hprefix tailTrace_711359
  have hstable : (prefixWord ++ tailWord_711359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711359).length < 2 ^ (prefixWord ++ tailWord_711359).sum := by decide
  have hdescent : baseEnd_711359 < baseStart_711359 := by decide
  rcases family_descends (prefixWord ++ tailWord_711359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711361 : List Nat := [1, 2, 6, 2, 1, 1, 2, 7]
def baseStart_711361 : Nat := 118140960795 + 711361 * 2 ^ 59
def prefixEnd_711361 : Nat := 4983230072969 + 3 ^ 40 * 711361 * 2
def baseEnd_711361 : Nat := 27057045323192335593779

theorem tailTrace_711361 : CollatzResearch.WordTrace tailWord_711361 prefixEnd_711361 27057045323192335593779 := by
  unfold tailWord_711361
  simp only [CollatzResearch.WordTrace]
  refine ⟨25945467175868062631533937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17296978117245375087689291 25945467175868062631533937)
  ·
    refine ⟨19459100381901046973650453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25945467175868062631533937 19459100381901046973650453)
    ·
      refine ⟨912145330401611576889865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19459100381901046973650453 912145330401611576889865)
      ·
        refine ⟨684108997801208682667399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912145330401611576889865 684108997801208682667399)
        ·
          refine ⟨1026163496701813024001099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684108997801208682667399 1026163496701813024001099)
          ·
            refine ⟨1539245245052719536001649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026163496701813024001099 1539245245052719536001649)
            ·
              refine ⟨1154433933789539652001237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539245245052719536001649 1154433933789539652001237)
              ·
                refine ⟨27057045323192335593779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1154433933789539652001237 27057045323192335593779)
                ·
                  rfl

theorem cell22_711361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 7].length) (baseStart_711361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711361 prefixEnd_711361 := by exact prefixLift 711361
  have htrace : WordTrace (prefixWord ++ tailWord_711361) baseStart_711361 baseEnd_711361 := by
    simpa [prefixWord, tailWord_711361, baseEnd_711361] using wordTrace_append hprefix tailTrace_711361
  have hstable : (prefixWord ++ tailWord_711361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711361).length < 2 ^ (prefixWord ++ tailWord_711361).sum := by decide
  have hdescent : baseEnd_711361 < baseStart_711361 := by decide
  rcases family_descends (prefixWord ++ tailWord_711361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711410 : List Nat := [3, 2, 1, 3, 1, 4, 2, 2, 1, 3]
def baseStart_711410 : Nat := 118140960795 + 711410 * 2 ^ 59
def prefixEnd_711410 : Nat := 4983230072969 + 3 ^ 40 * 711410 * 2
def baseEnd_711410 : Nat := 243530181610111225868861

theorem tailTrace_711410 : CollatzResearch.WordTrace tailWord_711410 prefixEnd_711410 243530181610111225868861 := by
  unfold tailWord_711410
  simp only [CollatzResearch.WordTrace]
  refine ⟨6486813588172636000016921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17298169568460362666711789 6486813588172636000016921)
  ·
    refine ⟨4865110191129477000012691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6486813588172636000016921 4865110191129477000012691)
    ·
      refine ⟨7297665286694215500019037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4865110191129477000012691 7297665286694215500019037)
      ·
        refine ⟨2736624482510330812507139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7297665286694215500019037 2736624482510330812507139)
        ·
          refine ⟨4104936723765496218760709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736624482510330812507139 4104936723765496218760709)
          ·
            refine ⟨769675635706030541017633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4104936723765496218760709 769675635706030541017633)
            ·
              refine ⟨577256726779522905763225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 769675635706030541017633 577256726779522905763225)
              ·
                refine ⟨432942545084642179322419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577256726779522905763225 432942545084642179322419)
                ·
                  refine ⟨649413817626963268983629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432942545084642179322419 649413817626963268983629)
                  ·
                    refine ⟨243530181610111225868861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 649413817626963268983629 243530181610111225868861)
                    ·
                      rfl

theorem cell22_711410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 1, 3].length) (baseStart_711410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711410 prefixEnd_711410 := by exact prefixLift 711410
  have htrace : WordTrace (prefixWord ++ tailWord_711410) baseStart_711410 baseEnd_711410 := by
    simpa [prefixWord, tailWord_711410, baseEnd_711410] using wordTrace_append hprefix tailTrace_711410
  have hstable : (prefixWord ++ tailWord_711410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711410).length < 2 ^ (prefixWord ++ tailWord_711410).sum := by decide
  have hdescent : baseEnd_711410 < baseStart_711410 := by decide
  rcases family_descends (prefixWord ++ tailWord_711410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711453 : List Nat := [1, 4, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_711453 : Nat := 118140960795 + 711453 * 2 ^ 59
def prefixEnd_711453 : Nat := 4983230072969 + 3 ^ 40 * 711453 * 2
def baseEnd_711453 : Nat := 243544901388873447043729

theorem tailTrace_711453 : CollatzResearch.WordTrace tailWord_711453 prefixEnd_711453 243544901388873447043729 := by
  unfold tailWord_711453
  simp only [CollatzResearch.WordTrace]
  refine ⟨25948822691534762343883013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17299215127689841562588675 25948822691534762343883013)
  ·
    refine ⟨4865404254662767939478065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25948822691534762343883013 4865404254662767939478065)
    ·
      refine ⟨3649053190997075954608549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4865404254662767939478065 3649053190997075954608549)
      ·
        refine ⟨684197473311951741489103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3649053190997075954608549 684197473311951741489103)
        ·
          refine ⟨1026296209967927612233655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684197473311951741489103 1026296209967927612233655)
          ·
            refine ⟨1539444314951891418350483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026296209967927612233655 1539444314951891418350483)
            ·
              refine ⟨2309166472427837127525725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539444314951891418350483 2309166472427837127525725)
              ·
                refine ⟨865937427160438922822147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2309166472427837127525725 865937427160438922822147)
                ·
                  refine ⟨1298906140740658384233221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 865937427160438922822147 1298906140740658384233221)
                  ·
                    refine ⟨243544901388873447043729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1298906140740658384233221 243544901388873447043729)
                    ·
                      rfl

theorem cell22_711453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_711453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711453 prefixEnd_711453 := by exact prefixLift 711453
  have htrace : WordTrace (prefixWord ++ tailWord_711453) baseStart_711453 baseEnd_711453 := by
    simpa [prefixWord, tailWord_711453, baseEnd_711453] using wordTrace_append hprefix tailTrace_711453
  have hstable : (prefixWord ++ tailWord_711453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711453).length < 2 ^ (prefixWord ++ tailWord_711453).sum := by decide
  have hdescent : baseEnd_711453 < baseStart_711453 := by decide
  rcases family_descends (prefixWord ++ tailWord_711453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711464 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_711464 : Nat := 118140960795 + 711464 * 2 ^ 59
def prefixEnd_711464 : Nat := 4983230072969 + 3 ^ 40 * 711464 * 2
def baseEnd_711464 : Nat := 243548666913673085018695

theorem tailTrace_711464 : CollatzResearch.WordTrace tailWord_711464 prefixEnd_711464 243548666913673085018695 := by
  unfold tailWord_711464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12974611947247455611266723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17299482596329940815022297 12974611947247455611266723)
  ·
    refine ⟨19461917920871183416900085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12974611947247455611266723 19461917920871183416900085)
    ·
      refine ⟨1824554805081673445334383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19461917920871183416900085 1824554805081673445334383)
      ·
        refine ⟨2736832207622510168001575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824554805081673445334383 2736832207622510168001575)
        ·
          refine ⟨4105248311433765252002363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736832207622510168001575 4105248311433765252002363)
          ·
            refine ⟨6157872467150647878003545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105248311433765252002363 6157872467150647878003545)
            ·
              refine ⟨4618404350362985908502659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6157872467150647878003545 4618404350362985908502659)
              ·
                refine ⟨6927606525544478862753989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4618404350362985908502659 6927606525544478862753989)
                ·
                  refine ⟨1298926223539589786766373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6927606525544478862753989 1298926223539589786766373)
                  ·
                    refine ⟨243548666913673085018695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1298926223539589786766373 243548666913673085018695)
                    ·
                      rfl

theorem cell22_711464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_711464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711464 prefixEnd_711464 := by exact prefixLift 711464
  have htrace : WordTrace (prefixWord ++ tailWord_711464) baseStart_711464 baseEnd_711464 := by
    simpa [prefixWord, tailWord_711464, baseEnd_711464] using wordTrace_append hprefix tailTrace_711464
  have hstable : (prefixWord ++ tailWord_711464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711464).length < 2 ^ (prefixWord ++ tailWord_711464).sum := by decide
  have hdescent : baseEnd_711464 < baseStart_711464 := by decide
  rcases family_descends (prefixWord ++ tailWord_711464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711524 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 7]
def baseStart_711524 : Nat := 118140960795 + 711524 * 2 ^ 59
def prefixEnd_711524 : Nat := 4983230072969 + 3 ^ 40 * 711524 * 2
def baseEnd_711524 : Nat := 81189735379950976172837

theorem tailTrace_711524 : CollatzResearch.WordTrace tailWord_711524 prefixEnd_711524 81189735379950976172837 := by
  unfold tailWord_711524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12975706137138770734858813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17300941516185027646478417 12975706137138770734858813)
  ·
    refine ⟨4865889801427039025572055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12975706137138770734858813 4865889801427039025572055)
    ·
      refine ⟨7298834702140558538358083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4865889801427039025572055 7298834702140558538358083)
      ·
        refine ⟨10948252053210837807537125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7298834702140558538358083 10948252053210837807537125)
        ·
          refine ⟨2052797259977032088913211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10948252053210837807537125 2052797259977032088913211)
          ·
            refine ⟨3079195889965548133369817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2052797259977032088913211 3079195889965548133369817)
            ·
              refine ⟨2309396917474161100027363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3079195889965548133369817 2309396917474161100027363)
              ·
                refine ⟨3464095376211241650041045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2309396917474161100027363 3464095376211241650041045)
                ·
                  refine ⟨81189735379950976172837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3464095376211241650041045 81189735379950976172837)
                  ·
                    rfl

theorem cell22_711524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_711524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711524 prefixEnd_711524 := by exact prefixLift 711524
  have htrace : WordTrace (prefixWord ++ tailWord_711524) baseStart_711524 baseEnd_711524 := by
    simpa [prefixWord, tailWord_711524, baseEnd_711524] using wordTrace_append hprefix tailTrace_711524
  have hstable : (prefixWord ++ tailWord_711524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711524).length < 2 ^ (prefixWord ++ tailWord_711524).sum := by decide
  have hdescent : baseEnd_711524 < baseStart_711524 := by decide
  rcases family_descends (prefixWord ++ tailWord_711524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711528 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 3, 3]
def baseStart_711528 : Nat := 118140960795 + 711528 * 2 ^ 59
def prefixEnd_711528 : Nat := 4983230072969 + 3 ^ 40 * 711528 * 2
def baseEnd_711528 : Nat := 243570575421598251418499

theorem tailTrace_711528 : CollatzResearch.WordTrace tailWord_711528 prefixEnd_711528 243570575421598251418499 := by
  unfold tailWord_711528
  simp only [CollatzResearch.WordTrace]
  refine ⟨12975779083131525076431619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17301038777508700101908825 12975779083131525076431619)
  ·
    refine ⟨19463668624697287614647429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12975779083131525076431619 19463668624697287614647429)
    ·
      refine ⟨3649437867130741427746393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19463668624697287614647429 3649437867130741427746393)
      ·
        refine ⟨2737078400348056070809795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3649437867130741427746393 2737078400348056070809795)
        ·
          refine ⟨4105617600522084106214693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737078400348056070809795 4105617600522084106214693)
          ·
            refine ⟨769803300097890769915255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4105617600522084106214693 769803300097890769915255)
            ·
              refine ⟨1154704950146836154872883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769803300097890769915255 1154704950146836154872883)
              ·
                refine ⟨1732057425220254232309325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154704950146836154872883 1732057425220254232309325)
                ·
                  refine ⟨649521534457595337115997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1732057425220254232309325 649521534457595337115997)
                  ·
                    refine ⟨243570575421598251418499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 649521534457595337115997 243570575421598251418499)
                    ·
                      rfl

theorem cell22_711528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_711528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711528 prefixEnd_711528 := by exact prefixLift 711528
  have htrace : WordTrace (prefixWord ++ tailWord_711528) baseStart_711528 baseEnd_711528 := by
    simpa [prefixWord, tailWord_711528, baseEnd_711528] using wordTrace_append hprefix tailTrace_711528
  have hstable : (prefixWord ++ tailWord_711528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711528).length < 2 ^ (prefixWord ++ tailWord_711528).sum := by decide
  have hdescent : baseEnd_711528 < baseStart_711528 := by decide
  rcases family_descends (prefixWord ++ tailWord_711528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711541 : List Nat := [1, 3, 4, 1, 1, 3, 1, 3, 5]
def baseStart_711541 : Nat := 118140960795 + 711541 * 2 ^ 59
def prefixEnd_711541 : Nat := 4983230072969 + 3 ^ 40 * 711541 * 2
def baseEnd_711541 : Nat := 81191675195756850281153

theorem tailTrace_711541 : CollatzResearch.WordTrace tailWord_711541 prefixEnd_711541 81191675195756850281153 := by
  unfold tailWord_711541
  simp only [CollatzResearch.WordTrace]
  refine ⟨25952032315215953373086477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17301354876810635582057651 25952032315215953373086477)
  ·
    refine ⟨9732012118205982514907429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25952032315215953373086477 9732012118205982514907429)
    ·
      refine ⟨1824752272163621721545143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9732012118205982514907429 1824752272163621721545143)
      ·
        refine ⟨2737128408245432582317715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824752272163621721545143 2737128408245432582317715)
        ·
          refine ⟨4105692612368148873476573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737128408245432582317715 4105692612368148873476573)
          ·
            refine ⟨1539634729638055827553715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4105692612368148873476573 1539634729638055827553715)
            ·
              refine ⟨2309452094457083741330573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1539634729638055827553715 2309452094457083741330573)
              ·
                refine ⟨866044535421406402998965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2309452094457083741330573 866044535421406402998965)
                ·
                  refine ⟨81191675195756850281153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 866044535421406402998965 81191675195756850281153)
                  ·
                    rfl

theorem cell22_711541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_711541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711541 prefixEnd_711541 := by exact prefixLift 711541
  have htrace : WordTrace (prefixWord ++ tailWord_711541) baseStart_711541 baseEnd_711541 := by
    simpa [prefixWord, tailWord_711541, baseEnd_711541] using wordTrace_append hprefix tailTrace_711541
  have hstable : (prefixWord ++ tailWord_711541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711541).length < 2 ^ (prefixWord ++ tailWord_711541).sum := by decide
  have hdescent : baseEnd_711541 < baseStart_711541 := by decide
  rcases family_descends (prefixWord ++ tailWord_711541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711616 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 2, 4]
def baseStart_711616 : Nat := 118140960795 + 711616 * 2 ^ 59
def prefixEnd_711616 : Nat := 4983230072969 + 3 ^ 40 * 711616 * 2
def baseEnd_711616 : Nat := 243600699619995355218229

theorem tailTrace_711616 : CollatzResearch.WordTrace tailWord_711616 prefixEnd_711616 243600699619995355218229 := by
  unfold tailWord_711616
  simp only [CollatzResearch.WordTrace]
  refine ⟨12977383894972120591033351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17303178526629494121377801 12977383894972120591033351)
  ·
    refine ⟨19466075842458180886550027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12977383894972120591033351 19466075842458180886550027)
    ·
      refine ⟨29199113763687271329825041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19466075842458180886550027 29199113763687271329825041)
      ·
        refine ⟨21899335322765453497368781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29199113763687271329825041 21899335322765453497368781)
        ·
          refine ⟨8212250746037045061513293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21899335322765453497368781 8212250746037045061513293)
          ·
            refine ⟨3079594029763891898067485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8212250746037045061513293 3079594029763891898067485)
            ·
              refine ⟨1154847761161459461775307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3079594029763891898067485 1154847761161459461775307)
              ·
                refine ⟨1732271641742189192662961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1154847761161459461775307 1732271641742189192662961)
                ·
                  refine ⟨1299203731306641894497221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1732271641742189192662961 1299203731306641894497221)
                  ·
                    refine ⟨243600699619995355218229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1299203731306641894497221 243600699619995355218229)
                    ·
                      rfl

theorem cell22_711616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_711616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711616 prefixEnd_711616 := by exact prefixLift 711616
  have htrace : WordTrace (prefixWord ++ tailWord_711616) baseStart_711616 baseEnd_711616 := by
    simpa [prefixWord, tailWord_711616, baseEnd_711616] using wordTrace_append hprefix tailTrace_711616
  have hstable : (prefixWord ++ tailWord_711616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711616).length < 2 ^ (prefixWord ++ tailWord_711616).sum := by decide
  have hdescent : baseEnd_711616 < baseStart_711616 := by decide
  rcases family_descends (prefixWord ++ tailWord_711616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711674 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 1, 7]
def baseStart_711674 : Nat := 118140960795 + 711674 * 2 ^ 59
def prefixEnd_711674 : Nat := 4983230072969 + 3 ^ 40 * 711674 * 2
def baseEnd_711674 : Nat := 243620554205302537268051

theorem tailTrace_711674 : CollatzResearch.WordTrace tailWord_711674 prefixEnd_711674 243620554205302537268051 := by
  unfold tailWord_711674
  simp only [CollatzResearch.WordTrace]
  refine ⟨6489220805933529271919519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17304588815822744725118717 6489220805933529271919519)
  ·
    refine ⟨9733831208900293907879279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6489220805933529271919519 9733831208900293907879279)
    ·
      refine ⟨14600746813350440861818919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9733831208900293907879279 14600746813350440861818919)
      ·
        refine ⟨21901120220025661292728379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14600746813350440861818919 21901120220025661292728379)
        ·
          refine ⟨32851680330038491939092569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21901120220025661292728379 32851680330038491939092569)
          ·
            refine ⟨24638760247528868954319427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32851680330038491939092569 24638760247528868954319427)
            ·
              refine ⟨36958140371293303431479141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24638760247528868954319427 36958140371293303431479141)
              ·
                refine ⟨6929651319617494393402339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36958140371293303431479141 6929651319617494393402339)
                ·
                  refine ⟨10394476979426241590103509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6929651319617494393402339 10394476979426241590103509)
                  ·
                    refine ⟨243620554205302537268051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10394476979426241590103509 243620554205302537268051)
                    ·
                      rfl

theorem cell22_711674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_711674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711674 prefixEnd_711674 := by exact prefixLift 711674
  have htrace : WordTrace (prefixWord ++ tailWord_711674) baseStart_711674 baseEnd_711674 := by
    simpa [prefixWord, tailWord_711674, baseEnd_711674] using wordTrace_append hprefix tailTrace_711674
  have hstable : (prefixWord ++ tailWord_711674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711674).length < 2 ^ (prefixWord ++ tailWord_711674).sum := by decide
  have hdescent : baseEnd_711674 < baseStart_711674 := by decide
  rcases family_descends (prefixWord ++ tailWord_711674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711706 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_711706 : Nat := 118140960795 + 711706 * 2 ^ 59
def prefixEnd_711706 : Nat := 4983230072969 + 3 ^ 40 * 711706 * 2
def baseEnd_711706 : Nat := 243631508459265120467953

theorem tailTrace_711706 : CollatzResearch.WordTrace tailWord_711706 prefixEnd_711706 243631508459265120467953 := by
  unfold tailWord_711706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6489512589904546638210743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17305366906412124368561981 6489512589904546638210743)
  ·
    refine ⟨9734268884856819957316115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6489512589904546638210743 9734268884856819957316115)
    ·
      refine ⟨14601403327285229935974173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9734268884856819957316115 14601403327285229935974173)
      ·
        refine ⟨5475526247731961225990315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14601403327285229935974173 5475526247731961225990315)
        ·
          refine ⟨8213289371597941838985473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5475526247731961225990315 8213289371597941838985473)
          ·
            refine ⟨6159967028698456379239105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8213289371597941838985473 6159967028698456379239105)
            ·
              refine ⟨4619975271523842284429329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6159967028698456379239105 4619975271523842284429329)
              ·
                refine ⟨3464981453642881713321997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4619975271523842284429329 3464981453642881713321997)
                ·
                  refine ⟨1299368045116080642495749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3464981453642881713321997 1299368045116080642495749)
                  ·
                    refine ⟨243631508459265120467953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1299368045116080642495749 243631508459265120467953)
                    ·
                      rfl

theorem cell22_711706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_711706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711706 prefixEnd_711706 := by exact prefixLift 711706
  have htrace : WordTrace (prefixWord ++ tailWord_711706) baseStart_711706 baseEnd_711706 := by
    simpa [prefixWord, tailWord_711706, baseEnd_711706] using wordTrace_append hprefix tailTrace_711706
  have hstable : (prefixWord ++ tailWord_711706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711706).length < 2 ^ (prefixWord ++ tailWord_711706).sum := by decide
  have hdescent : baseEnd_711706 < baseStart_711706 := by decide
  rcases family_descends (prefixWord ++ tailWord_711706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711736 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_711736 : Nat := 118140960795 + 711736 * 2 ^ 59
def prefixEnd_711736 : Nat := 4983230072969 + 3 ^ 40 * 711736 * 2
def baseEnd_711736 : Nat := 243641778072355042217861

theorem tailTrace_711736 : CollatzResearch.WordTrace tailWord_711736 prefixEnd_711736 243641778072355042217861 := by
  unfold tailWord_711736
  simp only [CollatzResearch.WordTrace]
  refine ⟨12979572274754750838217531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17306096366339667784290041 12979572274754750838217531)
  ·
    refine ⟨19469358412132126257326297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12979572274754750838217531 19469358412132126257326297)
    ·
      refine ⟨14602018809099094692994723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19469358412132126257326297 14602018809099094692994723)
      ·
        refine ⟨21903028213648642039492085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14602018809099094692994723 21903028213648642039492085)
        ·
          refine ⟨2053408895029560191202383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21903028213648642039492085 2053408895029560191202383)
          ·
            refine ⟨3080113342544340286803575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2053408895029560191202383 3080113342544340286803575)
            ·
              refine ⟨4620170013816510430205363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3080113342544340286803575 4620170013816510430205363)
              ·
                refine ⟨6930255020724765645308045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4620170013816510430205363 6930255020724765645308045)
                ·
                  refine ⟨2598845632771787116990517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6930255020724765645308045 2598845632771787116990517)
                  ·
                    refine ⟨243641778072355042217861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2598845632771787116990517 243641778072355042217861)
                    ·
                      rfl

theorem cell22_711736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_711736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711736 prefixEnd_711736 := by exact prefixLift 711736
  have htrace : WordTrace (prefixWord ++ tailWord_711736) baseStart_711736 baseEnd_711736 := by
    simpa [prefixWord, tailWord_711736, baseEnd_711736] using wordTrace_append hprefix tailTrace_711736
  have hstable : (prefixWord ++ tailWord_711736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711736).length < 2 ^ (prefixWord ++ tailWord_711736).sum := by decide
  have hdescent : baseEnd_711736 < baseStart_711736 := by decide
  rcases family_descends (prefixWord ++ tailWord_711736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711740 : List Nat := [2, 2, 2, 2, 2, 3, 3, 1, 1, 4]
def baseStart_711740 : Nat := 118140960795 + 711740 * 2 ^ 59
def prefixEnd_711740 : Nat := 4983230072969 + 3 ^ 40 * 711740 * 2
def baseEnd_711740 : Nat := 243643147354100365117849

theorem tailTrace_711740 : CollatzResearch.WordTrace tailWord_711740 prefixEnd_711740 243643147354100365117849 := by
  unfold tailWord_711740
  simp only [CollatzResearch.WordTrace]
  refine ⟨12979645220747505179790337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17306193627663340239720449 12979645220747505179790337)
  ·
    refine ⟨9734733915560628884842753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12979645220747505179790337 9734733915560628884842753)
    ·
      refine ⟨7301050436670471663632065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9734733915560628884842753 7301050436670471663632065)
      ·
        refine ⟨5475787827502853747724049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7301050436670471663632065 5475787827502853747724049)
        ·
          refine ⟨4106840870627140310793037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5475787827502853747724049 4106840870627140310793037)
          ·
            refine ⟨1540065326485177616547389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4106840870627140310793037 1540065326485177616547389)
            ·
              refine ⟨577524497431941606205271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1540065326485177616547389 577524497431941606205271)
              ·
                refine ⟨866286746147912409307907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577524497431941606205271 866286746147912409307907)
                ·
                  refine ⟨1299430119221868613961861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866286746147912409307907 1299430119221868613961861)
                  ·
                    refine ⟨243643147354100365117849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1299430119221868613961861 243643147354100365117849)
                    ·
                      rfl

theorem cell22_711740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_711740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711740 prefixEnd_711740 := by exact prefixLift 711740
  have htrace : WordTrace (prefixWord ++ tailWord_711740) baseStart_711740 baseEnd_711740 := by
    simpa [prefixWord, tailWord_711740, baseEnd_711740] using wordTrace_append hprefix tailTrace_711740
  have hstable : (prefixWord ++ tailWord_711740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711740).length < 2 ^ (prefixWord ++ tailWord_711740).sum := by decide
  have hdescent : baseEnd_711740 < baseStart_711740 := by decide
  rcases family_descends (prefixWord ++ tailWord_711740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711783 : List Nat := [1, 1, 5, 1, 1, 4, 3, 6]
def baseStart_711783 : Nat := 118140960795 + 711783 * 2 ^ 59
def prefixEnd_711783 : Nat := 4983230072969 + 3 ^ 40 * 711783 * 2
def baseEnd_711783 : Nat := 27073096348095842921413

theorem tailTrace_711783 : CollatzResearch.WordTrace tailWord_711783 prefixEnd_711783 27073096348095842921413 := by
  unfold tailWord_711783
  simp only [CollatzResearch.WordTrace]
  refine ⟨25960858780339228703396003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17307239186892819135597335 25960858780339228703396003)
  ·
    refine ⟨38941288170508843055094005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25960858780339228703396003 38941288170508843055094005)
    ·
      refine ⟨3650745765985204036415063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38941288170508843055094005 3650745765985204036415063)
      ·
        refine ⟨5476118648977806054622595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3650745765985204036415063 5476118648977806054622595)
        ·
          refine ⟨8214177973466709081933893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5476118648977806054622595 8214177973466709081933893)
          ·
            refine ⟨1540158370025007952862605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8214177973466709081933893 1540158370025007952862605)
            ·
              refine ⟨577559388759377982323477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1540158370025007952862605 577559388759377982323477)
              ·
                refine ⟨27073096348095842921413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 577559388759377982323477 27073096348095842921413)
                ·
                  rfl

theorem cell22_711783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 6].length) (baseStart_711783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711783 prefixEnd_711783 := by exact prefixLift 711783
  have htrace : WordTrace (prefixWord ++ tailWord_711783) baseStart_711783 baseEnd_711783 := by
    simpa [prefixWord, tailWord_711783, baseEnd_711783] using wordTrace_append hprefix tailTrace_711783
  have hstable : (prefixWord ++ tailWord_711783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711783).length < 2 ^ (prefixWord ++ tailWord_711783).sum := by decide
  have hdescent : baseEnd_711783 < baseStart_711783 := by decide
  rcases family_descends (prefixWord ++ tailWord_711783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711811 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 7]
def baseStart_711811 : Nat := 118140960795 + 711811 * 2 ^ 59
def prefixEnd_711811 : Nat := 4983230072969 + 3 ^ 40 * 711811 * 2
def baseEnd_711811 : Nat := 81222484035026615530877

theorem tailTrace_711811 : CollatzResearch.WordTrace tailWord_711811 prefixEnd_711811 81222484035026615530877 := by
  unfold tailWord_711811
  simp only [CollatzResearch.WordTrace]
  refine ⟨25961880024237789485415287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17307920016158526323610191 25961880024237789485415287)
  ·
    refine ⟨38942820036356684228122931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25961880024237789485415287 38942820036356684228122931)
    ·
      refine ⟨58414230054535026342184397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38942820036356684228122931 58414230054535026342184397)
      ·
        refine ⟨21905336270450634878319149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58414230054535026342184397 21905336270450634878319149)
        ·
          refine ⟨8214501101418988079369681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21905336270450634878319149 8214501101418988079369681)
          ·
            refine ⟨6160875826064241059527261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8214501101418988079369681 6160875826064241059527261)
            ·
              refine ⟨2310328434774090397322723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6160875826064241059527261 2310328434774090397322723)
              ·
                refine ⟨3465492652161135595984085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310328434774090397322723 3465492652161135595984085)
                ·
                  refine ⟨81222484035026615530877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3465492652161135595984085 81222484035026615530877)
                  ·
                    rfl

theorem cell22_711811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 7].length) (baseStart_711811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711811 prefixEnd_711811 := by exact prefixLift 711811
  have htrace : WordTrace (prefixWord ++ tailWord_711811) baseStart_711811 baseEnd_711811 := by
    simpa [prefixWord, tailWord_711811, baseEnd_711811] using wordTrace_append hprefix tailTrace_711811
  have hstable : (prefixWord ++ tailWord_711811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711811).length < 2 ^ (prefixWord ++ tailWord_711811).sum := by decide
  have hdescent : baseEnd_711811 < baseStart_711811 := by decide
  rcases family_descends (prefixWord ++ tailWord_711811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711892 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_711892 : Nat := 118140960795 + 711892 * 2 ^ 59
def prefixEnd_711892 : Nat := 4983230072969 + 3 ^ 40 * 711892 * 2
def baseEnd_711892 : Nat := 243695180060422635317383

theorem tailTrace_711892 : CollatzResearch.WordTrace tailWord_711892 prefixEnd_711892 243695180060422635317383 := by
  unfold tailWord_711892
  simp only [CollatzResearch.WordTrace]
  refine ⟨12982417168472170159556965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17309889557962893546075953 12982417168472170159556965)
  ·
    refine ⟨2434203219088531904916931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12982417168472170159556965 2434203219088531904916931)
    ·
      refine ⟨3651304828632797857375397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2434203219088531904916931 3651304828632797857375397)
      ·
        refine ⟨684619655368649598257887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3651304828632797857375397 684619655368649598257887)
        ·
          refine ⟨1026929483052974397386831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 684619655368649598257887 1026929483052974397386831)
          ·
            refine ⟨1540394224579461596080247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026929483052974397386831 1540394224579461596080247)
            ·
              refine ⟨2310591336869192394120371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540394224579461596080247 2310591336869192394120371)
              ·
                refine ⟨3465887005303788591180557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2310591336869192394120371 3465887005303788591180557)
                ·
                  refine ⟨1299707626988920721692709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3465887005303788591180557 1299707626988920721692709)
                  ·
                    refine ⟨243695180060422635317383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1299707626988920721692709 243695180060422635317383)
                    ·
                      rfl

theorem cell22_711892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_711892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711892 prefixEnd_711892 := by exact prefixLift 711892
  have htrace : WordTrace (prefixWord ++ tailWord_711892) baseStart_711892 baseEnd_711892 := by
    simpa [prefixWord, tailWord_711892, baseEnd_711892] using wordTrace_append hprefix tailTrace_711892
  have hstable : (prefixWord ++ tailWord_711892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711892).length < 2 ^ (prefixWord ++ tailWord_711892).sum := by decide
  have hdescent : baseEnd_711892 < baseStart_711892 := by decide
  rcases family_descends (prefixWord ++ tailWord_711892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711903 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 2, 4]
def baseStart_711903 : Nat := 118140960795 + 711903 * 2 ^ 59
def prefixEnd_711903 : Nat := 4983230072969 + 3 ^ 40 * 711903 * 2
def baseEnd_711903 : Nat := 243698945585222273292349

theorem tailTrace_711903 : CollatzResearch.WordTrace tailWord_711903 prefixEnd_711903 243698945585222273292349 := by
  unfold tailWord_711903
  simp only [CollatzResearch.WordTrace]
  refine ⟨25965235539904489197764363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17310157026602992798509575 25965235539904489197764363)
  ·
    refine ⟨38947853309856733796646545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25965235539904489197764363 38947853309856733796646545)
    ·
      refine ⟨29210889982392550347484909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38947853309856733796646545 29210889982392550347484909)
      ·
        refine ⟨10954083743397206380306841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29210889982392550347484909 10954083743397206380306841)
        ·
          refine ⟨8215562807547904785230131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10954083743397206380306841 8215562807547904785230131)
          ·
            refine ⟨12323344211321857177845197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8215562807547904785230131 12323344211321857177845197)
            ·
              refine ⟨4621254079245696441691949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12323344211321857177845197 4621254079245696441691949)
              ·
                refine ⟨1732970279717136165634481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4621254079245696441691949 1732970279717136165634481)
                ·
                  refine ⟨1299727709787852124225861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1732970279717136165634481 1299727709787852124225861)
                  ·
                    refine ⟨243698945585222273292349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1299727709787852124225861 243698945585222273292349)
                    ·
                      rfl

theorem cell22_711903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_711903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711903 prefixEnd_711903 := by exact prefixLift 711903
  have htrace : WordTrace (prefixWord ++ tailWord_711903) baseStart_711903 baseEnd_711903 := by
    simpa [prefixWord, tailWord_711903, baseEnd_711903] using wordTrace_append hprefix tailTrace_711903
  have hstable : (prefixWord ++ tailWord_711903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711903).length < 2 ^ (prefixWord ++ tailWord_711903).sum := by decide
  have hdescent : baseEnd_711903 < baseStart_711903 := by decide
  rcases family_descends (prefixWord ++ tailWord_711903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_711950 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 5, 3]
def baseStart_711950 : Nat := 118140960795 + 711950 * 2 ^ 59
def prefixEnd_711950 : Nat := 4983230072969 + 3 ^ 40 * 711950 * 2
def baseEnd_711950 : Nat := 243715034645729817367205

theorem tailTrace_711950 : CollatzResearch.WordTrace tailWord_711950 prefixEnd_711950 243715034645729817367205 := by
  unfold tailWord_711950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3245868721341777028090663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17311299847156144149816869 3245868721341777028090663)
  ·
    refine ⟨4868803082012665542135995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3245868721341777028090663 4868803082012665542135995)
    ·
      refine ⟨7303204623018998313203993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4868803082012665542135995 7303204623018998313203993)
      ·
        refine ⟨5477403467264248734902995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7303204623018998313203993 5477403467264248734902995)
        ·
          refine ⟨8216105200896373102354493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5477403467264248734902995 8216105200896373102354493)
          ·
            refine ⟨3081039450336139913382935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8216105200896373102354493 3081039450336139913382935)
            ·
              refine ⟨4621559175504209870074403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3081039450336139913382935 4621559175504209870074403)
              ·
                refine ⟨6932338763256314805111605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4621559175504209870074403 6932338763256314805111605)
                ·
                  refine ⟨649906759055279512979213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6932338763256314805111605 649906759055279512979213)
                  ·
                    refine ⟨243715034645729817367205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 649906759055279512979213 243715034645729817367205)
                    ·
                      rfl

theorem cell22_711950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_711950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_711950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_711950 prefixEnd_711950 := by exact prefixLift 711950
  have htrace : WordTrace (prefixWord ++ tailWord_711950) baseStart_711950 baseEnd_711950 := by
    simpa [prefixWord, tailWord_711950, baseEnd_711950] using wordTrace_append hprefix tailTrace_711950
  have hstable : (prefixWord ++ tailWord_711950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_711950).length < 2 ^ (prefixWord ++ tailWord_711950).sum := by decide
  have hdescent : baseEnd_711950 < baseStart_711950 := by decide
  rcases family_descends (prefixWord ++ tailWord_711950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712072 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 2, 4]
def baseStart_712072 : Nat := 118140960795 + 712072 * 2 ^ 59
def prefixEnd_712072 : Nat := 4983230072969 + 3 ^ 40 * 712072 * 2
def baseEnd_712072 : Nat := 243756797738962165816831

theorem tailTrace_712072 : CollatzResearch.WordTrace tailWord_712072 prefixEnd_712072 243756797738962165816831 := by
  unfold tailWord_712072
  simp only [CollatzResearch.WordTrace]
  refine ⟨12985699738146115530333235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17314266317528154040444313 12985699738146115530333235)
  ·
    refine ⟨19478549607219173295499853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12985699738146115530333235 19478549607219173295499853)
    ·
      refine ⟨7304456102707189985812445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19478549607219173295499853 7304456102707189985812445)
      ·
        refine ⟨2739171038515196244679667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7304456102707189985812445 2739171038515196244679667)
        ·
          refine ⟨4108756557772794367019501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739171038515196244679667 4108756557772794367019501)
          ·
            refine ⟨1540783709164797887632313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4108756557772794367019501 1540783709164797887632313)
            ·
              refine ⟨1155587781873598415724235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1540783709164797887632313 1155587781873598415724235)
              ·
                refine ⟨1733381672810397623586353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1155587781873598415724235 1733381672810397623586353)
                ·
                  refine ⟨1300036254607798217689765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1733381672810397623586353 1300036254607798217689765)
                  ·
                    refine ⟨243756797738962165816831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1300036254607798217689765 243756797738962165816831)
                    ·
                      rfl

theorem cell22_712072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_712072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712072 prefixEnd_712072 := by exact prefixLift 712072
  have htrace : WordTrace (prefixWord ++ tailWord_712072) baseStart_712072 baseEnd_712072 := by
    simpa [prefixWord, tailWord_712072, baseEnd_712072] using wordTrace_append hprefix tailTrace_712072
  have hstable : (prefixWord ++ tailWord_712072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712072).length < 2 ^ (prefixWord ++ tailWord_712072).sum := by decide
  have hdescent : baseEnd_712072 < baseStart_712072 := by decide
  rcases family_descends (prefixWord ++ tailWord_712072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712083 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 6, 6]
def baseStart_712083 : Nat := 118140960795 + 712083 * 2 ^ 59
def prefixEnd_712083 : Nat := 4983230072969 + 3 ^ 40 * 712083 * 2
def baseEnd_712083 : Nat := 243760563263761803791797

theorem tailTrace_712083 : CollatzResearch.WordTrace tailWord_712083 prefixEnd_712083 243760563263761803791797 := by
  unfold tailWord_712083
  simp only [CollatzResearch.WordTrace]
  refine ⟨25971800679252379939316903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17314533786168253292877935 25971800679252379939316903)
  ·
    refine ⟨38957701018878569908975355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25971800679252379939316903 38957701018878569908975355)
    ·
      refine ⟨58436551528317854863463033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38957701018878569908975355 58436551528317854863463033)
      ·
        refine ⟨43827413646238391147597275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58436551528317854863463033 43827413646238391147597275)
        ·
          refine ⟨65741120469357586721395913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43827413646238391147597275 65741120469357586721395913)
          ·
            refine ⟨49305840352018190041046935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65741120469357586721395913 49305840352018190041046935)
            ·
              refine ⟨73958760528027285061570403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49305840352018190041046935 73958760528027285061570403)
              ·
                refine ⟨110938140792040927592355605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73958760528027285061570403 110938140792040927592355605)
                ·
                  refine ⟨5200225349626918480891669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110938140792040927592355605 5200225349626918480891669)
                  ·
                    refine ⟨243760563263761803791797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5200225349626918480891669 243760563263761803791797)
                    ·
                      rfl

theorem cell22_712083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 6].length) (baseStart_712083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712083 prefixEnd_712083 := by exact prefixLift 712083
  have htrace : WordTrace (prefixWord ++ tailWord_712083) baseStart_712083 baseEnd_712083 := by
    simpa [prefixWord, tailWord_712083, baseEnd_712083] using wordTrace_append hprefix tailTrace_712083
  have hstable : (prefixWord ++ tailWord_712083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712083).length < 2 ^ (prefixWord ++ tailWord_712083).sum := by decide
  have hdescent : baseEnd_712083 < baseStart_712083 := by decide
  rcases family_descends (prefixWord ++ tailWord_712083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712104 : List Nat := [2, 1, 6, 1, 2, 2, 1, 7]
def baseStart_712104 : Nat := 118140960795 + 712104 * 2 ^ 59
def prefixEnd_712104 : Nat := 4983230072969 + 3 ^ 40 * 712104 * 2
def baseEnd_712104 : Nat := 27085305776991638779637

theorem tailTrace_712104 : CollatzResearch.WordTrace tailWord_712104 prefixEnd_712104 27085305776991638779637 := by
  unfold tailWord_712104
  simp only [CollatzResearch.WordTrace]
  refine ⟨12986283306088150262915683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17315044408117533683887577 12986283306088150262915683)
  ·
    refine ⟨19479424959132225394373525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12986283306088150262915683 19479424959132225394373525)
    ·
      refine ⟨913098044959323065361259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19479424959132225394373525 913098044959323065361259)
      ·
        refine ⟨1369647067438984598041889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913098044959323065361259 1369647067438984598041889)
        ·
          refine ⟨1027235300579238448531417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1369647067438984598041889 1027235300579238448531417)
          ·
            refine ⟨770426475434428836398563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027235300579238448531417 770426475434428836398563)
            ·
              refine ⟨1155639713151643254597845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770426475434428836398563 1155639713151643254597845)
              ·
                refine ⟨27085305776991638779637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1155639713151643254597845 27085305776991638779637)
                ·
                  rfl

theorem cell22_712104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 7].length) (baseStart_712104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712104 prefixEnd_712104 := by exact prefixLift 712104
  have htrace : WordTrace (prefixWord ++ tailWord_712104) baseStart_712104 baseEnd_712104 := by
    simpa [prefixWord, tailWord_712104, baseEnd_712104] using wordTrace_append hprefix tailTrace_712104
  have hstable : (prefixWord ++ tailWord_712104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712104).length < 2 ^ (prefixWord ++ tailWord_712104).sum := by decide
  have hdescent : baseEnd_712104 < baseStart_712104 := by decide
  rcases family_descends (prefixWord ++ tailWord_712104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712226 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_712226 : Nat := 118140960795 + 712226 * 2 ^ 59
def prefixEnd_712226 : Nat := 4983230072969 + 3 ^ 40 * 712226 * 2
def baseEnd_712226 : Nat := 243809515086157097466359

theorem tailTrace_712226 : CollatzResearch.WordTrace tailWord_712226 prefixEnd_712226 243809515086157097466359 := by
  unfold tailWord_712226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6494254079433578840443133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17318010878489543574515021 6494254079433578840443133)
  ·
    refine ⟨2435345279787592065166175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6494254079433578840443133 2435345279787592065166175)
    ·
      refine ⟨3653017919681388097749263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2435345279787592065166175 3653017919681388097749263)
      ·
        refine ⟨5479526879522082146623895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3653017919681388097749263 5479526879522082146623895)
        ·
          refine ⟨8219290319283123219935843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5479526879522082146623895 8219290319283123219935843)
          ·
            refine ⟨12328935478924684829903765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8219290319283123219935843 12328935478924684829903765)
            ·
              refine ⟨577918850574594601401739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12328935478924684829903765 577918850574594601401739)
              ·
                refine ⟨866878275861891902102609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577918850574594601401739 866878275861891902102609)
                ·
                  refine ⟨650158706896418926576957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 866878275861891902102609 650158706896418926576957)
                  ·
                    refine ⟨243809515086157097466359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 650158706896418926576957 243809515086157097466359)
                    ·
                      rfl

theorem cell22_712226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_712226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712226 prefixEnd_712226 := by exact prefixLift 712226
  have htrace : WordTrace (prefixWord ++ tailWord_712226) baseStart_712226 baseEnd_712226 := by
    simpa [prefixWord, tailWord_712226, baseEnd_712226] using wordTrace_append hprefix tailTrace_712226
  have hstable : (prefixWord ++ tailWord_712226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712226).length < 2 ^ (prefixWord ++ tailWord_712226).sum := by decide
  have hdescent : baseEnd_712226 < baseStart_712226 := by decide
  rcases family_descends (prefixWord ++ tailWord_712226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712262 : List Nat := [6, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_712262 : Nat := 118140960795 + 712262 * 2 ^ 59
def prefixEnd_712262 : Nat := 4983230072969 + 3 ^ 40 * 712262 * 2
def baseEnd_712262 : Nat := 81273946207288334522083

theorem tailTrace_712262 : CollatzResearch.WordTrace tailWord_712262 prefixEnd_712262 81273946207288334522083 := by
  unfold tailWord_712262
  simp only [CollatzResearch.WordTrace]
  refine ⟨811822792050121672190095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17318886230402595673388693 811822792050121672190095)
  ·
    refine ⟨1217734188075182508285143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 811822792050121672190095 1217734188075182508285143)
    ·
      refine ⟨1826601282112773762427715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1217734188075182508285143 1826601282112773762427715)
      ·
        refine ⟨2739901923169160643641573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826601282112773762427715 2739901923169160643641573)
        ·
          refine ⟨513731610594217620682795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2739901923169160643641573 513731610594217620682795)
          ·
            refine ⟨770597415891326431024193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513731610594217620682795 770597415891326431024193)
            ·
              refine ⟨577948061918494823268145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770597415891326431024193 577948061918494823268145)
              ·
                refine ⟨433461046438871117451109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577948061918494823268145 433461046438871117451109)
                ·
                  refine ⟨81273946207288334522083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 433461046438871117451109 81273946207288334522083)
                  ·
                    rfl

theorem cell22_712262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_712262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712262 prefixEnd_712262 := by exact prefixLift 712262
  have htrace : WordTrace (prefixWord ++ tailWord_712262) baseStart_712262 baseEnd_712262 := by
    simpa [prefixWord, tailWord_712262, baseEnd_712262] using wordTrace_append hprefix tailTrace_712262
  have hstable : (prefixWord ++ tailWord_712262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712262).length < 2 ^ (prefixWord ++ tailWord_712262).sum := by decide
  have hdescent : baseEnd_712262 < baseStart_712262 := by decide
  rcases family_descends (prefixWord ++ tailWord_712262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712265 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_712265 : Nat := 118140960795 + 712265 * 2 ^ 59
def prefixEnd_712265 : Nat := 4983230072969 + 3 ^ 40 * 712265 * 2
def baseEnd_712265 : Nat := 243822865583173995741239

theorem tailTrace_712265 : CollatzResearch.WordTrace tailWord_712265 prefixEnd_712265 243822865583173995741239 := by
  unfold tailWord_712265
  simp only [CollatzResearch.WordTrace]
  refine ⟨25978438764593025022442249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17318959176395350014961499 25978438764593025022442249)
  ·
    refine ⟨19483829073444768766831687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25978438764593025022442249 19483829073444768766831687)
    ·
      refine ⟨29225743610167153150247531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19483829073444768766831687 29225743610167153150247531)
      ·
        refine ⟨43838615415250729725371297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29225743610167153150247531 43838615415250729725371297)
        ·
          refine ⟨32878961561438047294028473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43838615415250729725371297 32878961561438047294028473)
          ·
            refine ⟨24659221171078535470521355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32878961561438047294028473 24659221171078535470521355)
            ·
              refine ⟨36988831756617803205782033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24659221171078535470521355 36988831756617803205782033)
              ·
                refine ⟨27741623817463352404336525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36988831756617803205782033 27741623817463352404336525)
                ·
                  refine ⟨10403108931548757151626197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27741623817463352404336525 10403108931548757151626197)
                  ·
                    refine ⟨243822865583173995741239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10403108931548757151626197 243822865583173995741239)
                    ·
                      rfl

theorem cell22_712265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_712265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712265 prefixEnd_712265 := by exact prefixLift 712265
  have htrace : WordTrace (prefixWord ++ tailWord_712265) baseStart_712265 baseEnd_712265 := by
    simpa [prefixWord, tailWord_712265, baseEnd_712265] using wordTrace_append hprefix tailTrace_712265
  have hstable : (prefixWord ++ tailWord_712265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712265).length < 2 ^ (prefixWord ++ tailWord_712265).sum := by decide
  have hdescent : baseEnd_712265 < baseStart_712265 := by decide
  rcases family_descends (prefixWord ++ tailWord_712265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712284 : List Nat := [2, 2, 4, 1, 2, 1, 2, 3, 5]
def baseStart_712284 : Nat := 118140960795 + 712284 * 2 ^ 59
def prefixEnd_712284 : Nat := 4983230072969 + 3 ^ 40 * 712284 * 2
def baseEnd_712284 : Nat := 81276456557154759838727

theorem tailTrace_712284 : CollatzResearch.WordTrace tailWord_712284 prefixEnd_712284 81276456557154759838727 := by
  unfold tailWord_712284
  simp only [CollatzResearch.WordTrace]
  refine ⟨12989565875762095633691953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17319421167682794178255937 12989565875762095633691953)
  ·
    refine ⟨9742174406821571725268965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12989565875762095633691953 9742174406821571725268965)
    ·
      refine ⟨1826657701279044698487931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9742174406821571725268965 1826657701279044698487931)
      ·
        refine ⟨2739986551918567047731897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1826657701279044698487931 2739986551918567047731897)
        ·
          refine ⟨2054989913938925285798923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2739986551918567047731897 2054989913938925285798923)
          ·
            refine ⟨3082484870908387928698385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2054989913938925285798923 3082484870908387928698385)
            ·
              refine ⟨2311863653181290946523789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3082484870908387928698385 2311863653181290946523789)
              ·
                refine ⟨866948869942984104946421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2311863653181290946523789 866948869942984104946421)
                ·
                  refine ⟨81276456557154759838727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 866948869942984104946421 81276456557154759838727)
                  ·
                    rfl

theorem cell22_712284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_712284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712284 prefixEnd_712284 := by exact prefixLift 712284
  have htrace : WordTrace (prefixWord ++ tailWord_712284) baseStart_712284 baseEnd_712284 := by
    simpa [prefixWord, tailWord_712284, baseEnd_712284] using wordTrace_append hprefix tailTrace_712284
  have hstable : (prefixWord ++ tailWord_712284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712284).length < 2 ^ (prefixWord ++ tailWord_712284).sum := by decide
  have hdescent : baseEnd_712284 < baseStart_712284 := by decide
  rcases family_descends (prefixWord ++ tailWord_712284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712297 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_712297 : Nat := 118140960795 + 712297 * 2 ^ 59
def prefixEnd_712297 : Nat := 4983230072969 + 3 ^ 40 * 712297 * 2
def baseEnd_712297 : Nat := 243833819837136578941141

theorem tailTrace_712297 : CollatzResearch.WordTrace tailWord_712297 prefixEnd_712297 243833819837136578941141 := by
  unfold tailWord_712297
  simp only [CollatzResearch.WordTrace]
  refine ⟨25979605900477094487607145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17319737266984729658404763 25979605900477094487607145)
  ·
    refine ⟨19484704425357820865705359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25979605900477094487607145 19484704425357820865705359)
    ·
      refine ⟨29227056638036731298558039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19484704425357820865705359 29227056638036731298558039)
      ·
        refine ⟨43840584957055096947837059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29227056638036731298558039 43840584957055096947837059)
        ·
          refine ⟨65760877435582645421755589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43840584957055096947837059 65760877435582645421755589)
          ·
            refine ⟨12330164519171746016579173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65760877435582645421755589 12330164519171746016579173)
            ·
              refine ⟨2311905847344702378108595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12330164519171746016579173 2311905847344702378108595)
              ·
                refine ⟨3467858771017053567162893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2311905847344702378108595 3467858771017053567162893)
                ·
                  refine ⟨1300447039131395087686085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3467858771017053567162893 1300447039131395087686085)
                  ·
                    refine ⟨243833819837136578941141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1300447039131395087686085 243833819837136578941141)
                    ·
                      rfl

theorem cell22_712297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_712297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712297 prefixEnd_712297 := by exact prefixLift 712297
  have htrace : WordTrace (prefixWord ++ tailWord_712297) baseStart_712297 baseEnd_712297 := by
    simpa [prefixWord, tailWord_712297, baseEnd_712297] using wordTrace_append hprefix tailTrace_712297
  have hstable : (prefixWord ++ tailWord_712297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712297).length < 2 ^ (prefixWord ++ tailWord_712297).sum := by decide
  have hdescent : baseEnd_712297 < baseStart_712297 := by decide
  rcases family_descends (prefixWord ++ tailWord_712297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712329 : List Nat := [1, 2, 1, 1, 4, 1, 4, 4, 4]
def baseStart_712329 : Nat := 118140960795 + 712329 * 2 ^ 59
def prefixEnd_712329 : Nat := 4983230072969 + 3 ^ 40 * 712329 * 2
def baseEnd_712329 : Nat := 81281591363699720713681

theorem tailTrace_712329 : CollatzResearch.WordTrace tailWord_712329 prefixEnd_712329 81281591363699720713681 := by
  unfold tailWord_712329
  simp only [CollatzResearch.WordTrace]
  refine ⟨25980773036361163952772041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17320515357574109301848027 25980773036361163952772041)
  ·
    refine ⟨19485579777270872964579031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25980773036361163952772041 19485579777270872964579031)
    ·
      refine ⟨29228369665906309446868547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19485579777270872964579031 29228369665906309446868547)
      ·
        refine ⟨43842554498859464170302821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29228369665906309446868547 43842554498859464170302821)
        ·
          refine ⟨8220478968536149531931779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43842554498859464170302821 8220478968536149531931779)
          ·
            refine ⟨12330718452804224297897669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8220478968536149531931779 12330718452804224297897669)
            ·
              refine ⟨2312009709900792055855813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12330718452804224297897669 2312009709900792055855813)
              ·
                refine ⟨433501820606398510472965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2312009709900792055855813 433501820606398510472965)
                ·
                  refine ⟨81281591363699720713681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 433501820606398510472965 81281591363699720713681)
                  ·
                    rfl

theorem cell22_712329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 4].length) (baseStart_712329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712329 prefixEnd_712329 := by exact prefixLift 712329
  have htrace : WordTrace (prefixWord ++ tailWord_712329) baseStart_712329 baseEnd_712329 := by
    simpa [prefixWord, tailWord_712329, baseEnd_712329] using wordTrace_append hprefix tailTrace_712329
  have hstable : (prefixWord ++ tailWord_712329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712329).length < 2 ^ (prefixWord ++ tailWord_712329).sum := by decide
  have hdescent : baseEnd_712329 < baseStart_712329 := by decide
  rcases family_descends (prefixWord ++ tailWord_712329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712344 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 1, 5]
def baseStart_712344 : Nat := 118140960795 + 712344 * 2 ^ 59
def prefixEnd_712344 : Nat := 4983230072969 + 3 ^ 40 * 712344 * 2
def baseEnd_712344 : Nat := 243849908897644123015997

theorem tailTrace_712344 : CollatzResearch.WordTrace tailWord_712344 prefixEnd_712344 243849908897644123015997 := by
  unfold tailWord_712344
  simp only [CollatzResearch.WordTrace]
  refine ⟨12990660065653410757284043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17320880087537881009712057 12990660065653410757284043)
  ·
    refine ⟨19485990098480116135926065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12990660065653410757284043 19485990098480116135926065)
    ·
      refine ⟨14614492573860087101944549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19485990098480116135926065 14614492573860087101944549)
      ·
        refine ⟨2740217357598766331614603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14614492573860087101944549 2740217357598766331614603)
        ·
          refine ⟨4110326036398149497421905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2740217357598766331614603 4110326036398149497421905)
          ·
            refine ⟨3082744527298612123066429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4110326036398149497421905 3082744527298612123066429)
            ·
              refine ⟨1156029197736979546149911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3082744527298612123066429 1156029197736979546149911)
              ·
                refine ⟨1734043796605469319224867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156029197736979546149911 1734043796605469319224867)
                ·
                  refine ⟨2601065694908203978837301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734043796605469319224867 2601065694908203978837301)
                  ·
                    refine ⟨243849908897644123015997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2601065694908203978837301 243849908897644123015997)
                    ·
                      rfl

theorem cell22_712344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_712344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712344 prefixEnd_712344 := by exact prefixLift 712344
  have htrace : WordTrace (prefixWord ++ tailWord_712344) baseStart_712344 baseEnd_712344 := by
    simpa [prefixWord, tailWord_712344, baseEnd_712344] using wordTrace_append hprefix tailTrace_712344
  have hstable : (prefixWord ++ tailWord_712344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712344).length < 2 ^ (prefixWord ++ tailWord_712344).sum := by decide
  have hdescent : baseEnd_712344 < baseStart_712344 := by decide
  rcases family_descends (prefixWord ++ tailWord_712344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712434 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 2, 5]
def baseStart_712434 : Nat := 118140960795 + 712434 * 2 ^ 59
def prefixEnd_712434 : Nat := 4983230072969 + 3 ^ 40 * 712434 * 2
def baseEnd_712434 : Nat := 243880717736913888265721

theorem tailTrace_712434 : CollatzResearch.WordTrace tailWord_712434 prefixEnd_712434 243880717736913888265721 := by
  unfold tailWord_712434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6496150675245191721336089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17323068467320511256896237 6496150675245191721336089)
  ·
    refine ⟨4872113006433893791002067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6496150675245191721336089 4872113006433893791002067)
    ·
      refine ⟨7308169509650840686503101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4872113006433893791002067 7308169509650840686503101)
      ·
        refine ⟨2740563566119065257438663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7308169509650840686503101 2740563566119065257438663)
        ·
          refine ⟨4110845349178597886157995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2740563566119065257438663 4110845349178597886157995)
          ·
            refine ⟨6166268023767896829236993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4110845349178597886157995 6166268023767896829236993)
            ·
              refine ⟨4624701017825922621927745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6166268023767896829236993 4624701017825922621927745)
              ·
                refine ⟨3468525763369441966445809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4624701017825922621927745 3468525763369441966445809)
                ·
                  refine ⟨2601394322527081474834357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3468525763369441966445809 2601394322527081474834357)
                  ·
                    refine ⟨243880717736913888265721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2601394322527081474834357 243880717736913888265721)
                    ·
                      rfl

theorem cell22_712434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_712434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712434 prefixEnd_712434 := by exact prefixLift 712434
  have htrace : WordTrace (prefixWord ++ tailWord_712434) baseStart_712434 baseEnd_712434 := by
    simpa [prefixWord, tailWord_712434, baseEnd_712434] using wordTrace_append hprefix tailTrace_712434
  have hstable : (prefixWord ++ tailWord_712434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712434).length < 2 ^ (prefixWord ++ tailWord_712434).sum := by decide
  have hdescent : baseEnd_712434 < baseStart_712434 := by decide
  rcases family_descends (prefixWord ++ tailWord_712434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712449 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_712449 : Nat := 118140960795 + 712449 * 2 ^ 59
def prefixEnd_712449 : Nat := 4983230072969 + 3 ^ 40 * 712449 * 2
def baseEnd_712449 : Nat := 243885852543458849140675

theorem tailTrace_712449 : CollatzResearch.WordTrace tailWord_712449 prefixEnd_712449 243885852543458849140675 := by
  unfold tailWord_712449
  simp only [CollatzResearch.WordTrace]
  refine ⟨25985149795926424447140401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17323433197284282964760267 25985149795926424447140401)
  ·
    refine ⟨19488862346944818335355301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25985149795926424447140401 19488862346944818335355301)
    ·
      refine ⟨3654161690052153437879119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19488862346944818335355301 3654161690052153437879119)
      ·
        refine ⟨5481242535078230156818679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3654161690052153437879119 5481242535078230156818679)
        ·
          refine ⟨8221863802617345235228019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481242535078230156818679 8221863802617345235228019)
          ·
            refine ⟨12332795703926017852842029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8221863802617345235228019 12332795703926017852842029)
            ·
              refine ⟨4624798388972256694815761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12332795703926017852842029 4624798388972256694815761)
              ·
                refine ⟨3468598791729192521111821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4624798388972256694815761 3468598791729192521111821)
                ·
                  refine ⟨1300724546898447195416933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3468598791729192521111821 1300724546898447195416933)
                  ·
                    refine ⟨243885852543458849140675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1300724546898447195416933 243885852543458849140675)
                    ·
                      rfl

theorem cell22_712449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_712449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712449 prefixEnd_712449 := by exact prefixLift 712449
  have htrace : WordTrace (prefixWord ++ tailWord_712449) baseStart_712449 baseEnd_712449 := by
    simpa [prefixWord, tailWord_712449, baseEnd_712449] using wordTrace_append hprefix tailTrace_712449
  have hstable : (prefixWord ++ tailWord_712449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712449).length < 2 ^ (prefixWord ++ tailWord_712449).sum := by decide
  have hdescent : baseEnd_712449 < baseStart_712449 := by decide
  rcases family_descends (prefixWord ++ tailWord_712449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712479 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 1, 5]
def baseStart_712479 : Nat := 118140960795 + 712479 * 2 ^ 59
def prefixEnd_712479 : Nat := 4983230072969 + 3 ^ 40 * 712479 * 2
def baseEnd_712479 : Nat := 243896122156548770890583

theorem tailTrace_712479 : CollatzResearch.WordTrace tailWord_712479 prefixEnd_712479 243896122156548770890583 := by
  unfold tailWord_712479
  simp only [CollatzResearch.WordTrace]
  refine ⟨25986243985817739570732491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17324162657211826380488327 25986243985817739570732491)
  ·
    refine ⟨38979365978726609356098737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25986243985817739570732491 38979365978726609356098737)
    ·
      refine ⟨29234524484044957017074053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38979365978726609356098737 29234524484044957017074053)
      ·
        refine ⟨5481473340758429440701385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29234524484044957017074053 5481473340758429440701385)
        ·
          refine ⟨4111105005568822080526039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5481473340758429440701385 4111105005568822080526039)
          ·
            refine ⟨6166657508353233120789059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4111105005568822080526039 6166657508353233120789059)
            ·
              refine ⟨9249986262529849681183589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6166657508353233120789059 9249986262529849681183589)
              ·
                refine ⟨1734372424224346815221923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9249986262529849681183589 1734372424224346815221923)
                ·
                  refine ⟨2601558636336520222832885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1734372424224346815221923 2601558636336520222832885)
                  ·
                    refine ⟨243896122156548770890583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2601558636336520222832885 243896122156548770890583)
                    ·
                      rfl

theorem cell22_712479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_712479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712479 prefixEnd_712479 := by exact prefixLift 712479
  have htrace : WordTrace (prefixWord ++ tailWord_712479) baseStart_712479 baseEnd_712479 := by
    simpa [prefixWord, tailWord_712479, baseEnd_712479] using wordTrace_append hprefix tailTrace_712479
  have hstable : (prefixWord ++ tailWord_712479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712479).length < 2 ^ (prefixWord ++ tailWord_712479).sum := by decide
  have hdescent : baseEnd_712479 < baseStart_712479 := by decide
  rcases family_descends (prefixWord ++ tailWord_712479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712481 : List Nat := [1, 2, 3, 2, 1, 3, 1, 5, 4]
def baseStart_712481 : Nat := 118140960795 + 712481 * 2 ^ 59
def prefixEnd_712481 : Nat := 4983230072969 + 3 ^ 40 * 712481 * 2
def baseEnd_712481 : Nat := 81298935599140477446859

theorem tailTrace_712481 : CollatzResearch.WordTrace tailWord_712481 prefixEnd_712481 81298935599140477446859 := by
  unfold tailWord_712481
  simp only [CollatzResearch.WordTrace]
  refine ⟨25986316931810493912305297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17324211287873662608203531 25986316931810493912305297)
  ·
    refine ⟨19489737698857870434228973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25986316931810493912305297 19489737698857870434228973)
    ·
      refine ⟨7308651637071701412835865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19489737698857870434228973 7308651637071701412835865)
      ·
        refine ⟨5481488727803776059626899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7308651637071701412835865 5481488727803776059626899)
        ·
          refine ⟨8222233091705664089440349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5481488727803776059626899 8222233091705664089440349)
          ·
            refine ⟨3083337409389624033540131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8222233091705664089440349 3083337409389624033540131)
            ·
              refine ⟨4625006114084436050310197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3083337409389624033540131 4625006114084436050310197)
              ·
                refine ⟨433594323195415879716581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4625006114084436050310197 433594323195415879716581)
                ·
                  refine ⟨81298935599140477446859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 433594323195415879716581 81298935599140477446859)
                  ·
                    rfl

theorem cell22_712481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 4].length) (baseStart_712481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712481 prefixEnd_712481 := by exact prefixLift 712481
  have htrace : WordTrace (prefixWord ++ tailWord_712481) baseStart_712481 baseEnd_712481 := by
    simpa [prefixWord, tailWord_712481, baseEnd_712481] using wordTrace_append hprefix tailTrace_712481
  have hstable : (prefixWord ++ tailWord_712481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712481).length < 2 ^ (prefixWord ++ tailWord_712481).sum := by decide
  have hdescent : baseEnd_712481 < baseStart_712481 := by decide
  rcases family_descends (prefixWord ++ tailWord_712481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712569 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_712569 : Nat := 118140960795 + 712569 * 2 ^ 59
def prefixEnd_712569 : Nat := 4983230072969 + 3 ^ 40 * 712569 * 2
def baseEnd_712569 : Nat := 243926930995818536140307

theorem tailTrace_712569 : CollatzResearch.WordTrace tailWord_712569 prefixEnd_712569 243926930995818536140307 := by
  unfold tailWord_712569
  simp only [CollatzResearch.WordTrace]
  refine ⟨25989526555491684941508761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17326351036994456627672507 25989526555491684941508761)
  ·
    refine ⟨19492144916618763706131571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25989526555491684941508761 19492144916618763706131571)
    ·
      refine ⟨29238217374928145559197357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19492144916618763706131571 29238217374928145559197357)
      ·
        refine ⟨10964331515598054584699009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29238217374928145559197357 10964331515598054584699009)
        ·
          refine ⟨8223248636698540938524257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10964331515598054584699009 8223248636698540938524257)
          ·
            refine ⟨6167436477523905703893193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8223248636698540938524257 6167436477523905703893193)
            ·
              refine ⟨4625577358142929277919895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6167436477523905703893193 4625577358142929277919895)
              ·
                refine ⟨6938366037214393916879843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4625577358142929277919895 6938366037214393916879843)
                ·
                  refine ⟨10407549055821590875319765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6938366037214393916879843 10407549055821590875319765)
                  ·
                    refine ⟨243926930995818536140307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10407549055821590875319765 243926930995818536140307)
                    ·
                      rfl

theorem cell22_712569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_712569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712569 prefixEnd_712569 := by exact prefixLift 712569
  have htrace : WordTrace (prefixWord ++ tailWord_712569) baseStart_712569 baseEnd_712569 := by
    simpa [prefixWord, tailWord_712569, baseEnd_712569] using wordTrace_append hprefix tailTrace_712569
  have hstable : (prefixWord ++ tailWord_712569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712569).length < 2 ^ (prefixWord ++ tailWord_712569).sum := by decide
  have hdescent : baseEnd_712569 < baseStart_712569 := by decide
  rcases family_descends (prefixWord ++ tailWord_712569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712601 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 1, 4]
def baseStart_712601 : Nat := 118140960795 + 712601 * 2 ^ 59
def prefixEnd_712601 : Nat := 4983230072969 + 3 ^ 40 * 712601 * 2
def baseEnd_712601 : Nat := 243937885249781119340209

theorem tailTrace_712601 : CollatzResearch.WordTrace tailWord_712601 prefixEnd_712601 243937885249781119340209 := by
  unfold tailWord_712601
  simp only [CollatzResearch.WordTrace]
  refine ⟨25990693691375754406673657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17327129127583836271115771 25990693691375754406673657)
  ·
    refine ⟨19493020268531815805005243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25990693691375754406673657 19493020268531815805005243)
    ·
      refine ⟨29239530402797723707507865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19493020268531815805005243 29239530402797723707507865)
      ·
        refine ⟨21929647802098292780630899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29239530402797723707507865 21929647802098292780630899)
        ·
          refine ⟨32894471703147439170946349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21929647802098292780630899 32894471703147439170946349)
          ·
            refine ⟨12335426888680289689104881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32894471703147439170946349 12335426888680289689104881)
            ·
              refine ⟨9251570166510217266828661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12335426888680289689104881 9251570166510217266828661)
              ·
                refine ⟨867334703110332868765187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9251570166510217266828661 867334703110332868765187)
                ·
                  refine ⟨1301002054665499303147781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867334703110332868765187 1301002054665499303147781)
                  ·
                    refine ⟨243937885249781119340209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1301002054665499303147781 243937885249781119340209)
                    ·
                      rfl

theorem cell22_712601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_712601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712601 prefixEnd_712601 := by exact prefixLift 712601
  have htrace : WordTrace (prefixWord ++ tailWord_712601) baseStart_712601 baseEnd_712601 := by
    simpa [prefixWord, tailWord_712601, baseEnd_712601] using wordTrace_append hprefix tailTrace_712601
  have hstable : (prefixWord ++ tailWord_712601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712601).length < 2 ^ (prefixWord ++ tailWord_712601).sum := by decide
  have hdescent : baseEnd_712601 < baseStart_712601 := by decide
  rcases family_descends (prefixWord ++ tailWord_712601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712609 : List Nat := [1, 2, 3, 4, 2, 2, 2, 2, 1, 3]
def baseStart_712609 : Nat := 118140960795 + 712609 * 2 ^ 59
def prefixEnd_712609 : Nat := 4983230072969 + 3 ^ 40 * 712609 * 2
def baseEnd_712609 : Nat := 243940623813271765140185

theorem tailTrace_712609 : CollatzResearch.WordTrace tailWord_712609 prefixEnd_712609 243940623813271765140185 := by
  unfold tailWord_712609
  simp only [CollatzResearch.WordTrace]
  refine ⟨25990985475346771772964881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17327323650231181181976587 25990985475346771772964881)
  ·
    refine ⟨19493239106510078829723661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25990985475346771772964881 19493239106510078829723661)
    ·
      refine ⟨7309964664941279561146373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19493239106510078829723661 7309964664941279561146373)
      ·
        refine ⟨1370618374676489917714945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7309964664941279561146373 1370618374676489917714945)
        ·
          refine ⟨1027963781007367438286209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1370618374676489917714945 1027963781007367438286209)
          ·
            refine ⟨770972835755525578714657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027963781007367438286209 770972835755525578714657)
            ·
              refine ⟨578229626816644184035993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770972835755525578714657 578229626816644184035993)
              ·
                refine ⟨433672220112483138026995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578229626816644184035993 433672220112483138026995)
                ·
                  refine ⟨650508330168724707040493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 433672220112483138026995 650508330168724707040493)
                  ·
                    refine ⟨243940623813271765140185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 650508330168724707040493 243940623813271765140185)
                    ·
                      rfl

theorem cell22_712609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_712609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712609 prefixEnd_712609 := by exact prefixLift 712609
  have htrace : WordTrace (prefixWord ++ tailWord_712609) baseStart_712609 baseEnd_712609 := by
    simpa [prefixWord, tailWord_712609, baseEnd_712609] using wordTrace_append hprefix tailTrace_712609
  have hstable : (prefixWord ++ tailWord_712609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712609).length < 2 ^ (prefixWord ++ tailWord_712609).sum := by decide
  have hdescent : baseEnd_712609 < baseStart_712609 := by decide
  rcases family_descends (prefixWord ++ tailWord_712609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712631 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 6, 3]
def baseStart_712631 : Nat := 118140960795 + 712631 * 2 ^ 59
def prefixEnd_712631 : Nat := 4983230072969 + 3 ^ 40 * 712631 * 2
def baseEnd_712631 : Nat := 243948154862871041090117

theorem tailTrace_712631 : CollatzResearch.WordTrace tailWord_712631 prefixEnd_712631 243948154862871041090117 := by
  unfold tailWord_712631
  simp only [CollatzResearch.WordTrace]
  refine ⟨25991787881267069530265747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17327858587511379686843831 25991787881267069530265747)
  ·
    refine ⟨38987681821900604295398621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25991787881267069530265747 38987681821900604295398621)
    ·
      refine ⟨14620380683212726610774483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38987681821900604295398621 14620380683212726610774483)
      ·
        refine ⟨21930571024819089916161725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14620380683212726610774483 21930571024819089916161725)
        ·
          refine ⟨8223964134307158718560647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21930571024819089916161725 8223964134307158718560647)
          ·
            refine ⟨12335946201460738077840971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8223964134307158718560647 12335946201460738077840971)
            ·
              refine ⟨18503919302191107116761457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12335946201460738077840971 18503919302191107116761457)
              ·
                refine ⟨13877939476643330337571093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18503919302191107116761457 13877939476643330337571093)
                ·
                  refine ⟨650528412967656109573645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13877939476643330337571093 650528412967656109573645)
                  ·
                    refine ⟨243948154862871041090117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 650528412967656109573645 243948154862871041090117)
                    ·
                      rfl

theorem cell22_712631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_712631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712631 prefixEnd_712631 := by exact prefixLift 712631
  have htrace : WordTrace (prefixWord ++ tailWord_712631) baseStart_712631 baseEnd_712631 := by
    simpa [prefixWord, tailWord_712631, baseEnd_712631] using wordTrace_append hprefix tailTrace_712631
  have hstable : (prefixWord ++ tailWord_712631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712631).length < 2 ^ (prefixWord ++ tailWord_712631).sum := by decide
  have hdescent : baseEnd_712631 < baseStart_712631 := by decide
  rcases family_descends (prefixWord ++ tailWord_712631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712661 : List Nat := [1, 3, 2, 3, 2, 2, 9]
def baseStart_712661 : Nat := 118140960795 + 712661 * 2 ^ 59
def prefixEnd_712661 : Nat := 4983230072969 + 3 ^ 40 * 712661 * 2
def baseEnd_712661 : Nat := 9035497202813368994075

theorem tailTrace_712661 : CollatzResearch.WordTrace tailWord_712661 prefixEnd_712661 9035497202813368994075 := by
  unfold tailWord_712661
  simp only [CollatzResearch.WordTrace]
  refine ⟨25992882071158384653857837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17328588047438923102571891 25992882071158384653857837)
  ·
    refine ⟨9747330776684394245196689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25992882071158384653857837 9747330776684394245196689)
    ·
      refine ⟨7310498082513295683897517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9747330776684394245196689 7310498082513295683897517)
      ·
        refine ⟨2741436780942485881461569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7310498082513295683897517 2741436780942485881461569)
        ·
          refine ⟨2056077585706864411096177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2741436780942485881461569 2056077585706864411096177)
          ·
            refine ⟨1542058189280148308322133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2056077585706864411096177 1542058189280148308322133)
            ·
              refine ⟨9035497202813368994075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1542058189280148308322133 9035497202813368994075)
              ·
                rfl

theorem cell22_712661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 9].length) (baseStart_712661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712661 prefixEnd_712661 := by exact prefixLift 712661
  have htrace : WordTrace (prefixWord ++ tailWord_712661) baseStart_712661 baseEnd_712661 := by
    simpa [prefixWord, tailWord_712661, baseEnd_712661] using wordTrace_append hprefix tailTrace_712661
  have hstable : (prefixWord ++ tailWord_712661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712661).length < 2 ^ (prefixWord ++ tailWord_712661).sum := by decide
  have hdescent : baseEnd_712661 < baseStart_712661 := by decide
  rcases family_descends (prefixWord ++ tailWord_712661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712727 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 3, 3]
def baseStart_712727 : Nat := 118140960795 + 712727 * 2 ^ 59
def prefixEnd_712727 : Nat := 4983230072969 + 3 ^ 40 * 712727 * 2
def baseEnd_712727 : Nat := 243981017624758790689823

theorem tailTrace_712727 : CollatzResearch.WordTrace tailWord_712727 prefixEnd_712727 243981017624758790689823 := by
  unfold tailWord_712727
  simp only [CollatzResearch.WordTrace]
  refine ⟨25995289288919277925760435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17330192859279518617173623 25995289288919277925760435)
  ·
    refine ⟨38992933933378916888640653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25995289288919277925760435 38992933933378916888640653)
    ·
      refine ⟨14622350225017093833240245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38992933933378916888640653 14622350225017093833240245)
      ·
        refine ⟨1370845333595352546866273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14622350225017093833240245 1370845333595352546866273)
        ·
          refine ⟨1028134000196514410149705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1370845333595352546866273 1028134000196514410149705)
          ·
            refine ⟨771100500147385807612279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028134000196514410149705 771100500147385807612279)
            ·
              refine ⟨1156650750221078711418419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771100500147385807612279 1156650750221078711418419)
              ·
                refine ⟨1734976125331618067127629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156650750221078711418419 1734976125331618067127629)
                ·
                  refine ⟨650616046999356775172861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1734976125331618067127629 650616046999356775172861)
                  ·
                    refine ⟨243981017624758790689823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 650616046999356775172861 243981017624758790689823)
                    ·
                      rfl

theorem cell22_712727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_712727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712727 prefixEnd_712727 := by exact prefixLift 712727
  have htrace : WordTrace (prefixWord ++ tailWord_712727) baseStart_712727 baseEnd_712727 := by
    simpa [prefixWord, tailWord_712727, baseEnd_712727] using wordTrace_append hprefix tailTrace_712727
  have hstable : (prefixWord ++ tailWord_712727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712727).length < 2 ^ (prefixWord ++ tailWord_712727).sum := by decide
  have hdescent : baseEnd_712727 < baseStart_712727 := by decide
  rcases family_descends (prefixWord ++ tailWord_712727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712740 : List Nat := [2, 3, 1, 4, 2, 1, 1, 3, 5]
def baseStart_712740 : Nat := 118140960795 + 712740 * 2 ^ 59
def prefixEnd_712740 : Nat := 4983230072969 + 3 ^ 40 * 712740 * 2
def baseEnd_712740 : Nat := 81328489263477030038261

theorem tailTrace_712740 : CollatzResearch.WordTrace tailWord_712740 prefixEnd_712740 81328489263477030038261 := by
  unfold tailWord_712740
  simp only [CollatzResearch.WordTrace]
  refine ⟨12997881718936090572991837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17330508958581454097322449 12997881718936090572991837)
  ·
    refine ⟨4874205644601033964871939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12997881718936090572991837 4874205644601033964871939)
    ·
      refine ⟨7311308466901550947307909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4874205644601033964871939 7311308466901550947307909)
      ·
        refine ⟨1370870337544040802620233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7311308466901550947307909 1370870337544040802620233)
        ·
          refine ⟨1028152753158030601965175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1370870337544040802620233 1028152753158030601965175)
          ·
            refine ⟨1542229129737045902947763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028152753158030601965175 1542229129737045902947763)
            ·
              refine ⟨2313343694605568854421645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1542229129737045902947763 2313343694605568854421645)
              ·
                refine ⟨867503885477088320408117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2313343694605568854421645 867503885477088320408117)
                ·
                  refine ⟨81328489263477030038261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 867503885477088320408117 81328489263477030038261)
                  ·
                    rfl

theorem cell22_712740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_712740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712740 prefixEnd_712740 := by exact prefixLift 712740
  have htrace : WordTrace (prefixWord ++ tailWord_712740) baseStart_712740 baseEnd_712740 := by
    simpa [prefixWord, tailWord_712740, baseEnd_712740] using wordTrace_append hprefix tailTrace_712740
  have hstable : (prefixWord ++ tailWord_712740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712740).length < 2 ^ (prefixWord ++ tailWord_712740).sum := by decide
  have hdescent : baseEnd_712740 < baseStart_712740 := by decide
  rcases family_descends (prefixWord ++ tailWord_712740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712753 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_712753 : Nat := 118140960795 + 712753 * 2 ^ 59
def prefixEnd_712753 : Nat := 4983230072969 + 3 ^ 40 * 712753 * 2
def baseEnd_712753 : Nat := 243989917956103389539743

theorem tailTrace_712753 : CollatzResearch.WordTrace tailWord_712753 prefixEnd_712753 243989917956103389539743 := by
  unfold tailWord_712753
  simp only [CollatzResearch.WordTrace]
  refine ⟨25996237586825084366206913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17330825057883389577471275 25996237586825084366206913)
  ·
    refine ⟨19497178190118813274655185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25996237586825084366206913 19497178190118813274655185)
    ·
      refine ⟨14622883642589109955991389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19497178190118813274655185 14622883642589109955991389)
      ·
        refine ⟨5483581365970916233496771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14622883642589109955991389 5483581365970916233496771)
        ·
          refine ⟨8225372048956374350245157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5483581365970916233496771 8225372048956374350245157)
          ·
            refine ⟨1542257259179320190670967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8225372048956374350245157 1542257259179320190670967)
            ·
              refine ⟨2313385888768980286006451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1542257259179320190670967 2313385888768980286006451)
              ·
                refine ⟨3470078833153470429009677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313385888768980286006451 3470078833153470429009677)
                ·
                  refine ⟨1301279562432551410878629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3470078833153470429009677 1301279562432551410878629)
                  ·
                    refine ⟨243989917956103389539743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1301279562432551410878629 243989917956103389539743)
                    ·
                      rfl

theorem cell22_712753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_712753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712753 prefixEnd_712753 := by exact prefixLift 712753
  have htrace : WordTrace (prefixWord ++ tailWord_712753) baseStart_712753 baseEnd_712753 := by
    simpa [prefixWord, tailWord_712753, baseEnd_712753] using wordTrace_append hprefix tailTrace_712753
  have hstable : (prefixWord ++ tailWord_712753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712753).length < 2 ^ (prefixWord ++ tailWord_712753).sum := by decide
  have hdescent : baseEnd_712753 < baseStart_712753 := by decide
  rcases family_descends (prefixWord ++ tailWord_712753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712800 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 2, 3]
def baseStart_712800 : Nat := 118140960795 + 712800 * 2 ^ 59
def prefixEnd_712800 : Nat := 4983230072969 + 3 ^ 40 * 712800 * 2
def baseEnd_712800 : Nat := 244006007016610933614599

theorem tailTrace_712800 : CollatzResearch.WordTrace tailWord_712800 prefixEnd_712800 244006007016610933614599 := by
  unfold tailWord_712800
  simp only [CollatzResearch.WordTrace]
  refine ⟨12998975908827405696583927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17331967878436540928778569 12998975908827405696583927)
  ·
    refine ⟨19498463863241108544875891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12998975908827405696583927 19498463863241108544875891)
    ·
      refine ⟨29247695794861662817313837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19498463863241108544875891 29247695794861662817313837)
      ·
        refine ⟨10967885923073123556492689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29247695794861662817313837 10967885923073123556492689)
        ·
          refine ⟨8225914442304842667369517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10967885923073123556492689 8225914442304842667369517)
          ·
            refine ⟨3084717915864316000263569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8225914442304842667369517 3084717915864316000263569)
            ·
              refine ⟨2313538436898237000197677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3084717915864316000263569 2313538436898237000197677)
              ·
                refine ⟨867576913836838875074129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2313538436898237000197677 867576913836838875074129)
                ·
                  refine ⟨650682685377629156305597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 867576913836838875074129 650682685377629156305597)
                  ·
                    refine ⟨244006007016610933614599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 650682685377629156305597 244006007016610933614599)
                    ·
                      rfl

theorem cell22_712800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2, 3].length) (baseStart_712800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712800 prefixEnd_712800 := by exact prefixLift 712800
  have htrace : WordTrace (prefixWord ++ tailWord_712800) baseStart_712800 baseEnd_712800 := by
    simpa [prefixWord, tailWord_712800, baseEnd_712800] using wordTrace_append hprefix tailTrace_712800
  have hstable : (prefixWord ++ tailWord_712800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712800).length < 2 ^ (prefixWord ++ tailWord_712800).sum := by decide
  have hdescent : baseEnd_712800 < baseStart_712800 := by decide
  rcases family_descends (prefixWord ++ tailWord_712800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712815 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 2, 4]
def baseStart_712815 : Nat := 118140960795 + 712815 * 2 ^ 59
def prefixEnd_712815 : Nat := 4983230072969 + 3 ^ 40 * 712815 * 2
def baseEnd_712815 : Nat := 244011141823155894489553

theorem tailTrace_712815 : CollatzResearch.WordTrace tailWord_712815 prefixEnd_712815 244011141823155894489553 := by
  unfold tailWord_712815
  simp only [CollatzResearch.WordTrace]
  refine ⟨25998498912600468954963899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17332332608400312636642599 25998498912600468954963899)
  ·
    refine ⟨38997748368900703432445849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25998498912600468954963899 38997748368900703432445849)
    ·
      refine ⟨29248311276675527574334387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38997748368900703432445849 29248311276675527574334387)
      ·
        refine ⟨43872466915013291361501581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29248311276675527574334387 43872466915013291361501581)
        ·
          refine ⟨16452175093129984260563093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43872466915013291361501581 16452175093129984260563093)
          ·
            refine ⟨771195707490468012213895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16452175093129984260563093 771195707490468012213895)
            ·
              refine ⟨1156793561235702018320843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771195707490468012213895 1156793561235702018320843)
              ·
                refine ⟨1735190341853553027481265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1156793561235702018320843 1735190341853553027481265)
                ·
                  refine ⟨1301392756390164770610949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1735190341853553027481265 1301392756390164770610949)
                  ·
                    refine ⟨244011141823155894489553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1301392756390164770610949 244011141823155894489553)
                    ·
                      rfl

theorem cell22_712815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 4].length) (baseStart_712815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712815 prefixEnd_712815 := by exact prefixLift 712815
  have htrace : WordTrace (prefixWord ++ tailWord_712815) baseStart_712815 baseEnd_712815 := by
    simpa [prefixWord, tailWord_712815, baseEnd_712815] using wordTrace_append hprefix tailTrace_712815
  have hstable : (prefixWord ++ tailWord_712815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712815).length < 2 ^ (prefixWord ++ tailWord_712815).sum := by decide
  have hdescent : baseEnd_712815 < baseStart_712815 := by decide
  rcases family_descends (prefixWord ++ tailWord_712815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712935 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 3, 5]
def baseStart_712935 : Nat := 118140960795 + 712935 * 2 ^ 59
def prefixEnd_712935 : Nat := 4983230072969 + 3 ^ 40 * 712935 * 2
def baseEnd_712935 : Nat := 244052220275515581489185

theorem tailTrace_712935 : CollatzResearch.WordTrace tailWord_712935 prefixEnd_712935 244052220275515581489185 := by
  unfold tailWord_712935
  simp only [CollatzResearch.WordTrace]
  refine ⟨26002875672165729449332259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17335250448110486299554839 26002875672165729449332259)
  ·
    refine ⟨39004313508248594173998389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26002875672165729449332259 39004313508248594173998389)
    ·
      refine ⟨3656654391398305703812349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39004313508248594173998389 3656654391398305703812349)
      ·
        refine ⟨1371245396774364638929631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3656654391398305703812349 1371245396774364638929631)
        ·
          refine ⟨2056868095161546958394447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1371245396774364638929631 2056868095161546958394447)
          ·
            refine ⟨3085302142742320437591671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2056868095161546958394447 3085302142742320437591671)
            ·
              refine ⟨4627953214113480656387507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085302142742320437591671 4627953214113480656387507)
              ·
                refine ⟨6941929821170220984581261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4627953214113480656387507 6941929821170220984581261)
                ·
                  refine ⟨2603223682938832869217973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6941929821170220984581261 2603223682938832869217973)
                  ·
                    refine ⟨244052220275515581489185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2603223682938832869217973 244052220275515581489185)
                    ·
                      rfl

theorem cell22_712935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_712935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712935 prefixEnd_712935 := by exact prefixLift 712935
  have htrace : WordTrace (prefixWord ++ tailWord_712935) baseStart_712935 baseEnd_712935 := by
    simpa [prefixWord, tailWord_712935, baseEnd_712935] using wordTrace_append hprefix tailTrace_712935
  have hstable : (prefixWord ++ tailWord_712935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712935).length < 2 ^ (prefixWord ++ tailWord_712935).sum := by decide
  have hdescent : baseEnd_712935 < baseStart_712935 := by decide
  rcases family_descends (prefixWord ++ tailWord_712935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712954 : List Nat := [3, 1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_712954 : Nat := 118140960795 + 712954 * 2 ^ 59
def prefixEnd_712954 : Nat := 4983230072969 + 3 ^ 40 * 712954 * 2
def baseEnd_712954 : Nat := 81352908121268621754709

theorem tailTrace_712954 : CollatzResearch.WordTrace tailWord_712954 prefixEnd_712954 81352908121268621754709 := by
  unfold tailWord_712954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6500892164774223923568479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17335712439397930462849277 6500892164774223923568479)
  ·
    refine ⟨9751338247161335885352719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6500892164774223923568479 9751338247161335885352719)
    ·
      refine ⟨14627007370742003828029079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9751338247161335885352719 14627007370742003828029079)
      ·
        refine ⟨21940511056113005742043619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14627007370742003828029079 21940511056113005742043619)
        ·
          refine ⟨32910766584169508613065429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21940511056113005742043619 32910766584169508613065429)
          ·
            refine ⟨771346091816472858118721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 32910766584169508613065429 771346091816472858118721)
            ·
              refine ⟨578509568862354643589041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771346091816472858118721 578509568862354643589041)
              ·
                refine ⟨433882176646765982691781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578509568862354643589041 433882176646765982691781)
                ·
                  refine ⟨81352908121268621754709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 433882176646765982691781 81352908121268621754709)
                  ·
                    rfl

theorem cell22_712954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_712954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712954 prefixEnd_712954 := by exact prefixLift 712954
  have htrace : WordTrace (prefixWord ++ tailWord_712954) baseStart_712954 baseEnd_712954 := by
    simpa [prefixWord, tailWord_712954, baseEnd_712954] using wordTrace_append hprefix tailTrace_712954
  have hstable : (prefixWord ++ tailWord_712954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712954).length < 2 ^ (prefixWord ++ tailWord_712954).sum := by decide
  have hdescent : baseEnd_712954 < baseStart_712954 := by decide
  rcases family_descends (prefixWord ++ tailWord_712954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_712999 : List Nat := [1, 1, 8, 1, 1, 1, 9]
def baseStart_712999 : Nat := 118140960795 + 712999 * 2 ^ 59
def prefixEnd_712999 : Nat := 4983230072969 + 3 ^ 40 * 712999 * 2
def baseEnd_712999 : Nat := 9039782547534842514407

theorem tailTrace_712999 : CollatzResearch.WordTrace tailWord_712999 prefixEnd_712999 9039782547534842514407 := by
  unfold tailWord_712999
  simp only [CollatzResearch.WordTrace]
  refine ⟨26005209943933868379662051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17336806629289245586441367 26005209943933868379662051)
  ·
    refine ⟨39007814915900802569493077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26005209943933868379662051 39007814915900802569493077)
    ·
      refine ⟨457122831045712530111247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 39007814915900802569493077 457122831045712530111247)
      ·
        refine ⟨685684246568568795166871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457122831045712530111247 685684246568568795166871)
        ·
          refine ⟨1028526369852853192750307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685684246568568795166871 1028526369852853192750307)
          ·
            refine ⟨1542789554779279789125461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1028526369852853192750307 1542789554779279789125461)
            ·
              refine ⟨9039782547534842514407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1542789554779279789125461 9039782547534842514407)
              ·
                rfl

theorem cell22_712999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 9].length) (baseStart_712999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_712999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_712999 prefixEnd_712999 := by exact prefixLift 712999
  have htrace : WordTrace (prefixWord ++ tailWord_712999) baseStart_712999 baseEnd_712999 := by
    simpa [prefixWord, tailWord_712999, baseEnd_712999] using wordTrace_append hprefix tailTrace_712999
  have hstable : (prefixWord ++ tailWord_712999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_712999).length < 2 ^ (prefixWord ++ tailWord_712999).sum := by decide
  have hdescent : baseEnd_712999 < baseStart_712999 := by decide
  rcases family_descends (prefixWord ++ tailWord_712999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713072 : List Nat := [2, 1, 1, 1, 4, 5, 1, 1, 6]
def baseStart_713072 : Nat := 118140960795 + 713072 * 2 ^ 59
def prefixEnd_713072 : Nat := 4983230072969 + 3 ^ 40 * 713072 * 2
def baseEnd_713072 : Nat := 81366372725097630271255

theorem tailTrace_713072 : CollatzResearch.WordTrace tailWord_713072 prefixEnd_713072 81366372725097630271255 := by
  unfold tailWord_713072
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003936236334700923534735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17338581648446267898046313 13003936236334700923534735)
  ·
    refine ⟨19505904354502051385302103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13003936236334700923534735 19505904354502051385302103)
    ·
      refine ⟨29258856531753077077953155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19505904354502051385302103 29258856531753077077953155)
      ·
        refine ⟨43888284797629615616929733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29258856531753077077953155 43888284797629615616929733)
        ·
          refine ⟨8229053399555552928174325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43888284797629615616929733 8229053399555552928174325)
          ·
            refine ⟨771473756208333087016343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8229053399555552928174325 771473756208333087016343)
            ·
              refine ⟨1157210634312499630524515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771473756208333087016343 1157210634312499630524515)
              ·
                refine ⟨1735815951468749445786773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1157210634312499630524515 1735815951468749445786773)
                ·
                  refine ⟨81366372725097630271255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1735815951468749445786773 81366372725097630271255)
                  ·
                    rfl

theorem cell22_713072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 6].length) (baseStart_713072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713072 prefixEnd_713072 := by exact prefixLift 713072
  have htrace : WordTrace (prefixWord ++ tailWord_713072) baseStart_713072 baseEnd_713072 := by
    simpa [prefixWord, tailWord_713072, baseEnd_713072] using wordTrace_append hprefix tailTrace_713072
  have hstable : (prefixWord ++ tailWord_713072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713072).length < 2 ^ (prefixWord ++ tailWord_713072).sum := by decide
  have hdescent : baseEnd_713072 < baseStart_713072 := by decide
  rcases family_descends (prefixWord ++ tailWord_713072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713078 : List Nat := [5, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_713078 : Nat := 118140960795 + 713078 * 2 ^ 59
def prefixEnd_713078 : Nat := 4983230072969 + 3 ^ 40 * 713078 * 2
def baseEnd_713078 : Nat := 81367057365970291721249

theorem tailTrace_713078 : CollatzResearch.WordTrace tailWord_713078 prefixEnd_713078 81367057365970291721249 := by
  unfold tailWord_713078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1625505706915479054486743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17338727540431776581191925 1625505706915479054486743)
  ·
    refine ⟨2438258560373218581730115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1625505706915479054486743 2438258560373218581730115)
    ·
      refine ⟨3657387840559827872595173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2438258560373218581730115 3657387840559827872595173)
      ·
        refine ⟨685760220104967726111595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3657387840559827872595173 685760220104967726111595)
        ·
          refine ⟨1028640330157451589167393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 685760220104967726111595 1028640330157451589167393)
          ·
            refine ⟨771480247618088691875545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028640330157451589167393 771480247618088691875545)
            ·
              refine ⟨578610185713566518906659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771480247618088691875545 578610185713566518906659)
              ·
                refine ⟨867915278570349778359989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 578610185713566518906659 867915278570349778359989)
                ·
                  refine ⟨81367057365970291721249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 867915278570349778359989 81367057365970291721249)
                  ·
                    rfl

theorem cell22_713078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_713078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713078 prefixEnd_713078 := by exact prefixLift 713078
  have htrace : WordTrace (prefixWord ++ tailWord_713078) baseStart_713078 baseEnd_713078 := by
    simpa [prefixWord, tailWord_713078, baseEnd_713078] using wordTrace_append hprefix tailTrace_713078
  have hstable : (prefixWord ++ tailWord_713078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713078).length < 2 ^ (prefixWord ++ tailWord_713078).sum := by decide
  have hdescent : baseEnd_713078 < baseStart_713078 := by decide
  rcases family_descends (prefixWord ++ tailWord_713078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713087 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 2, 3]
def baseStart_713087 : Nat := 118140960795 + 713087 * 2 ^ 59
def prefixEnd_713087 : Nat := 4983230072969 + 3 ^ 40 * 713087 * 2
def baseEnd_713087 : Nat := 244104252981837851688719

theorem tailTrace_713087 : CollatzResearch.WordTrace tailWord_713087 prefixEnd_713087 244104252981837851688719 := by
  unfold tailWord_713087
  simp only [CollatzResearch.WordTrace]
  refine ⟨26008419567615059408865515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17338946378410039605910343 26008419567615059408865515)
  ·
    refine ⟨39012629351422589113298273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26008419567615059408865515 39012629351422589113298273)
    ·
      refine ⟨29259472013566941834973705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39012629351422589113298273 29259472013566941834973705)
      ·
        refine ⟨21944604010175206376230279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29259472013566941834973705 21944604010175206376230279)
        ·
          refine ⟨32916906015262809564345419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21944604010175206376230279 32916906015262809564345419)
          ·
            refine ⟨49375359022894214346518129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32916906015262809564345419 49375359022894214346518129)
            ·
              refine ⟨37031519267170660759888597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49375359022894214346518129 37031519267170660759888597)
              ·
                refine ⟨867926232824312361559889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37031519267170660759888597 867926232824312361559889)
                ·
                  refine ⟨650944674618234271169917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 867926232824312361559889 650944674618234271169917)
                  ·
                    refine ⟨244104252981837851688719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 650944674618234271169917 244104252981837851688719)
                    ·
                      rfl

theorem cell22_713087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 3].length) (baseStart_713087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713087 prefixEnd_713087 := by exact prefixLift 713087
  have htrace : WordTrace (prefixWord ++ tailWord_713087) baseStart_713087 baseEnd_713087 := by
    simpa [prefixWord, tailWord_713087, baseEnd_713087] using wordTrace_append hprefix tailTrace_713087
  have hstable : (prefixWord ++ tailWord_713087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713087).length < 2 ^ (prefixWord ++ tailWord_713087).sum := by decide
  have hdescent : baseEnd_713087 < baseStart_713087 := by decide
  rcases family_descends (prefixWord ++ tailWord_713087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713091 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 1, 4]
def baseStart_713091 : Nat := 118140960795 + 713091 * 2 ^ 59
def prefixEnd_713091 : Nat := 4983230072969 + 3 ^ 40 * 713091 * 2
def baseEnd_713091 : Nat := 244105622263583174588707

theorem tailTrace_713091 : CollatzResearch.WordTrace tailWord_713091 prefixEnd_713091 244105622263583174588707 := by
  unfold tailWord_713091
  simp only [CollatzResearch.WordTrace]
  refine ⟨26008565459600568092011127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17339043639733712061340751 26008565459600568092011127)
  ·
    refine ⟨39012848189400852138016691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26008565459600568092011127 39012848189400852138016691)
    ·
      refine ⟨58519272284101278207025037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39012848189400852138016691 58519272284101278207025037)
      ·
        refine ⟨21944727106537979327634389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58519272284101278207025037 21944727106537979327634389)
        ·
          refine ⟨514329541559483890491431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 21944727106537979327634389 514329541559483890491431)
          ·
            refine ⟨771494312339225835737147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514329541559483890491431 771494312339225835737147)
            ·
              refine ⟨1157241468508838753605721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771494312339225835737147 1157241468508838753605721)
              ·
                refine ⟨867931101381629065204291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1157241468508838753605721 867931101381629065204291)
                ·
                  refine ⟨1301896652072443597806437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 867931101381629065204291 1301896652072443597806437)
                  ·
                    refine ⟨244105622263583174588707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1301896652072443597806437 244105622263583174588707)
                    ·
                      rfl

theorem cell22_713091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 4].length) (baseStart_713091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713091 prefixEnd_713091 := by exact prefixLift 713091
  have htrace : WordTrace (prefixWord ++ tailWord_713091) baseStart_713091 baseEnd_713091 := by
    simpa [prefixWord, tailWord_713091, baseEnd_713091] using wordTrace_append hprefix tailTrace_713091
  have hstable : (prefixWord ++ tailWord_713091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713091).length < 2 ^ (prefixWord ++ tailWord_713091).sum := by decide
  have hdescent : baseEnd_713091 < baseStart_713091 := by decide
  rcases family_descends (prefixWord ++ tailWord_713091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713100 : List Nat := [2, 2, 1, 2, 1, 4, 2, 8]
def baseStart_713100 : Nat := 118140960795 + 713100 * 2 ^ 59
def prefixEnd_713100 : Nat := 4983230072969 + 3 ^ 40 * 713100 * 2
def baseEnd_713100 : Nat := 27123189238612239012631

theorem tailTrace_713100 : CollatzResearch.WordTrace tailWord_713100 prefixEnd_713100 27123189238612239012631 := by
  unfold tailWord_713100
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004446858283981314544377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17339262477711975086059169 13004446858283981314544377)
  ·
    refine ⟨9753335143712985985908283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13004446858283981314544377 9753335143712985985908283)
    ·
      refine ⟨14630002715569478978862425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9753335143712985985908283 14630002715569478978862425)
      ·
        refine ⟨10972502036677109234146819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14630002715569478978862425 10972502036677109234146819)
        ·
          refine ⟨16458753055015663851220229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10972502036677109234146819 16458753055015663851220229)
          ·
            refine ⟨3086016197815436972103793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16458753055015663851220229 3086016197815436972103793)
            ·
              refine ⟨2314512148361577729077845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3086016197815436972103793 2314512148361577729077845)
              ·
                refine ⟨27123189238612239012631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2314512148361577729077845 27123189238612239012631)
                ·
                  rfl

theorem cell22_713100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 8].length) (baseStart_713100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713100 prefixEnd_713100 := by exact prefixLift 713100
  have htrace : WordTrace (prefixWord ++ tailWord_713100) baseStart_713100 baseEnd_713100 := by
    simpa [prefixWord, tailWord_713100, baseEnd_713100] using wordTrace_append hprefix tailTrace_713100
  have hstable : (prefixWord ++ tailWord_713100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713100).length < 2 ^ (prefixWord ++ tailWord_713100).sum := by decide
  have hdescent : baseEnd_713100 < baseStart_713100 := by decide
  rcases family_descends (prefixWord ++ tailWord_713100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713117 : List Nat := [1, 4, 2, 1, 5, 9]
def baseStart_713117 : Nat := 118140960795 + 713117 * 2 ^ 59
def prefixEnd_713117 : Nat := 4983230072969 + 3 ^ 40 * 713117 * 2
def baseEnd_713117 : Nat := 3013759538208984857267

theorem tailTrace_713117 : CollatzResearch.WordTrace tailWord_713117 prefixEnd_713117 3013759538208984857267 := by
  unfold tailWord_713117
  simp only [CollatzResearch.WordTrace]
  refine ⟨26009513757506374532457605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17339675838337583021638403 26009513757506374532457605)
  ·
    refine ⟨4876783829532445224835801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26009513757506374532457605 4876783829532445224835801)
    ·
      refine ⟨3657587872149333918626851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4876783829532445224835801 3657587872149333918626851)
      ·
        refine ⟨5486381808224000877940277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657587872149333918626851 5486381808224000877940277)
        ·
          refine ⟨514348294521000082306901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5486381808224000877940277 514348294521000082306901)
          ·
            refine ⟨3013759538208984857267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 514348294521000082306901 3013759538208984857267)
            ·
              rfl

theorem cell22_713117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 9].length) (baseStart_713117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713117 prefixEnd_713117 := by exact prefixLift 713117
  have htrace : WordTrace (prefixWord ++ tailWord_713117) baseStart_713117 baseEnd_713117 := by
    simpa [prefixWord, tailWord_713117, baseEnd_713117] using wordTrace_append hprefix tailTrace_713117
  have hstable : (prefixWord ++ tailWord_713117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713117).length < 2 ^ (prefixWord ++ tailWord_713117).sum := by decide
  have hdescent : baseEnd_713117 < baseStart_713117 := by decide
  rcases family_descends (prefixWord ++ tailWord_713117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713132 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 3, 3]
def baseStart_713132 : Nat := 118140960795 + 713132 * 2 ^ 59
def prefixEnd_713132 : Nat := 4983230072969 + 3 ^ 40 * 713132 * 2
def baseEnd_713132 : Nat := 244119657401472734313581

theorem tailTrace_713132 : CollatzResearch.WordTrace tailWord_713132 prefixEnd_713132 244119657401472734313581 := by
  unfold tailWord_713132
  simp only [CollatzResearch.WordTrace]
  refine ⟨13005030426226016047126825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17340040568301354729502433 13005030426226016047126825)
  ·
    refine ⟨9753772819669512035345119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13005030426226016047126825 9753772819669512035345119)
    ·
      refine ⟨14630659229504268053017679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9753772819669512035345119 14630659229504268053017679)
      ·
        refine ⟨21945988844256402079526519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14630659229504268053017679 21945988844256402079526519)
        ·
          refine ⟨32918983266384603119289779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21945988844256402079526519 32918983266384603119289779)
          ·
            refine ⟨49378474899576904678934669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32918983266384603119289779 49378474899576904678934669)
            ·
              refine ⟨18516928087341339254600501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49378474899576904678934669 18516928087341339254600501)
              ·
                refine ⟨1735962008188250555118797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18516928087341339254600501 1735962008188250555118797)
                ·
                  refine ⟨650985753070593958169549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1735962008188250555118797 650985753070593958169549)
                  ·
                    refine ⟨244119657401472734313581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 650985753070593958169549 244119657401472734313581)
                    ·
                      rfl

theorem cell22_713132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_713132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713132 prefixEnd_713132 := by exact prefixLift 713132
  have htrace : WordTrace (prefixWord ++ tailWord_713132) baseStart_713132 baseEnd_713132 := by
    simpa [prefixWord, tailWord_713132, baseEnd_713132] using wordTrace_append hprefix tailTrace_713132
  have hstable : (prefixWord ++ tailWord_713132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713132).length < 2 ^ (prefixWord ++ tailWord_713132).sum := by decide
  have hdescent : baseEnd_713132 < baseStart_713132 := by decide
  rcases family_descends (prefixWord ++ tailWord_713132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713149 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_713149 : Nat := 118140960795 + 713149 * 2 ^ 59
def prefixEnd_713149 : Nat := 4983230072969 + 3 ^ 40 * 713149 * 2
def baseEnd_713149 : Nat := 244125476848890356638529

theorem tailTrace_713149 : CollatzResearch.WordTrace tailWord_713149 prefixEnd_713149 244125476848890356638529 := by
  unfold tailWord_713149
  simp only [CollatzResearch.WordTrace]
  refine ⟨26010680893390443997622501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17340453928926962665081667 26010680893390443997622501)
  ·
    refine ⟨4877002667510708249554219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26010680893390443997622501 4877002667510708249554219)
    ·
      refine ⟨7315504001266062374331329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4877002667510708249554219 7315504001266062374331329)
      ·
        refine ⟨5486628000949546780748497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7315504001266062374331329 5486628000949546780748497)
        ·
          refine ⟨4114971000712160085561373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5486628000949546780748497 4114971000712160085561373)
          ·
            refine ⟨1543114125267060032085515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4114971000712160085561373 1543114125267060032085515)
            ·
              refine ⟨2314671187900590048128273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1543114125267060032085515 2314671187900590048128273)
              ·
                refine ⟨1736003390925442536096205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2314671187900590048128273 1736003390925442536096205)
                ·
                  refine ⟨651001271597040951036077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1736003390925442536096205 651001271597040951036077)
                  ·
                    refine ⟨244125476848890356638529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 651001271597040951036077 244125476848890356638529)
                    ·
                      rfl

theorem cell22_713149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_713149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713149 prefixEnd_713149 := by exact prefixLift 713149
  have htrace : WordTrace (prefixWord ++ tailWord_713149) baseStart_713149 baseEnd_713149 := by
    simpa [prefixWord, tailWord_713149, baseEnd_713149] using wordTrace_append hprefix tailTrace_713149
  have hstable : (prefixWord ++ tailWord_713149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713149).length < 2 ^ (prefixWord ++ tailWord_713149).sum := by decide
  have hdescent : baseEnd_713149 < baseStart_713149 := by decide
  rcases family_descends (prefixWord ++ tailWord_713149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713312 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_713312 : Nat := 118140960795 + 713312 * 2 ^ 59
def prefixEnd_713312 : Nat := 4983230072969 + 3 ^ 40 * 713312 * 2
def baseEnd_713312 : Nat := 244181275080012264813029

theorem tailTrace_713312 : CollatzResearch.WordTrace tailWord_713312 prefixEnd_713312 244181275080012264813029 := by
  unfold tailWord_713312
  simp only [CollatzResearch.WordTrace]
  refine ⟨13008312995899961417903095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17344417327866615223870793 13008312995899961417903095)
  ·
    refine ⟨19512469493849942126854643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13008312995899961417903095 19512469493849942126854643)
    ·
      refine ⟨29268704240774913190281965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19512469493849942126854643 29268704240774913190281965)
      ·
        refine ⟨10975764090290592446355737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29268704240774913190281965 10975764090290592446355737)
        ·
          refine ⟨8231823067717944334766803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10975764090290592446355737 8231823067717944334766803)
          ·
            refine ⟨12347734601576916502150205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8231823067717944334766803 12347734601576916502150205)
            ·
              refine ⟨4630400475591343688306327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12347734601576916502150205 4630400475591343688306327)
              ·
                refine ⟨6945600713387015532459491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630400475591343688306327 6945600713387015532459491)
                ·
                  refine ⟨10418401070080523298689237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6945600713387015532459491 10418401070080523298689237)
                  ·
                    refine ⟨244181275080012264813029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10418401070080523298689237 244181275080012264813029)
                    ·
                      rfl

theorem cell22_713312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_713312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713312 prefixEnd_713312 := by exact prefixLift 713312
  have htrace : WordTrace (prefixWord ++ tailWord_713312) baseStart_713312 baseEnd_713312 := by
    simpa [prefixWord, tailWord_713312, baseEnd_713312] using wordTrace_append hprefix tailTrace_713312
  have hstable : (prefixWord ++ tailWord_713312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713312).length < 2 ^ (prefixWord ++ tailWord_713312).sum := by decide
  have hdescent : baseEnd_713312 < baseStart_713312 := by decide
  rcases family_descends (prefixWord ++ tailWord_713312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713406 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_713406 : Nat := 118140960795 + 713406 * 2 ^ 59
def prefixEnd_713406 : Nat := 4983230072969 + 3 ^ 40 * 713406 * 2
def baseEnd_713406 : Nat := 244213453201027352962741

theorem tailTrace_713406 : CollatzResearch.WordTrace tailWord_713406 prefixEnd_713406 244213453201027352962741 := by
  unfold tailWord_713406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3252506806682422111216009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17346702968972917926485381 3252506806682422111216009)
  ·
    refine ⟨2439380105011816583412007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3252506806682422111216009 2439380105011816583412007)
    ·
      refine ⟨3659070157517724875118011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2439380105011816583412007 3659070157517724875118011)
      ·
        refine ⟨5488605236276587312677017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659070157517724875118011 5488605236276587312677017)
        ·
          refine ⟨4116453927207440484507763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5488605236276587312677017 4116453927207440484507763)
          ·
            refine ⟨6174680890811160726761645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4116453927207440484507763 6174680890811160726761645)
            ·
              refine ⟨2315505334054185272535617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6174680890811160726761645 2315505334054185272535617)
              ·
                refine ⟨1736629000540638954401713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2315505334054185272535617 1736629000540638954401713)
                ·
                  refine ⟨1302471750405479215801285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1736629000540638954401713 1302471750405479215801285)
                  ·
                    refine ⟨244213453201027352962741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1302471750405479215801285 244213453201027352962741)
                    ·
                      rfl

theorem cell22_713406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_713406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713406 prefixEnd_713406 := by exact prefixLift 713406
  have htrace : WordTrace (prefixWord ++ tailWord_713406) baseStart_713406 baseEnd_713406 := by
    simpa [prefixWord, tailWord_713406, baseEnd_713406] using wordTrace_append hprefix tailTrace_713406
  have hstable : (prefixWord ++ tailWord_713406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713406).length < 2 ^ (prefixWord ++ tailWord_713406).sum := by decide
  have hdescent : baseEnd_713406 < baseStart_713406 := by decide
  rcases family_descends (prefixWord ++ tailWord_713406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713461 : List Nat := [1, 3, 6, 1, 2, 1, 2, 2, 4]
def baseStart_713461 : Nat := 118140960795 + 713461 * 2 ^ 59
def prefixEnd_713461 : Nat := 4983230072969 + 3 ^ 40 * 713461 * 2
def baseEnd_713461 : Nat := 81410760275008514279191

theorem tailTrace_713461 : CollatzResearch.WordTrace tailWord_713461 prefixEnd_713461 81410760275008514279191 := by
  unfold tailWord_713461
  simp only [CollatzResearch.WordTrace]
  refine ⟨26022060468260121282980237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17348040312173414188653491 26022060468260121282980237)
  ·
    refine ⟨9758272675597545481117589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26022060468260121282980237 9758272675597545481117589)
    ·
      refine ⟨457419031668634944427387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9758272675597545481117589 457419031668634944427387)
      ·
        refine ⟨686128547502952416641081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 457419031668634944427387 686128547502952416641081)
        ·
          refine ⟨514596410627214312480811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 686128547502952416641081 514596410627214312480811)
          ·
            refine ⟨771894615940821468721217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 514596410627214312480811 771894615940821468721217)
            ·
              refine ⟨578920961955616101540913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771894615940821468721217 578920961955616101540913)
              ·
                refine ⟨434190721466712076155685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 578920961955616101540913 434190721466712076155685)
                ·
                  refine ⟨81410760275008514279191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 434190721466712076155685 81410760275008514279191)
                  ·
                    rfl

theorem cell22_713461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_713461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713461 prefixEnd_713461 := by exact prefixLift 713461
  have htrace : WordTrace (prefixWord ++ tailWord_713461) baseStart_713461 baseEnd_713461 := by
    simpa [prefixWord, tailWord_713461, baseEnd_713461] using wordTrace_append hprefix tailTrace_713461
  have hstable : (prefixWord ++ tailWord_713461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713461).length < 2 ^ (prefixWord ++ tailWord_713461).sum := by decide
  have hdescent : baseEnd_713461 < baseStart_713461 := by decide
  rcases family_descends (prefixWord ++ tailWord_713461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713464 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_713464 : Nat := 118140960795 + 713464 * 2 ^ 59
def prefixEnd_713464 : Nat := 4983230072969 + 3 ^ 40 * 713464 * 2
def baseEnd_713464 : Nat := 244233307786334535012563

theorem tailTrace_713464 : CollatzResearch.WordTrace tailWord_713464 prefixEnd_713464 244233307786334535012563 := by
  unfold tailWord_713464
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011084943624626397669723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17348113258166168530226297 13011084943624626397669723)
  ·
    refine ⟨19516627415436939596504585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13011084943624626397669723 19516627415436939596504585)
    ·
      refine ⟨14637470561577704697378439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19516627415436939596504585 14637470561577704697378439)
      ·
        refine ⟨21956205842366557046067659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14637470561577704697378439 21956205842366557046067659)
        ·
          refine ⟨32934308763549835569101489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21956205842366557046067659 32934308763549835569101489)
          ·
            refine ⟨24700731572662376676826117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32934308763549835569101489 24700731572662376676826117)
            ·
              refine ⟨4631387169874195626904897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24700731572662376676826117 4631387169874195626904897)
              ·
                refine ⟨3473540377405646720178673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4631387169874195626904897 3473540377405646720178673)
                ·
                  refine ⟨2605155283054235040134005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3473540377405646720178673 2605155283054235040134005)
                  ·
                    refine ⟨244233307786334535012563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2605155283054235040134005 244233307786334535012563)
                    ·
                      rfl

theorem cell22_713464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_713464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713464 prefixEnd_713464 := by exact prefixLift 713464
  have htrace : WordTrace (prefixWord ++ tailWord_713464) baseStart_713464 baseEnd_713464 := by
    simpa [prefixWord, tailWord_713464, baseEnd_713464] using wordTrace_append hprefix tailTrace_713464
  have hstable : (prefixWord ++ tailWord_713464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713464).length < 2 ^ (prefixWord ++ tailWord_713464).sum := by decide
  have hdescent : baseEnd_713464 < baseStart_713464 := by decide
  rcases family_descends (prefixWord ++ tailWord_713464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713496 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 1, 4]
def baseStart_713496 : Nat := 118140960795 + 713496 * 2 ^ 59
def prefixEnd_713496 : Nat := 4983230072969 + 3 ^ 40 * 713496 * 2
def baseEnd_713496 : Nat := 244244262040297118212465

theorem tailTrace_713496 : CollatzResearch.WordTrace tailWord_713496 prefixEnd_713496 244244262040297118212465 := by
  unfold tailWord_713496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011668511566661130252171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17348891348755548173669561 13011668511566661130252171)
  ·
    refine ⟨19517502767349991695378257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13011668511566661130252171 19517502767349991695378257)
    ·
      refine ⟨14638127075512493771533693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19517502767349991695378257 14638127075512493771533693)
      ·
        refine ⟨5489297653317185164325135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14638127075512493771533693 5489297653317185164325135)
        ·
          refine ⟨8233946479975777746487703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5489297653317185164325135 8233946479975777746487703)
          ·
            refine ⟨12350919719963666619731555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233946479975777746487703 12350919719963666619731555)
            ·
              refine ⟨18526379579945499929597333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12350919719963666619731555 18526379579945499929597333)
              ·
                refine ⟨868424042809945309199875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18526379579945499929597333 868424042809945309199875)
                ·
                  refine ⟨1302636064214917963799813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868424042809945309199875 1302636064214917963799813)
                  ·
                    refine ⟨244244262040297118212465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1302636064214917963799813 244244262040297118212465)
                    ·
                      rfl

theorem cell22_713496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_713496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713496 prefixEnd_713496 := by exact prefixLift 713496
  have htrace : WordTrace (prefixWord ++ tailWord_713496) baseStart_713496 baseEnd_713496 := by
    simpa [prefixWord, tailWord_713496, baseEnd_713496] using wordTrace_append hprefix tailTrace_713496
  have hstable : (prefixWord ++ tailWord_713496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713496).length < 2 ^ (prefixWord ++ tailWord_713496).sum := by decide
  have hdescent : baseEnd_713496 < baseStart_713496 := by decide
  rcases family_descends (prefixWord ++ tailWord_713496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713517 : List Nat := [1, 5, 3, 2, 1, 2, 1, 2, 5]
def baseStart_713517 : Nat := 118140960795 + 713517 * 2 ^ 59
def prefixEnd_713517 : Nat := 4983230072969 + 3 ^ 40 * 713517 * 2
def baseEnd_713517 : Nat := 81417150256486687812467

theorem tailTrace_713517 : CollatzResearch.WordTrace tailWord_713517 prefixEnd_713517 81417150256486687812467 := by
  unfold tailWord_713517
  simp only [CollatzResearch.WordTrace]
  refine ⟨26024102956057242847018805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17349401970704828564679203 26024102956057242847018805)
  ·
    refine ⟨2439759652130366516908013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26024102956057242847018805 2439759652130366516908013)
    ·
      refine ⟨914909869548887443840505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2439759652130366516908013 914909869548887443840505)
      ·
        refine ⟨686182402161665582880379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 914909869548887443840505 686182402161665582880379)
        ·
          refine ⟨1029273603242498374320569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686182402161665582880379 1029273603242498374320569)
          ·
            refine ⟨771955202431873780740427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1029273603242498374320569 771955202431873780740427)
            ·
              refine ⟨1157932803647810671110641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 771955202431873780740427 1157932803647810671110641)
              ·
                refine ⟨868449602735858003332981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1157932803647810671110641 868449602735858003332981)
                ·
                  refine ⟨81417150256486687812467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 868449602735858003332981 81417150256486687812467)
                  ·
                    rfl

theorem cell22_713517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_713517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713517 prefixEnd_713517 := by exact prefixLift 713517
  have htrace : WordTrace (prefixWord ++ tailWord_713517) baseStart_713517 baseEnd_713517 := by
    simpa [prefixWord, tailWord_713517, baseEnd_713517] using wordTrace_append hprefix tailTrace_713517
  have hstable : (prefixWord ++ tailWord_713517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713517).length < 2 ^ (prefixWord ++ tailWord_713517).sum := by decide
  have hdescent : baseEnd_713517 < baseStart_713517 := by decide
  rcases family_descends (prefixWord ++ tailWord_713517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713539 : List Nat := [1, 1, 1, 3, 1, 4, 2, 9]
def baseStart_713539 : Nat := 118140960795 + 713539 * 2 ^ 59
def prefixEnd_713539 : Nat := 4983230072969 + 3 ^ 40 * 713539 * 2
def baseEnd_713539 : Nat := 27139886868784371043037

theorem tailTrace_713539 : CollatzResearch.WordTrace tailWord_713539 prefixEnd_713539 27139886868784371043037 := by
  unfold tailWord_713539
  simp only [CollatzResearch.WordTrace]
  refine ⟨26024905361977540604319671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17349936907985027069546447 26024905361977540604319671)
  ·
    refine ⟨39037358042966310906479507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26024905361977540604319671 39037358042966310906479507)
    ·
      refine ⟨58556037064449466359719261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39037358042966310906479507 58556037064449466359719261)
      ·
        refine ⟨21958513899168549884894723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58556037064449466359719261 21958513899168549884894723)
        ·
          refine ⟨32937770848752824827342085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21958513899168549884894723 32937770848752824827342085)
          ·
            refine ⟨6175832034141154655126641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32937770848752824827342085 6175832034141154655126641)
            ·
              refine ⟨4631874025605865991344981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6175832034141154655126641 4631874025605865991344981)
              ·
                refine ⟨27139886868784371043037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4631874025605865991344981 27139886868784371043037)
                ·
                  rfl

theorem cell22_713539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 9].length) (baseStart_713539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713539 prefixEnd_713539 := by exact prefixLift 713539
  have htrace : WordTrace (prefixWord ++ tailWord_713539) baseStart_713539 baseEnd_713539 := by
    simpa [prefixWord, tailWord_713539, baseEnd_713539] using wordTrace_append hprefix tailTrace_713539
  have hstable : (prefixWord ++ tailWord_713539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713539).length < 2 ^ (prefixWord ++ tailWord_713539).sum := by decide
  have hdescent : baseEnd_713539 < baseStart_713539 := by decide
  rcases family_descends (prefixWord ++ tailWord_713539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713678 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 1, 5]
def baseStart_713678 : Nat := 118140960795 + 713678 * 2 ^ 59
def prefixEnd_713678 : Nat := 4983230072969 + 3 ^ 40 * 713678 * 2
def baseEnd_713678 : Nat := 244306564359709310161907

theorem tailTrace_713678 : CollatzResearch.WordTrace tailWord_713678 prefixEnd_713678 244306564359709310161907 := by
  unfold tailWord_713678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3253746888559245917953711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17353316738982644895753125 3253746888559245917953711)
  ·
    refine ⟨4880620332838868876930567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3253746888559245917953711 4880620332838868876930567)
    ·
      refine ⟨7320930499258303315395851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4880620332838868876930567 7320930499258303315395851)
      ·
        refine ⟨10981395748887454973093777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7320930499258303315395851 10981395748887454973093777)
        ·
          refine ⟨8236046811665591229820333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10981395748887454973093777 8236046811665591229820333)
          ·
            refine ⟨3088517554374596711182625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8236046811665591229820333 3088517554374596711182625)
            ·
              refine ⟨2316388165780947533386969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3088517554374596711182625 2316388165780947533386969)
              ·
                refine ⟨1737291124335710650040227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316388165780947533386969 1737291124335710650040227)
                ·
                  refine ⟨2605936686503565975060341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737291124335710650040227 2605936686503565975060341)
                  ·
                    refine ⟨244306564359709310161907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2605936686503565975060341 244306564359709310161907)
                    ·
                      rfl

theorem cell22_713678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_713678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713678 prefixEnd_713678 := by exact prefixLift 713678
  have htrace : WordTrace (prefixWord ++ tailWord_713678) baseStart_713678 baseEnd_713678 := by
    simpa [prefixWord, tailWord_713678, baseEnd_713678] using wordTrace_append hprefix tailTrace_713678
  have hstable : (prefixWord ++ tailWord_713678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713678).length < 2 ^ (prefixWord ++ tailWord_713678).sum := by decide
  have hdescent : baseEnd_713678 < baseStart_713678 := by decide
  rcases family_descends (prefixWord ++ tailWord_713678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713682 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 1, 4]
def baseStart_713682 : Nat := 118140960795 + 713682 * 2 ^ 59
def prefixEnd_713682 : Nat := 4983230072969 + 3 ^ 40 * 713682 * 2
def baseEnd_713682 : Nat := 244307933641454633061895

theorem tailTrace_713682 : CollatzResearch.WordTrace tailWord_713682 prefixEnd_713682 244307933641454633061895 := by
  unfold tailWord_713682
  simp only [CollatzResearch.WordTrace]
  refine ⟨6507530250114869006693825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17353414000306317351183533 6507530250114869006693825)
  ·
    refine ⟨4880647687586151755020369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6507530250114869006693825 4880647687586151755020369)
    ·
      refine ⟨3660485765689613816265277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4880647687586151755020369 3660485765689613816265277)
      ·
        refine ⟨1372682162133605181099479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3660485765689613816265277 1372682162133605181099479)
        ·
          refine ⟨2059023243200407771649219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372682162133605181099479 2059023243200407771649219)
          ·
            refine ⟨3088534864800611657473829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059023243200407771649219 3088534864800611657473829)
            ·
              refine ⟨579100287150114685776343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3088534864800611657473829 579100287150114685776343)
              ·
                refine ⟨868650430725172028664515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 579100287150114685776343 868650430725172028664515)
                ·
                  refine ⟨1302975646087758042996773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868650430725172028664515 1302975646087758042996773)
                  ·
                    refine ⟨244307933641454633061895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1302975646087758042996773 244307933641454633061895)
                    ·
                      rfl

theorem cell22_713682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_713682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713682 prefixEnd_713682 := by exact prefixLift 713682
  have htrace : WordTrace (prefixWord ++ tailWord_713682) baseStart_713682 baseEnd_713682 := by
    simpa [prefixWord, tailWord_713682, baseEnd_713682] using wordTrace_append hprefix tailTrace_713682
  have hstable : (prefixWord ++ tailWord_713682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713682).length < 2 ^ (prefixWord ++ tailWord_713682).sum := by decide
  have hdescent : baseEnd_713682 < baseStart_713682 := by decide
  rcases family_descends (prefixWord ++ tailWord_713682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713695 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 4, 3]
def baseStart_713695 : Nat := 118140960795 + 713695 * 2 ^ 59
def prefixEnd_713695 : Nat := 4983230072969 + 3 ^ 40 * 713695 * 2
def baseEnd_713695 : Nat := 244312383807126932486855

theorem tailTrace_713695 : CollatzResearch.WordTrace tailWord_713695 prefixEnd_713695 244312383807126932486855 := by
  unfold tailWord_713695
  simp only [CollatzResearch.WordTrace]
  refine ⟨26030595149412379246998539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17353730099608252831332359 26030595149412379246998539)
  ·
    refine ⟨39045892724118568870497809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26030595149412379246998539 39045892724118568870497809)
    ·
      refine ⟨29284419543088926652873357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39045892724118568870497809 29284419543088926652873357)
      ·
        refine ⟨10981657328658347494827509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29284419543088926652873357 10981657328658347494827509)
        ·
          refine ⟨1029530374561720077640079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10981657328658347494827509 1029530374561720077640079)
          ·
            refine ⟨1544295561842580116460119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029530374561720077640079 1544295561842580116460119)
            ·
              refine ⟨2316443342763870174690179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544295561842580116460119 2316443342763870174690179)
              ·
                refine ⟨3474665014145805262035269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316443342763870174690179 3474665014145805262035269)
                ·
                  refine ⟨651499690152338486631613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3474665014145805262035269 651499690152338486631613)
                  ·
                    refine ⟨244312383807126932486855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 651499690152338486631613 244312383807126932486855)
                    ·
                      rfl

theorem cell22_713695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 3].length) (baseStart_713695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713695 prefixEnd_713695 := by exact prefixLift 713695
  have htrace : WordTrace (prefixWord ++ tailWord_713695) baseStart_713695 baseEnd_713695 := by
    simpa [prefixWord, tailWord_713695, baseEnd_713695] using wordTrace_append hprefix tailTrace_713695
  have hstable : (prefixWord ++ tailWord_713695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713695).length < 2 ^ (prefixWord ++ tailWord_713695).sum := by decide
  have hdescent : baseEnd_713695 < baseStart_713695 := by decide
  rcases family_descends (prefixWord ++ tailWord_713695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713813 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_713813 : Nat := 118140960795 + 713813 * 2 ^ 59
def prefixEnd_713813 : Nat := 4983230072969 + 3 ^ 40 * 713813 * 2
def baseEnd_713813 : Nat := 244352777618613958036493

theorem tailTrace_713813 : CollatzResearch.WordTrace tailWord_713813 prefixEnd_713813 244352777618613958036493 := by
  unfold tailWord_713813
  simp only [CollatzResearch.WordTrace]
  refine ⟨26034898962984885399794093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17356599308656590266529395 26034898962984885399794093)
  ·
    refine ⟨9763087111119332024922785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26034898962984885399794093 9763087111119332024922785)
    ·
      refine ⟨7322315333339499018692089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9763087111119332024922785 7322315333339499018692089)
      ·
        refine ⟨5491736500004624264019067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7322315333339499018692089 5491736500004624264019067)
        ·
          refine ⟨8237604750006936396028601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491736500004624264019067 8237604750006936396028601)
          ·
            refine ⟨6178203562505202297021451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8237604750006936396028601 6178203562505202297021451)
            ·
              refine ⟨9267305343757803445532177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6178203562505202297021451 9267305343757803445532177)
              ·
                refine ⟨6950479007818352584149133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9267305343757803445532177 6950479007818352584149133)
                ·
                  refine ⟨2606429627931882219055925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6950479007818352584149133 2606429627931882219055925)
                  ·
                    refine ⟨244352777618613958036493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2606429627931882219055925 244352777618613958036493)
                    ·
                      rfl

theorem cell22_713813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_713813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713813 prefixEnd_713813 := by exact prefixLift 713813
  have htrace : WordTrace (prefixWord ++ tailWord_713813) baseStart_713813 baseEnd_713813 := by
    simpa [prefixWord, tailWord_713813, baseEnd_713813] using wordTrace_append hprefix tailTrace_713813
  have hstable : (prefixWord ++ tailWord_713813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713813).length < 2 ^ (prefixWord ++ tailWord_713813).sum := by decide
  have hdescent : baseEnd_713813 < baseStart_713813 := by decide
  rcases family_descends (prefixWord ++ tailWord_713813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713828 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_713828 : Nat := 118140960795 + 713828 * 2 ^ 59
def prefixEnd_713828 : Nat := 4983230072969 + 3 ^ 40 * 713828 * 2
def baseEnd_713828 : Nat := 244357912425158918911447

theorem tailTrace_713828 : CollatzResearch.WordTrace tailWord_713828 prefixEnd_713828 244357912425158918911447 := by
  unfold tailWord_713828
  simp only [CollatzResearch.WordTrace]
  refine ⟨13017723028965271480795069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17356964038620361974393425 13017723028965271480795069)
  ·
    refine ⟨4881646135861976805298151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13017723028965271480795069 4881646135861976805298151)
    ·
      refine ⟨7322469203792965207947227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4881646135861976805298151 7322469203792965207947227)
      ·
        refine ⟨10983703805689447811920841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7322469203792965207947227 10983703805689447811920841)
        ·
          refine ⟨8237777854267085858940631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10983703805689447811920841 8237777854267085858940631)
          ·
            refine ⟨12356666781400628788410947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8237777854267085858940631 12356666781400628788410947)
            ·
              refine ⟨18535000172100943182616421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12356666781400628788410947 18535000172100943182616421)
              ·
                refine ⟨3475312532268926846740579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18535000172100943182616421 3475312532268926846740579)
                ·
                  refine ⟨5212968798403390270110869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475312532268926846740579 5212968798403390270110869)
                  ·
                    refine ⟨244357912425158918911447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5212968798403390270110869 244357912425158918911447)
                    ·
                      rfl

theorem cell22_713828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_713828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713828 prefixEnd_713828 := by exact prefixLift 713828
  have htrace : WordTrace (prefixWord ++ tailWord_713828) baseStart_713828 baseEnd_713828 := by
    simpa [prefixWord, tailWord_713828, baseEnd_713828] using wordTrace_append hprefix tailTrace_713828
  have hstable : (prefixWord ++ tailWord_713828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713828).length < 2 ^ (prefixWord ++ tailWord_713828).sum := by decide
  have hdescent : baseEnd_713828 < baseStart_713828 := by decide
  rcases family_descends (prefixWord ++ tailWord_713828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713832 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 6]
def baseStart_713832 : Nat := 118140960795 + 713832 * 2 ^ 59
def prefixEnd_713832 : Nat := 4983230072969 + 3 ^ 40 * 713832 * 2
def baseEnd_713832 : Nat := 81453093902301413937145

theorem tailTrace_713832 : CollatzResearch.WordTrace tailWord_713832 prefixEnd_713832 81453093902301413937145 := by
  unfold tailWord_713832
  simp only [CollatzResearch.WordTrace]
  refine ⟨13017795974958025822367875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17357061299944034429823833 13017795974958025822367875)
  ·
    refine ⟨19526693962437038733551813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13017795974958025822367875 19526693962437038733551813)
    ·
      refine ⟨3661255117956944762540965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19526693962437038733551813 3661255117956944762540965)
      ·
        refine ⟨686485334616927142976431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3661255117956944762540965 686485334616927142976431)
        ·
          refine ⟨1029728001925390714464647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 686485334616927142976431 1029728001925390714464647)
          ·
            refine ⟨1544592002888086071696971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1029728001925390714464647 1544592002888086071696971)
            ·
              refine ⟨2316888004332129107545457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1544592002888086071696971 2316888004332129107545457)
              ·
                refine ⟨1737666003249096830659093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316888004332129107545457 1737666003249096830659093)
                ·
                  refine ⟨81453093902301413937145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1737666003249096830659093 81453093902301413937145)
                  ·
                    rfl

theorem cell22_713832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 6].length) (baseStart_713832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713832 prefixEnd_713832 := by exact prefixLift 713832
  have htrace : WordTrace (prefixWord ++ tailWord_713832) baseStart_713832 baseEnd_713832 := by
    simpa [prefixWord, tailWord_713832, baseEnd_713832] using wordTrace_append hprefix tailTrace_713832
  have hstable : (prefixWord ++ tailWord_713832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713832).length < 2 ^ (prefixWord ++ tailWord_713832).sum := by decide
  have hdescent : baseEnd_713832 < baseStart_713832 := by decide
  rcases family_descends (prefixWord ++ tailWord_713832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713875 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 3, 3]
def baseStart_713875 : Nat := 118140960795 + 713875 * 2 ^ 59
def prefixEnd_713875 : Nat := 4983230072969 + 3 ^ 40 * 713875 * 2
def baseEnd_713875 : Nat := 244374001485666462986303

theorem tailTrace_713875 : CollatzResearch.WordTrace tailWord_713875 prefixEnd_713875 244374001485666462986303 := by
  unfold tailWord_713875
  simp only [CollatzResearch.WordTrace]
  refine ⟨26037160288760269988551079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17358106859173513325700719 26037160288760269988551079)
  ·
    refine ⟨39055740433140404982826619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26037160288760269988551079 39055740433140404982826619)
    ·
      refine ⟨58583610649710607474239929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39055740433140404982826619 58583610649710607474239929)
      ·
        refine ⟨43937707987282955605679947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58583610649710607474239929 43937707987282955605679947)
        ·
          refine ⟨65906561980924433408519921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43937707987282955605679947 65906561980924433408519921)
          ·
            refine ⟨49429921485693325056389941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65906561980924433408519921 49429921485693325056389941)
            ·
              refine ⟨4634055139283749224036557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49429921485693325056389941 4634055139283749224036557)
              ·
                refine ⟨1737770677231405959013709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4634055139283749224036557 1737770677231405959013709)
                ·
                  refine ⟨651664003961777234630141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1737770677231405959013709 651664003961777234630141)
                  ·
                    refine ⟨244374001485666462986303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 651664003961777234630141 244374001485666462986303)
                    ·
                      rfl

theorem cell22_713875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 3].length) (baseStart_713875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713875 prefixEnd_713875 := by exact prefixLift 713875
  have htrace : WordTrace (prefixWord ++ tailWord_713875) baseStart_713875 baseEnd_713875 := by
    simpa [prefixWord, tailWord_713875, baseEnd_713875] using wordTrace_append hprefix tailTrace_713875
  have hstable : (prefixWord ++ tailWord_713875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713875).length < 2 ^ (prefixWord ++ tailWord_713875).sum := by decide
  have hdescent : baseEnd_713875 < baseStart_713875 := by decide
  rcases family_descends (prefixWord ++ tailWord_713875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713892 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_713892 : Nat := 118140960795 + 713892 * 2 ^ 59
def prefixEnd_713892 : Nat := 4983230072969 + 3 ^ 40 * 713892 * 2
def baseEnd_713892 : Nat := 244379820933084085311251

theorem tailTrace_713892 : CollatzResearch.WordTrace tailWord_713892 prefixEnd_713892 244379820933084085311251 := by
  unfold tailWord_713892
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018890164849340945959965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17358520219799121261279953 13018890164849340945959965)
  ·
    refine ⟨4882083811818502854734987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13018890164849340945959965 4882083811818502854734987)
    ·
      refine ⟨7323125717727754282102481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4882083811818502854734987 7323125717727754282102481)
      ·
        refine ⟨5492344288295815711576861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7323125717727754282102481 5492344288295815711576861)
        ·
          refine ⟨2059629108110930891841323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5492344288295815711576861 2059629108110930891841323)
          ·
            refine ⟨3089443662166396337761985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059629108110930891841323 3089443662166396337761985)
            ·
              refine ⟨2317082746624797253321489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089443662166396337761985 2317082746624797253321489)
              ·
                refine ⟨1737812059968597939991117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317082746624797253321489 1737812059968597939991117)
                ·
                  refine ⟨651679522488224227496669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1737812059968597939991117 651679522488224227496669)
                  ·
                    refine ⟨244379820933084085311251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 651679522488224227496669 244379820933084085311251)
                    ·
                      rfl

theorem cell22_713892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_713892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713892 prefixEnd_713892 := by exact prefixLift 713892
  have htrace : WordTrace (prefixWord ++ tailWord_713892) baseStart_713892 baseEnd_713892 := by
    simpa [prefixWord, tailWord_713892, baseEnd_713892] using wordTrace_append hprefix tailTrace_713892
  have hstable : (prefixWord ++ tailWord_713892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713892).length < 2 ^ (prefixWord ++ tailWord_713892).sum := by decide
  have hdescent : baseEnd_713892 < baseStart_713892 := by decide
  rcases family_descends (prefixWord ++ tailWord_713892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713903 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 1, 7]
def baseStart_713903 : Nat := 118140960795 + 713903 * 2 ^ 59
def prefixEnd_713903 : Nat := 4983230072969 + 3 ^ 40 * 713903 * 2
def baseEnd_713903 : Nat := 244383586457883723286217

theorem tailTrace_713903 : CollatzResearch.WordTrace tailWord_713903 prefixEnd_713903 244383586457883723286217 := by
  unfold tailWord_713903
  simp only [CollatzResearch.WordTrace]
  refine ⟨26038181532658830770570363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17358787688439220513713575 26038181532658830770570363)
  ·
    refine ⟨39057272298988246155855545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26038181532658830770570363 39057272298988246155855545)
    ·
      refine ⟨29292954224241184616891659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39057272298988246155855545 29292954224241184616891659)
      ·
        refine ⟨43939431336361776925337489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29292954224241184616891659 43939431336361776925337489)
        ·
          refine ⟨32954573502271332694003117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43939431336361776925337489 32954573502271332694003117)
          ·
            refine ⟨12357965063351749760251169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32954573502271332694003117 12357965063351749760251169)
            ·
              refine ⟨9268473797513812320188377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12357965063351749760251169 9268473797513812320188377)
              ·
                refine ⟨6951355348135359240141283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9268473797513812320188377 6951355348135359240141283)
                ·
                  refine ⟨10427033022203038860211925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6951355348135359240141283 10427033022203038860211925)
                  ·
                    refine ⟨244383586457883723286217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10427033022203038860211925 244383586457883723286217)
                    ·
                      rfl

theorem cell22_713903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_713903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713903 prefixEnd_713903 := by exact prefixLift 713903
  have htrace : WordTrace (prefixWord ++ tailWord_713903) baseStart_713903 baseEnd_713903 := by
    simpa [prefixWord, tailWord_713903, baseEnd_713903] using wordTrace_append hprefix tailTrace_713903
  have hstable : (prefixWord ++ tailWord_713903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713903).length < 2 ^ (prefixWord ++ tailWord_713903).sum := by decide
  have hdescent : baseEnd_713903 < baseStart_713903 := by decide
  rcases family_descends (prefixWord ++ tailWord_713903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713905 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 7]
def baseStart_713905 : Nat := 118140960795 + 713905 * 2 ^ 59
def prefixEnd_713905 : Nat := 4983230072969 + 3 ^ 40 * 713905 * 2
def baseEnd_713905 : Nat := 81461423699585461578737

theorem tailTrace_713905 : CollatzResearch.WordTrace tailWord_713905 prefixEnd_713905 81461423699585461578737 := by
  unfold tailWord_713905
  simp only [CollatzResearch.WordTrace]
  refine ⟨26038254478651585112143169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17358836319101056741428779 26038254478651585112143169)
  ·
    refine ⟨19528690858988688834107377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26038254478651585112143169 19528690858988688834107377)
    ·
      refine ⟨14646518144241516625580533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19528690858988688834107377 14646518144241516625580533)
      ·
        refine ⟨1373111076022642183648175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14646518144241516625580533 1373111076022642183648175)
        ·
          refine ⟨2059666614033963275472263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373111076022642183648175 2059666614033963275472263)
          ·
            refine ⟨3089499921050944913208395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059666614033963275472263 3089499921050944913208395)
            ·
              refine ⟨4634249881576417369812593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089499921050944913208395 4634249881576417369812593)
              ·
                refine ⟨3475687411182313027359445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4634249881576417369812593 3475687411182313027359445)
                ·
                  refine ⟨81461423699585461578737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3475687411182313027359445 81461423699585461578737)
                  ·
                    rfl

theorem cell22_713905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_713905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713905 prefixEnd_713905 := by exact prefixLift 713905
  have htrace : WordTrace (prefixWord ++ tailWord_713905) baseStart_713905 baseEnd_713905 := by
    simpa [prefixWord, tailWord_713905, baseEnd_713905] using wordTrace_append hprefix tailTrace_713905
  have hstable : (prefixWord ++ tailWord_713905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713905).length < 2 ^ (prefixWord ++ tailWord_713905).sum := by decide
  have hdescent : baseEnd_713905 < baseStart_713905 := by decide
  rcases family_descends (prefixWord ++ tailWord_713905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713952 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 1, 4]
def baseStart_713952 : Nat := 118140960795 + 713952 * 2 ^ 59
def prefixEnd_713952 : Nat := 4983230072969 + 3 ^ 40 * 713952 * 2
def baseEnd_713952 : Nat := 244400360159263928811067

theorem tailTrace_713952 : CollatzResearch.WordTrace tailWord_713952 prefixEnd_713952 244400360159263928811067 := by
  unfold tailWord_713952
  simp only [CollatzResearch.WordTrace]
  refine ⟨13019984354740656069552055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17359979139654208092736073 13019984354740656069552055)
  ·
    refine ⟨19529976532110984104328083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13019984354740656069552055 19529976532110984104328083)
    ·
      refine ⟨29294964798166476156492125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19529976532110984104328083 29294964798166476156492125)
      ·
        refine ⟨10985611799312428558684547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29294964798166476156492125 10985611799312428558684547)
        ·
          refine ⟨16478417698968642838026821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10985611799312428558684547 16478417698968642838026821)
          ·
            refine ⟨3089703318556620532130029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16478417698968642838026821 3089703318556620532130029)
            ·
              refine ⟨1158638744458732699548761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3089703318556620532130029 1158638744458732699548761)
              ·
                refine ⟨868979058344049524661571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1158638744458732699548761 868979058344049524661571)
                ·
                  refine ⟨1303468587516074286992357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 868979058344049524661571 1303468587516074286992357)
                  ·
                    refine ⟨244400360159263928811067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1303468587516074286992357 244400360159263928811067)
                    ·
                      rfl

theorem cell22_713952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_713952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713952 prefixEnd_713952 := by exact prefixLift 713952
  have htrace : WordTrace (prefixWord ++ tailWord_713952) baseStart_713952 baseEnd_713952 := by
    simpa [prefixWord, tailWord_713952, baseEnd_713952] using wordTrace_append hprefix tailTrace_713952
  have hstable : (prefixWord ++ tailWord_713952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713952).length < 2 ^ (prefixWord ++ tailWord_713952).sum := by decide
  have hdescent : baseEnd_713952 < baseStart_713952 := by decide
  rcases family_descends (prefixWord ++ tailWord_713952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_713995 : List Nat := [1, 1, 1, 1, 5, 3, 3, 7]
def baseStart_713995 : Nat := 118140960795 + 713995 * 2 ^ 59
def prefixEnd_713995 : Nat := 4983230072969 + 3 ^ 40 * 713995 * 2
def baseEnd_713995 : Nat := 27157231104225127776215

theorem tailTrace_713995 : CollatzResearch.WordTrace tailWord_713995 prefixEnd_713995 27157231104225127776215 := by
  unfold tailWord_713995
  simp only [CollatzResearch.WordTrace]
  refine ⟨26041537048325530482919439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17361024698883686988612959 26041537048325530482919439)
  ·
    refine ⟨39062305572488295724379159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26041537048325530482919439 39062305572488295724379159)
    ·
      refine ⟨58593458358732443586568739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39062305572488295724379159 58593458358732443586568739)
      ·
        refine ⟨87890187538098665379853109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58593458358732443586568739 87890187538098665379853109)
        ·
          refine ⟨8239705081696749879361229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87890187538098665379853109 8239705081696749879361229)
          ·
            refine ⟨3089889405636281204760461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8239705081696749879361229 3089889405636281204760461)
            ·
              refine ⟨1158708527113605451785173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3089889405636281204760461 1158708527113605451785173)
              ·
                refine ⟨27157231104225127776215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1158708527113605451785173 27157231104225127776215)
                ·
                  rfl

theorem cell22_713995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 7].length) (baseStart_713995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_713995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_713995 prefixEnd_713995 := by exact prefixLift 713995
  have htrace : WordTrace (prefixWord ++ tailWord_713995) baseStart_713995 baseEnd_713995 := by
    simpa [prefixWord, tailWord_713995, baseEnd_713995] using wordTrace_append hprefix tailTrace_713995
  have hstable : (prefixWord ++ tailWord_713995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_713995).length < 2 ^ (prefixWord ++ tailWord_713995).sum := by decide
  have hdescent : baseEnd_713995 < baseStart_713995 := by decide
  rcases family_descends (prefixWord ++ tailWord_713995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714044 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 3, 3]
def baseStart_714044 : Nat := 118140960795 + 714044 * 2 ^ 59
def prefixEnd_714044 : Nat := 4983230072969 + 3 ^ 40 * 714044 * 2
def baseEnd_714044 : Nat := 244431853639406355510785

theorem tailTrace_714044 : CollatzResearch.WordTrace tailWord_714044 prefixEnd_714044 244431853639406355510785 := by
  unfold tailWord_714044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13021662112574005925726593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17362216150098674567635457 13021662112574005925726593)
  ·
    refine ⟨9766246584430504444294945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13021662112574005925726593 9766246584430504444294945)
    ·
      refine ⟨7324684938322878333221209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9766246584430504444294945 7324684938322878333221209)
      ·
        refine ⟨5493513703742158749915907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7324684938322878333221209 5493513703742158749915907)
        ·
          refine ⟨8240270555613238124873861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493513703742158749915907 8240270555613238124873861)
          ·
            refine ⟨1545050729177482148413849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8240270555613238124873861 1545050729177482148413849)
            ·
              refine ⟨1158788046883111611310387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1545050729177482148413849 1158788046883111611310387)
              ·
                refine ⟨1738182070324667416965581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1158788046883111611310387 1738182070324667416965581)
                ·
                  refine ⟨651818276371750281362093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1738182070324667416965581 651818276371750281362093)
                  ·
                    refine ⟨244431853639406355510785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 651818276371750281362093 244431853639406355510785)
                    ·
                      rfl

theorem cell22_714044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_714044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714044 prefixEnd_714044 := by exact prefixLift 714044
  have htrace : WordTrace (prefixWord ++ tailWord_714044) baseStart_714044 baseEnd_714044 := by
    simpa [prefixWord, tailWord_714044, baseEnd_714044] using wordTrace_append hprefix tailTrace_714044
  have hstable : (prefixWord ++ tailWord_714044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714044).length < 2 ^ (prefixWord ++ tailWord_714044).sum := by decide
  have hdescent : baseEnd_714044 < baseStart_714044 := by decide
  rcases family_descends (prefixWord ++ tailWord_714044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714121 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 1, 4]
def baseStart_714121 : Nat := 118140960795 + 714121 * 2 ^ 59
def prefixEnd_714121 : Nat := 4983230072969 + 3 ^ 40 * 714121 * 2
def baseEnd_714121 : Nat := 244458212313003821335549

theorem tailTrace_714121 : CollatzResearch.WordTrace tailWord_714121 prefixEnd_714121 244458212313003821335549 := by
  unfold tailWord_714121
  simp only [CollatzResearch.WordTrace]
  refine ⟨26046132645869054002006217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17364088430579369334670811 26046132645869054002006217)
  ·
    refine ⟨19534599484401790501504663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26046132645869054002006217 19534599484401790501504663)
    ·
      refine ⟨29301899226602685752256995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19534599484401790501504663 29301899226602685752256995)
      ·
        refine ⟨43952848839904028628385493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29301899226602685752256995 43952848839904028628385493)
        ·
          refine ⟨1030144894685250670977785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 43952848839904028628385493 1030144894685250670977785)
          ·
            refine ⟨772608671013938003233339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1030144894685250670977785 772608671013938003233339)
            ·
              refine ⟨1158913006520907004850009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772608671013938003233339 1158913006520907004850009)
              ·
                refine ⟨869184754890680253637507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1158913006520907004850009 869184754890680253637507)
                ·
                  refine ⟨1303777132336020380456261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 869184754890680253637507 1303777132336020380456261)
                  ·
                    refine ⟨244458212313003821335549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1303777132336020380456261 244458212313003821335549)
                    ·
                      rfl

theorem cell22_714121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 4].length) (baseStart_714121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714121 prefixEnd_714121 := by exact prefixLift 714121
  have htrace : WordTrace (prefixWord ++ tailWord_714121) baseStart_714121 baseEnd_714121 := by
    simpa [prefixWord, tailWord_714121, baseEnd_714121] using wordTrace_append hprefix tailTrace_714121
  have hstable : (prefixWord ++ tailWord_714121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714121).length < 2 ^ (prefixWord ++ tailWord_714121).sum := by decide
  have hdescent : baseEnd_714121 < baseStart_714121 := by decide
  rcases family_descends (prefixWord ++ tailWord_714121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714151 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 2, 3]
def baseStart_714151 : Nat := 118140960795 + 714151 * 2 ^ 59
def prefixEnd_714151 : Nat := 4983230072969 + 3 ^ 40 * 714151 * 2
def baseEnd_714151 : Nat := 244468481926093743085457

theorem tailTrace_714151 : CollatzResearch.WordTrace tailWord_714151 prefixEnd_714151 244468481926093743085457 := by
  unfold tailWord_714151
  simp only [CollatzResearch.WordTrace]
  refine ⟨26047226835760369125598307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17364817890506912750398871 26047226835760369125598307)
  ·
    refine ⟨39070840253640553688397461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26047226835760369125598307 39070840253640553688397461)
    ·
      refine ⟨1831445636889400954143631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39070840253640553688397461 1831445636889400954143631)
      ·
        refine ⟨2747168455334101431215447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831445636889400954143631 2747168455334101431215447)
        ·
          refine ⟨4120752683001152146823171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747168455334101431215447 4120752683001152146823171)
          ·
            refine ⟨6181129024501728220234757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4120752683001152146823171 6181129024501728220234757)
            ·
              refine ⟨1158961692094074041294017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6181129024501728220234757 1158961692094074041294017)
              ·
                refine ⟨869221269070555530970513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1158961692094074041294017 869221269070555530970513)
                ·
                  refine ⟨651915951802916648227885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 869221269070555530970513 651915951802916648227885)
                  ·
                    refine ⟨244468481926093743085457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 651915951802916648227885 244468481926093743085457)
                    ·
                      rfl

theorem cell22_714151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_714151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714151 prefixEnd_714151 := by exact prefixLift 714151
  have htrace : WordTrace (prefixWord ++ tailWord_714151) baseStart_714151 baseEnd_714151 := by
    simpa [prefixWord, tailWord_714151, baseEnd_714151] using wordTrace_append hprefix tailTrace_714151
  have hstable : (prefixWord ++ tailWord_714151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714151).length < 2 ^ (prefixWord ++ tailWord_714151).sum := by decide
  have hdescent : baseEnd_714151 < baseStart_714151 := by decide
  rcases family_descends (prefixWord ++ tailWord_714151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714207 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 4, 5]
def baseStart_714207 : Nat := 118140960795 + 714207 * 2 ^ 59
def prefixEnd_714207 : Nat := 4983230072969 + 3 ^ 40 * 714207 * 2
def baseEnd_714207 : Nat := 244487651870528263685285

theorem tailTrace_714207 : CollatzResearch.WordTrace tailWord_714207 prefixEnd_714207 244487651870528263685285 := by
  unfold tailWord_714207
  simp only [CollatzResearch.WordTrace]
  refine ⟨26049269323557490689636875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17366179549038327126424583 26049269323557490689636875)
  ·
    refine ⟨39073903985336236034455313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26049269323557490689636875 39073903985336236034455313)
    ·
      refine ⟨29305427989002177025841485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39073903985336236034455313 29305427989002177025841485)
      ·
        refine ⟨10989535495875816384690557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29305427989002177025841485 10989535495875816384690557)
        ·
          refine ⟨4121075810953431144258959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10989535495875816384690557 4121075810953431144258959)
          ·
            refine ⟨6181613716430146716388439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121075810953431144258959 6181613716430146716388439)
            ·
              refine ⟨9272420574645220074582659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6181613716430146716388439 9272420574645220074582659)
              ·
                refine ⟨13908630861967830111873989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9272420574645220074582659 13908630861967830111873989)
                ·
                  refine ⟨2607868286618968145976373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13908630861967830111873989 2607868286618968145976373)
                  ·
                    refine ⟨244487651870528263685285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2607868286618968145976373 244487651870528263685285)
                    ·
                      rfl

theorem cell22_714207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_714207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714207 prefixEnd_714207 := by exact prefixLift 714207
  have htrace : WordTrace (prefixWord ++ tailWord_714207) baseStart_714207 baseEnd_714207 := by
    simpa [prefixWord, tailWord_714207, baseEnd_714207] using wordTrace_append hprefix tailTrace_714207
  have hstable : (prefixWord ++ tailWord_714207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714207).length < 2 ^ (prefixWord ++ tailWord_714207).sum := by decide
  have hdescent : baseEnd_714207 < baseStart_714207 := by decide
  rcases family_descends (prefixWord ++ tailWord_714207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714209 : List Nat := [1, 2, 3, 1, 2, 3, 3, 2, 5]
def baseStart_714209 : Nat := 118140960795 + 714209 * 2 ^ 59
def prefixEnd_714209 : Nat := 4983230072969 + 3 ^ 40 * 714209 * 2
def baseEnd_714209 : Nat := 81496112170466975045093

theorem tailTrace_714209 : CollatzResearch.WordTrace tailWord_714209 prefixEnd_714209 81496112170466975045093 := by
  unfold tailWord_714209
  simp only [CollatzResearch.WordTrace]
  refine ⟨26049342269550245031209681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17366228179700163354139787 26049342269550245031209681)
  ·
    refine ⟨19537006702162683773407261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26049342269550245031209681 19537006702162683773407261)
    ·
      refine ⟨7326377513311006415027723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19537006702162683773407261 7326377513311006415027723)
      ·
        refine ⟨10989566269966509622541585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7326377513311006415027723 10989566269966509622541585)
        ·
          refine ⟨8242174702474882216906189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10989566269966509622541585 8242174702474882216906189)
          ·
            refine ⟨3090815513428080831339821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8242174702474882216906189 3090815513428080831339821)
            ·
              refine ⟨1159055817535530311752433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3090815513428080831339821 1159055817535530311752433)
              ·
                refine ⟨869291863151647733814325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1159055817535530311752433 869291863151647733814325)
                ·
                  refine ⟨81496112170466975045093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 869291863151647733814325 81496112170466975045093)
                  ·
                    rfl

theorem cell22_714209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_714209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714209 prefixEnd_714209 := by exact prefixLift 714209
  have htrace : WordTrace (prefixWord ++ tailWord_714209) baseStart_714209 baseEnd_714209 := by
    simpa [prefixWord, tailWord_714209, baseEnd_714209] using wordTrace_append hprefix tailTrace_714209
  have hstable : (prefixWord ++ tailWord_714209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714209).length < 2 ^ (prefixWord ++ tailWord_714209).sum := by decide
  have hdescent : baseEnd_714209 < baseStart_714209 := by decide
  rcases family_descends (prefixWord ++ tailWord_714209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714213 : List Nat := [1, 3, 1, 5, 1, 1, 2, 4, 1, 3]
def baseStart_714213 : Nat := 118140960795 + 714213 * 2 ^ 59
def prefixEnd_714213 : Nat := 4983230072969 + 3 ^ 40 * 714213 * 2
def baseEnd_714213 : Nat := 244489705793146248035267

theorem tailTrace_714213 : CollatzResearch.WordTrace tailWord_714213 prefixEnd_714213 244489705793146248035267 := by
  unfold tailWord_714213
  simp only [CollatzResearch.WordTrace]
  refine ⟨26049488161535753714355293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17366325441023835809570195 26049488161535753714355293)
  ·
    refine ⟨9768558060575907642883235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26049488161535753714355293 9768558060575907642883235)
    ·
      refine ⟨14652837090863861464324853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9768558060575907642883235 14652837090863861464324853)
      ·
        refine ⟨1373703477268487012280455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14652837090863861464324853 1373703477268487012280455)
        ·
          refine ⟨2060555215902730518420683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373703477268487012280455 2060555215902730518420683)
          ·
            refine ⟨3090832823854095777631025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060555215902730518420683 3090832823854095777631025)
            ·
              refine ⟨2318124617890571833223269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090832823854095777631025 2318124617890571833223269)
              ·
                refine ⟨434648365854482218729363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2318124617890571833223269 434648365854482218729363)
                ·
                  refine ⟨651972548781723328094045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434648365854482218729363 651972548781723328094045)
                  ·
                    refine ⟨244489705793146248035267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 651972548781723328094045 244489705793146248035267)
                    ·
                      rfl

theorem cell22_714213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_714213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714213 prefixEnd_714213 := by exact prefixLift 714213
  have htrace : WordTrace (prefixWord ++ tailWord_714213) baseStart_714213 baseEnd_714213 := by
    simpa [prefixWord, tailWord_714213, baseEnd_714213] using wordTrace_append hprefix tailTrace_714213
  have hstable : (prefixWord ++ tailWord_714213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714213).length < 2 ^ (prefixWord ++ tailWord_714213).sum := by decide
  have hdescent : baseEnd_714213 < baseStart_714213 := by decide
  rcases family_descends (prefixWord ++ tailWord_714213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714365 : List Nat := [1, 4, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_714365 : Nat := 118140960795 + 714365 * 2 ^ 59
def prefixEnd_714365 : Nat := 4983230072969 + 3 ^ 40 * 714365 * 2
def baseEnd_714365 : Nat := 244541738499468518234801

theorem tailTrace_714365 : CollatzResearch.WordTrace tailWord_714365 prefixEnd_714365 244541738499468518234801 := by
  unfold tailWord_714365
  simp only [CollatzResearch.WordTrace]
  refine ⟨26055032056985083673888549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17370021371323389115925699 26055032056985083673888549)
  ·
    refine ⟨4885318510684703188854103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26055032056985083673888549 4885318510684703188854103)
    ·
      refine ⟨7327977766027054783281155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4885318510684703188854103 7327977766027054783281155)
      ·
        refine ⟨10991966649040582174921733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7327977766027054783281155 10991966649040582174921733)
        ·
          refine ⟨2060993746695109157797825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10991966649040582174921733 2060993746695109157797825)
          ·
            refine ⟨1545745310021331868348369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2060993746695109157797825 1545745310021331868348369)
            ·
              refine ⟨1159308982515998901261277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1545745310021331868348369 1159308982515998901261277)
              ·
                refine ⟨434740868443499587972979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1159308982515998901261277 434740868443499587972979)
                ·
                  refine ⟨652111302665249381959469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 434740868443499587972979 652111302665249381959469)
                  ·
                    refine ⟨244541738499468518234801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 652111302665249381959469 244541738499468518234801)
                    ·
                      rfl

theorem cell22_714365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_714365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714365 prefixEnd_714365 := by exact prefixLift 714365
  have htrace : WordTrace (prefixWord ++ tailWord_714365) baseStart_714365 baseEnd_714365 := by
    simpa [prefixWord, tailWord_714365, baseEnd_714365] using wordTrace_append hprefix tailTrace_714365
  have hstable : (prefixWord ++ tailWord_714365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714365).length < 2 ^ (prefixWord ++ tailWord_714365).sum := by decide
  have hdescent : baseEnd_714365 < baseStart_714365 := by decide
  rcases family_descends (prefixWord ++ tailWord_714365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714378 : List Nat := [3, 1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_714378 : Nat := 118140960795 + 714378 * 2 ^ 59
def prefixEnd_714378 : Nat := 4983230072969 + 3 ^ 40 * 714378 * 2
def baseEnd_714378 : Nat := 81515396221713605886587

theorem tailTrace_714378 : CollatzResearch.WordTrace tailWord_714378 prefixEnd_714378 81515396221713605886587 := by
  unfold tailWord_714378
  simp only [CollatzResearch.WordTrace]
  refine ⟨6513876551484496723527947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17370337470625324596074525 6513876551484496723527947)
  ·
    refine ⟨9770814827226745085291921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6513876551484496723527947 9770814827226745085291921)
    ·
      refine ⟨7328111120420058813968941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9770814827226745085291921 7328111120420058813968941)
      ·
        refine ⟨2748041670157522055238353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7328111120420058813968941 2748041670157522055238353)
        ·
          refine ⟨2061031252618141541428765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2748041670157522055238353 2061031252618141541428765)
          ·
            refine ⟨772886719731803078035787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2061031252618141541428765 772886719731803078035787)
            ·
              refine ⟨1159330079597704617053681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 772886719731803078035787 1159330079597704617053681)
              ·
                refine ⟨869497559698278462790261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1159330079597704617053681 869497559698278462790261)
                ·
                  refine ⟨81515396221713605886587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 869497559698278462790261 81515396221713605886587)
                  ·
                    rfl

theorem cell22_714378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_714378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714378 prefixEnd_714378 := by exact prefixLift 714378
  have htrace : WordTrace (prefixWord ++ tailWord_714378) baseStart_714378 baseEnd_714378 := by
    simpa [prefixWord, tailWord_714378, baseEnd_714378] using wordTrace_append hprefix tailTrace_714378
  have hstable : (prefixWord ++ tailWord_714378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714378).length < 2 ^ (prefixWord ++ tailWord_714378).sum := by decide
  have hdescent : baseEnd_714378 < baseStart_714378 := by decide
  rcases family_descends (prefixWord ++ tailWord_714378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714419 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 1, 6]
def baseStart_714419 : Nat := 118140960795 + 714419 * 2 ^ 59
def prefixEnd_714419 : Nat := 4983230072969 + 3 ^ 40 * 714419 * 2
def baseEnd_714419 : Nat := 244560223803030377384635

theorem tailTrace_714419 : CollatzResearch.WordTrace tailWord_714419 prefixEnd_714419 244560223803030377384635 := by
  unfold tailWord_714419
  simp only [CollatzResearch.WordTrace]
  refine ⟨26057001598789450896354311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17371334399192967264236207 26057001598789450896354311)
  ·
    refine ⟨39085502398184176344531467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26057001598789450896354311 39085502398184176344531467)
    ·
      refine ⟨58628253597276264516797201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39085502398184176344531467 58628253597276264516797201)
      ·
        refine ⟨43971190197957198387597901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58628253597276264516797201 43971190197957198387597901)
        ·
          refine ⟨16489196324233949395349213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43971190197957198387597901 16489196324233949395349213)
          ·
            refine ⟨6183448621587731023255955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16489196324233949395349213 6183448621587731023255955)
            ·
              refine ⟨9275172932381596534883933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6183448621587731023255955 9275172932381596534883933)
              ·
                refine ⟨3478189849643098700581475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9275172932381596534883933 3478189849643098700581475)
                ·
                  refine ⟨5217284774464648050872213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3478189849643098700581475 5217284774464648050872213)
                  ·
                    refine ⟨244560223803030377384635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5217284774464648050872213 244560223803030377384635)
                    ·
                      rfl

theorem cell22_714419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_714419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714419 prefixEnd_714419 := by exact prefixLift 714419
  have htrace : WordTrace (prefixWord ++ tailWord_714419) baseStart_714419 baseEnd_714419 := by
    simpa [prefixWord, tailWord_714419, baseEnd_714419] using wordTrace_append hprefix tailTrace_714419
  have hstable : (prefixWord ++ tailWord_714419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714419).length < 2 ^ (prefixWord ++ tailWord_714419).sum := by decide
  have hdescent : baseEnd_714419 < baseStart_714419 := by decide
  rcases family_descends (prefixWord ++ tailWord_714419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714423 : List Nat := [1, 1, 3, 1, 5, 1, 3, 3, 4]
def baseStart_714423 : Nat := 118140960795 + 714423 * 2 ^ 59
def prefixEnd_714423 : Nat := 4983230072969 + 3 ^ 40 * 714423 * 2
def baseEnd_714423 : Nat := 81520531028258566761541

theorem tailTrace_714423 : CollatzResearch.WordTrace tailWord_714423 prefixEnd_714423 81520531028258566761541 := by
  unfold tailWord_714423
  simp only [CollatzResearch.WordTrace]
  refine ⟨26057147490774959579499923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17371431660516639719666615 26057147490774959579499923)
  ·
    refine ⟨39085721236162439369249885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26057147490774959579499923 39085721236162439369249885)
    ·
      refine ⟨14657145463560914763468707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39085721236162439369249885 14657145463560914763468707)
      ·
        refine ⟨21985718195341372145203061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14657145463560914763468707 21985718195341372145203061)
        ·
          refine ⟨2061161080813253638612787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21985718195341372145203061 2061161080813253638612787)
          ·
            refine ⟨3091741621219880457919181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061161080813253638612787 3091741621219880457919181)
            ·
              refine ⟨1159403107957455171719693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3091741621219880457919181 1159403107957455171719693)
              ·
                refine ⟨434776165484045689394885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1159403107957455171719693 434776165484045689394885)
                ·
                  refine ⟨81520531028258566761541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 434776165484045689394885 81520531028258566761541)
                  ·
                    rfl

theorem cell22_714423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 4].length) (baseStart_714423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714423 prefixEnd_714423 := by exact prefixLift 714423
  have htrace : WordTrace (prefixWord ++ tailWord_714423) baseStart_714423 baseEnd_714423 := by
    simpa [prefixWord, tailWord_714423, baseEnd_714423] using wordTrace_append hprefix tailTrace_714423
  have hstable : (prefixWord ++ tailWord_714423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714423).length < 2 ^ (prefixWord ++ tailWord_714423).sum := by decide
  have hdescent : baseEnd_714423 < baseStart_714423 := by decide
  rcases family_descends (prefixWord ++ tailWord_714423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714556 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_714556 : Nat := 118140960795 + 714556 * 2 ^ 59
def prefixEnd_714556 : Nat := 4983230072969 + 3 ^ 40 * 714556 * 2
def baseEnd_714556 : Nat := 244607121702807686709215

theorem tailTrace_714556 : CollatzResearch.WordTrace tailWord_714556 prefixEnd_714556 244607121702807686709215 := by
  unfold tailWord_714556
  simp only [CollatzResearch.WordTrace]
  refine ⟨13030999199646561647045761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17374665599528748862727681 13030999199646561647045761)
  ·
    refine ⟨9773249399734921235284321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13030999199646561647045761 9773249399734921235284321)
    ·
      refine ⟨7329937049801190926463241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9773249399734921235284321 7329937049801190926463241)
      ·
        refine ⟨5497452787350893194847431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7329937049801190926463241 5497452787350893194847431)
        ·
          refine ⟨8246179181026339792271147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5497452787350893194847431 8246179181026339792271147)
          ·
            refine ⟨12369268771539509688406721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8246179181026339792271147 12369268771539509688406721)
            ·
              refine ⟨9276951578654632266305041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12369268771539509688406721 9276951578654632266305041)
              ·
                refine ⟨6957713683990974199728781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9276951578654632266305041 6957713683990974199728781)
                ·
                  refine ⟨2609142631496615324898293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6957713683990974199728781 2609142631496615324898293)
                  ·
                    refine ⟨244607121702807686709215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2609142631496615324898293 244607121702807686709215)
                    ·
                      rfl

theorem cell22_714556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_714556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714556 prefixEnd_714556 := by exact prefixLift 714556
  have htrace : WordTrace (prefixWord ++ tailWord_714556) baseStart_714556 baseEnd_714556 := by
    simpa [prefixWord, tailWord_714556, baseEnd_714556] using wordTrace_append hprefix tailTrace_714556
  have hstable : (prefixWord ++ tailWord_714556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714556).length < 2 ^ (prefixWord ++ tailWord_714556).sum := by decide
  have hdescent : baseEnd_714556 < baseStart_714556 := by decide
  rcases family_descends (prefixWord ++ tailWord_714556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714558 : List Nat := [4, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_714558 : Nat := 118140960795 + 714558 * 2 ^ 59
def prefixEnd_714558 : Nat := 4983230072969 + 3 ^ 40 * 714558 * 2
def baseEnd_714558 : Nat := 81535935447893449386403

theorem tailTrace_714558 : CollatzResearch.WordTrace tailWord_714558 prefixEnd_714558 81535935447893449386403 := by
  unfold tailWord_714558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3257758918160734704458041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17374714230190585090442885 3257758918160734704458041)
  ·
    refine ⟨2443319188620551028343531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3257758918160734704458041 2443319188620551028343531)
    ·
      refine ⟨3664978782930826542515297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2443319188620551028343531 3664978782930826542515297)
      ·
        refine ⟨2748734087198119906886473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3664978782930826542515297 2748734087198119906886473)
        ·
          refine ⟨2061550565398589930164855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2748734087198119906886473 2061550565398589930164855)
          ·
            refine ⟨3092325848097884895247283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2061550565398589930164855 3092325848097884895247283)
            ·
              refine ⟨4638488772146827342870925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3092325848097884895247283 4638488772146827342870925)
              ·
                refine ⟨1739433289555060253576597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4638488772146827342870925 1739433289555060253576597)
                ·
                  refine ⟨81535935447893449386403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1739433289555060253576597 81535935447893449386403)
                  ·
                    rfl

theorem cell22_714558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_714558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714558 prefixEnd_714558 := by exact prefixLift 714558
  have htrace : WordTrace (prefixWord ++ tailWord_714558) baseStart_714558 baseEnd_714558 := by
    simpa [prefixWord, tailWord_714558, baseEnd_714558] using wordTrace_append hprefix tailTrace_714558
  have hstable : (prefixWord ++ tailWord_714558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714558).length < 2 ^ (prefixWord ++ tailWord_714558).sum := by decide
  have hdescent : baseEnd_714558 < baseStart_714558 := by decide
  rcases family_descends (prefixWord ++ tailWord_714558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714586 : List Nat := [3, 1, 1, 2, 1, 3, 3, 8]
def baseStart_714586 : Nat := 118140960795 + 714586 * 2 ^ 59
def prefixEnd_714586 : Nat := 4983230072969 + 3 ^ 40 * 714586 * 2
def baseEnd_714586 : Nat := 27179710146210845384347

theorem tailTrace_714586 : CollatzResearch.WordTrace tailWord_714586 prefixEnd_714586 27179710146210845384347 := by
  unfold tailWord_714586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6515773147296109604420903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17375395059456292278455741 6515773147296109604420903)
  ·
    refine ⟨9773659720944164406631355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6515773147296109604420903 9773659720944164406631355)
    ·
      refine ⟨14660489581416246609947033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9773659720944164406631355 14660489581416246609947033)
      ·
        refine ⟨10995367186062184957460275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14660489581416246609947033 10995367186062184957460275)
        ·
          refine ⟨16493050779093277436190413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10995367186062184957460275 16493050779093277436190413)
          ·
            refine ⟨6184894042159979038571405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16493050779093277436190413 6184894042159979038571405)
            ·
              refine ⟨2319335265809992139464277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6184894042159979038571405 2319335265809992139464277)
              ·
                refine ⟨27179710146210845384347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2319335265809992139464277 27179710146210845384347)
                ·
                  rfl

theorem cell22_714586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_714586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714586 prefixEnd_714586 := by exact prefixLift 714586
  have htrace : WordTrace (prefixWord ++ tailWord_714586) baseStart_714586 baseEnd_714586 := by
    simpa [prefixWord, tailWord_714586, baseEnd_714586] using wordTrace_append hprefix tailTrace_714586
  have hstable : (prefixWord ++ tailWord_714586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714586).length < 2 ^ (prefixWord ++ tailWord_714586).sum := by decide
  have hdescent : baseEnd_714586 < baseStart_714586 := by decide
  rcases family_descends (prefixWord ++ tailWord_714586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714716 : List Nat := [2, 2, 6, 1, 1, 2, 1, 2, 5]
def baseStart_714716 : Nat := 118140960795 + 714716 * 2 ^ 59
def prefixEnd_714716 : Nat := 4983230072969 + 3 ^ 40 * 714716 * 2
def baseEnd_714716 : Nat := 81553964324206867569575

theorem tailTrace_714716 : CollatzResearch.WordTrace tailWord_714716 prefixEnd_714716 81553964324206867569575 := by
  unfold tailWord_714716
  simp only [CollatzResearch.WordTrace]
  refine ⟨13033917039356735309958001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17378556052475647079944001 13033917039356735309958001)
  ·
    refine ⟨9775437779517551482468501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13033917039356735309958001 9775437779517551482468501)
    ·
      refine ⟨458223645914885225740711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9775437779517551482468501 458223645914885225740711)
      ·
        refine ⟨687335468872327838611067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458223645914885225740711 687335468872327838611067)
        ·
          refine ⟨1031003203308491757916601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 687335468872327838611067 1031003203308491757916601)
          ·
            refine ⟨773252402481368818437451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031003203308491757916601 773252402481368818437451)
            ·
              refine ⟨1159878603722053227656177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773252402481368818437451 1159878603722053227656177)
              ·
                refine ⟨869908952791539920742133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1159878603722053227656177 869908952791539920742133)
                ·
                  refine ⟨81553964324206867569575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 869908952791539920742133 81553964324206867569575)
                  ·
                    rfl

theorem cell22_714716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_714716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714716 prefixEnd_714716 := by exact prefixLift 714716
  have htrace : WordTrace (prefixWord ++ tailWord_714716) baseStart_714716 baseEnd_714716 := by
    simpa [prefixWord, tailWord_714716, baseEnd_714716] using wordTrace_append hprefix tailTrace_714716
  have hstable : (prefixWord ++ tailWord_714716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714716).length < 2 ^ (prefixWord ++ tailWord_714716).sum := by decide
  have hdescent : baseEnd_714716 < baseStart_714716 := by decide
  rcases family_descends (prefixWord ++ tailWord_714716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714753 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_714753 : Nat := 118140960795 + 714753 * 2 ^ 59
def prefixEnd_714753 : Nat := 4983230072969 + 3 ^ 40 * 714753 * 2
def baseEnd_714753 : Nat := 244674558828764839533611

theorem tailTrace_714753 : CollatzResearch.WordTrace tailWord_714753 prefixEnd_714753 244674558828764839533611 := by
  unfold tailWord_714753
  simp only [CollatzResearch.WordTrace]
  refine ⟨26069183579579425939012913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17379455719719617292675275 26069183579579425939012913)
  ·
    refine ⟨19551887684684569454259685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26069183579579425939012913 19551887684684569454259685)
    ·
      refine ⟨3665978940878356772673691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19551887684684569454259685 3665978940878356772673691)
      ·
        refine ⟨5498968411317535159010537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3665978940878356772673691 5498968411317535159010537)
        ·
          refine ⟨4124226308488151369257903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5498968411317535159010537 4124226308488151369257903)
          ·
            refine ⟨6186339462732227053886855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4124226308488151369257903 6186339462732227053886855)
            ·
              refine ⟨9279509194098340580830283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6186339462732227053886855 9279509194098340580830283)
              ·
                refine ⟨13919263791147510871245425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9279509194098340580830283 13919263791147510871245425)
                ·
                  refine ⟨10439447843360633153434069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13919263791147510871245425 10439447843360633153434069)
                  ·
                    refine ⟨244674558828764839533611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10439447843360633153434069 244674558828764839533611)
                    ·
                      rfl

theorem cell22_714753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_714753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714753 prefixEnd_714753 := by exact prefixLift 714753
  have htrace : WordTrace (prefixWord ++ tailWord_714753) baseStart_714753 baseEnd_714753 := by
    simpa [prefixWord, tailWord_714753, baseEnd_714753] using wordTrace_append hprefix tailTrace_714753
  have hstable : (prefixWord ++ tailWord_714753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714753).length < 2 ^ (prefixWord ++ tailWord_714753).sum := by decide
  have hdescent : baseEnd_714753 < baseStart_714753 := by decide
  rcases family_descends (prefixWord ++ tailWord_714753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714783 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 7]
def baseStart_714783 : Nat := 118140960795 + 714783 * 2 ^ 59
def prefixEnd_714783 : Nat := 4983230072969 + 3 ^ 40 * 714783 * 2
def baseEnd_714783 : Nat := 81561609480618253761173

theorem tailTrace_714783 : CollatzResearch.WordTrace tailWord_714783 prefixEnd_714783 81561609480618253761173 := by
  unfold tailWord_714783
  simp only [CollatzResearch.WordTrace]
  refine ⟨26070277769470741062605003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17380185179647160708403335 26070277769470741062605003)
  ·
    refine ⟨39105416654206111593907505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26070277769470741062605003 39105416654206111593907505)
    ·
      refine ⟨29329062490654583695430629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39105416654206111593907505 29329062490654583695430629)
      ·
        refine ⟨5499199216997734442893243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29329062490654583695430629 5499199216997734442893243)
        ·
          refine ⟨8248798825496601664339865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5499199216997734442893243 8248798825496601664339865)
          ·
            refine ⟨6186599119122451248254899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8248798825496601664339865 6186599119122451248254899)
            ·
              refine ⟨9279898678683676872382349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6186599119122451248254899 9279898678683676872382349)
              ·
                refine ⟨3479962004506378827143381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9279898678683676872382349 3479962004506378827143381)
                ·
                  refine ⟨81561609480618253761173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3479962004506378827143381 81561609480618253761173)
                  ·
                    rfl

theorem cell22_714783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 7].length) (baseStart_714783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714783 prefixEnd_714783 := by exact prefixLift 714783
  have htrace : WordTrace (prefixWord ++ tailWord_714783) baseStart_714783 baseEnd_714783 := by
    simpa [prefixWord, tailWord_714783, baseEnd_714783] using wordTrace_append hprefix tailTrace_714783
  have hstable : (prefixWord ++ tailWord_714783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714783).length < 2 ^ (prefixWord ++ tailWord_714783).sum := by decide
  have hdescent : baseEnd_714783 < baseStart_714783 := by decide
  rcases family_descends (prefixWord ++ tailWord_714783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714800 : List Nat := [2, 1, 1, 1, 2, 6, 1, 3, 5]
def baseStart_714800 : Nat := 118140960795 + 714800 * 2 ^ 59
def prefixEnd_714800 : Nat := 4983230072969 + 3 ^ 40 * 714800 * 2
def baseEnd_714800 : Nat := 81563549296424127869489

theorem tailTrace_714800 : CollatzResearch.WordTrace tailWord_714800 prefixEnd_714800 81563549296424127869489 := by
  unfold tailWord_714800
  simp only [CollatzResearch.WordTrace]
  refine ⟨13035448905204576482986927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17380598540272768643982569 13035448905204576482986927)
  ·
    refine ⟨19553173357806864724480391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13035448905204576482986927 19553173357806864724480391)
    ·
      refine ⟨29329760036710297086720587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19553173357806864724480391 29329760036710297086720587)
      ·
        refine ⟨43994640055065445630080881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29329760036710297086720587 43994640055065445630080881)
        ·
          refine ⟨32995980041299084222560661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43994640055065445630080881 32995980041299084222560661)
          ·
            refine ⟨1546686564435894572932531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 32995980041299084222560661 1546686564435894572932531)
            ·
              refine ⟨2320029846653841859398797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546686564435894572932531 2320029846653841859398797)
              ·
                refine ⟨870011192495190697274549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2320029846653841859398797 870011192495190697274549)
                ·
                  refine ⟨81563549296424127869489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 870011192495190697274549 81563549296424127869489)
                  ·
                    rfl

theorem cell22_714800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_714800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714800 prefixEnd_714800 := by exact prefixLift 714800
  have htrace : WordTrace (prefixWord ++ tailWord_714800) baseStart_714800 baseEnd_714800 := by
    simpa [prefixWord, tailWord_714800, baseEnd_714800] using wordTrace_append hprefix tailTrace_714800
  have hstable : (prefixWord ++ tailWord_714800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714800).length < 2 ^ (prefixWord ++ tailWord_714800).sum := by decide
  have hdescent : baseEnd_714800 < baseStart_714800 := by decide
  rcases family_descends (prefixWord ++ tailWord_714800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714838 : List Nat := [5, 2, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_714838 : Nat := 118140960795 + 714838 * 2 ^ 59
def prefixEnd_714838 : Nat := 4983230072969 + 3 ^ 40 * 714838 * 2
def baseEnd_714838 : Nat := 244703656065852951158351

theorem tailTrace_714838 : CollatzResearch.WordTrace tailWord_714838 prefixEnd_714838 244703656065852951158351 := by
  unfold tailWord_714838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629517736516967840991073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17381522522847656970571445 1629517736516967840991073)
  ·
    refine ⟨1222138302387725880743305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1629517736516967840991073 1222138302387725880743305)
    ·
      refine ⟨916603726790794410557479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1222138302387725880743305 916603726790794410557479)
      ·
        refine ⟨1374905590186191615836219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916603726790794410557479 1374905590186191615836219)
        ·
          refine ⟨2062358385279287423754329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1374905590186191615836219 2062358385279287423754329)
          ·
            refine ⟨1546768788959465567815747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2062358385279287423754329 1546768788959465567815747)
            ·
              refine ⟨2320153183439198351723621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546768788959465567815747 2320153183439198351723621)
              ·
                refine ⟨435028721894849690948179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2320153183439198351723621 435028721894849690948179)
                ·
                  refine ⟨652543082842274536422269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435028721894849690948179 652543082842274536422269)
                  ·
                    refine ⟨244703656065852951158351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 652543082842274536422269 244703656065852951158351)
                    ·
                      rfl

theorem cell22_714838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_714838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714838 prefixEnd_714838 := by exact prefixLift 714838
  have htrace : WordTrace (prefixWord ++ tailWord_714838) baseStart_714838 baseEnd_714838 := by
    simpa [prefixWord, tailWord_714838, baseEnd_714838] using wordTrace_append hprefix tailTrace_714838
  have hstable : (prefixWord ++ tailWord_714838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714838).length < 2 ^ (prefixWord ++ tailWord_714838).sum := by decide
  have hdescent : baseEnd_714838 < baseStart_714838 := by decide
  rcases family_descends (prefixWord ++ tailWord_714838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714860 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_714860 : Nat := 118140960795 + 714860 * 2 ^ 59
def prefixEnd_714860 : Nat := 4983230072969 + 3 ^ 40 * 714860 * 2
def baseEnd_714860 : Nat := 244711187115452227108283

theorem tailTrace_714860 : CollatzResearch.WordTrace tailWord_714860 prefixEnd_714860 244711187115452227108283 := by
  unfold tailWord_714860
  simp only [CollatzResearch.WordTrace]
  refine ⟨13036543095095891606579017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17382057460127855475438689 13036543095095891606579017)
  ·
    refine ⟨9777407321321918704934263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13036543095095891606579017 9777407321321918704934263)
    ·
      refine ⟨14666110981982878057401395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9777407321321918704934263 14666110981982878057401395)
      ·
        refine ⟨21999166472974317086102093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14666110981982878057401395 21999166472974317086102093)
        ·
          refine ⟨8249687427365368907288285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21999166472974317086102093 8249687427365368907288285)
          ·
            refine ⟨3093632785262013340233107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8249687427365368907288285 3093632785262013340233107)
            ·
              refine ⟨4640449177893020010349661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093632785262013340233107 4640449177893020010349661)
              ·
                refine ⟨1740168441709882503881123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4640449177893020010349661 1740168441709882503881123)
                ·
                  refine ⟨2610252662564823755821685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1740168441709882503881123 2610252662564823755821685)
                  ·
                    refine ⟨244711187115452227108283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2610252662564823755821685 244711187115452227108283)
                    ·
                      rfl

theorem cell22_714860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_714860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714860 prefixEnd_714860 := by exact prefixLift 714860
  have htrace : WordTrace (prefixWord ++ tailWord_714860) baseStart_714860 baseEnd_714860 := by
    simpa [prefixWord, tailWord_714860, baseEnd_714860] using wordTrace_append hprefix tailTrace_714860
  have hstable : (prefixWord ++ tailWord_714860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714860).length < 2 ^ (prefixWord ++ tailWord_714860).sum := by decide
  have hdescent : baseEnd_714860 < baseStart_714860 := by decide
  rcases family_descends (prefixWord ++ tailWord_714860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714881 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 1, 4]
def baseStart_714881 : Nat := 118140960795 + 714881 * 2 ^ 59
def prefixEnd_714881 : Nat := 4983230072969 + 3 ^ 40 * 714881 * 2
def baseEnd_714881 : Nat := 244718375844615172333219

theorem tailTrace_714881 : CollatzResearch.WordTrace tailWord_714881 prefixEnd_714881 244718375844615172333219 := by
  unfold tailWord_714881
  simp only [CollatzResearch.WordTrace]
  refine ⟨26073852123115703799672497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17382568082077135866448331 26073852123115703799672497)
  ·
    refine ⟨19555389092336777849754373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26073852123115703799672497 19555389092336777849754373)
    ·
      refine ⟨3666635454813145846828945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19555389092336777849754373 3666635454813145846828945)
      ·
        refine ⟨2749976591109859385121709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3666635454813145846828945 2749976591109859385121709)
        ·
          refine ⟨1031241221666197269420641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2749976591109859385121709 1031241221666197269420641)
          ·
            refine ⟨773430916249647952065481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1031241221666197269420641 773430916249647952065481)
            ·
              refine ⟨580073187187235964049111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773430916249647952065481 580073187187235964049111)
              ·
                refine ⟨870109780780853946073667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580073187187235964049111 870109780780853946073667)
                ·
                  refine ⟨1305164671171280919110501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870109780780853946073667 1305164671171280919110501)
                  ·
                    refine ⟨244718375844615172333219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1305164671171280919110501 244718375844615172333219)
                    ·
                      rfl

theorem cell22_714881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_714881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714881 prefixEnd_714881 := by exact prefixLift 714881
  have htrace : WordTrace (prefixWord ++ tailWord_714881) baseStart_714881 baseEnd_714881 := by
    simpa [prefixWord, tailWord_714881, baseEnd_714881] using wordTrace_append hprefix tailTrace_714881
  have hstable : (prefixWord ++ tailWord_714881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714881).length < 2 ^ (prefixWord ++ tailWord_714881).sum := by decide
  have hdescent : baseEnd_714881 < baseStart_714881 := by decide
  rcases family_descends (prefixWord ++ tailWord_714881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714890 : List Nat := [3, 1, 2, 3, 1, 3, 9]
def baseStart_714890 : Nat := 118140960795 + 714890 * 2 ^ 59
def prefixEnd_714890 : Nat := 4983230072969 + 3 ^ 40 * 714890 * 2
def baseEnd_714890 : Nat := 9063757656612672179933

theorem tailTrace_714890 : CollatzResearch.WordTrace tailWord_714890 prefixEnd_714890 9063757656612672179933 := by
  unfold tailWord_714890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6518545095020774584187531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17382786920055398891166749 6518545095020774584187531)
  ·
    refine ⟨9777817642531161876281297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6518545095020774584187531 9777817642531161876281297)
    ·
      refine ⟨7333363231898371407210973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9777817642531161876281297 7333363231898371407210973)
      ·
        refine ⟨2750011211961889277704115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7333363231898371407210973 2750011211961889277704115)
        ·
          refine ⟨4125016817942833916556173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750011211961889277704115 4125016817942833916556173)
          ·
            refine ⟨1546881306728562718708565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4125016817942833916556173 1546881306728562718708565)
            ·
              refine ⟨9063757656612672179933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1546881306728562718708565 9063757656612672179933)
              ·
                rfl

theorem cell22_714890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 9].length) (baseStart_714890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714890 prefixEnd_714890 := by exact prefixLift 714890
  have htrace : WordTrace (prefixWord ++ tailWord_714890) baseStart_714890 baseEnd_714890 := by
    simpa [prefixWord, tailWord_714890, baseEnd_714890] using wordTrace_append hprefix tailTrace_714890
  have hstable : (prefixWord ++ tailWord_714890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714890).length < 2 ^ (prefixWord ++ tailWord_714890).sum := by decide
  have hdescent : baseEnd_714890 < baseStart_714890 := by decide
  rcases family_descends (prefixWord ++ tailWord_714890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714894 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 4, 3]
def baseStart_714894 : Nat := 118140960795 + 714894 * 2 ^ 59
def prefixEnd_714894 : Nat := 4983230072969 + 3 ^ 40 * 714894 * 2
def baseEnd_714894 : Nat := 244722826010287471758179

theorem tailTrace_714894 : CollatzResearch.WordTrace tailWord_714894 prefixEnd_714894 244722826010287471758179 := by
  unfold tailWord_714894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3259290784008575877486967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17382884181379071346597157 3259290784008575877486967)
  ·
    refine ⟨4888936176012863816230451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3259290784008575877486967 4888936176012863816230451)
    ·
      refine ⟨7333404264019295724345677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4888936176012863816230451 7333404264019295724345677)
      ·
        refine ⟨2750026599007235896629629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7333404264019295724345677 2750026599007235896629629)
        ·
          refine ⟨1031259974627713461236111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2750026599007235896629629 1031259974627713461236111)
          ·
            refine ⟨1546889961941570191854167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031259974627713461236111 1546889961941570191854167)
            ·
              refine ⟨2320334942912355287781251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1546889961941570191854167 2320334942912355287781251)
              ·
                refine ⟨3480502414368532931671877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2320334942912355287781251 3480502414368532931671877)
                ·
                  refine ⟨652594202694099924688477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3480502414368532931671877 652594202694099924688477)
                  ·
                    refine ⟨244722826010287471758179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 652594202694099924688477 244722826010287471758179)
                    ·
                      rfl

theorem cell22_714894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_714894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714894 prefixEnd_714894 := by exact prefixLift 714894
  have htrace : WordTrace (prefixWord ++ tailWord_714894) baseStart_714894 baseEnd_714894 := by
    simpa [prefixWord, tailWord_714894, baseEnd_714894] using wordTrace_append hprefix tailTrace_714894
  have hstable : (prefixWord ++ tailWord_714894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714894).length < 2 ^ (prefixWord ++ tailWord_714894).sum := by decide
  have hdescent : baseEnd_714894 < baseStart_714894 := by decide
  rcases family_descends (prefixWord ++ tailWord_714894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714911 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 2, 3]
def baseStart_714911 : Nat := 118140960795 + 714911 * 2 ^ 59
def prefixEnd_714911 : Nat := 4983230072969 + 3 ^ 40 * 714911 * 2
def baseEnd_714911 : Nat := 244728645457705094083127

theorem tailTrace_714911 : CollatzResearch.WordTrace tailWord_714911 prefixEnd_714911 244728645457705094083127 := by
  unfold tailWord_714911
  simp only [CollatzResearch.WordTrace]
  refine ⟨26074946313007018923264587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17383297542004679282176391 26074946313007018923264587)
  ·
    refine ⟨39112419469510528384896881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26074946313007018923264587 39112419469510528384896881)
    ·
      refine ⟨29334314602132896288672661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39112419469510528384896881 29334314602132896288672661)
      ·
        refine ⟨1375045996974979513531531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29334314602132896288672661 1375045996974979513531531)
        ·
          refine ⟨2062568995462469270297297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1375045996974979513531531 2062568995462469270297297)
          ·
            refine ⟨1546926746596851952722973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2062568995462469270297297 1546926746596851952722973)
            ·
              refine ⟨580097529973819482271115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1546926746596851952722973 580097529973819482271115)
              ·
                refine ⟨870146294960729223406673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580097529973819482271115 870146294960729223406673)
                ·
                  refine ⟨652609721220546917555005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 870146294960729223406673 652609721220546917555005)
                  ·
                    refine ⟨244728645457705094083127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 652609721220546917555005 244728645457705094083127)
                    ·
                      rfl

theorem cell22_714911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 2, 3].length) (baseStart_714911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714911 prefixEnd_714911 := by exact prefixLift 714911
  have htrace : WordTrace (prefixWord ++ tailWord_714911) baseStart_714911 baseEnd_714911 := by
    simpa [prefixWord, tailWord_714911, baseEnd_714911] using wordTrace_append hprefix tailTrace_714911
  have hstable : (prefixWord ++ tailWord_714911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714911).length < 2 ^ (prefixWord ++ tailWord_714911).sum := by decide
  have hdescent : baseEnd_714911 < baseStart_714911 := by decide
  rcases family_descends (prefixWord ++ tailWord_714911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714935 : List Nat := [1, 1, 3, 1, 4, 2, 1, 2, 7]
def baseStart_714935 : Nat := 118140960795 + 714935 * 2 ^ 59
def prefixEnd_714935 : Nat := 4983230072969 + 3 ^ 40 * 714935 * 2
def baseEnd_714935 : Nat := 81578953716059010494351

theorem tailTrace_714935 : CollatzResearch.WordTrace tailWord_714935 prefixEnd_714935 81578953716059010494351 := by
  unfold tailWord_714935
  simp only [CollatzResearch.WordTrace]
  refine ⟨26075821664920071022138259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17383881109946714014758839 26075821664920071022138259)
  ·
    refine ⟨39113732497380106533207389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26075821664920071022138259 39113732497380106533207389)
    ·
      refine ⟨14667649686517539949952771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39113732497380106533207389 14667649686517539949952771)
      ·
        refine ⟨22001474529776309924929157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14667649686517539949952771 22001474529776309924929157)
        ·
          refine ⟨4125276474333058110924217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22001474529776309924929157 4125276474333058110924217)
          ·
            refine ⟨3093957355749793583193163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4125276474333058110924217 3093957355749793583193163)
            ·
              refine ⟨4640936033624690374789745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3093957355749793583193163 4640936033624690374789745)
              ·
                refine ⟨3480702025218517781092309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4640936033624690374789745 3480702025218517781092309)
                ·
                  refine ⟨81578953716059010494351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3480702025218517781092309 81578953716059010494351)
                  ·
                    rfl

theorem cell22_714935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 7].length) (baseStart_714935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714935 prefixEnd_714935 := by exact prefixLift 714935
  have htrace : WordTrace (prefixWord ++ tailWord_714935) baseStart_714935 baseEnd_714935 := by
    simpa [prefixWord, tailWord_714935, baseEnd_714935] using wordTrace_append hprefix tailTrace_714935
  have hstable : (prefixWord ++ tailWord_714935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714935).length < 2 ^ (prefixWord ++ tailWord_714935).sum := by decide
  have hdescent : baseEnd_714935 < baseStart_714935 := by decide
  rcases family_descends (prefixWord ++ tailWord_714935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_714980 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 8]
def baseStart_714980 : Nat := 118140960795 + 714980 * 2 ^ 59
def prefixEnd_714980 : Nat := 4983230072969 + 3 ^ 40 * 714980 * 2
def baseEnd_714980 : Nat := 81584088522603971369305

theorem tailTrace_714980 : CollatzResearch.WordTrace tailWord_714980 prefixEnd_714980 81584088522603971369305 := by
  unfold tailWord_714980
  simp only [CollatzResearch.WordTrace]
  refine ⟨13038731474878521853763197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17384975299838029138350929 13038731474878521853763197)
  ·
    refine ⟨4889524303079445695161199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13038731474878521853763197 4889524303079445695161199)
    ·
      refine ⟨7334286454619168542741799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4889524303079445695161199 7334286454619168542741799)
      ·
        refine ⟨11001429681928752814112699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7334286454619168542741799 11001429681928752814112699)
        ·
          refine ⟨16502144522893129221169049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11001429681928752814112699 16502144522893129221169049)
          ·
            refine ⟨12376608392169846915876787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16502144522893129221169049 12376608392169846915876787)
            ·
              refine ⟨18564912588254770373815181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12376608392169846915876787 18564912588254770373815181)
              ·
                refine ⟨6961842220595538890180693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18564912588254770373815181 6961842220595538890180693)
                ·
                  refine ⟨81584088522603971369305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6961842220595538890180693 81584088522603971369305)
                  ·
                    rfl

theorem cell22_714980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_714980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_714980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_714980 prefixEnd_714980 := by exact prefixLift 714980
  have htrace : WordTrace (prefixWord ++ tailWord_714980) baseStart_714980 baseEnd_714980 := by
    simpa [prefixWord, tailWord_714980, baseEnd_714980] using wordTrace_append hprefix tailTrace_714980
  have hstable : (prefixWord ++ tailWord_714980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_714980).length < 2 ^ (prefixWord ++ tailWord_714980).sum := by decide
  have hdescent : baseEnd_714980 < baseStart_714980 := by decide
  rcases family_descends (prefixWord ++ tailWord_714980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715029 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 2, 3]
def baseStart_715029 : Nat := 118140960795 + 715029 * 2 ^ 59
def prefixEnd_715029 : Nat := 4983230072969 + 3 ^ 40 * 715029 * 2
def baseEnd_715029 : Nat := 244769039269192119632765

theorem tailTrace_715029 : CollatzResearch.WordTrace tailWord_715029 prefixEnd_715029 244769039269192119632765 := by
  unfold tailWord_715029
  simp only [CollatzResearch.WordTrace]
  refine ⟨26079250126579525076060141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17386166751053016717373427 26079250126579525076060141)
  ·
    refine ⟨9779718797467321903522553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26079250126579525076060141 9779718797467321903522553)
    ·
      refine ⟨7334789098100491427641915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9779718797467321903522553 7334789098100491427641915)
      ·
        refine ⟨11002183647150737141462873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7334789098100491427641915 11002183647150737141462873)
        ·
          refine ⟨8251637735363052856097155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11002183647150737141462873 8251637735363052856097155)
          ·
            refine ⟨12377456603044579284145733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8251637735363052856097155 12377456603044579284145733)
            ·
              refine ⟨2320773113070858615777325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12377456603044579284145733 2320773113070858615777325)
              ·
                refine ⟨870289917401571980916497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2320773113070858615777325 870289917401571980916497)
                ·
                  refine ⟨652717438051178985687373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 870289917401571980916497 652717438051178985687373)
                  ·
                    refine ⟨244769039269192119632765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 652717438051178985687373 244769039269192119632765)
                    ·
                      rfl

theorem cell22_715029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_715029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715029 prefixEnd_715029 := by exact prefixLift 715029
  have htrace : WordTrace (prefixWord ++ tailWord_715029) baseStart_715029 baseEnd_715029 := by
    simpa [prefixWord, tailWord_715029, baseEnd_715029] using wordTrace_append hprefix tailTrace_715029
  have hstable : (prefixWord ++ tailWord_715029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715029).length < 2 ^ (prefixWord ++ tailWord_715029).sum := by decide
  have hdescent : baseEnd_715029 < baseStart_715029 := by decide
  rcases family_descends (prefixWord ++ tailWord_715029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715044 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_715044 : Nat := 118140960795 + 715044 * 2 ^ 59
def prefixEnd_715044 : Nat := 4983230072969 + 3 ^ 40 * 715044 * 2
def baseEnd_715044 : Nat := 244774174075737080507719

theorem tailTrace_715044 : CollatzResearch.WordTrace tailWord_715044 prefixEnd_715044 244774174075737080507719 := by
  unfold tailWord_715044
  simp only [CollatzResearch.WordTrace]
  refine ⟨13039898610762591318928093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17386531481016788425237457 13039898610762591318928093)
  ·
    refine ⟨4889961979035971744598035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13039898610762591318928093 4889961979035971744598035)
    ·
      refine ⟨7334942968553957616897053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4889961979035971744598035 7334942968553957616897053)
      ·
        refine ⟨2750603613207734106336395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7334942968553957616897053 2750603613207734106336395)
        ·
          refine ⟨4125905419811601159504593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2750603613207734106336395 4125905419811601159504593)
          ·
            refine ⟨3094429064858700869628445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4125905419811601159504593 3094429064858700869628445)
            ·
              refine ⟨1160410899322012826110667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3094429064858700869628445 1160410899322012826110667)
              ·
                refine ⟨1740616348983019239166001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160410899322012826110667 1740616348983019239166001)
                ·
                  refine ⟨1305462261737264429374501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1740616348983019239166001 1305462261737264429374501)
                  ·
                    refine ⟨244774174075737080507719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1305462261737264429374501 244774174075737080507719)
                    ·
                      rfl

theorem cell22_715044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_715044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715044 prefixEnd_715044 := by exact prefixLift 715044
  have htrace : WordTrace (prefixWord ++ tailWord_715044) baseStart_715044 baseEnd_715044 := by
    simpa [prefixWord, tailWord_715044, baseEnd_715044] using wordTrace_append hprefix tailTrace_715044
  have hstable : (prefixWord ++ tailWord_715044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715044).length < 2 ^ (prefixWord ++ tailWord_715044).sum := by decide
  have hdescent : baseEnd_715044 < baseStart_715044 := by decide
  rcases family_descends (prefixWord ++ tailWord_715044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715050 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 1, 4]
def baseStart_715050 : Nat := 118140960795 + 715050 * 2 ^ 59
def prefixEnd_715050 : Nat := 4983230072969 + 3 ^ 40 * 715050 * 2
def baseEnd_715050 : Nat := 244776227998355064857701

theorem tailTrace_715050 : CollatzResearch.WordTrace tailWord_715050 prefixEnd_715050 244776227998355064857701 := by
  unfold tailWord_715050
  simp only [CollatzResearch.WordTrace]
  refine ⟨6520004014875861415643651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17386677373002297108383069 6520004014875861415643651)
  ·
    refine ⟨9780006022313792123465477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6520004014875861415643651 9780006022313792123465477)
    ·
      refine ⟨1833751129183836023149777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9780006022313792123465477 1833751129183836023149777)
      ·
        refine ⟨1375313346887877017362333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1833751129183836023149777 1375313346887877017362333)
        ·
          refine ⟨515742505082953881510875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1375313346887877017362333 515742505082953881510875)
          ·
            refine ⟨773613757624430822266313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515742505082953881510875 773613757624430822266313)
            ·
              refine ⟨580210318218323116699735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 773613757624430822266313 580210318218323116699735)
              ·
                refine ⟨870315477327484675049603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580210318218323116699735 870315477327484675049603)
                ·
                  refine ⟨1305473215991227012574405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 870315477327484675049603 1305473215991227012574405)
                  ·
                    refine ⟨244776227998355064857701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1305473215991227012574405 244776227998355064857701)
                    ·
                      rfl

theorem cell22_715050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_715050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715050 prefixEnd_715050 := by exact prefixLift 715050
  have htrace : WordTrace (prefixWord ++ tailWord_715050) baseStart_715050 baseEnd_715050 := by
    simpa [prefixWord, tailWord_715050, baseEnd_715050] using wordTrace_append hprefix tailTrace_715050
  have hstable : (prefixWord ++ tailWord_715050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715050).length < 2 ^ (prefixWord ++ tailWord_715050).sum := by decide
  have hdescent : baseEnd_715050 < baseStart_715050 := by decide
  rcases family_descends (prefixWord ++ tailWord_715050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715125 : List Nat := [1, 3, 4, 1, 2, 2, 3, 2, 1, 3]
def baseStart_715125 : Nat := 118140960795 + 715125 * 2 ^ 59
def prefixEnd_715125 : Nat := 4983230072969 + 3 ^ 40 * 715125 * 2
def baseEnd_715125 : Nat := 244801902031079869232471

theorem tailTrace_715125 : CollatzResearch.WordTrace tailWord_715125 prefixEnd_715125 244801902031079869232471 := by
  unfold tailWord_715125
  simp only [CollatzResearch.WordTrace]
  refine ⟨26082751534231733471554829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17388501022821155647703219 26082751534231733471554829)
  ·
    refine ⟨9781031825336900051833061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26082751534231733471554829 9781031825336900051833061)
    ·
      refine ⟨1833943467250668759718699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9781031825336900051833061 1833943467250668759718699)
      ·
        refine ⟨2750915200876003139578049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1833943467250668759718699 2750915200876003139578049)
        ·
          refine ⟨2063186400657002354683537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2750915200876003139578049 2063186400657002354683537)
          ·
            refine ⟨1547389800492751766012653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2063186400657002354683537 1547389800492751766012653)
            ·
              refine ⟨580271175184781912254745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1547389800492751766012653 580271175184781912254745)
              ·
                refine ⟨435203381388586434191059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 580271175184781912254745 435203381388586434191059)
                ·
                  refine ⟨652805072082879651286589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435203381388586434191059 652805072082879651286589)
                  ·
                    refine ⟨244801902031079869232471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 652805072082879651286589 244801902031079869232471)
                    ·
                      rfl

theorem cell22_715125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_715125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715125 prefixEnd_715125 := by exact prefixLift 715125
  have htrace : WordTrace (prefixWord ++ tailWord_715125) baseStart_715125 baseEnd_715125 := by
    simpa [prefixWord, tailWord_715125, baseEnd_715125] using wordTrace_append hprefix tailTrace_715125
  have hstable : (prefixWord ++ tailWord_715125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715125).length < 2 ^ (prefixWord ++ tailWord_715125).sum := by decide
  have hdescent : baseEnd_715125 < baseStart_715125 := by decide
  rcases family_descends (prefixWord ++ tailWord_715125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715132 : List Nat := [2, 2, 2, 1, 1, 1, 2, 5, 6]
def baseStart_715132 : Nat := 118140960795 + 715132 * 2 ^ 59
def prefixEnd_715132 : Nat := 4983230072969 + 3 ^ 40 * 715132 * 2
def baseEnd_715132 : Nat := 81601432758044728102483

theorem tailTrace_715132 : CollatzResearch.WordTrace tailWord_715132 prefixEnd_715132 81601432758044728102483 := by
  unfold tailWord_715132
  simp only [CollatzResearch.WordTrace]
  refine ⟨13041503422603186833529825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17388671230137582444706433 13041503422603186833529825)
  ·
    refine ⟨9781127566952390125147369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13041503422603186833529825 9781127566952390125147369)
    ·
      refine ⟨7335845675214292593860527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9781127566952390125147369 7335845675214292593860527)
      ·
        refine ⟨11003768512821438890790791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7335845675214292593860527 11003768512821438890790791)
        ·
          refine ⟨16505652769232158336186187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11003768512821438890790791 16505652769232158336186187)
          ·
            refine ⟨24758479153848237504279281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16505652769232158336186187 24758479153848237504279281)
            ·
              refine ⟨18568859365386178128209461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24758479153848237504279281 18568859365386178128209461)
              ·
                refine ⟨1740830565504954199519637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18568859365386178128209461 1740830565504954199519637)
                ·
                  refine ⟨81601432758044728102483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1740830565504954199519637 81601432758044728102483)
                  ·
                    rfl

theorem cell22_715132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_715132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715132 prefixEnd_715132 := by exact prefixLift 715132
  have htrace : WordTrace (prefixWord ++ tailWord_715132) baseStart_715132 baseEnd_715132 := by
    simpa [prefixWord, tailWord_715132, baseEnd_715132] using wordTrace_append hprefix tailTrace_715132
  have hstable : (prefixWord ++ tailWord_715132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715132).length < 2 ^ (prefixWord ++ tailWord_715132).sum := by decide
  have hdescent : baseEnd_715132 < baseStart_715132 := by decide
  rcases family_descends (prefixWord ++ tailWord_715132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715138 : List Nat := [3, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_715138 : Nat := 118140960795 + 715138 * 2 ^ 59
def prefixEnd_715138 : Nat := 4983230072969 + 3 ^ 40 * 715138 * 2
def baseEnd_715138 : Nat := 81602117398917389552477

theorem tailTrace_715138 : CollatzResearch.WordTrace tailWord_715138 prefixEnd_715138 81602117398917389552477 := by
  unfold tailWord_715138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6520806420796159172944517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17388817122123091127852045 6520806420796159172944517)
  ·
    refine ⟨1222651203899279844927097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6520806420796159172944517 1222651203899279844927097)
    ·
      refine ⟨916988402924459883695323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1222651203899279844927097 916988402924459883695323)
      ·
        refine ⟨1375482604386689825542985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 916988402924459883695323 1375482604386689825542985)
        ·
          refine ⟨1031611953290017369157239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1375482604386689825542985 1031611953290017369157239)
          ·
            refine ⟨1547417929935026053735859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1031611953290017369157239 1547417929935026053735859)
            ·
              refine ⟨2321126894902539080603789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1547417929935026053735859 2321126894902539080603789)
              ·
                refine ⟨870422585588452155226421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2321126894902539080603789 870422585588452155226421)
                ·
                  refine ⟨81602117398917389552477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 870422585588452155226421 81602117398917389552477)
                  ·
                    rfl

theorem cell22_715138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_715138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715138 prefixEnd_715138 := by exact prefixLift 715138
  have htrace : WordTrace (prefixWord ++ tailWord_715138) baseStart_715138 baseEnd_715138 := by
    simpa [prefixWord, tailWord_715138, baseEnd_715138] using wordTrace_append hprefix tailTrace_715138
  have hstable : (prefixWord ++ tailWord_715138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715138).length < 2 ^ (prefixWord ++ tailWord_715138).sum := by decide
  have hdescent : baseEnd_715138 < baseStart_715138 := by decide
  rcases family_descends (prefixWord ++ tailWord_715138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715192 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_715192 : Nat := 118140960795 + 715192 * 2 ^ 59
def prefixEnd_715192 : Nat := 4983230072969 + 3 ^ 40 * 715192 * 2
def baseEnd_715192 : Nat := 244824837500314027807265

theorem tailTrace_715192 : CollatzResearch.WordTrace tailWord_715192 prefixEnd_715192 244824837500314027807265 := by
  unfold tailWord_715192
  simp only [CollatzResearch.WordTrace]
  refine ⟨13042597612494501957121915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17390130149992669276162553 13042597612494501957121915)
  ·
    refine ⟨19563896418741752935682873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13042597612494501957121915 19563896418741752935682873)
    ·
      refine ⟨14672922314056314701762155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19563896418741752935682873 14672922314056314701762155)
      ·
        refine ⟨22009383471084472052643233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14672922314056314701762155 22009383471084472052643233)
        ·
          refine ⟨16507037603313354039482425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22009383471084472052643233 16507037603313354039482425)
          ·
            refine ⟨12380278202485015529611819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16507037603313354039482425 12380278202485015529611819)
            ·
              refine ⟨18570417303727523294417729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12380278202485015529611819 18570417303727523294417729)
              ·
                refine ⟨13927812977795642470813297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18570417303727523294417729 13927812977795642470813297)
                ·
                  refine ⟨10445859733346731853109973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13927812977795642470813297 10445859733346731853109973)
                  ·
                    refine ⟨244824837500314027807265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10445859733346731853109973 244824837500314027807265)
                    ·
                      rfl

theorem cell22_715192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_715192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715192 prefixEnd_715192 := by exact prefixLift 715192
  have htrace : WordTrace (prefixWord ++ tailWord_715192) baseStart_715192 baseEnd_715192 := by
    simpa [prefixWord, tailWord_715192, baseEnd_715192] using wordTrace_append hprefix tailTrace_715192
  have hstable : (prefixWord ++ tailWord_715192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715192).length < 2 ^ (prefixWord ++ tailWord_715192).sum := by decide
  have hdescent : baseEnd_715192 < baseStart_715192 := by decide
  rcases family_descends (prefixWord ++ tailWord_715192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715209 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 5, 3]
def baseStart_715209 : Nat := 118140960795 + 715209 * 2 ^ 59
def prefixEnd_715209 : Nat := 4983230072969 + 3 ^ 40 * 715209 * 2
def baseEnd_715209 : Nat := 244830656947731650132213

theorem tailTrace_715209 : CollatzResearch.WordTrace tailWord_715209 prefixEnd_715209 244830656947731650132213 := by
  unfold tailWord_715209
  simp only [CollatzResearch.WordTrace]
  refine ⟨26085815265927415817612681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17390543510618277211741787 26085815265927415817612681)
  ·
    refine ⟨19564361449445561863209511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26085815265927415817612681 19564361449445561863209511)
    ·
      refine ⟨29346542174168342794814267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19564361449445561863209511 29346542174168342794814267)
      ·
        refine ⟨44019813261252514192221401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29346542174168342794814267 44019813261252514192221401)
        ·
          refine ⟨33014859945939385644166051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44019813261252514192221401 33014859945939385644166051)
          ·
            refine ⟨49522289918909078466249077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33014859945939385644166051 49522289918909078466249077)
            ·
              refine ⟨4642714679897726106210851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49522289918909078466249077 4642714679897726106210851)
              ·
                refine ⟨6964072019846589159316277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4642714679897726106210851 6964072019846589159316277)
                ·
                  refine ⟨652881751860617733685901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6964072019846589159316277 652881751860617733685901)
                  ·
                    refine ⟨244830656947731650132213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 652881751860617733685901 244830656947731650132213)
                    ·
                      rfl

theorem cell22_715209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 5, 3].length) (baseStart_715209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715209 prefixEnd_715209 := by exact prefixLift 715209
  have htrace : WordTrace (prefixWord ++ tailWord_715209) baseStart_715209 baseEnd_715209 := by
    simpa [prefixWord, tailWord_715209, baseEnd_715209] using wordTrace_append hprefix tailTrace_715209
  have hstable : (prefixWord ++ tailWord_715209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715209).length < 2 ^ (prefixWord ++ tailWord_715209).sum := by decide
  have hdescent : baseEnd_715209 < baseStart_715209 := by decide
  rcases family_descends (prefixWord ++ tailWord_715209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715239 : List Nat := [1, 1, 5, 2, 1, 1, 3, 1, 7]
def baseStart_715239 : Nat := 118140960795 + 715239 * 2 ^ 59
def prefixEnd_715239 : Nat := 4983230072969 + 3 ^ 40 * 715239 * 2
def baseEnd_715239 : Nat := 81613642186940523960707

theorem tailTrace_715239 : CollatzResearch.WordTrace tailWord_715239 prefixEnd_715239 81613642186940523960707 := by
  unfold tailWord_715239
  simp only [CollatzResearch.WordTrace]
  refine ⟨26086909455818730941204771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17391272970545820627469847 26086909455818730941204771)
  ·
    refine ⟨39130364183728096411807157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26086909455818730941204771 39130364183728096411807157)
    ·
      refine ⟨3668471642224509038606921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39130364183728096411807157 3668471642224509038606921)
      ·
        refine ⟨2751353731668381778955191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3668471642224509038606921 2751353731668381778955191)
        ·
          refine ⟨4127030597502572668432787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751353731668381778955191 4127030597502572668432787)
          ·
            refine ⟨6190545896253859002649181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127030597502572668432787 6190545896253859002649181)
            ·
              refine ⟨2321454711095197125993443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6190545896253859002649181 2321454711095197125993443)
              ·
                refine ⟨3482182066642795688990165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2321454711095197125993443 3482182066642795688990165)
                ·
                  refine ⟨81613642186940523960707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3482182066642795688990165 81613642186940523960707)
                  ·
                    rfl

theorem cell22_715239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 7].length) (baseStart_715239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715239 prefixEnd_715239 := by exact prefixLift 715239
  have htrace : WordTrace (prefixWord ++ tailWord_715239) baseStart_715239 baseEnd_715239 := by
    simpa [prefixWord, tailWord_715239, baseEnd_715239] using wordTrace_append hprefix tailTrace_715239
  have hstable : (prefixWord ++ tailWord_715239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715239).length < 2 ^ (prefixWord ++ tailWord_715239).sum := by decide
  have hdescent : baseEnd_715239 < baseStart_715239 := by decide
  rcases family_descends (prefixWord ++ tailWord_715239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715256 : List Nat := [2, 1, 2, 1, 1, 4, 5, 1, 5]
def baseStart_715256 : Nat := 118140960795 + 715256 * 2 ^ 59
def prefixEnd_715256 : Nat := 4983230072969 + 3 ^ 40 * 715256 * 2
def baseEnd_715256 : Nat := 81615582002746398069023

theorem tailTrace_715256 : CollatzResearch.WordTrace tailWord_715256 prefixEnd_715256 81615582002746398069023 := by
  unfold tailWord_715256
  simp only [CollatzResearch.WordTrace]
  refine ⟨13043764748378571422286811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17391686331171428563049081 13043764748378571422286811)
  ·
    refine ⟨19565647122567857133430217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13043764748378571422286811 19565647122567857133430217)
    ·
      refine ⟨14674235341925892850072663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19565647122567857133430217 14674235341925892850072663)
      ·
        refine ⟨22011353012888839275108995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14674235341925892850072663 22011353012888839275108995)
        ·
          refine ⟨33017029519333258912663493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22011353012888839275108995 33017029519333258912663493)
          ·
            refine ⟨6190693034874986046124405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33017029519333258912663493 6190693034874986046124405)
            ·
              refine ⟨580377472019529941824163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6190693034874986046124405 580377472019529941824163)
              ·
                refine ⟨870566208029294912736245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580377472019529941824163 870566208029294912736245)
                ·
                  refine ⟨81615582002746398069023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 870566208029294912736245 81615582002746398069023)
                  ·
                    rfl

theorem cell22_715256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 5].length) (baseStart_715256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715256 prefixEnd_715256 := by exact prefixLift 715256
  have htrace : WordTrace (prefixWord ++ tailWord_715256) baseStart_715256 baseEnd_715256 := by
    simpa [prefixWord, tailWord_715256, baseEnd_715256] using wordTrace_append hprefix tailTrace_715256
  have hstable : (prefixWord ++ tailWord_715256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715256).length < 2 ^ (prefixWord ++ tailWord_715256).sum := by decide
  have hdescent : baseEnd_715256 < baseStart_715256 := by decide
  rcases family_descends (prefixWord ++ tailWord_715256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715269 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_715269 : Nat := 118140960795 + 715269 * 2 ^ 59
def prefixEnd_715269 : Nat := 4983230072969 + 3 ^ 40 * 715269 * 2
def baseEnd_715269 : Nat := 244851196173911493632029

theorem tailTrace_715269 : CollatzResearch.WordTrace tailWord_715269 prefixEnd_715269 244851196173911493632029 := by
  unfold tailWord_715269
  simp only [CollatzResearch.WordTrace]
  refine ⟨26088003645710046064796861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17392002430473364043197907 26088003645710046064796861)
  ·
    refine ⟨9783001367141267274298823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26088003645710046064796861 9783001367141267274298823)
    ·
      refine ⟨14674502050711900911448235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9783001367141267274298823 14674502050711900911448235)
      ·
        refine ⟨22011753076067851367172353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14674502050711900911448235 22011753076067851367172353)
        ·
          refine ⟨16508814807050888525379265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22011753076067851367172353 16508814807050888525379265)
          ·
            refine ⟨12381611105288166394034449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16508814807050888525379265 12381611105288166394034449)
            ·
              refine ⟨9286208328966124795525837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12381611105288166394034449 9286208328966124795525837)
              ·
                refine ⟨3482328123362296798322189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9286208328966124795525837 3482328123362296798322189)
                ·
                  refine ⟨1305873046260861299370821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3482328123362296798322189 1305873046260861299370821)
                  ·
                    refine ⟨244851196173911493632029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1305873046260861299370821 244851196173911493632029)
                    ·
                      rfl

theorem cell22_715269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_715269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715269 prefixEnd_715269 := by exact prefixLift 715269
  have htrace : WordTrace (prefixWord ++ tailWord_715269) baseStart_715269 baseEnd_715269 := by
    simpa [prefixWord, tailWord_715269, baseEnd_715269] using wordTrace_append hprefix tailTrace_715269
  have hstable : (prefixWord ++ tailWord_715269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715269).length < 2 ^ (prefixWord ++ tailWord_715269).sum := by decide
  have hdescent : baseEnd_715269 < baseStart_715269 := by decide
  rcases family_descends (prefixWord ++ tailWord_715269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715301 : List Nat := [1, 3, 1, 2, 2, 1, 2, 6, 4]
def baseStart_715301 : Nat := 118140960795 + 715301 * 2 ^ 59
def prefixEnd_715301 : Nat := 4983230072969 + 3 ^ 40 * 715301 * 2
def baseEnd_715301 : Nat := 81620716809291358943977

theorem tailTrace_715301 : CollatzResearch.WordTrace tailWord_715301 prefixEnd_715301 81620716809291358943977 := by
  unfold tailWord_715301
  simp only [CollatzResearch.WordTrace]
  refine ⟨26089170781594115529961757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17392780521062743686641171 26089170781594115529961757)
  ·
    refine ⟨9783439043097793323735659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26089170781594115529961757 9783439043097793323735659)
    ·
      refine ⟨14675158564646689985603489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9783439043097793323735659 14675158564646689985603489)
      ·
        refine ⟨11006368923485017489202617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14675158564646689985603489 11006368923485017489202617)
        ·
          refine ⟨8254776692613763116901963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11006368923485017489202617 8254776692613763116901963)
          ·
            refine ⟨12382165038920644675352945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254776692613763116901963 12382165038920644675352945)
            ·
              refine ⟨9286623779190483506514709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12382165038920644675352945 9286623779190483506514709)
              ·
                refine ⟨435310489649553914367877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9286623779190483506514709 435310489649553914367877)
                ·
                  refine ⟨81620716809291358943977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 435310489649553914367877 81620716809291358943977)
                  ·
                    rfl

theorem cell22_715301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_715301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715301 prefixEnd_715301 := by exact prefixLift 715301
  have htrace : WordTrace (prefixWord ++ tailWord_715301) baseStart_715301 baseEnd_715301 := by
    simpa [prefixWord, tailWord_715301, baseEnd_715301] using wordTrace_append hprefix tailTrace_715301
  have hstable : (prefixWord ++ tailWord_715301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715301).length < 2 ^ (prefixWord ++ tailWord_715301).sum := by decide
  have hdescent : baseEnd_715301 < baseStart_715301 := by decide
  rcases family_descends (prefixWord ++ tailWord_715301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715314 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_715314 : Nat := 118140960795 + 715314 * 2 ^ 59
def prefixEnd_715314 : Nat := 4983230072969 + 3 ^ 40 * 715314 * 2
def baseEnd_715314 : Nat := 244866600593546376256891

theorem tailTrace_715314 : CollatzResearch.WordTrace tailWord_715314 prefixEnd_715314 244866600593546376256891 := by
  unfold tailWord_715314
  simp only [CollatzResearch.WordTrace]
  refine ⟨6522411232636754687546249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17393096620364679166789997 6522411232636754687546249)
  ·
    refine ⟨4891808424477566015659687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6522411232636754687546249 4891808424477566015659687)
    ·
      refine ⟨7337712636716349023489531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4891808424477566015659687 7337712636716349023489531)
      ·
        refine ⟨11006568955074523535234297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7337712636716349023489531 11006568955074523535234297)
        ·
          refine ⟨8254926716305892651425723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11006568955074523535234297 8254926716305892651425723)
          ·
            refine ⟨12382390074458838977138585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8254926716305892651425723 12382390074458838977138585)
            ·
              refine ⟨9286792555844129232853939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12382390074458838977138585 9286792555844129232853939)
              ·
                refine ⟨13930188833766193849280909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9286792555844129232853939 13930188833766193849280909)
                ·
                  refine ⟨5223820812662322693480341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13930188833766193849280909 5223820812662322693480341)
                  ·
                    refine ⟨244866600593546376256891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5223820812662322693480341 244866600593546376256891)
                    ·
                      rfl

theorem cell22_715314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_715314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715314 prefixEnd_715314 := by exact prefixLift 715314
  have htrace : WordTrace (prefixWord ++ tailWord_715314) baseStart_715314 baseEnd_715314 := by
    simpa [prefixWord, tailWord_715314, baseEnd_715314] using wordTrace_append hprefix tailTrace_715314
  have hstable : (prefixWord ++ tailWord_715314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715314).length < 2 ^ (prefixWord ++ tailWord_715314).sum := by decide
  have hdescent : baseEnd_715314 < baseStart_715314 := by decide
  rcases family_descends (prefixWord ++ tailWord_715314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715382 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_715382 : Nat := 118140960795 + 715382 * 2 ^ 59
def prefixEnd_715382 : Nat := 4983230072969 + 3 ^ 40 * 715382 * 2
def baseEnd_715382 : Nat := 244889878383216865556683

theorem tailTrace_715382 : CollatzResearch.WordTrace tailWord_715382 prefixEnd_715382 244889878383216865556683 := by
  unfold tailWord_715382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630757818393791647728775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17394750062867110909106933 1630757818393791647728775)
  ·
    refine ⟨2446136727590687471593163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1630757818393791647728775 2446136727590687471593163)
    ·
      refine ⟨3669205091386031207389745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2446136727590687471593163 3669205091386031207389745)
      ·
        refine ⟨2751903818539523405542309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3669205091386031207389745 2751903818539523405542309)
        ·
          refine ⟨515981965976160638539183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2751903818539523405542309 515981965976160638539183)
          ·
            refine ⟨773972948964240957808775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 515981965976160638539183 773972948964240957808775)
            ·
              refine ⟨1160959423446361436713163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 773972948964240957808775 1160959423446361436713163)
              ·
                refine ⟨1741439135169542155069745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1160959423446361436713163 1741439135169542155069745)
                ·
                  refine ⟨1306079351377156616302309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1741439135169542155069745 1306079351377156616302309)
                  ·
                    refine ⟨244889878383216865556683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1306079351377156616302309 244889878383216865556683)
                    ·
                      rfl

theorem cell22_715382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_715382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715382 prefixEnd_715382 := by exact prefixLift 715382
  have htrace : WordTrace (prefixWord ++ tailWord_715382) baseStart_715382 baseEnd_715382 := by
    simpa [prefixWord, tailWord_715382, baseEnd_715382] using wordTrace_append hprefix tailTrace_715382
  have hstable : (prefixWord ++ tailWord_715382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715382).length < 2 ^ (prefixWord ++ tailWord_715382).sum := by decide
  have hdescent : baseEnd_715382 < baseStart_715382 := by decide
  rcases family_descends (prefixWord ++ tailWord_715382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715406 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_715406 : Nat := 118140960795 + 715406 * 2 ^ 59
def prefixEnd_715406 : Nat := 4983230072969 + 3 ^ 40 * 715406 * 2
def baseEnd_715406 : Nat := 244898094073688802956609

theorem tailTrace_715406 : CollatzResearch.WordTrace tailWord_715406 prefixEnd_715406 244898094073688802956609 := by
  unfold tailWord_715406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3261625055776714807816759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17395333630809145641689381 3261625055776714807816759)
  ·
    refine ⟨4892437583665072211725139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3261625055776714807816759 4892437583665072211725139)
    ·
      refine ⟨7338656375497608317587709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4892437583665072211725139 7338656375497608317587709)
      ·
        refine ⟨2751996140811603119095391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7338656375497608317587709 2751996140811603119095391)
        ·
          refine ⟨4127994211217404678643087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2751996140811603119095391 4127994211217404678643087)
          ·
            refine ⟨6191991316826107017964631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4127994211217404678643087 6191991316826107017964631)
            ·
              refine ⟨9287986975239160526946947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6191991316826107017964631 9287986975239160526946947)
              ·
                refine ⟨13931980462858740790420421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9287986975239160526946947 13931980462858740790420421)
                ·
                  refine ⟨2612246336786013898203829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13931980462858740790420421 2612246336786013898203829)
                  ·
                    refine ⟨244898094073688802956609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2612246336786013898203829 244898094073688802956609)
                    ·
                      rfl

theorem cell22_715406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_715406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715406 prefixEnd_715406 := by exact prefixLift 715406
  have htrace : WordTrace (prefixWord ++ tailWord_715406) baseStart_715406 baseEnd_715406 := by
    simpa [prefixWord, tailWord_715406, baseEnd_715406] using wordTrace_append hprefix tailTrace_715406
  have hstable : (prefixWord ++ tailWord_715406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715406).length < 2 ^ (prefixWord ++ tailWord_715406).sum := by decide
  have hdescent : baseEnd_715406 < baseStart_715406 := by decide
  rcases family_descends (prefixWord ++ tailWord_715406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715412 : List Nat := [2, 4, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_715412 : Nat := 118140960795 + 715412 * 2 ^ 59
def prefixEnd_715412 : Nat := 4983230072969 + 3 ^ 40 * 715412 * 2
def baseEnd_715412 : Nat := 244900147996306787306591

theorem tailTrace_715412 : CollatzResearch.WordTrace tailWord_715412 prefixEnd_715412 244900147996306787306591 := by
  unfold tailWord_715412
  simp only [CollatzResearch.WordTrace]
  refine ⟨13046609642095990743626245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17395479522794654324834993 13046609642095990743626245)
  ·
    refine ⟨2446239307892998264429921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13046609642095990743626245 2446239307892998264429921)
    ·
      refine ⟨1834679480919748698322441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2446239307892998264429921 1834679480919748698322441)
      ·
        refine ⟨1376009610689811523741831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1834679480919748698322441 1376009610689811523741831)
        ·
          refine ⟨2064014416034717285612747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1376009610689811523741831 2064014416034717285612747)
          ·
            refine ⟨3096021624052075928419121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064014416034717285612747 3096021624052075928419121)
            ·
              refine ⟨2322016218039056946314341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3096021624052075928419121 2322016218039056946314341)
              ·
                refine ⟨435378040882323177433939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2322016218039056946314341 435378040882323177433939)
                ·
                  refine ⟨653067061323484766150909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435378040882323177433939 653067061323484766150909)
                  ·
                    refine ⟨244900147996306787306591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653067061323484766150909 244900147996306787306591)
                    ·
                      rfl

theorem cell22_715412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_715412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715412 prefixEnd_715412 := by exact prefixLift 715412
  have htrace : WordTrace (prefixWord ++ tailWord_715412) baseStart_715412 baseEnd_715412 := by
    simpa [prefixWord, tailWord_715412, baseEnd_715412] using wordTrace_append hprefix tailTrace_715412
  have hstable : (prefixWord ++ tailWord_715412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715412).length < 2 ^ (prefixWord ++ tailWord_715412).sum := by decide
  have hdescent : baseEnd_715412 < baseStart_715412 := by decide
  rcases family_descends (prefixWord ++ tailWord_715412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715421 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_715421 : Nat := 118140960795 + 715421 * 2 ^ 59
def prefixEnd_715421 : Nat := 4983230072969 + 3 ^ 40 * 715421 * 2
def baseEnd_715421 : Nat := 244903228880233763831563

theorem tailTrace_715421 : CollatzResearch.WordTrace tailWord_715421 prefixEnd_715421 244903228880233763831563 := by
  unfold tailWord_715421
  simp only [CollatzResearch.WordTrace]
  refine ⟨26093547541159376024330117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17395698360772917349553411 26093547541159376024330117)
  ·
    refine ⟨4892540163967383004561897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26093547541159376024330117 4892540163967383004561897)
    ·
      refine ⟨3669405122975537253421423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4892540163967383004561897 3669405122975537253421423)
      ·
        refine ⟨5504107684463305880132135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3669405122975537253421423 5504107684463305880132135)
        ·
          refine ⟨8256161526694958820198203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5504107684463305880132135 8256161526694958820198203)
          ·
            refine ⟨12384242290042438230297305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8256161526694958820198203 12384242290042438230297305)
            ·
              refine ⟨9288181717531828672722979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12384242290042438230297305 9288181717531828672722979)
              ·
                refine ⟨13932272576297743009084469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9288181717531828672722979 13932272576297743009084469)
                ·
                  refine ⟨1306150554027913407101669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13932272576297743009084469 1306150554027913407101669)
                  ·
                    refine ⟨244903228880233763831563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1306150554027913407101669 244903228880233763831563)
                    ·
                      rfl

theorem cell22_715421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_715421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715421 prefixEnd_715421 := by exact prefixLift 715421
  have htrace : WordTrace (prefixWord ++ tailWord_715421) baseStart_715421 baseEnd_715421 := by
    simpa [prefixWord, tailWord_715421, baseEnd_715421] using wordTrace_append hprefix tailTrace_715421
  have hstable : (prefixWord ++ tailWord_715421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715421).length < 2 ^ (prefixWord ++ tailWord_715421).sum := by decide
  have hdescent : baseEnd_715421 < baseStart_715421 := by decide
  rcases family_descends (prefixWord ++ tailWord_715421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715425 : List Nat := [1, 2, 3, 3, 3, 1, 3, 1, 5]
def baseStart_715425 : Nat := 118140960795 + 715425 * 2 ^ 59
def prefixEnd_715425 : Nat := 4983230072969 + 3 ^ 40 * 715425 * 2
def baseEnd_715425 : Nat := 81634866053993028910517

theorem tailTrace_715425 : CollatzResearch.WordTrace tailWord_715425 prefixEnd_715425 81634866053993028910517 := by
  unfold tailWord_715425
  simp only [CollatzResearch.WordTrace]
  refine ⟨26093693433144884707475729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17395795622096589804983819 26093693433144884707475729)
  ·
    refine ⟨19570270074858663530606797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26093693433144884707475729 19570270074858663530606797)
    ·
      refine ⟨7338851278071998823977549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19570270074858663530606797 7338851278071998823977549)
      ·
        refine ⟨2752069229276999558991581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7338851278071998823977549 2752069229276999558991581)
        ·
          refine ⟨1032025960978874834621843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2752069229276999558991581 1032025960978874834621843)
          ·
            refine ⟨1548038941468312251932765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032025960978874834621843 1548038941468312251932765)
            ·
              refine ⟨580514603050617094474787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1548038941468312251932765 580514603050617094474787)
              ·
                refine ⟨870771904575925641712181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580514603050617094474787 870771904575925641712181)
                ·
                  refine ⟨81634866053993028910517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 870771904575925641712181 81634866053993028910517)
                  ·
                    rfl

theorem cell22_715425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 5].length) (baseStart_715425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715425 prefixEnd_715425 := by exact prefixLift 715425
  have htrace : WordTrace (prefixWord ++ tailWord_715425) baseStart_715425 baseEnd_715425 := by
    simpa [prefixWord, tailWord_715425, baseEnd_715425] using wordTrace_append hprefix tailTrace_715425
  have hstable : (prefixWord ++ tailWord_715425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715425).length < 2 ^ (prefixWord ++ tailWord_715425).sum := by decide
  have hdescent : baseEnd_715425 < baseStart_715425 := by decide
  rcases family_descends (prefixWord ++ tailWord_715425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715446 : List Nat := [5, 1, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_715446 : Nat := 118140960795 + 715446 * 2 ^ 59
def prefixEnd_715446 : Nat := 4983230072969 + 3 ^ 40 * 715446 * 2
def baseEnd_715446 : Nat := 244911786891142031956487

theorem tailTrace_715446 : CollatzResearch.WordTrace tailWord_715446 prefixEnd_715446 244911786891142031956487 := by
  unfold tailWord_715446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1630903710379300330874387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17396306244045870195993461 1630903710379300330874387)
  ·
    refine ⟨2446355565568950496311581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1630903710379300330874387 2446355565568950496311581)
    ·
      refine ⟨917383337088356436116843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2446355565568950496311581 917383337088356436116843)
      ·
        refine ⟨1376075005632534654175265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917383337088356436116843 1376075005632534654175265)
        ·
          refine ⟨1032056254224400990631449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1376075005632534654175265 1032056254224400990631449)
          ·
            refine ⟨774042190668300742973587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1032056254224400990631449 774042190668300742973587)
            ·
              refine ⟨1161063286002451114460381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774042190668300742973587 1161063286002451114460381)
              ·
                refine ⟨435398732250919167922643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1161063286002451114460381 435398732250919167922643)
                ·
                  refine ⟨653098098376378751883965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435398732250919167922643 653098098376378751883965)
                  ·
                    refine ⟨244911786891142031956487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653098098376378751883965 244911786891142031956487)
                    ·
                      rfl

theorem cell22_715446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_715446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715446 prefixEnd_715446 := by exact prefixLift 715446
  have htrace : WordTrace (prefixWord ++ tailWord_715446) baseStart_715446 baseEnd_715446 := by
    simpa [prefixWord, tailWord_715446, baseEnd_715446] using wordTrace_append hprefix tailTrace_715446
  have hstable : (prefixWord ++ tailWord_715446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715446).length < 2 ^ (prefixWord ++ tailWord_715446).sum := by decide
  have hdescent : baseEnd_715446 < baseStart_715446 := by decide
  rcases family_descends (prefixWord ++ tailWord_715446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715481 : List Nat := [1, 2, 1, 2, 3, 2, 4, 7]
def baseStart_715481 : Nat := 118140960795 + 715481 * 2 ^ 59
def prefixEnd_715481 : Nat := 4983230072969 + 3 ^ 40 * 715481 * 2
def baseEnd_715481 : Nat := 27213752011823734147931

theorem tailTrace_715481 : CollatzResearch.WordTrace tailWord_715481 prefixEnd_715481 27213752011823734147931 := by
  unfold tailWord_715481
  simp only [CollatzResearch.WordTrace]
  refine ⟨26095735920942006271514297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17397157280628004181009531 26095735920942006271514297)
  ·
    refine ⟨19571801940706504703635723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26095735920942006271514297 19571801940706504703635723)
    ·
      refine ⟨29357702911059757055453585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19571801940706504703635723 29357702911059757055453585)
      ·
        refine ⟨22018277183294817791590189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29357702911059757055453585 22018277183294817791590189)
        ·
          refine ⟨8256853943735556671846321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22018277183294817791590189 8256853943735556671846321)
          ·
            refine ⟨6192640457801667503884741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8256853943735556671846321 6192640457801667503884741)
            ·
              refine ⟨1161120085837812656978389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6192640457801667503884741 1161120085837812656978389)
              ·
                refine ⟨27213752011823734147931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1161120085837812656978389 27213752011823734147931)
                ·
                  rfl

theorem cell22_715481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 7].length) (baseStart_715481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715481 prefixEnd_715481 := by exact prefixLift 715481
  have htrace : WordTrace (prefixWord ++ tailWord_715481) baseStart_715481 baseEnd_715481 := by
    simpa [prefixWord, tailWord_715481, baseEnd_715481] using wordTrace_append hprefix tailTrace_715481
  have hstable : (prefixWord ++ tailWord_715481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715481).length < 2 ^ (prefixWord ++ tailWord_715481).sum := by decide
  have hdescent : baseEnd_715481 < baseStart_715481 := by decide
  rcases family_descends (prefixWord ++ tailWord_715481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715620 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_715620 : Nat := 118140960795 + 715620 * 2 ^ 59
def prefixEnd_715620 : Nat := 4983230072969 + 3 ^ 40 * 715620 * 2
def baseEnd_715620 : Nat := 244971350647063578105953

theorem tailTrace_715620 : CollatzResearch.WordTrace tailWord_715620 prefixEnd_715620 244971350647063578105953 := by
  unfold tailWord_715620
  simp only [CollatzResearch.WordTrace]
  refine ⟨13050402833719216505412157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17400537111625622007216209 13050402833719216505412157)
  ·
    refine ⟨4893901062644706189529559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13050402833719216505412157 4893901062644706189529559)
    ·
      refine ⟨7340851593967059284294339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4893901062644706189529559 7340851593967059284294339)
      ·
        refine ⟨11011277390950588926441509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7340851593967059284294339 11011277390950588926441509)
        ·
          refine ⟨2064614510803235423707783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11011277390950588926441509 2064614510803235423707783)
          ·
            refine ⟨3096921766204853135561675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2064614510803235423707783 3096921766204853135561675)
            ·
              refine ⟨4645382649307279703342513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3096921766204853135561675 4645382649307279703342513)
              ·
                refine ⟨3484036986980459777506885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4645382649307279703342513 3484036986980459777506885)
                ·
                  refine ⟨653256935058836208282541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3484036986980459777506885 653256935058836208282541)
                  ·
                    refine ⟨244971350647063578105953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653256935058836208282541 244971350647063578105953)
                    ·
                      rfl

theorem cell22_715620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_715620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715620 prefixEnd_715620 := by exact prefixLift 715620
  have htrace : WordTrace (prefixWord ++ tailWord_715620) baseStart_715620 baseEnd_715620 := by
    simpa [prefixWord, tailWord_715620, baseEnd_715620] using wordTrace_append hprefix tailTrace_715620
  have hstable : (prefixWord ++ tailWord_715620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715620).length < 2 ^ (prefixWord ++ tailWord_715620).sum := by decide
  have hdescent : baseEnd_715620 < baseStart_715620 := by decide
  rcases family_descends (prefixWord ++ tailWord_715620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715633 : List Nat := [1, 2, 2, 2, 1, 6, 8]
def baseStart_715633 : Nat := 118140960795 + 715633 * 2 ^ 59
def prefixEnd_715633 : Nat := 4983230072969 + 3 ^ 40 * 715633 * 2
def baseEnd_715633 : Nat := 9073177807879106575219

theorem tailTrace_715633 : CollatzResearch.WordTrace tailWord_715633 prefixEnd_715633 9073177807879106575219 := by
  unfold tailWord_715633
  simp only [CollatzResearch.WordTrace]
  refine ⟨26101279816391336231047553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17400853210927557487365035 26101279816391336231047553)
  ·
    refine ⟨19575959862293502173285665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26101279816391336231047553 19575959862293502173285665)
    ·
      refine ⟨14681969896720126629964249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19575959862293502173285665 14681969896720126629964249)
      ·
        refine ⟨11011477422540094972473187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14681969896720126629964249 11011477422540094972473187)
        ·
          refine ⟨16517216133810142458709781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11011477422540094972473187 16517216133810142458709781)
          ·
            refine ⟨774244506272350427752021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16517216133810142458709781 774244506272350427752021)
            ·
              refine ⟨9073177807879106575219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 774244506272350427752021 9073177807879106575219)
              ·
                rfl

theorem cell22_715633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 8].length) (baseStart_715633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715633 prefixEnd_715633 := by exact prefixLift 715633
  have htrace : WordTrace (prefixWord ++ tailWord_715633) baseStart_715633 baseEnd_715633 := by
    simpa [prefixWord, tailWord_715633, baseEnd_715633] using wordTrace_append hprefix tailTrace_715633
  have hstable : (prefixWord ++ tailWord_715633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715633).length < 2 ^ (prefixWord ++ tailWord_715633).sum := by decide
  have hdescent : baseEnd_715633 < baseStart_715633 := by decide
  rcases family_descends (prefixWord ++ tailWord_715633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715710 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 2, 5]
def baseStart_715710 : Nat := 118140960795 + 715710 * 2 ^ 59
def prefixEnd_715710 : Nat := 4983230072969 + 3 ^ 40 * 715710 * 2
def baseEnd_715710 : Nat := 245002159486333343355677

theorem tailTrace_715710 : CollatzResearch.WordTrace tailWord_715710 prefixEnd_715710 245002159486333343355677 := by
  unfold tailWord_715710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3263011029639047297700073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17402725491408252254400389 3263011029639047297700073)
  ·
    refine ⟨2447258272229285473275055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3263011029639047297700073 2447258272229285473275055)
    ·
      refine ⟨3670887408343928209912583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2447258272229285473275055 3670887408343928209912583)
      ·
        refine ⟨5506331112515892314868875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3670887408343928209912583 5506331112515892314868875)
        ·
          refine ⟨8259496668773838472303313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5506331112515892314868875 8259496668773838472303313)
          ·
            refine ⟨6194622501580378854227485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8259496668773838472303313 6194622501580378854227485)
            ·
              refine ⟨2322983438092642070335307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6194622501580378854227485 2322983438092642070335307)
              ·
                refine ⟨3484475157138963105502961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2322983438092642070335307 3484475157138963105502961)
                ·
                  refine ⟨2613356367854222329127221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3484475157138963105502961 2613356367854222329127221)
                  ·
                    refine ⟨245002159486333343355677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2613356367854222329127221 245002159486333343355677)
                    ·
                      rfl

theorem cell22_715710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_715710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715710 prefixEnd_715710 := by exact prefixLift 715710
  have htrace : WordTrace (prefixWord ++ tailWord_715710) baseStart_715710 baseEnd_715710 := by
    simpa [prefixWord, tailWord_715710, baseEnd_715710] using wordTrace_append hprefix tailTrace_715710
  have hstable : (prefixWord ++ tailWord_715710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715710).length < 2 ^ (prefixWord ++ tailWord_715710).sum := by decide
  have hdescent : baseEnd_715710 < baseStart_715710 := by decide
  rcases family_descends (prefixWord ++ tailWord_715710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715718 : List Nat := [6, 1, 3, 1, 1, 1, 3, 6]
def baseStart_715718 : Nat := 118140960795 + 715718 * 2 ^ 59
def prefixEnd_715718 : Nat := 4983230072969 + 3 ^ 40 * 715718 * 2
def baseEnd_715718 : Nat := 27222766449980443239517

theorem tailTrace_715718 : CollatzResearch.WordTrace tailWord_715718 prefixEnd_715718 27222766449980443239517 := by
  unfold tailWord_715718
  simp only [CollatzResearch.WordTrace]
  refine ⟨815761875658856117121619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 17402920014055597165261205 815761875658856117121619)
  ·
    refine ⟨1223642813488284175682429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 815761875658856117121619 1223642813488284175682429)
    ·
      refine ⟨458866055058106565880911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1223642813488284175682429 458866055058106565880911)
      ·
        refine ⟨688299082587159848821367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458866055058106565880911 688299082587159848821367)
        ·
          refine ⟨1032448623880739773232051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688299082587159848821367 1032448623880739773232051)
          ·
            refine ⟨1548672935821109659848077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032448623880739773232051 1548672935821109659848077)
            ·
              refine ⟨580752350932916122443029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1548672935821109659848077 580752350932916122443029)
              ·
                refine ⟨27222766449980443239517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 580752350932916122443029 27222766449980443239517)
                ·
                  rfl

theorem cell22_715718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_715718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715718 prefixEnd_715718 := by exact prefixLift 715718
  have htrace : WordTrace (prefixWord ++ tailWord_715718) baseStart_715718 baseEnd_715718 := by
    simpa [prefixWord, tailWord_715718, baseEnd_715718] using wordTrace_append hprefix tailTrace_715718
  have hstable : (prefixWord ++ tailWord_715718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715718).length < 2 ^ (prefixWord ++ tailWord_715718).sum := by decide
  have hdescent : baseEnd_715718 < baseStart_715718 := by decide
  rcases family_descends (prefixWord ++ tailWord_715718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715723 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 8]
def baseStart_715723 : Nat := 118140960795 + 715723 * 2 ^ 59
def prefixEnd_715723 : Nat := 4983230072969 + 3 ^ 40 * 715723 * 2
def baseEnd_715723 : Nat := 81668869884001880926879

theorem tailTrace_715723 : CollatzResearch.WordTrace tailWord_715723 prefixEnd_715723 81668869884001880926879 := by
  unfold tailWord_715723
  simp only [CollatzResearch.WordTrace]
  refine ⟨26104562386065281601823823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17403041590710187734549215 26104562386065281601823823)
  ·
    refine ⟨39156843579097922402735735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26104562386065281601823823 39156843579097922402735735)
    ·
      refine ⟨58735265368646883604103603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39156843579097922402735735 58735265368646883604103603)
      ·
        refine ⟨88102898052970325406155405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58735265368646883604103603 88102898052970325406155405)
        ·
          refine ⟨33038586769863872027308277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88102898052970325406155405 33038586769863872027308277)
          ·
            refine ⟨3097367509674738002560151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33038586769863872027308277 3097367509674738002560151)
            ·
              refine ⟨4646051264512107003840227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3097367509674738002560151 4646051264512107003840227)
              ·
                refine ⟨6969076896768160505760341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4646051264512107003840227 6969076896768160505760341)
                ·
                  refine ⟨81668869884001880926879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6969076896768160505760341 81668869884001880926879)
                  ·
                    rfl

theorem cell22_715723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 8].length) (baseStart_715723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715723 prefixEnd_715723 := by exact prefixLift 715723
  have htrace : WordTrace (prefixWord ++ tailWord_715723) baseStart_715723 baseEnd_715723 := by
    simpa [prefixWord, tailWord_715723, baseEnd_715723] using wordTrace_append hprefix tailTrace_715723
  have hstable : (prefixWord ++ tailWord_715723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715723).length < 2 ^ (prefixWord ++ tailWord_715723).sum := by decide
  have hdescent : baseEnd_715723 < baseStart_715723 := by decide
  rcases family_descends (prefixWord ++ tailWord_715723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715768 : List Nat := [2, 1, 2, 1, 1, 3, 1, 11]
def baseStart_715768 : Nat := 118140960795 + 715768 * 2 ^ 59
def prefixEnd_715768 : Nat := 4983230072969 + 3 ^ 40 * 715768 * 2
def baseEnd_715768 : Nat := 27224668230182280600611

theorem tailTrace_715768 : CollatzResearch.WordTrace tailWord_715768 prefixEnd_715768 27224668230182280600611 := by
  unfold tailWord_715768
  simp only [CollatzResearch.WordTrace]
  refine ⟨13053101835451127143605979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17404135780601502858141305 13053101835451127143605979)
  ·
    refine ⟨19579652753176690715408969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13053101835451127143605979 19579652753176690715408969)
    ·
      refine ⟨14684739564882518036556727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19579652753176690715408969 14684739564882518036556727)
      ·
        refine ⟨22027109347323777054835091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14684739564882518036556727 22027109347323777054835091)
        ·
          refine ⟨33040664020985665582252637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22027109347323777054835091 33040664020985665582252637)
          ·
            refine ⟨12390249007869624593344739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33040664020985665582252637 12390249007869624593344739)
            ·
              refine ⟨18585373511804436890017109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12390249007869624593344739 18585373511804436890017109)
              ·
                refine ⟨27224668230182280600611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 18585373511804436890017109 27224668230182280600611)
                ·
                  rfl

theorem cell22_715768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 11].length) (baseStart_715768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715768 prefixEnd_715768 := by exact prefixLift 715768
  have htrace : WordTrace (prefixWord ++ tailWord_715768) baseStart_715768 baseEnd_715768 := by
    simpa [prefixWord, tailWord_715768, baseEnd_715768] using wordTrace_append hprefix tailTrace_715768
  have hstable : (prefixWord ++ tailWord_715768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715768).length < 2 ^ (prefixWord ++ tailWord_715768).sum := by decide
  have hdescent : baseEnd_715768 < baseStart_715768 := by decide
  rcases family_descends (prefixWord ++ tailWord_715768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715772 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 1, 5]
def baseStart_715772 : Nat := 118140960795 + 715772 * 2 ^ 59
def prefixEnd_715772 : Nat := 4983230072969 + 3 ^ 40 * 715772 * 2
def baseEnd_715772 : Nat := 245023383353385848305487

theorem tailTrace_715772 : CollatzResearch.WordTrace tailWord_715772 prefixEnd_715772 245023383353385848305487 := by
  unfold tailWord_715772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13053174781443881485178785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17404233041925175313571713 13053174781443881485178785)
  ·
    refine ⟨9789881086082911113884089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13053174781443881485178785 9789881086082911113884089)
    ·
      refine ⟨7342410814562183335413067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9789881086082911113884089 7342410814562183335413067)
      ·
        refine ⟨11013616221843275003119601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7342410814562183335413067 11013616221843275003119601)
        ·
          refine ⟨8260212166382456252339701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11013616221843275003119601 8260212166382456252339701)
          ·
            refine ⟨774394890598355273656847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8260212166382456252339701 774394890598355273656847)
            ·
              refine ⟨1161592335897532910485271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 774394890598355273656847 1161592335897532910485271)
              ·
                refine ⟨1742388503846299365727907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1161592335897532910485271 1742388503846299365727907)
                ·
                  refine ⟨2613582755769449048591861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1742388503846299365727907 2613582755769449048591861)
                  ·
                    refine ⟨245023383353385848305487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2613582755769449048591861 245023383353385848305487)
                    ·
                      rfl

theorem cell22_715772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_715772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715772 prefixEnd_715772 := by exact prefixLift 715772
  have htrace : WordTrace (prefixWord ++ tailWord_715772) baseStart_715772 baseEnd_715772 := by
    simpa [prefixWord, tailWord_715772, baseEnd_715772] using wordTrace_append hprefix tailTrace_715772
  have hstable : (prefixWord ++ tailWord_715772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715772).length < 2 ^ (prefixWord ++ tailWord_715772).sum := by decide
  have hdescent : baseEnd_715772 < baseStart_715772 := by decide
  rcases family_descends (prefixWord ++ tailWord_715772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715875 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 6]
def baseStart_715875 : Nat := 118140960795 + 715875 * 2 ^ 59
def prefixEnd_715875 : Nat := 4983230072969 + 3 ^ 40 * 715875 * 2
def baseEnd_715875 : Nat := 81686214119442637660057

theorem tailTrace_715875 : CollatzResearch.WordTrace tailWord_715875 prefixEnd_715875 81686214119442637660057 := by
  unfold tailWord_715875
  simp only [CollatzResearch.WordTrace]
  refine ⟨26110106281514611561357079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17406737521009741040904719 26110106281514611561357079)
  ·
    refine ⟨39165159422271917342035619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26110106281514611561357079 39165159422271917342035619)
    ·
      refine ⟨58747739133407876013053429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39165159422271917342035619 58747739133407876013053429)
      ·
        refine ⟨5507600543756988376223759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58747739133407876013053429 5507600543756988376223759)
        ·
          refine ⟨8261400815635482564335639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5507600543756988376223759 8261400815635482564335639)
          ·
            refine ⟨12392101223453223846503459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8261400815635482564335639 12392101223453223846503459)
            ·
              refine ⟨18588151835179835769755189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12392101223453223846503459 18588151835179835769755189)
              ·
                refine ⟨1742639234548109603414549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18588151835179835769755189 1742639234548109603414549)
                ·
                  refine ⟨81686214119442637660057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1742639234548109603414549 81686214119442637660057)
                  ·
                    rfl

theorem cell22_715875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 6].length) (baseStart_715875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715875 prefixEnd_715875 := by exact prefixLift 715875
  have htrace : WordTrace (prefixWord ++ tailWord_715875) baseStart_715875 baseEnd_715875 := by
    simpa [prefixWord, tailWord_715875, baseEnd_715875] using wordTrace_append hprefix tailTrace_715875
  have hstable : (prefixWord ++ tailWord_715875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715875).length < 2 ^ (prefixWord ++ tailWord_715875).sum := by decide
  have hdescent : baseEnd_715875 < baseStart_715875 := by decide
  rcases family_descends (prefixWord ++ tailWord_715875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715894 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_715894 : Nat := 118140960795 + 715894 * 2 ^ 59
def prefixEnd_715894 : Nat := 4983230072969 + 3 ^ 40 * 715894 * 2
def baseEnd_715894 : Nat := 245065146446618196755113

theorem tailTrace_715894 : CollatzResearch.WordTrace tailWord_715894 prefixEnd_715894 245065146446618196755113 := by
  unfold tailWord_715894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1631924954277861112893671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17407199512297185204199157 1631924954277861112893671)
  ·
    refine ⟨2447887431416791669340507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1631924954277861112893671 2447887431416791669340507)
    ·
      refine ⟨3671831147125187504010761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2447887431416791669340507 3671831147125187504010761)
      ·
        refine ⟨2753873360343890628008071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3671831147125187504010761 2753873360343890628008071)
        ·
          refine ⟨4130810040515835942012107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2753873360343890628008071 4130810040515835942012107)
          ·
            refine ⟨6196215060773753913018161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4130810040515835942012107 6196215060773753913018161)
            ·
              refine ⟨4647161295580315434763621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6196215060773753913018161 4647161295580315434763621)
              ·
                refine ⟨871342742921309144018179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4647161295580315434763621 871342742921309144018179)
                ·
                  refine ⟨1307014114381963716027269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871342742921309144018179 1307014114381963716027269)
                  ·
                    refine ⟨245065146446618196755113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1307014114381963716027269 245065146446618196755113)
                    ·
                      rfl

theorem cell22_715894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_715894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715894 prefixEnd_715894 := by exact prefixLift 715894
  have htrace : WordTrace (prefixWord ++ tailWord_715894) baseStart_715894 baseEnd_715894 := by
    simpa [prefixWord, tailWord_715894, baseEnd_715894] using wordTrace_append hprefix tailTrace_715894
  have hstable : (prefixWord ++ tailWord_715894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715894).length < 2 ^ (prefixWord ++ tailWord_715894).sum := by decide
  have hdescent : baseEnd_715894 < baseStart_715894 := by decide
  rcases family_descends (prefixWord ++ tailWord_715894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715902 : List Nat := [4, 2, 4, 1, 1, 1, 2, 3, 1, 3]
def baseStart_715902 : Nat := 118140960795 + 715902 * 2 ^ 59
def prefixEnd_715902 : Nat := 4983230072969 + 3 ^ 40 * 715902 * 2
def baseEnd_715902 : Nat := 245067885010108842555089

theorem tailTrace_715902 : CollatzResearch.WordTrace tailWord_715902 prefixEnd_715902 245067885010108842555089 := by
  unfold tailWord_715902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3263886381552099396573745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17407394034944530115059973 3263886381552099396573745)
  ·
    refine ⟨2447914786164074547430309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3263886381552099396573745 2447914786164074547430309)
    ·
      refine ⟨458984022405763977643183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2447914786164074547430309 458984022405763977643183)
      ·
        refine ⟨688476033608645966464775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 458984022405763977643183 688476033608645966464775)
        ·
          refine ⟨1032714050412968949697163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688476033608645966464775 1032714050412968949697163)
          ·
            refine ⟨1549071075619453424545745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032714050412968949697163 1549071075619453424545745)
            ·
              refine ⟨1161803306714590068409309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549071075619453424545745 1161803306714590068409309)
              ·
                refine ⟨435676240017971275653491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1161803306714590068409309 435676240017971275653491)
                ·
                  refine ⟨653514360026956913480237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435676240017971275653491 653514360026956913480237)
                  ·
                    refine ⟨245067885010108842555089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653514360026956913480237 245067885010108842555089)
                    ·
                      rfl

theorem cell22_715902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_715902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715902 prefixEnd_715902 := by exact prefixLift 715902
  have htrace : WordTrace (prefixWord ++ tailWord_715902) baseStart_715902 baseEnd_715902 := by
    simpa [prefixWord, tailWord_715902, baseEnd_715902] using wordTrace_append hprefix tailTrace_715902
  have hstable : (prefixWord ++ tailWord_715902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715902).length < 2 ^ (prefixWord ++ tailWord_715902).sum := by decide
  have hdescent : baseEnd_715902 < baseStart_715902 := by decide
  rcases family_descends (prefixWord ++ tailWord_715902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715907 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 4, 3]
def baseStart_715907 : Nat := 118140960795 + 715907 * 2 ^ 59
def prefixEnd_715907 : Nat := 4983230072969 + 3 ^ 40 * 715907 * 2
def baseEnd_715907 : Nat := 245069596612290496180073

theorem tailTrace_715907 : CollatzResearch.WordTrace tailWord_715907 prefixEnd_715907 245069596612290496180073 := by
  unfold tailWord_715907
  simp only [CollatzResearch.WordTrace]
  refine ⟨26111273417398681026521975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17407515611599120684347983 26111273417398681026521975)
  ·
    refine ⟨39166910126098021539782963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26111273417398681026521975 39166910126098021539782963)
    ·
      refine ⟨58750365189147032309674445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39166910126098021539782963 58750365189147032309674445)
      ·
        refine ⟨22031386945930137116127917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58750365189147032309674445 22031386945930137116127917)
        ·
          refine ⟨8261770104723801418547969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22031386945930137116127917 8261770104723801418547969)
          ·
            refine ⟨6196327578542851063910977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8261770104723801418547969 6196327578542851063910977)
            ·
              refine ⟨4647245683907138297933233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6196327578542851063910977 4647245683907138297933233)
              ·
                refine ⟨3485434262930353723449925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4647245683907138297933233 3485434262930353723449925)
                ·
                  refine ⟨653518924299441323146861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3485434262930353723449925 653518924299441323146861)
                  ·
                    refine ⟨245069596612290496180073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653518924299441323146861 245069596612290496180073)
                    ·
                      rfl

theorem cell22_715907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 3].length) (baseStart_715907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715907 prefixEnd_715907 := by exact prefixLift 715907
  have htrace : WordTrace (prefixWord ++ tailWord_715907) baseStart_715907 baseEnd_715907 := by
    simpa [prefixWord, tailWord_715907, baseEnd_715907] using wordTrace_append hprefix tailTrace_715907
  have hstable : (prefixWord ++ tailWord_715907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715907).length < 2 ^ (prefixWord ++ tailWord_715907).sum := by decide
  have hdescent : baseEnd_715907 < baseStart_715907 := by decide
  rcases family_descends (prefixWord ++ tailWord_715907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715941 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 2, 3]
def baseStart_715941 : Nat := 118140960795 + 715941 * 2 ^ 59
def prefixEnd_715941 : Nat := 4983230072969 + 3 ^ 40 * 715941 * 2
def baseEnd_715941 : Nat := 245081235507125740829969

theorem tailTrace_715941 : CollatzResearch.WordTrace tailWord_715941 prefixEnd_715941 245081235507125740829969 := by
  unfold tailWord_715941
  simp only [CollatzResearch.WordTrace]
  refine ⟨26112513499275504833259677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17408342332850336555506451 26112513499275504833259677)
  ·
    refine ⟨9792192562228314312472379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26112513499275504833259677 9792192562228314312472379)
    ·
      refine ⟨14688288843342471468708569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9792192562228314312472379 14688288843342471468708569)
      ·
        refine ⟨11016216632506853601531427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14688288843342471468708569 11016216632506853601531427)
        ·
          refine ⟨16524324948760280402297141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11016216632506853601531427 16524324948760280402297141)
          ·
            refine ⟨1549155463946276287715357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16524324948760280402297141 1549155463946276287715357)
            ·
              refine ⟨580933298979853607893259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1549155463946276287715357 580933298979853607893259)
              ·
                refine ⟨871399948469780411839889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580933298979853607893259 871399948469780411839889)
                ·
                  refine ⟨653549961352335308879917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 871399948469780411839889 653549961352335308879917)
                  ·
                    refine ⟨245081235507125740829969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653549961352335308879917 245081235507125740829969)
                    ·
                      rfl

theorem cell22_715941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_715941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715941 prefixEnd_715941 := by exact prefixLift 715941
  have htrace : WordTrace (prefixWord ++ tailWord_715941) baseStart_715941 baseEnd_715941 := by
    simpa [prefixWord, tailWord_715941, baseEnd_715941] using wordTrace_append hprefix tailTrace_715941
  have hstable : (prefixWord ++ tailWord_715941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715941).length < 2 ^ (prefixWord ++ tailWord_715941).sum := by decide
  have hdescent : baseEnd_715941 < baseStart_715941 := by decide
  rcases family_descends (prefixWord ++ tailWord_715941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715954 : List Nat := [3, 2, 1, 1, 1, 6, 2, 6]
def baseStart_715954 : Nat := 118140960795 + 715954 * 2 ^ 59
def prefixEnd_715954 : Nat := 4983230072969 + 3 ^ 40 * 715954 * 2
def baseEnd_715954 : Nat := 27231742852533115583881

theorem tailTrace_715954 : CollatzResearch.WordTrace tailWord_715954 prefixEnd_715954 27231742852533115583881 := by
  unfold tailWord_715954
  simp only [CollatzResearch.WordTrace]
  refine ⟨6528246912057102013370729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17408658432152272035655277 6528246912057102013370729)
  ·
    refine ⟨4896185184042826510028047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6528246912057102013370729 4896185184042826510028047)
    ·
      refine ⟨7344277776064239765042071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4896185184042826510028047 7344277776064239765042071)
      ·
        refine ⟨11016416664096359647563107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7344277776064239765042071 11016416664096359647563107)
        ·
          refine ⟨16524624996144539471344661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11016416664096359647563107 16524624996144539471344661)
          ·
            refine ⟨774591796694275287719281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16524624996144539471344661 774591796694275287719281)
            ·
              refine ⟨580943847520706465789461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 774591796694275287719281 580943847520706465789461)
              ·
                refine ⟨27231742852533115583881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 580943847520706465789461 27231742852533115583881)
                ·
                  rfl

theorem cell22_715954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_715954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715954 prefixEnd_715954 := by exact prefixLift 715954
  have htrace : WordTrace (prefixWord ++ tailWord_715954) baseStart_715954 baseEnd_715954 := by
    simpa [prefixWord, tailWord_715954, baseEnd_715954] using wordTrace_append hprefix tailTrace_715954
  have hstable : (prefixWord ++ tailWord_715954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715954).length < 2 ^ (prefixWord ++ tailWord_715954).sum := by decide
  have hdescent : baseEnd_715954 < baseStart_715954 := by decide
  rcases family_descends (prefixWord ++ tailWord_715954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_715999 : List Nat := [1, 1, 2, 3, 2, 1, 6, 1, 5]
def baseStart_715999 : Nat := 118140960795 + 715999 * 2 ^ 59
def prefixEnd_715999 : Nat := 4983230072969 + 3 ^ 40 * 715999 * 2
def baseEnd_715999 : Nat := 81700363364144307626597

theorem tailTrace_715999 : CollatzResearch.WordTrace tailWord_715999 prefixEnd_715999 81700363364144307626597 := by
  unfold tailWord_715999
  simp only [CollatzResearch.WordTrace]
  refine ⟨26114628933065380738871051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17409752622043587159247367 26114628933065380738871051)
  ·
    refine ⟨39171943399598071108306577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26114628933065380738871051 39171943399598071108306577)
    ·
      refine ⟨29378957549698553331229933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39171943399598071108306577 29378957549698553331229933)
      ·
        refine ⟨11017109081136957499211225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29378957549698553331229933 11017109081136957499211225)
        ·
          refine ⟨8262831810852718124408419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11017109081136957499211225 8262831810852718124408419)
          ·
            refine ⟨12394247716279077186612629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8262831810852718124408419 12394247716279077186612629)
            ·
              refine ⟨580980361700581743122467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12394247716279077186612629 580980361700581743122467)
              ·
                refine ⟨871470542550872614683701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 580980361700581743122467 871470542550872614683701)
                ·
                  refine ⟨81700363364144307626597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 871470542550872614683701 81700363364144307626597)
                  ·
                    rfl

theorem cell22_715999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 1, 5].length) (baseStart_715999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_715999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_715999 prefixEnd_715999 := by exact prefixLift 715999
  have htrace : WordTrace (prefixWord ++ tailWord_715999) baseStart_715999 baseEnd_715999 := by
    simpa [prefixWord, tailWord_715999, baseEnd_715999] using wordTrace_append hprefix tailTrace_715999
  have hstable : (prefixWord ++ tailWord_715999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_715999).length < 2 ^ (prefixWord ++ tailWord_715999).sum := by decide
  have hdescent : baseEnd_715999 < baseStart_715999 := by decide
  rcases family_descends (prefixWord ++ tailWord_715999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716042 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 5, 5]
def baseStart_716042 : Nat := 118140960795 + 716042 * 2 ^ 59
def prefixEnd_716042 : Nat := 4983230072969 + 3 ^ 40 * 716042 * 2
def baseEnd_716042 : Nat := 245115809871195144054659

theorem tailTrace_716042 : CollatzResearch.WordTrace tailWord_716042 prefixEnd_716042 245115809871195144054659 := by
  unfold tailWord_716042
  simp only [CollatzResearch.WordTrace]
  refine ⟨6529049317977399770671595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17410798181273066055124253 6529049317977399770671595)
  ·
    refine ⟨9793573976966099656007393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6529049317977399770671595 9793573976966099656007393)
    ·
      refine ⟨7345180482724574742005545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9793573976966099656007393 7345180482724574742005545)
      ·
        refine ⟨5508885362043431056504159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7345180482724574742005545 5508885362043431056504159)
        ·
          refine ⟨8263328043065146584756239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5508885362043431056504159 8263328043065146584756239)
          ·
            refine ⟨12394992064597719877134359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8263328043065146584756239 12394992064597719877134359)
            ·
              refine ⟨18592488096896579815701539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12394992064597719877134359 18592488096896579815701539)
              ·
                refine ⟨27888732145344869723552309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18592488096896579815701539 27888732145344869723552309)
                ·
                  refine ⟨2614568638626081536583029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27888732145344869723552309 2614568638626081536583029)
                  ·
                    refine ⟨245115809871195144054659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2614568638626081536583029 245115809871195144054659)
                    ·
                      rfl

theorem cell22_716042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_716042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716042 prefixEnd_716042 := by exact prefixLift 716042
  have htrace : WordTrace (prefixWord ++ tailWord_716042) baseStart_716042 baseEnd_716042 := by
    simpa [prefixWord, tailWord_716042, baseEnd_716042] using wordTrace_append hprefix tailTrace_716042
  have hstable : (prefixWord ++ tailWord_716042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716042).length < 2 ^ (prefixWord ++ tailWord_716042).sum := by decide
  have hdescent : baseEnd_716042 < baseStart_716042 := by decide
  rcases family_descends (prefixWord ++ tailWord_716042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716089 : List Nat := [1, 2, 1, 6, 2, 1, 9]
def baseStart_716089 : Nat := 118140960795 + 716089 * 2 ^ 59
def prefixEnd_716089 : Nat := 4983230072969 + 3 ^ 40 * 716089 * 2
def baseEnd_716089 : Nat := 9078959219692692152945

theorem tailTrace_716089 : CollatzResearch.WordTrace tailWord_716089 prefixEnd_716089 9078959219692692152945 := by
  unfold tailWord_716089
  simp only [CollatzResearch.WordTrace]
  refine ⟨26117911502739326109647321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17411941001826217406431547 26117911502739326109647321)
  ·
    refine ⟨19588433627054494582235491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26117911502739326109647321 19588433627054494582235491)
    ·
      refine ⟨29382650440581741873353237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19588433627054494582235491 29382650440581741873353237)
      ·
        refine ⟨1377311739402269150313433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29382650440581741873353237 1377311739402269150313433)
        ·
          refine ⟨1032983804551701862735075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1377311739402269150313433 1032983804551701862735075)
          ·
            refine ⟨1549475706827552794102613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032983804551701862735075 1549475706827552794102613)
            ·
              refine ⟨9078959219692692152945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1549475706827552794102613 9078959219692692152945)
              ·
                rfl

theorem cell22_716089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 9].length) (baseStart_716089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716089 prefixEnd_716089 := by exact prefixLift 716089
  have htrace : WordTrace (prefixWord ++ tailWord_716089) baseStart_716089 baseEnd_716089 := by
    simpa [prefixWord, tailWord_716089, baseEnd_716089] using wordTrace_append hprefix tailTrace_716089
  have hstable : (prefixWord ++ tailWord_716089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716089).length < 2 ^ (prefixWord ++ tailWord_716089).sum := by decide
  have hdescent : baseEnd_716089 < baseStart_716089 := by decide
  rcases family_descends (prefixWord ++ tailWord_716089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716093 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_716093 : Nat := 118140960795 + 716093 * 2 ^ 59
def prefixEnd_716093 : Nat := 4983230072969 + 3 ^ 40 * 716093 * 2
def baseEnd_716093 : Nat := 245133268213448011029503

theorem tailTrace_716093 : CollatzResearch.WordTrace tailWord_716093 prefixEnd_716093 245133268213448011029503 := by
  unfold tailWord_716093
  simp only [CollatzResearch.WordTrace]
  refine ⟨26118057394724834792792933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17412038263149889861861955 26118057394724834792792933)
  ·
    refine ⟨4897135761510906523648675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26118057394724834792792933 4897135761510906523648675)
    ·
      refine ⟨7345703642266359785473013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4897135761510906523648675 7345703642266359785473013)
      ·
        refine ⟨688659716462471229888095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7345703642266359785473013 688659716462471229888095)
        ·
          refine ⟨1032989574693706844832143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 688659716462471229888095 1032989574693706844832143)
          ·
            refine ⟨1549484362040560267248215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1032989574693706844832143 1549484362040560267248215)
            ·
              refine ⟨2324226543060840400872323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1549484362040560267248215 2324226543060840400872323)
              ·
                refine ⟨3486339814591260601308485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2324226543060840400872323 3486339814591260601308485)
                ·
                  refine ⟨653688715235861362745341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3486339814591260601308485 653688715235861362745341)
                  ·
                    refine ⟨245133268213448011029503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653688715235861362745341 245133268213448011029503)
                    ·
                      rfl

theorem cell22_716093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_716093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716093 prefixEnd_716093 := by exact prefixLift 716093
  have htrace : WordTrace (prefixWord ++ tailWord_716093) baseStart_716093 baseEnd_716093 := by
    simpa [prefixWord, tailWord_716093, baseEnd_716093] using wordTrace_append hprefix tailTrace_716093
  have hstable : (prefixWord ++ tailWord_716093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716093).length < 2 ^ (prefixWord ++ tailWord_716093).sum := by decide
  have hdescent : baseEnd_716093 < baseStart_716093 := by decide
  rcases family_descends (prefixWord ++ tailWord_716093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716168 : List Nat := [2, 1, 3, 3, 1, 4, 2, 1, 5]
def baseStart_716168 : Nat := 118140960795 + 716168 * 2 ^ 59
def prefixEnd_716168 : Nat := 4983230072969 + 3 ^ 40 * 716168 * 2
def baseEnd_716168 : Nat := 81719647415390938468091

theorem tailTrace_716168 : CollatzResearch.WordTrace tailWord_716168 prefixEnd_716168 81719647415390938468091 := by
  unfold tailWord_716168
  simp only [CollatzResearch.WordTrace]
  refine ⟨13060396434726561300886579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17413861912968748401182105 13060396434726561300886579)
  ·
    refine ⟨19590594652089841951329869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13060396434726561300886579 19590594652089841951329869)
    ·
      refine ⟨7346472994533690731748701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19590594652089841951329869 7346472994533690731748701)
      ·
        refine ⟨2754927372950134024405763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7346472994533690731748701 2754927372950134024405763)
        ·
          refine ⟨4132391059425201036608645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2754927372950134024405763 4132391059425201036608645)
          ·
            refine ⟨774823323642225194364121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4132391059425201036608645 774823323642225194364121)
            ·
              refine ⟨581117492731668895773091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 774823323642225194364121 581117492731668895773091)
              ·
                refine ⟨871676239097503343659637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581117492731668895773091 871676239097503343659637)
                ·
                  refine ⟨81719647415390938468091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 871676239097503343659637 81719647415390938468091)
                  ·
                    rfl

theorem cell22_716168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 5].length) (baseStart_716168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716168 prefixEnd_716168 := by exact prefixLift 716168
  have htrace : WordTrace (prefixWord ++ tailWord_716168) baseStart_716168 baseEnd_716168 := by
    simpa [prefixWord, tailWord_716168, baseEnd_716168] using wordTrace_append hprefix tailTrace_716168
  have hstable : (prefixWord ++ tailWord_716168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716168).length < 2 ^ (prefixWord ++ tailWord_716168).sum := by decide
  have hdescent : baseEnd_716168 < baseStart_716168 := by decide
  rcases family_descends (prefixWord ++ tailWord_716168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716181 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_716181 : Nat := 118140960795 + 716181 * 2 ^ 59
def prefixEnd_716181 : Nat := 4983230072969 + 3 ^ 40 * 716181 * 2
def baseEnd_716181 : Nat := 245163392411845114829233

theorem tailTrace_716181 : CollatzResearch.WordTrace tailWord_716181 prefixEnd_716181 245163392411845114829233 := by
  unfold tailWord_716181
  simp only [CollatzResearch.WordTrace]
  refine ⟨26121267018406025821996397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17414178012270683881330931 26121267018406025821996397)
  ·
    refine ⟨9795475131902259683248649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26121267018406025821996397 9795475131902259683248649)
    ·
      refine ⟨7346606348926694762436487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9795475131902259683248649 7346606348926694762436487)
      ·
        refine ⟨11019909523390042143654731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7346606348926694762436487 11019909523390042143654731)
        ·
          refine ⟨16529864285085063215482097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11019909523390042143654731 16529864285085063215482097)
          ·
            refine ⟨12397398213813797411611573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16529864285085063215482097 12397398213813797411611573)
            ·
              refine ⟨1162256082545043507338585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12397398213813797411611573 1162256082545043507338585)
              ·
                refine ⟨871692061908782630503939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162256082545043507338585 871692061908782630503939)
                ·
                  refine ⟨1307538092863173945755909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 871692061908782630503939 1307538092863173945755909)
                  ·
                    refine ⟨245163392411845114829233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1307538092863173945755909 245163392411845114829233)
                    ·
                      rfl

theorem cell22_716181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_716181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716181 prefixEnd_716181 := by exact prefixLift 716181
  have htrace : WordTrace (prefixWord ++ tailWord_716181) baseStart_716181 baseEnd_716181 := by
    simpa [prefixWord, tailWord_716181, baseEnd_716181] using wordTrace_append hprefix tailTrace_716181
  have hstable : (prefixWord ++ tailWord_716181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716181).length < 2 ^ (prefixWord ++ tailWord_716181).sum := by decide
  have hdescent : baseEnd_716181 < baseStart_716181 := by decide
  rcases family_descends (prefixWord ++ tailWord_716181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716196 : List Nat := [2, 3, 1, 2, 1, 1, 1, 7, 4]
def baseStart_716196 : Nat := 118140960795 + 716196 * 2 ^ 59
def prefixEnd_716196 : Nat := 4983230072969 + 3 ^ 40 * 716196 * 2
def baseEnd_716196 : Nat := 81722842406130025234729

theorem tailTrace_716196 : CollatzResearch.WordTrace tailWord_716196 prefixEnd_716196 81722842406130025234729 := by
  unfold tailWord_716196
  simp only [CollatzResearch.WordTrace]
  refine ⟨13060907056675841691896221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17414542742234455589194961 13060907056675841691896221)
  ·
    refine ⟨4897840146253440634461083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13060907056675841691896221 4897840146253440634461083)
    ·
      refine ⟨7346760219380160951691625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4897840146253440634461083 7346760219380160951691625)
      ·
        refine ⟨5510070164535120713768719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7346760219380160951691625 5510070164535120713768719)
        ·
          refine ⟨8265105246802681070653079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5510070164535120713768719 8265105246802681070653079)
          ·
            refine ⟨12397657870204021605979619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8265105246802681070653079 12397657870204021605979619)
            ·
              refine ⟨18596486805306032408969429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12397657870204021605979619 18596486805306032408969429)
              ·
                refine ⟨435855159499360134585221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18596486805306032408969429 435855159499360134585221)
                ·
                  refine ⟨81722842406130025234729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 435855159499360134585221 81722842406130025234729)
                  ·
                    rfl

theorem cell22_716196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_716196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716196 prefixEnd_716196 := by exact prefixLift 716196
  have htrace : WordTrace (prefixWord ++ tailWord_716196) baseStart_716196 baseEnd_716196 := by
    simpa [prefixWord, tailWord_716196, baseEnd_716196] using wordTrace_append hprefix tailTrace_716196
  have hstable : (prefixWord ++ tailWord_716196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716196).length < 2 ^ (prefixWord ++ tailWord_716196).sum := by decide
  have hdescent : baseEnd_716196 < baseStart_716196 := by decide
  rcases family_descends (prefixWord ++ tailWord_716196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716213 : List Nat := [1, 3, 3, 2, 2, 2, 1, 4, 4]
def baseStart_716213 : Nat := 118140960795 + 716213 * 2 ^ 59
def prefixEnd_716213 : Nat := 4983230072969 + 3 ^ 40 * 716213 * 2
def baseEnd_716213 : Nat := 81724782221935899343045

theorem tailTrace_716213 : CollatzResearch.WordTrace tailWord_716213 prefixEnd_716213 81724782221935899343045 := by
  unfold tailWord_716213
  simp only [CollatzResearch.WordTrace]
  refine ⟨26122434154290095287161293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17414956102860063524774195 26122434154290095287161293)
  ·
    refine ⟨9795912807858785732685485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26122434154290095287161293 9795912807858785732685485)
    ·
      refine ⟨3673467302947044649757057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9795912807858785732685485 3673467302947044649757057)
      ·
        refine ⟨2755100477210283487317793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3673467302947044649757057 2755100477210283487317793)
        ·
          refine ⟨2066325357907712615488345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2755100477210283487317793 2066325357907712615488345)
          ·
            refine ⟨1549744018430784461616259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2066325357907712615488345 1549744018430784461616259)
            ·
              refine ⟨2324616027646176692424389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1549744018430784461616259 2324616027646176692424389)
              ·
                refine ⟨435865505183658129829573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2324616027646176692424389 435865505183658129829573)
                ·
                  refine ⟨81724782221935899343045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 435865505183658129829573 81724782221935899343045)
                  ·
                    rfl

theorem cell22_716213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_716213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716213 prefixEnd_716213 := by exact prefixLift 716213
  have htrace : WordTrace (prefixWord ++ tailWord_716213) baseStart_716213 baseEnd_716213 := by
    simpa [prefixWord, tailWord_716213, baseEnd_716213] using wordTrace_append hprefix tailTrace_716213
  have hstable : (prefixWord ++ tailWord_716213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716213).length < 2 ^ (prefixWord ++ tailWord_716213).sum := by decide
  have hdescent : baseEnd_716213 < baseStart_716213 := by decide
  rcases family_descends (prefixWord ++ tailWord_716213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716224 : List Nat := [2, 1, 1, 2, 3, 1, 5, 7]
def baseStart_716224 : Nat := 118140960795 + 716224 * 2 ^ 59
def prefixEnd_716224 : Nat := 4983230072969 + 3 ^ 40 * 716224 * 2
def baseEnd_716224 : Nat := 27242012465623037333789

theorem tailTrace_716224 : CollatzResearch.WordTrace tailWord_716224 prefixEnd_716224 27242012465623037333789 := by
  unfold tailWord_716224
  simp only [CollatzResearch.WordTrace]
  refine ⟨13061417678625122082905863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17415223571500162777207817 13061417678625122082905863)
  ·
    refine ⟨19592126517937683124358795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13061417678625122082905863 19592126517937683124358795)
    ·
      refine ⟨29388189776906524686538193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19592126517937683124358795 29388189776906524686538193)
      ·
        refine ⟨22041142332679893514903645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29388189776906524686538193 22041142332679893514903645)
        ·
          refine ⟨8265428374754960068088867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22041142332679893514903645 8265428374754960068088867)
          ·
            refine ⟨12398142562132440102133301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8265428374754960068088867 12398142562132440102133301)
            ·
              refine ⟨1162325865199916259574997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12398142562132440102133301 1162325865199916259574997)
              ·
                refine ⟨27242012465623037333789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1162325865199916259574997 27242012465623037333789)
                ·
                  rfl

theorem cell22_716224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 7].length) (baseStart_716224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716224 prefixEnd_716224 := by exact prefixLift 716224
  have htrace : WordTrace (prefixWord ++ tailWord_716224) baseStart_716224 baseEnd_716224 := by
    simpa [prefixWord, tailWord_716224, baseEnd_716224] using wordTrace_append hprefix tailTrace_716224
  have hstable : (prefixWord ++ tailWord_716224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716224).length < 2 ^ (prefixWord ++ tailWord_716224).sum := by decide
  have hdescent : baseEnd_716224 < baseStart_716224 := by decide
  rcases family_descends (prefixWord ++ tailWord_716224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716228 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_716228 : Nat := 118140960795 + 716228 * 2 ^ 59
def prefixEnd_716228 : Nat := 4983230072969 + 3 ^ 40 * 716228 * 2
def baseEnd_716228 : Nat := 245179481472352658904089

theorem tailTrace_716228 : CollatzResearch.WordTrace tailWord_716228 prefixEnd_716228 245179481472352658904089 := by
  unfold tailWord_716228
  simp only [CollatzResearch.WordTrace]
  refine ⟨13061490624617876424478669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17415320832823835232638225 13061490624617876424478669)
  ·
    refine ⟨4898058984231703659179501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13061490624617876424478669 4898058984231703659179501)
    ·
      refine ⟨1836772119086888872192313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4898058984231703659179501 1836772119086888872192313)
      ·
        refine ⟨1377579089315166654144235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1836772119086888872192313 1377579089315166654144235)
        ·
          refine ⟨2066368633972749981216353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377579089315166654144235 2066368633972749981216353)
          ·
            refine ⟨1549776475479562485912265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2066368633972749981216353 1549776475479562485912265)
            ·
              refine ⟨1162332356609671864434199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549776475479562485912265 1162332356609671864434199)
              ·
                refine ⟨1743498534914507796651299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162332356609671864434199 1743498534914507796651299)
                ·
                  refine ⟨2615247802371761694976949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743498534914507796651299 2615247802371761694976949)
                  ·
                    refine ⟨245179481472352658904089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2615247802371761694976949 245179481472352658904089)
                    ·
                      rfl

theorem cell22_716228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_716228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716228 prefixEnd_716228 := by exact prefixLift 716228
  have htrace : WordTrace (prefixWord ++ tailWord_716228) baseStart_716228 baseEnd_716228 := by
    simpa [prefixWord, tailWord_716228, baseEnd_716228] using wordTrace_append hprefix tailTrace_716228
  have hstable : (prefixWord ++ tailWord_716228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716228).length < 2 ^ (prefixWord ++ tailWord_716228).sum := by decide
  have hdescent : baseEnd_716228 < baseStart_716228 := by decide
  rcases family_descends (prefixWord ++ tailWord_716228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716273 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 3, 3]
def baseStart_716273 : Nat := 118140960795 + 716273 * 2 ^ 59
def prefixEnd_716273 : Nat := 4983230072969 + 3 ^ 40 * 716273 * 2
def baseEnd_716273 : Nat := 245194885891987541528951

theorem tailTrace_716273 : CollatzResearch.WordTrace tailWord_716273 prefixEnd_716273 245194885891987541528951 := by
  unfold tailWord_716273
  simp only [CollatzResearch.WordTrace]
  refine ⟨26124622534072725534345473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17416415022715150356230315 26124622534072725534345473)
  ·
    refine ⟨19593466900554544150759105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26124622534072725534345473 19593466900554544150759105)
    ·
      refine ⟨14695100175415908113069329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19593466900554544150759105 14695100175415908113069329)
      ·
        refine ⟨11021325131561931084801997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14695100175415908113069329 11021325131561931084801997)
        ·
          refine ⟨4132996924335724156800749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11021325131561931084801997 4132996924335724156800749)
          ·
            refine ⟨1549873846625896558800281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4132996924335724156800749 1549873846625896558800281)
            ·
              refine ⟨1162405384969422419100211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1549873846625896558800281 1162405384969422419100211)
              ·
                refine ⟨1743608077454133628650317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162405384969422419100211 1743608077454133628650317)
                ·
                  refine ⟨653853029045300110743869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1743608077454133628650317 653853029045300110743869)
                  ·
                    refine ⟨245194885891987541528951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653853029045300110743869 245194885891987541528951)
                    ·
                      rfl

theorem cell22_716273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_716273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716273 prefixEnd_716273 := by exact prefixLift 716273
  have htrace : WordTrace (prefixWord ++ tailWord_716273) baseStart_716273 baseEnd_716273 := by
    simpa [prefixWord, tailWord_716273, baseEnd_716273] using wordTrace_append hprefix tailTrace_716273
  have hstable : (prefixWord ++ tailWord_716273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716273).length < 2 ^ (prefixWord ++ tailWord_716273).sum := by decide
  have hdescent : baseEnd_716273 < baseStart_716273 := by decide
  rcases family_descends (prefixWord ++ tailWord_716273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716290 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_716290 : Nat := 118140960795 + 716290 * 2 ^ 59
def prefixEnd_716290 : Nat := 4983230072969 + 3 ^ 40 * 716290 * 2
def baseEnd_716290 : Nat := 245200705339405163853899

theorem tailTrace_716290 : CollatzResearch.WordTrace tailWord_716290 prefixEnd_716290 245200705339405163853899 := by
  unfold tailWord_716290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6531310643752784359428581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17416828383340758291809549 6531310643752784359428581)
  ·
    refine ⟨1224620745703647067392859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6531310643752784359428581 1224620745703647067392859)
    ·
      refine ⟨1836931118555470601089289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1224620745703647067392859 1836931118555470601089289)
      ·
        refine ⟨1377698338916602950816967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1836931118555470601089289 1377698338916602950816967)
        ·
          refine ⟨2066547508374904426225451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1377698338916602950816967 2066547508374904426225451)
          ·
            refine ⟨3099821262562356639338177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066547508374904426225451 3099821262562356639338177)
            ·
              refine ⟨2324865946921767479503633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3099821262562356639338177 2324865946921767479503633)
              ·
                refine ⟨1743649460191325609627725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2324865946921767479503633 1743649460191325609627725)
                ·
                  refine ⟨653868547571747103610397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1743649460191325609627725 653868547571747103610397)
                  ·
                    refine ⟨245200705339405163853899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653868547571747103610397 245200705339405163853899)
                    ·
                      rfl

theorem cell22_716290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_716290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716290 prefixEnd_716290 := by exact prefixLift 716290
  have htrace : WordTrace (prefixWord ++ tailWord_716290) baseStart_716290 baseEnd_716290 := by
    simpa [prefixWord, tailWord_716290, baseEnd_716290] using wordTrace_append hprefix tailTrace_716290
  have hstable : (prefixWord ++ tailWord_716290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716290).length < 2 ^ (prefixWord ++ tailWord_716290).sum := by decide
  have hdescent : baseEnd_716290 < baseStart_716290 := by decide
  rcases family_descends (prefixWord ++ tailWord_716290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716346 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_716346 : Nat := 118140960795 + 716346 * 2 ^ 59
def prefixEnd_716346 : Nat := 4983230072969 + 3 ^ 40 * 716346 * 2
def baseEnd_716346 : Nat := 245219875283839684453727

theorem tailTrace_716346 : CollatzResearch.WordTrace tailWord_716346 prefixEnd_716346 245219875283839684453727 := by
  unfold tailWord_716346
  simp only [CollatzResearch.WordTrace]
  refine ⟨6531821265702064750438223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17418190041872172667835261 6531821265702064750438223)
  ·
    refine ⟨9797731898553097125657335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6531821265702064750438223 9797731898553097125657335)
    ·
      refine ⟨14696597847829645688486003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9797731898553097125657335 14696597847829645688486003)
      ·
        refine ⟨22044896771744468532729005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14696597847829645688486003 22044896771744468532729005)
        ·
          refine ⟨8266836289404175699773377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22044896771744468532729005 8266836289404175699773377)
          ·
            refine ⟨6200127217053131774830033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8266836289404175699773377 6200127217053131774830033)
            ·
              refine ⟨4650095412789848831122525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200127217053131774830033 4650095412789848831122525)
              ·
                refine ⟨1743785779796193311670947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4650095412789848831122525 1743785779796193311670947)
                ·
                  refine ⟨2615678669694289967506421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1743785779796193311670947 2615678669694289967506421)
                  ·
                    refine ⟨245219875283839684453727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2615678669694289967506421 245219875283839684453727)
                    ·
                      rfl

theorem cell22_716346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_716346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716346 prefixEnd_716346 := by exact prefixLift 716346
  have htrace : WordTrace (prefixWord ++ tailWord_716346) baseStart_716346 baseEnd_716346 := by
    simpa [prefixWord, tailWord_716346, baseEnd_716346] using wordTrace_append hprefix tailTrace_716346
  have hstable : (prefixWord ++ tailWord_716346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716346).length < 2 ^ (prefixWord ++ tailWord_716346).sum := by decide
  have hdescent : baseEnd_716346 < baseStart_716346 := by decide
  rcases family_descends (prefixWord ++ tailWord_716346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716380 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 2, 3]
def baseStart_716380 : Nat := 118140960795 + 716380 * 2 ^ 59
def prefixEnd_716380 : Nat := 4983230072969 + 3 ^ 40 * 716380 * 2
def baseEnd_716380 : Nat := 245231514178674929103623

theorem tailTrace_716380 : CollatzResearch.WordTrace tailWord_716380 prefixEnd_716380 245231514178674929103623 := by
  unfold tailWord_716380
  simp only [CollatzResearch.WordTrace]
  refine ⟨13064262572342541404245297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17419016763123388538993729 13064262572342541404245297)
  ·
    refine ⟨9798196929256906053183973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13064262572342541404245297 9798196929256906053183973)
    ·
      refine ⟨1837161924235669884971995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9798196929256906053183973 1837161924235669884971995)
      ·
        refine ⟨2755742886353504827457993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837161924235669884971995 2755742886353504827457993)
        ·
          refine ⟨2066807164765128620593495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2755742886353504827457993 2066807164765128620593495)
          ·
            refine ⟨3100210747147692930890243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2066807164765128620593495 3100210747147692930890243)
            ·
              refine ⟨4650316120721539396335365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100210747147692930890243 4650316120721539396335365)
              ·
                refine ⟨871934272635288636812881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4650316120721539396335365 871934272635288636812881)
                ·
                  refine ⟨653950704476466477609661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 871934272635288636812881 653950704476466477609661)
                  ·
                    refine ⟨245231514178674929103623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653950704476466477609661 245231514178674929103623)
                    ·
                      rfl

theorem cell22_716380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_716380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716380 prefixEnd_716380 := by exact prefixLift 716380
  have htrace : WordTrace (prefixWord ++ tailWord_716380) baseStart_716380 baseEnd_716380 := by
    simpa [prefixWord, tailWord_716380, baseEnd_716380] using wordTrace_append hprefix tailTrace_716380
  have hstable : (prefixWord ++ tailWord_716380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716380).length < 2 ^ (prefixWord ++ tailWord_716380).sum := by decide
  have hdescent : baseEnd_716380 < baseStart_716380 := by decide
  rcases family_descends (prefixWord ++ tailWord_716380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716421 : List Nat := [1, 3, 1, 1, 4, 1, 2, 2, 7]
def baseStart_716421 : Nat := 118140960795 + 716421 * 2 ^ 59
def prefixEnd_716421 : Nat := 4983230072969 + 3 ^ 40 * 716421 * 2
def baseEnd_716421 : Nat := 81748516438854829609499

theorem tailTrace_716421 : CollatzResearch.WordTrace tailWord_716421 prefixEnd_716421 81748516438854829609499 := by
  unfold tailWord_716421
  simp only [CollatzResearch.WordTrace]
  refine ⟨26130020537536546810733117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17420013691691031207155411 26130020537536546810733117)
  ·
    refine ⟨9798757701576205054024919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26130020537536546810733117 9798757701576205054024919)
    ·
      refine ⟨14698136552364307581037379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9798757701576205054024919 14698136552364307581037379)
      ·
        refine ⟨22047204828546461371556069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14698136552364307581037379 22047204828546461371556069)
        ·
          refine ⟨4133850905352461507166763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22047204828546461371556069 4133850905352461507166763)
          ·
            refine ⟨6200776358028692260750145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4133850905352461507166763 6200776358028692260750145)
            ·
              refine ⟨4650582268521519195562609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200776358028692260750145 4650582268521519195562609)
              ·
                refine ⟨3487936701391139396671957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4650582268521519195562609 3487936701391139396671957)
                ·
                  refine ⟨81748516438854829609499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3487936701391139396671957 81748516438854829609499)
                  ·
                    rfl

theorem cell22_716421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_716421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716421 prefixEnd_716421 := by exact prefixLift 716421
  have htrace : WordTrace (prefixWord ++ tailWord_716421) baseStart_716421 baseEnd_716421 := by
    simpa [prefixWord, tailWord_716421, baseEnd_716421] using wordTrace_append hprefix tailTrace_716421
  have hstable : (prefixWord ++ tailWord_716421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716421).length < 2 ^ (prefixWord ++ tailWord_716421).sum := by decide
  have hdescent : baseEnd_716421 < baseStart_716421 := by decide
  rcases family_descends (prefixWord ++ tailWord_716421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716425 : List Nat := [1, 2, 1, 1, 4, 1, 3, 5, 1, 3]
def baseStart_716425 : Nat := 118140960795 + 716425 * 2 ^ 59
def prefixEnd_716425 : Nat := 4983230072969 + 3 ^ 40 * 716425 * 2
def baseEnd_716425 : Nat := 245246918598309811728485

theorem tailTrace_716425 : CollatzResearch.WordTrace tailWord_716425 prefixEnd_716425 245246918598309811728485 := by
  unfold tailWord_716425
  simp only [CollatzResearch.WordTrace]
  refine ⟨26130166429522055493878729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17420110953014703662585819 26130166429522055493878729)
  ·
    refine ⟨19597624822141541620409047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26130166429522055493878729 19597624822141541620409047)
    ·
      refine ⟨29396437233212312430613571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19597624822141541620409047 29396437233212312430613571)
      ·
        refine ⟨44094655849818468645920357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29396437233212312430613571 44094655849818468645920357)
        ·
          refine ⟨8267747971840962871110067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44094655849818468645920357 8267747971840962871110067)
          ·
            refine ⟨12401621957761444306665101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8267747971840962871110067 12401621957761444306665101)
            ·
              refine ⟨4650608234160541614999413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12401621957761444306665101 4650608234160541614999413)
              ·
                refine ⟨435994521952550776406195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4650608234160541614999413 435994521952550776406195)
                ·
                  refine ⟨653991782928826164609293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 435994521952550776406195 653991782928826164609293)
                  ·
                    refine ⟨245246918598309811728485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 653991782928826164609293 245246918598309811728485)
                    ·
                      rfl

theorem cell22_716425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 5, 1, 3].length) (baseStart_716425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716425 prefixEnd_716425 := by exact prefixLift 716425
  have htrace : WordTrace (prefixWord ++ tailWord_716425) baseStart_716425 baseEnd_716425 := by
    simpa [prefixWord, tailWord_716425, baseEnd_716425] using wordTrace_append hprefix tailTrace_716425
  have hstable : (prefixWord ++ tailWord_716425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716425).length < 2 ^ (prefixWord ++ tailWord_716425).sum := by decide
  have hdescent : baseEnd_716425 < baseStart_716425 := by decide
  rcases family_descends (prefixWord ++ tailWord_716425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716496 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_716496 : Nat := 118140960795 + 716496 * 2 ^ 59
def prefixEnd_716496 : Nat := 4983230072969 + 3 ^ 40 * 716496 * 2
def baseEnd_716496 : Nat := 245271223349289293203267

theorem tailTrace_716496 : CollatzResearch.WordTrace tailWord_716496 prefixEnd_716496 245271223349289293203267 := by
  unfold tailWord_716496
  simp only [CollatzResearch.WordTrace]
  refine ⟨13066378006132417309856671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17421837341509889746475561 13066378006132417309856671)
  ·
    refine ⟨19599567009198625964785007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13066378006132417309856671 19599567009198625964785007)
    ·
      refine ⟨29399350513797938947177511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19599567009198625964785007 29399350513797938947177511)
      ·
        refine ⟨44099025770696908420766267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29399350513797938947177511 44099025770696908420766267)
        ·
          refine ⟨66148538656045362631149401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44099025770696908420766267 66148538656045362631149401)
          ·
            refine ⟨49611403992034021973362051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66148538656045362631149401 49611403992034021973362051)
            ·
              refine ⟨74417105988051032960043077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49611403992034021973362051 74417105988051032960043077)
              ·
                refine ⟨13953207372759568680008077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74417105988051032960043077 13953207372759568680008077)
                ·
                  refine ⟨5232452764784838255003029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13953207372759568680008077 5232452764784838255003029)
                  ·
                    refine ⟨245271223349289293203267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5232452764784838255003029 245271223349289293203267)
                    ·
                      rfl

theorem cell22_716496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_716496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716496 prefixEnd_716496 := by exact prefixLift 716496
  have htrace : WordTrace (prefixWord ++ tailWord_716496) baseStart_716496 baseEnd_716496 := by
    simpa [prefixWord, tailWord_716496, baseEnd_716496] using wordTrace_append hprefix tailTrace_716496
  have hstable : (prefixWord ++ tailWord_716496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716496).length < 2 ^ (prefixWord ++ tailWord_716496).sum := by decide
  have hdescent : baseEnd_716496 < baseStart_716496 := by decide
  rcases family_descends (prefixWord ++ tailWord_716496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716500 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 6]
def baseStart_716500 : Nat := 118140960795 + 716500 * 2 ^ 59
def prefixEnd_716500 : Nat := 4983230072969 + 3 ^ 40 * 716500 * 2
def baseEnd_716500 : Nat := 81757530877011538701085

theorem tailTrace_716500 : CollatzResearch.WordTrace tailWord_716500 prefixEnd_716500 81757530877011538701085 := by
  unfold tailWord_716500
  simp only [CollatzResearch.WordTrace]
  refine ⟨13066450952125171651429477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17421934602833562201905969 13066450952125171651429477)
  ·
    refine ⟨2449959553523469684643027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13066450952125171651429477 2449959553523469684643027)
    ·
      refine ⟨3674939330285204526964541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2449959553523469684643027 3674939330285204526964541)
      ·
        refine ⟨1378102248856951697611703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3674939330285204526964541 1378102248856951697611703)
        ·
          refine ⟨2067153373285427546417555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378102248856951697611703 2067153373285427546417555)
          ·
            refine ⟨3100730059928141319626333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067153373285427546417555 3100730059928141319626333)
            ·
              refine ⟨1162773772473052994859875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3100730059928141319626333 1162773772473052994859875)
              ·
                refine ⟨1744160658709579492289813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162773772473052994859875 1744160658709579492289813)
                ·
                  refine ⟨81757530877011538701085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1744160658709579492289813 81757530877011538701085)
                  ·
                    rfl

theorem cell22_716500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_716500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716500 prefixEnd_716500 := by exact prefixLift 716500
  have htrace : WordTrace (prefixWord ++ tailWord_716500) baseStart_716500 baseEnd_716500 := by
    simpa [prefixWord, tailWord_716500, baseEnd_716500] using wordTrace_append hprefix tailTrace_716500
  have hstable : (prefixWord ++ tailWord_716500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716500).length < 2 ^ (prefixWord ++ tailWord_716500).sum := by decide
  have hdescent : baseEnd_716500 < baseStart_716500 := by decide
  rcases family_descends (prefixWord ++ tailWord_716500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716519 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 1, 4]
def baseStart_716519 : Nat := 118140960795 + 716519 * 2 ^ 59
def prefixEnd_716519 : Nat := 4983230072969 + 3 ^ 40 * 716519 * 2
def baseEnd_716519 : Nat := 245279096719324899878197

theorem tailTrace_716519 : CollatzResearch.WordTrace tailWord_716519 prefixEnd_716519 245279096719324899878197 := by
  unfold tailWord_716519
  simp only [CollatzResearch.WordTrace]
  refine ⟨26133594891181509547800611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17422396594121006365200407 26133594891181509547800611)
  ·
    refine ⟨39200392336772264321700917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26133594891181509547800611 39200392336772264321700917)
    ·
      refine ⟨3675036781572399780159461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39200392336772264321700917 3675036781572399780159461)
      ·
        refine ⟨689069396544824958779899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3675036781572399780159461 689069396544824958779899)
        ·
          refine ⟨1033604094817237438169849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689069396544824958779899 1033604094817237438169849)
          ·
            refine ⟨775203071112928078627387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033604094817237438169849 775203071112928078627387)
            ·
              refine ⟨1162804606669392117941081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775203071112928078627387 1162804606669392117941081)
              ·
                refine ⟨872103455002044088455811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162804606669392117941081 872103455002044088455811)
                ·
                  refine ⟨1308155182503066132683717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872103455002044088455811 1308155182503066132683717)
                  ·
                    refine ⟨245279096719324899878197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1308155182503066132683717 245279096719324899878197)
                    ·
                      rfl

theorem cell22_716519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_716519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716519 prefixEnd_716519 := by exact prefixLift 716519
  have htrace : WordTrace (prefixWord ++ tailWord_716519) baseStart_716519 baseEnd_716519 := by
    simpa [prefixWord, tailWord_716519, baseEnd_716519] using wordTrace_append hprefix tailTrace_716519
  have hstable : (prefixWord ++ tailWord_716519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716519).length < 2 ^ (prefixWord ++ tailWord_716519).sum := by decide
  have hdescent : baseEnd_716519 < baseStart_716519 := by decide
  rcases family_descends (prefixWord ++ tailWord_716519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716530 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_716530 : Nat := 118140960795 + 716530 * 2 ^ 59
def prefixEnd_716530 : Nat := 4983230072969 + 3 ^ 40 * 716530 * 2
def baseEnd_716530 : Nat := 245282862244124537853163

theorem tailTrace_716530 : CollatzResearch.WordTrace tailWord_716530 prefixEnd_716530 245282862244124537853163 := by
  unfold tailWord_716530
  simp only [CollatzResearch.WordTrace]
  refine ⟨6533499023535414606612761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17422664062761105617634029 6533499023535414606612761)
  ·
    refine ⟨4900124267651560954959571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6533499023535414606612761 4900124267651560954959571)
    ·
      refine ⟨7350186401477341432439357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4900124267651560954959571 7350186401477341432439357)
      ·
        refine ⟨2756319900554003037164759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7350186401477341432439357 2756319900554003037164759)
        ·
          refine ⟨4134479850831004555747139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2756319900554003037164759 4134479850831004555747139)
          ·
            refine ⟨6201719776246506833620709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4134479850831004555747139 6201719776246506833620709)
            ·
              refine ⟨1162822458046220031303883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6201719776246506833620709 1162822458046220031303883)
              ·
                refine ⟨1744233687069330046955825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162822458046220031303883 1744233687069330046955825)
                ·
                  refine ⟨1308175265301997535216869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1744233687069330046955825 1308175265301997535216869)
                  ·
                    refine ⟨245282862244124537853163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1308175265301997535216869 245282862244124537853163)
                    ·
                      rfl

theorem cell22_716530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_716530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716530 prefixEnd_716530 := by exact prefixLift 716530
  have htrace : WordTrace (prefixWord ++ tailWord_716530) baseStart_716530 baseEnd_716530 := by
    simpa [prefixWord, tailWord_716530, baseEnd_716530] using wordTrace_append hprefix tailTrace_716530
  have hstable : (prefixWord ++ tailWord_716530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716530).length < 2 ^ (prefixWord ++ tailWord_716530).sum := by decide
  have hdescent : baseEnd_716530 < baseStart_716530 := by decide
  rcases family_descends (prefixWord ++ tailWord_716530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716532 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_716532 : Nat := 118140960795 + 716532 * 2 ^ 59
def prefixEnd_716532 : Nat := 4983230072969 + 3 ^ 40 * 716532 * 2
def baseEnd_716532 : Nat := 245283546884997199303157

theorem tailTrace_716532 : CollatzResearch.WordTrace tailWord_716532 prefixEnd_716532 245283546884997199303157 := by
  unfold tailWord_716532
  simp only [CollatzResearch.WordTrace]
  refine ⟨13067034520067206384011925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17422712693422941845349233 13067034520067206384011925)
  ·
    refine ⟨612517243128150299250559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13067034520067206384011925 612517243128150299250559)
    ·
      refine ⟨918775864692225448875839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612517243128150299250559 918775864692225448875839)
      ·
        refine ⟨1378163797038338173313759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918775864692225448875839 1378163797038338173313759)
        ·
          refine ⟨2067245695557507259970639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378163797038338173313759 2067245695557507259970639)
          ·
            refine ⟨3100868543336260889955959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067245695557507259970639 3100868543336260889955959)
            ·
              refine ⟨4651302815004391334933939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3100868543336260889955959 4651302815004391334933939)
              ·
                refine ⟨6976954222506587002400909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651302815004391334933939 6976954222506587002400909)
                ·
                  refine ⟨2616357833439970125900341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6976954222506587002400909 2616357833439970125900341)
                  ·
                    refine ⟨245283546884997199303157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2616357833439970125900341 245283546884997199303157)
                    ·
                      rfl

theorem cell22_716532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_716532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716532 prefixEnd_716532 := by exact prefixLift 716532
  have htrace : WordTrace (prefixWord ++ tailWord_716532) baseStart_716532 baseEnd_716532 := by
    simpa [prefixWord, tailWord_716532, baseEnd_716532] using wordTrace_append hprefix tailTrace_716532
  have hstable : (prefixWord ++ tailWord_716532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716532).length < 2 ^ (prefixWord ++ tailWord_716532).sum := by decide
  have hdescent : baseEnd_716532 < baseStart_716532 := by decide
  rcases family_descends (prefixWord ++ tailWord_716532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716551 : List Nat := [1, 1, 4, 4, 3, 1, 2, 2, 4]
def baseStart_716551 : Nat := 118140960795 + 716551 * 2 ^ 59
def prefixEnd_716551 : Nat := 4983230072969 + 3 ^ 40 * 716551 * 2
def baseEnd_716551 : Nat := 81763350324429161026033

theorem tailTrace_716551 : CollatzResearch.WordTrace tailWord_716551 prefixEnd_716551 81763350324429161026033 := by
  unfold tailWord_716551
  simp only [CollatzResearch.WordTrace]
  refine ⟨26134762027065579012965507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17423174684710386008643671 26134762027065579012965507)
  ·
    refine ⟨39202143040598368519448261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26134762027065579012965507 39202143040598368519448261)
    ·
      refine ⟨7350401820112194097396549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39202143040598368519448261 7350401820112194097396549)
      ·
        refine ⟨1378200341271036393261853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7350401820112194097396549 1378200341271036393261853)
        ·
          refine ⟨516825127976638647473195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1378200341271036393261853 516825127976638647473195)
          ·
            refine ⟨775237691964957971209793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516825127976638647473195 775237691964957971209793)
            ·
              refine ⟨581428268973718478407345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775237691964957971209793 581428268973718478407345)
              ·
                refine ⟨436071201730288858805509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581428268973718478407345 436071201730288858805509)
                ·
                  refine ⟨81763350324429161026033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436071201730288858805509 81763350324429161026033)
                  ·
                    rfl

theorem cell22_716551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 4].length) (baseStart_716551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716551 prefixEnd_716551 := by exact prefixLift 716551
  have htrace : WordTrace (prefixWord ++ tailWord_716551) baseStart_716551 baseEnd_716551 := by
    simpa [prefixWord, tailWord_716551, baseEnd_716551] using wordTrace_append hprefix tailTrace_716551
  have hstable : (prefixWord ++ tailWord_716551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716551).length < 2 ^ (prefixWord ++ tailWord_716551).sum := by decide
  have hdescent : baseEnd_716551 < baseStart_716551 := by decide
  rcases family_descends (prefixWord ++ tailWord_716551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716558 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_716558 : Nat := 118140960795 + 716558 * 2 ^ 59
def prefixEnd_716558 : Nat := 4983230072969 + 3 ^ 40 * 716558 * 2
def baseEnd_716558 : Nat := 245292447216341798153077

theorem tailTrace_716558 : CollatzResearch.WordTrace tailWord_716558 prefixEnd_716558 245292447216341798153077 := by
  unfold tailWord_716558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3266877167255027401058791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17423344892026812805646885 3266877167255027401058791)
  ·
    refine ⟨4900315750882541101588187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3266877167255027401058791 4900315750882541101588187)
    ·
      refine ⟨7350473626323811652382281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4900315750882541101588187 7350473626323811652382281)
      ·
        refine ⟨5512855219742858739286711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7350473626323811652382281 5512855219742858739286711)
        ·
          refine ⟨8269282829614288108930067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5512855219742858739286711 8269282829614288108930067)
          ·
            refine ⟨12403924244421432163395101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8269282829614288108930067 12403924244421432163395101)
            ·
              refine ⟨4651471591658037061273163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12403924244421432163395101 4651471591658037061273163)
              ·
                refine ⟨6977207387487055591909745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651471591658037061273163 6977207387487055591909745)
                ·
                  refine ⟨5232905540615291693932309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6977207387487055591909745 5232905540615291693932309)
                  ·
                    refine ⟨245292447216341798153077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5232905540615291693932309 245292447216341798153077)
                    ·
                      rfl

theorem cell22_716558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_716558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716558 prefixEnd_716558 := by exact prefixLift 716558
  have htrace : WordTrace (prefixWord ++ tailWord_716558) baseStart_716558 baseEnd_716558 := by
    simpa [prefixWord, tailWord_716558, baseEnd_716558] using wordTrace_append hprefix tailTrace_716558
  have hstable : (prefixWord ++ tailWord_716558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716558).length < 2 ^ (prefixWord ++ tailWord_716558).sum := by decide
  have hdescent : baseEnd_716558 < baseStart_716558 := by decide
  rcases family_descends (prefixWord ++ tailWord_716558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716562 : List Nat := [3, 2, 4, 1, 1, 3, 1, 7]
def baseStart_716562 : Nat := 118140960795 + 716562 * 2 ^ 59
def prefixEnd_716562 : Nat := 4983230072969 + 3 ^ 40 * 716562 * 2
def baseEnd_716562 : Nat := 27254868499787457894785

theorem tailTrace_716562 : CollatzResearch.WordTrace tailWord_716562 prefixEnd_716562 27254868499787457894785 := by
  unfold tailWord_716562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6533790807506431972903985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17423442153350485261077293 6533790807506431972903985)
  ·
    refine ⟨4900343105629823979677989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6533790807506431972903985 4900343105629823979677989)
    ·
      refine ⟨918814332305591996189623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4900343105629823979677989 918814332305591996189623)
      ·
        refine ⟨1378221498458387994284435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918814332305591996189623 1378221498458387994284435)
        ·
          refine ⟨2067332247687581991426653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378221498458387994284435 2067332247687581991426653)
          ·
            refine ⟨775249592882843246784995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2067332247687581991426653 775249592882843246784995)
            ·
              refine ⟨1162874389324264870177493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775249592882843246784995 1162874389324264870177493)
              ·
                refine ⟨27254868499787457894785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1162874389324264870177493 27254868499787457894785)
                ·
                  rfl

theorem cell22_716562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_716562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716562 prefixEnd_716562 := by exact prefixLift 716562
  have htrace : WordTrace (prefixWord ++ tailWord_716562) baseStart_716562 baseEnd_716562 := by
    simpa [prefixWord, tailWord_716562, baseEnd_716562] using wordTrace_append hprefix tailTrace_716562
  have hstable : (prefixWord ++ tailWord_716562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716562).length < 2 ^ (prefixWord ++ tailWord_716562).sum := by decide
  have hdescent : baseEnd_716562 < baseStart_716562 := by decide
  rcases family_descends (prefixWord ++ tailWord_716562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716594 : List Nat := [3, 2, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_716594 : Nat := 118140960795 + 716594 * 2 ^ 59
def prefixEnd_716594 : Nat := 4983230072969 + 3 ^ 40 * 716594 * 2
def baseEnd_716594 : Nat := 245304770752049704252967

theorem tailTrace_716594 : CollatzResearch.WordTrace tailWord_716594 prefixEnd_716594 245304770752049704252967 := by
  unfold tailWord_716594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6534082591477449339195209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17424220243939864904520557 6534082591477449339195209)
  ·
    refine ⟨4900561943608087004396407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6534082591477449339195209 4900561943608087004396407)
    ·
      refine ⟨7350842915412130506594611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4900561943608087004396407 7350842915412130506594611)
      ·
        refine ⟨11026264373118195759891917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7350842915412130506594611 11026264373118195759891917)
        ·
          refine ⟨4134849139919323409959469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11026264373118195759891917 4134849139919323409959469)
          ·
            refine ⟨1550568427469746278734801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4134849139919323409959469 1550568427469746278734801)
            ·
              refine ⟨1162926320602309709051101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550568427469746278734801 1162926320602309709051101)
              ·
                refine ⟨436097370225866140894163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1162926320602309709051101 436097370225866140894163)
                ·
                  refine ⟨654146055338799211341245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436097370225866140894163 654146055338799211341245)
                  ·
                    refine ⟨245304770752049704252967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654146055338799211341245 245304770752049704252967)
                    ·
                      rfl

theorem cell22_716594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_716594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716594 prefixEnd_716594 := by exact prefixLift 716594
  have htrace : WordTrace (prefixWord ++ tailWord_716594) baseStart_716594 baseEnd_716594 := by
    simpa [prefixWord, tailWord_716594, baseEnd_716594] using wordTrace_append hprefix tailTrace_716594
  have hstable : (prefixWord ++ tailWord_716594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716594).length < 2 ^ (prefixWord ++ tailWord_716594).sum := by decide
  have hdescent : baseEnd_716594 < baseStart_716594 := by decide
  rcases family_descends (prefixWord ++ tailWord_716594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716605 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_716605 : Nat := 118140960795 + 716605 * 2 ^ 59
def prefixEnd_716605 : Nat := 4983230072969 + 3 ^ 40 * 716605 * 2
def baseEnd_716605 : Nat := 245308536276849342227933

theorem tailTrace_716605 : CollatzResearch.WordTrace tailWord_716605 prefixEnd_716605 245308536276849342227933 := by
  unfold tailWord_716605
  simp only [CollatzResearch.WordTrace]
  refine ⟨26136731568869946235431269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17424487712579964156954179 26136731568869946235431269)
  ·
    refine ⟨4900637169163114919143363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26136731568869946235431269 4900637169163114919143363)
    ·
      refine ⟨7350955753744672378715045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4900637169163114919143363 7350955753744672378715045)
      ·
        refine ⟨1378304203827126071009071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7350955753744672378715045 1378304203827126071009071)
        ·
          refine ⟨2067456305740689106513607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378304203827126071009071 2067456305740689106513607)
          ·
            refine ⟨3101184458611033659770411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2067456305740689106513607 3101184458611033659770411)
            ·
              refine ⟨4651776687916550489655617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3101184458611033659770411 4651776687916550489655617)
              ·
                refine ⟨3488832515937412867241713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4651776687916550489655617 3488832515937412867241713)
                ·
                  refine ⟨2616624386953059650431285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3488832515937412867241713 2616624386953059650431285)
                  ·
                    refine ⟨245308536276849342227933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2616624386953059650431285 245308536276849342227933)
                    ·
                      rfl

theorem cell22_716605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_716605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716605 prefixEnd_716605 := by exact prefixLift 716605
  have htrace : WordTrace (prefixWord ++ tailWord_716605) baseStart_716605 baseEnd_716605 := by
    simpa [prefixWord, tailWord_716605, baseEnd_716605] using wordTrace_append hprefix tailTrace_716605
  have hstable : (prefixWord ++ tailWord_716605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716605).length < 2 ^ (prefixWord ++ tailWord_716605).sum := by decide
  have hdescent : baseEnd_716605 < baseStart_716605 := by decide
  rcases family_descends (prefixWord ++ tailWord_716605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716607 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 5]
def baseStart_716607 : Nat := 118140960795 + 716607 * 2 ^ 59
def prefixEnd_716607 : Nat := 4983230072969 + 3 ^ 40 * 716607 * 2
def baseEnd_716607 : Nat := 81769740305907334559309

theorem tailTrace_716607 : CollatzResearch.WordTrace tailWord_716607 prefixEnd_716607 81769740305907334559309 := by
  unfold tailWord_716607
  simp only [CollatzResearch.WordTrace]
  refine ⟨26136804514862700577004075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17424536343241800384669383 26136804514862700577004075)
  ·
    refine ⟨39205206772294050865506113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26136804514862700577004075 39205206772294050865506113)
    ·
      refine ⟨29403905079220538149129585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39205206772294050865506113 29403905079220538149129585)
      ·
        refine ⟨22052928809415403611847189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29403905079220538149129585 22052928809415403611847189)
        ·
          refine ⟨1033731037941347044305337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22052928809415403611847189 1033731037941347044305337)
          ·
            refine ⟨775298278456010283229003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1033731037941347044305337 775298278456010283229003)
            ·
              refine ⟨1162947417684015424843505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775298278456010283229003 1162947417684015424843505)
              ·
                refine ⟨872210563263011568632629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1162947417684015424843505 872210563263011568632629)
                ·
                  refine ⟨81769740305907334559309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 872210563263011568632629 81769740305907334559309)
                  ·
                    rfl

theorem cell22_716607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 5].length) (baseStart_716607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716607 prefixEnd_716607 := by exact prefixLift 716607
  have htrace : WordTrace (prefixWord ++ tailWord_716607) baseStart_716607 baseEnd_716607 := by
    simpa [prefixWord, tailWord_716607, baseEnd_716607] using wordTrace_append hprefix tailTrace_716607
  have hstable : (prefixWord ++ tailWord_716607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716607).length < 2 ^ (prefixWord ++ tailWord_716607).sum := by decide
  have hdescent : baseEnd_716607 < baseStart_716607 := by decide
  rcases family_descends (prefixWord ++ tailWord_716607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716652 : List Nat := [2, 2, 1, 1, 4, 2, 3, 3, 4]
def baseStart_716652 : Nat := 118140960795 + 716652 * 2 ^ 59
def prefixEnd_716652 : Nat := 4983230072969 + 3 ^ 40 * 716652 * 2
def baseEnd_716652 : Nat := 81774875112452295434263

theorem tailTrace_716652 : CollatzResearch.WordTrace tailWord_716652 prefixEnd_716652 81774875112452295434263 := by
  unfold tailWord_716652
  simp only [CollatzResearch.WordTrace]
  refine ⟨13069222899849836631196105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17425630533133115508261473 13069222899849836631196105)
  ·
    refine ⟨9801917174887377473397079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13069222899849836631196105 9801917174887377473397079)
    ·
      refine ⟨14702875762331066210095619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9801917174887377473397079 14702875762331066210095619)
      ·
        refine ⟨22054313643496599315143429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14702875762331066210095619 22054313643496599315143429)
        ·
          refine ⟨4135183808155612371589393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22054313643496599315143429 4135183808155612371589393)
          ·
            refine ⟨3101387856116709278692045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4135183808155612371589393 3101387856116709278692045)
            ·
              refine ⟨1163020446043765979509517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3101387856116709278692045 1163020446043765979509517)
              ·
                refine ⟨436132667266412242316069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1163020446043765979509517 436132667266412242316069)
                ·
                  refine ⟨81774875112452295434263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436132667266412242316069 81774875112452295434263)
                  ·
                    rfl

theorem cell22_716652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_716652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716652 prefixEnd_716652 := by exact prefixLift 716652
  have htrace : WordTrace (prefixWord ++ tailWord_716652) baseStart_716652 baseEnd_716652 := by
    simpa [prefixWord, tailWord_716652, baseEnd_716652] using wordTrace_append hprefix tailTrace_716652
  have hstable : (prefixWord ++ tailWord_716652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716652).length < 2 ^ (prefixWord ++ tailWord_716652).sum := by decide
  have hdescent : baseEnd_716652 < baseStart_716652 := by decide
  rcases family_descends (prefixWord ++ tailWord_716652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716665 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_716665 : Nat := 118140960795 + 716665 * 2 ^ 59
def prefixEnd_716665 : Nat := 4983230072969 + 3 ^ 40 * 716665 * 2
def baseEnd_716665 : Nat := 245329075503029185727749

theorem tailTrace_716665 : CollatzResearch.WordTrace tailWord_716665 prefixEnd_716665 245329075503029185727749 := by
  unfold tailWord_716665
  simp only [CollatzResearch.WordTrace]
  refine ⟨26138919948652576482615449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17425946632435050988410299 26138919948652576482615449)
  ·
    refine ⟨19604189961489432361961587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26138919948652576482615449 19604189961489432361961587)
    ·
      refine ⟨29406284942234148542942381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19604189961489432361961587 29406284942234148542942381)
      ·
        refine ⟨11027356853337805703603393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29406284942234148542942381 11027356853337805703603393)
        ·
          refine ⟨8270517640003354277702545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11027356853337805703603393 8270517640003354277702545)
          ·
            refine ⟨6202888230002515708276909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8270517640003354277702545 6202888230002515708276909)
            ·
              refine ⟨2326083086250943390603841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6202888230002515708276909 2326083086250943390603841)
              ·
                refine ⟨1744562314688207542952881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2326083086250943390603841 1744562314688207542952881)
                ·
                  refine ⟨1308421736016155657214661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1744562314688207542952881 1308421736016155657214661)
                  ·
                    refine ⟨245329075503029185727749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1308421736016155657214661 245329075503029185727749)
                    ·
                      rfl

theorem cell22_716665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_716665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716665 prefixEnd_716665 := by exact prefixLift 716665
  have htrace : WordTrace (prefixWord ++ tailWord_716665) baseStart_716665 baseEnd_716665 := by
    simpa [prefixWord, tailWord_716665, baseEnd_716665] using wordTrace_append hprefix tailTrace_716665
  have hstable : (prefixWord ++ tailWord_716665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716665).length < 2 ^ (prefixWord ++ tailWord_716665).sum := by decide
  have hdescent : baseEnd_716665 < baseStart_716665 := by decide
  rcases family_descends (prefixWord ++ tailWord_716665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716729 : List Nat := [1, 2, 1, 4, 2, 1, 3, 4, 1, 3]
def baseStart_716729 : Nat := 118140960795 + 716729 * 2 ^ 59
def prefixEnd_716729 : Nat := 4983230072969 + 3 ^ 40 * 716729 * 2
def baseEnd_716729 : Nat := 245350984010954352127553

theorem tailTrace_716729 : CollatzResearch.WordTrace tailWord_716729 prefixEnd_716729 245350984010954352127553 := by
  unfold tailWord_716729
  simp only [CollatzResearch.WordTrace]
  refine ⟨26141254220420715412945241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17427502813613810275296827 26141254220420715412945241)
  ·
    refine ⟨19605940665315536559708931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26141254220420715412945241 19605940665315536559708931)
    ·
      refine ⟨29408910997973304839563397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19605940665315536559708931 29408910997973304839563397)
      ·
        refine ⟨5514170812119994657418137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29408910997973304839563397 5514170812119994657418137)
        ·
          refine ⟨4135628109089995993063603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5514170812119994657418137 4135628109089995993063603)
          ·
            refine ⟨6203442163634993989595405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135628109089995993063603 6203442163634993989595405)
            ·
              refine ⟨2326290811363122746098277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6203442163634993989595405 2326290811363122746098277)
              ·
                refine ⟨436179527130585514893427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2326290811363122746098277 436179527130585514893427)
                ·
                  refine ⟨654269290695878272340141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436179527130585514893427 654269290695878272340141)
                  ·
                    refine ⟨245350984010954352127553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654269290695878272340141 245350984010954352127553)
                    ·
                      rfl

theorem cell22_716729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 1, 3].length) (baseStart_716729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716729 prefixEnd_716729 := by exact prefixLift 716729
  have htrace : WordTrace (prefixWord ++ tailWord_716729) baseStart_716729 baseEnd_716729 := by
    simpa [prefixWord, tailWord_716729, baseEnd_716729] using wordTrace_append hprefix tailTrace_716729
  have hstable : (prefixWord ++ tailWord_716729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716729).length < 2 ^ (prefixWord ++ tailWord_716729).sum := by decide
  have hdescent : baseEnd_716729 < baseStart_716729 := by decide
  rcases family_descends (prefixWord ++ tailWord_716729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716772 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_716772 : Nat := 118140960795 + 716772 * 2 ^ 59
def prefixEnd_716772 : Nat := 4983230072969 + 3 ^ 40 * 716772 * 2
def baseEnd_716772 : Nat := 245365703789716573302421

theorem tailTrace_716772 : CollatzResearch.WordTrace tailWord_716772 prefixEnd_716772 245365703789716573302421 := by
  unfold tailWord_716772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13071411279632466878380285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17428548372843289171173713 13071411279632466878380285)
  ·
    refine ⟨4901779229862175079392607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13071411279632466878380285 4901779229862175079392607)
    ·
      refine ⟨7352668844793262619088911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4901779229862175079392607 7352668844793262619088911)
      ·
        refine ⟨11029003267189893928633367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7352668844793262619088911 11029003267189893928633367)
        ·
          refine ⟨16543504900784840892950051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11029003267189893928633367 16543504900784840892950051)
          ·
            refine ⟨24815257351177261339425077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16543504900784840892950051 24815257351177261339425077)
            ·
              refine ⟨2326430376672868250571101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24815257351177261339425077 2326430376672868250571101)
              ·
                refine ⟨872411391252325593964163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2326430376672868250571101 872411391252325593964163)
                ·
                  refine ⟨1308617086878488390946245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 872411391252325593964163 1308617086878488390946245)
                  ·
                    refine ⟨245365703789716573302421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1308617086878488390946245 245365703789716573302421)
                    ·
                      rfl

theorem cell22_716772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_716772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716772 prefixEnd_716772 := by exact prefixLift 716772
  have htrace : WordTrace (prefixWord ++ tailWord_716772) baseStart_716772 baseEnd_716772 := by
    simpa [prefixWord, tailWord_716772, baseEnd_716772] using wordTrace_append hprefix tailTrace_716772
  have hstable : (prefixWord ++ tailWord_716772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716772).length < 2 ^ (prefixWord ++ tailWord_716772).sum := by decide
  have hdescent : baseEnd_716772 < baseStart_716772 := by decide
  rcases family_descends (prefixWord ++ tailWord_716772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716800 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_716800 : Nat := 118140960795 + 716800 * 2 ^ 59
def prefixEnd_716800 : Nat := 4983230072969 + 3 ^ 40 * 716800 * 2
def baseEnd_716800 : Nat := 245375288761933833602335

theorem tailTrace_716800 : CollatzResearch.WordTrace tailWord_716800 prefixEnd_716800 245375288761933833602335 := by
  unfold tailWord_716800
  simp only [CollatzResearch.WordTrace]
  refine ⟨13071921901581747269389927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17429229202108996359186569 13071921901581747269389927)
  ·
    refine ⟨19607882852372620904084891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13071921901581747269389927 19607882852372620904084891)
    ·
      refine ⟨29411824278558931356127337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19607882852372620904084891 29411824278558931356127337)
      ·
        refine ⟨22058868208919198517095503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29411824278558931356127337 22058868208919198517095503)
        ·
          refine ⟨33088302313378797775643255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22058868208919198517095503 33088302313378797775643255)
          ·
            refine ⟨49632453470068196663464883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33088302313378797775643255 49632453470068196663464883)
            ·
              refine ⟨74448680205102294995197325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49632453470068196663464883 74448680205102294995197325)
              ·
                refine ⟨27918255076913360623198997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74448680205102294995197325 27918255076913360623198997)
                ·
                  refine ⟨1308668206730313779212453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 27918255076913360623198997 1308668206730313779212453)
                  ·
                    refine ⟨245375288761933833602335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1308668206730313779212453 245375288761933833602335)
                    ·
                      rfl

theorem cell22_716800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_716800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716800 prefixEnd_716800 := by exact prefixLift 716800
  have htrace : WordTrace (prefixWord ++ tailWord_716800) baseStart_716800 baseEnd_716800 := by
    simpa [prefixWord, tailWord_716800, baseEnd_716800] using wordTrace_append hprefix tailTrace_716800
  have hstable : (prefixWord ++ tailWord_716800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716800).length < 2 ^ (prefixWord ++ tailWord_716800).sum := by decide
  have hdescent : baseEnd_716800 < baseStart_716800 := by decide
  rcases family_descends (prefixWord ++ tailWord_716800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716821 : List Nat := [1, 3, 2, 1, 5, 2, 1, 3, 4]
def baseStart_716821 : Nat := 118140960795 + 716821 * 2 ^ 59
def prefixEnd_716821 : Nat := 4983230072969 + 3 ^ 40 * 716821 * 2
def baseEnd_716821 : Nat := 81794159163698926275757

theorem tailTrace_716821 : CollatzResearch.WordTrace tailWord_716821 prefixEnd_716821 81794159163698926275757 := by
  unfold tailWord_716821
  simp only [CollatzResearch.WordTrace]
  refine ⟨26144609736087415125294317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17429739824058276750196211 26144609736087415125294317)
  ·
    refine ⟨9804228651032780671985369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26144609736087415125294317 9804228651032780671985369)
    ·
      refine ⟨7353171488274585503989027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9804228651032780671985369 7353171488274585503989027)
      ·
        refine ⟨11029757232411878255983541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7353171488274585503989027 11029757232411878255983541)
        ·
          refine ⟨1034039740538613586498457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11029757232411878255983541 1034039740538613586498457)
          ·
            refine ⟨775529805403960189873843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1034039740538613586498457 775529805403960189873843)
            ·
              refine ⟨1163294708105940284810765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775529805403960189873843 1163294708105940284810765)
              ·
                refine ⟨436235515539727606804037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1163294708105940284810765 436235515539727606804037)
                ·
                  refine ⟨81794159163698926275757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436235515539727606804037 81794159163698926275757)
                  ·
                    rfl

theorem cell22_716821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_716821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716821 prefixEnd_716821 := by exact prefixLift 716821
  have htrace : WordTrace (prefixWord ++ tailWord_716821) baseStart_716821 baseEnd_716821 := by
    simpa [prefixWord, tailWord_716821, baseEnd_716821] using wordTrace_append hprefix tailTrace_716821
  have hstable : (prefixWord ++ tailWord_716821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716821).length < 2 ^ (prefixWord ++ tailWord_716821).sum := by decide
  have hdescent : baseEnd_716821 < baseStart_716821 := by decide
  rcases family_descends (prefixWord ++ tailWord_716821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716847 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 3, 3]
def baseStart_716847 : Nat := 118140960795 + 716847 * 2 ^ 59
def prefixEnd_716847 : Nat := 4983230072969 + 3 ^ 40 * 716847 * 2
def baseEnd_716847 : Nat := 245391377822441377677191

theorem tailTrace_716847 : CollatzResearch.WordTrace tailWord_716847 prefixEnd_716847 245391377822441377677191 := by
  unfold tailWord_716847
  simp only [CollatzResearch.WordTrace]
  refine ⟨26145558033993221565740795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17430372022662147710493863 26145558033993221565740795)
  ·
    refine ⟨39218337050989832348611193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26145558033993221565740795 39218337050989832348611193)
    ·
      refine ⟨29413752788242374261458395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39218337050989832348611193 29413752788242374261458395)
      ·
        refine ⟨44120629182363561392187593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29413752788242374261458395 44120629182363561392187593)
        ·
          refine ⟨33090471886772671044140695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44120629182363561392187593 33090471886772671044140695)
          ·
            refine ⟨49635707830159006566211043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33090471886772671044140695 49635707830159006566211043)
            ·
              refine ⟨74453561745238509849316565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49635707830159006566211043 74453561745238509849316565)
              ·
                refine ⟨1745005353404027574593357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74453561745238509849316565 1745005353404027574593357)
                ·
                  refine ⟨654377007526510340472509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1745005353404027574593357 654377007526510340472509)
                  ·
                    refine ⟨245391377822441377677191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654377007526510340472509 245391377822441377677191)
                    ·
                      rfl

theorem cell22_716847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 3, 3].length) (baseStart_716847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716847 prefixEnd_716847 := by exact prefixLift 716847
  have htrace : WordTrace (prefixWord ++ tailWord_716847) baseStart_716847 baseEnd_716847 := by
    simpa [prefixWord, tailWord_716847, baseEnd_716847] using wordTrace_append hprefix tailTrace_716847
  have hstable : (prefixWord ++ tailWord_716847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716847).length < 2 ^ (prefixWord ++ tailWord_716847).sum := by decide
  have hdescent : baseEnd_716847 < baseStart_716847 := by decide
  rcases family_descends (prefixWord ++ tailWord_716847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716875 : List Nat := [1, 1, 1, 1, 3, 1, 2, 4, 1, 7]
def baseStart_716875 : Nat := 118140960795 + 716875 * 2 ^ 59
def prefixEnd_716875 : Nat := 4983230072969 + 3 ^ 40 * 716875 * 2
def baseEnd_716875 : Nat := 245400962794658637977105

theorem tailTrace_716875 : CollatzResearch.WordTrace tailWord_716875 prefixEnd_716875 245400962794658637977105 := by
  unfold tailWord_716875
  simp only [CollatzResearch.WordTrace]
  refine ⟨26146579277891782347760079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17431052851927854898506719 26146579277891782347760079)
  ·
    refine ⟨39219868916837673521640119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26146579277891782347760079 39219868916837673521640119)
    ·
      refine ⟨58829803375256510282460179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39219868916837673521640119 58829803375256510282460179)
      ·
        refine ⟨88244705062884765423690269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58829803375256510282460179 88244705062884765423690269)
        ·
          refine ⟨33091764398581787033883851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88244705062884765423690269 33091764398581787033883851)
          ·
            refine ⟨49637646597872680550825777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33091764398581787033883851 49637646597872680550825777)
            ·
              refine ⟨37228234948404510413119333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49637646597872680550825777 37228234948404510413119333)
              ·
                refine ⟨6980294052825845702459875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37228234948404510413119333 6980294052825845702459875)
                ·
                  refine ⟨10470441079238768553689813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6980294052825845702459875 10470441079238768553689813)
                  ·
                    refine ⟨245400962794658637977105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10470441079238768553689813 245400962794658637977105)
                    ·
                      rfl

theorem cell22_716875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_716875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716875 prefixEnd_716875 := by exact prefixLift 716875
  have htrace : WordTrace (prefixWord ++ tailWord_716875) baseStart_716875 baseEnd_716875 := by
    simpa [prefixWord, tailWord_716875, baseEnd_716875] using wordTrace_append hprefix tailTrace_716875
  have hstable : (prefixWord ++ tailWord_716875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716875).length < 2 ^ (prefixWord ++ tailWord_716875).sum := by decide
  have hdescent : baseEnd_716875 < baseStart_716875 := by decide
  rcases family_descends (prefixWord ++ tailWord_716875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716937 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_716937 : Nat := 118140960795 + 716937 * 2 ^ 59
def prefixEnd_716937 : Nat := 4983230072969 + 3 ^ 40 * 716937 * 2
def baseEnd_716937 : Nat := 245422186661711142926915

theorem tailTrace_716937 : CollatzResearch.WordTrace tailWord_716937 prefixEnd_716937 245422186661711142926915 := by
  unfold tailWord_716937
  simp only [CollatzResearch.WordTrace]
  refine ⟨26148840603667166936517065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17432560402444777957678043 26148840603667166936517065)
  ·
    refine ⟨19611630452750375202387799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26148840603667166936517065 19611630452750375202387799)
    ·
      refine ⟨29417445679125562803581699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19611630452750375202387799 29417445679125562803581699)
      ·
        refine ⟨44126168518688344205372549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29417445679125562803581699 44126168518688344205372549)
        ·
          refine ⟨8273656597254064538507353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44126168518688344205372549 8273656597254064538507353)
          ·
            refine ⟨6205242447940548403880515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8273656597254064538507353 6205242447940548403880515)
            ·
              refine ⟨9307863671910822605820773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6205242447940548403880515 9307863671910822605820773)
              ·
                refine ⟨1745224438483279238591395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9307863671910822605820773 1745224438483279238591395)
                ·
                  refine ⟨2617836657724918857887093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745224438483279238591395 2617836657724918857887093)
                  ·
                    refine ⟨245422186661711142926915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2617836657724918857887093 245422186661711142926915)
                    ·
                      rfl

theorem cell22_716937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_716937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716937 prefixEnd_716937 := by exact prefixLift 716937
  have htrace : WordTrace (prefixWord ++ tailWord_716937) baseStart_716937 baseEnd_716937 := by
    simpa [prefixWord, tailWord_716937, baseEnd_716937] using wordTrace_append hprefix tailTrace_716937
  have hstable : (prefixWord ++ tailWord_716937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716937).length < 2 ^ (prefixWord ++ tailWord_716937).sum := by decide
  have hdescent : baseEnd_716937 < baseStart_716937 := by decide
  rcases family_descends (prefixWord ++ tailWord_716937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_716990 : List Nat := [4, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_716990 : Nat := 118140960795 + 716990 * 2 ^ 59
def prefixEnd_716990 : Nat := 4983230072969 + 3 ^ 40 * 716990 * 2
def baseEnd_716990 : Nat := 81813443214945557117251

theorem tailTrace_716990 : CollatzResearch.WordTrace tailWord_716990 prefixEnd_716990 81813443214945557117251 := by
  unfold tailWord_716990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3268846709059394623524553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17433849114983437992130949 3268846709059394623524553)
  ·
    refine ⟨2451635031794545967643415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3268846709059394623524553 2451635031794545967643415)
    ·
      refine ⟨3677452547691818951465123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2451635031794545967643415 3677452547691818951465123)
      ·
        refine ⟨5516178821537728427197685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3677452547691818951465123 5516178821537728427197685)
        ·
          refine ⟨517141764519162040049783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5516178821537728427197685 517141764519162040049783)
          ·
            refine ⟨775712646778743060074675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517141764519162040049783 775712646778743060074675)
            ·
              refine ⟨1163568970168114590112013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775712646778743060074675 1163568970168114590112013)
              ·
                refine ⟨436338363813042971292005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1163568970168114590112013 436338363813042971292005)
                ·
                  refine ⟨81813443214945557117251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436338363813042971292005 81813443214945557117251)
                  ·
                    rfl

theorem cell22_716990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_716990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_716990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_716990 prefixEnd_716990 := by exact prefixLift 716990
  have htrace : WordTrace (prefixWord ++ tailWord_716990) baseStart_716990 baseEnd_716990 := by
    simpa [prefixWord, tailWord_716990, baseEnd_716990] using wordTrace_append hprefix tailTrace_716990
  have hstable : (prefixWord ++ tailWord_716990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_716990).length < 2 ^ (prefixWord ++ tailWord_716990).sum := by decide
  have hdescent : baseEnd_716990 < baseStart_716990 := by decide
  rcases family_descends (prefixWord ++ tailWord_716990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717016 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 3, 3]
def baseStart_717016 : Nat := 118140960795 + 717016 * 2 ^ 59
def prefixEnd_717016 : Nat := 4983230072969 + 3 ^ 40 * 717016 * 2
def baseEnd_717016 : Nat := 245449229976181270201673

theorem tailTrace_717016 : CollatzResearch.WordTrace tailWord_717016 prefixEnd_717016 245449229976181270201673 := by
  unfold tailWord_717016
  simp only [CollatzResearch.WordTrace]
  refine ⟨13075860985190481714321451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17434481313587308952428601 13075860985190481714321451)
  ·
    refine ⟨19613791477785722571482177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13075860985190481714321451 19613791477785722571482177)
    ·
      refine ⟨14710343608339291928611633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19613791477785722571482177 14710343608339291928611633)
      ·
        refine ⟨11032757706254468946458725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14710343608339291928611633 11032757706254468946458725)
        ·
          refine ⟨2068642069922712927461011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11032757706254468946458725 2068642069922712927461011)
          ·
            refine ⟨3102963104884069391191517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068642069922712927461011 3102963104884069391191517)
            ·
              refine ⟨1163611164331526021696819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3102963104884069391191517 1163611164331526021696819)
              ·
                refine ⟨1745416746497289032545229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163611164331526021696819 1745416746497289032545229)
                ·
                  refine ⟨654531279936483387204461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1745416746497289032545229 654531279936483387204461)
                  ·
                    refine ⟨245449229976181270201673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654531279936483387204461 245449229976181270201673)
                    ·
                      rfl

theorem cell22_717016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_717016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717016 prefixEnd_717016 := by exact prefixLift 717016
  have htrace : WordTrace (prefixWord ++ tailWord_717016) baseStart_717016 baseEnd_717016 := by
    simpa [prefixWord, tailWord_717016, baseEnd_717016] using wordTrace_append hprefix tailTrace_717016
  have hstable : (prefixWord ++ tailWord_717016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717016).length < 2 ^ (prefixWord ++ tailWord_717016).sum := by decide
  have hdescent : baseEnd_717016 < baseStart_717016 := by decide
  rcases family_descends (prefixWord ++ tailWord_717016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717063 : List Nat := [1, 1, 4, 5, 1, 1, 2, 2, 5]
def baseStart_717063 : Nat := 118140960795 + 717063 * 2 ^ 59
def prefixEnd_717063 : Nat := 4983230072969 + 3 ^ 40 * 717063 * 2
def baseEnd_717063 : Nat := 81821773012229604758843

theorem tailTrace_717063 : CollatzResearch.WordTrace tailWord_717063 prefixEnd_717063 81821773012229604758843 := by
  unfold tailWord_717063
  simp only [CollatzResearch.WordTrace]
  refine ⟨26153436201210690455603843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17435624134140460303735895 26153436201210690455603843)
  ·
    refine ⟨39230154301816035683405765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26153436201210690455603843 39230154301816035683405765)
    ·
      refine ⟨7355653931590506690638581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39230154301816035683405765 7355653931590506690638581)
      ·
        refine ⟨689592556086610002247367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7355653931590506690638581 689592556086610002247367)
        ·
          refine ⟨1034388834129915003371051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689592556086610002247367 1034388834129915003371051)
          ·
            refine ⟨1551583251194872505056577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034388834129915003371051 1551583251194872505056577)
            ·
              refine ⟨1163687438396154378792433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1551583251194872505056577 1163687438396154378792433)
              ·
                refine ⟨872765578797115784094325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1163687438396154378792433 872765578797115784094325)
                ·
                  refine ⟨81821773012229604758843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 872765578797115784094325 81821773012229604758843)
                  ·
                    rfl

theorem cell22_717063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 2, 5].length) (baseStart_717063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717063 prefixEnd_717063 := by exact prefixLift 717063
  have htrace : WordTrace (prefixWord ++ tailWord_717063) baseStart_717063 baseEnd_717063 := by
    simpa [prefixWord, tailWord_717063, baseEnd_717063] using wordTrace_append hprefix tailTrace_717063
  have hstable : (prefixWord ++ tailWord_717063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717063).length < 2 ^ (prefixWord ++ tailWord_717063).sum := by decide
  have hdescent : baseEnd_717063 < baseStart_717063 := by decide
  rcases family_descends (prefixWord ++ tailWord_717063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717089 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_717089 : Nat := 118140960795 + 717089 * 2 ^ 59
def prefixEnd_717089 : Nat := 4983230072969 + 3 ^ 40 * 717089 * 2
def baseEnd_717089 : Nat := 245474219368033413126449

theorem tailTrace_717089 : CollatzResearch.WordTrace tailWord_717089 prefixEnd_717089 245474219368033413126449 := by
  unfold tailWord_717089
  simp only [CollatzResearch.WordTrace]
  refine ⟨26154384499116496896050321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17436256332744331264033547 26154384499116496896050321)
  ·
    refine ⟨19615788374337372672037741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26154384499116496896050321 19615788374337372672037741)
    ·
      refine ⟨7355920640376514752014153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19615788374337372672037741 7355920640376514752014153)
      ·
        refine ⟨5516940480282386064010615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7355920640376514752014153 5516940480282386064010615)
        ·
          refine ⟨8275410720423579096015923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516940480282386064010615 8275410720423579096015923)
          ·
            refine ⟨12413116080635368644023885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8275410720423579096015923 12413116080635368644023885)
            ·
              refine ⟨4654918530238263241508957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12413116080635368644023885 4654918530238263241508957)
              ·
                refine ⟨1745594448839348715565859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4654918530238263241508957 1745594448839348715565859)
                ·
                  refine ⟨2618391673259023073348789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1745594448839348715565859 2618391673259023073348789)
                  ·
                    refine ⟨245474219368033413126449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2618391673259023073348789 245474219368033413126449)
                    ·
                      rfl

theorem cell22_717089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_717089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717089 prefixEnd_717089 := by exact prefixLift 717089
  have htrace : WordTrace (prefixWord ++ tailWord_717089) baseStart_717089 baseEnd_717089 := by
    simpa [prefixWord, tailWord_717089, baseEnd_717089] using wordTrace_append hprefix tailTrace_717089
  have hstable : (prefixWord ++ tailWord_717089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717089).length < 2 ^ (prefixWord ++ tailWord_717089).sum := by decide
  have hdescent : baseEnd_717089 < baseStart_717089 := by decide
  rcases family_descends (prefixWord ++ tailWord_717089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717104 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_717104 : Nat := 118140960795 + 717104 * 2 ^ 59
def prefixEnd_717104 : Nat := 4983230072969 + 3 ^ 40 * 717104 * 2
def baseEnd_717104 : Nat := 245479354174578374001403

theorem tailTrace_717104 : CollatzResearch.WordTrace tailWord_717104 prefixEnd_717104 245479354174578374001403 := by
  unfold tailWord_717104
  simp only [CollatzResearch.WordTrace]
  refine ⟨13077465797031077228923183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17436621062708102971897577 13077465797031077228923183)
  ·
    refine ⟨19616198695546615843384775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13077465797031077228923183 19616198695546615843384775)
    ·
      refine ⟨29424298043319923765077163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19616198695546615843384775 29424298043319923765077163)
      ·
        refine ⟨44136447064979885647615745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29424298043319923765077163 44136447064979885647615745)
        ·
          refine ⟨33102335298734914235711809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44136447064979885647615745 33102335298734914235711809)
          ·
            refine ⟨24826751474051185676783857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33102335298734914235711809 24826751474051185676783857)
            ·
              refine ⟨18620063605538389257587893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24826751474051185676783857 18620063605538389257587893)
              ·
                refine ⟨1745630963019223992898865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18620063605538389257587893 1745630963019223992898865)
                ·
                  refine ⟨1309223222264417994674149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1745630963019223992898865 1309223222264417994674149)
                  ·
                    refine ⟨245479354174578374001403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1309223222264417994674149 245479354174578374001403)
                    ·
                      rfl

theorem cell22_717104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_717104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717104 prefixEnd_717104 := by exact prefixLift 717104
  have htrace : WordTrace (prefixWord ++ tailWord_717104) baseStart_717104 baseEnd_717104 := by
    simpa [prefixWord, tailWord_717104, baseEnd_717104] using wordTrace_append hprefix tailTrace_717104
  have hstable : (prefixWord ++ tailWord_717104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717104).length < 2 ^ (prefixWord ++ tailWord_717104).sum := by decide
  have hdescent : baseEnd_717104 < baseStart_717104 := by decide
  rcases family_descends (prefixWord ++ tailWord_717104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717108 : List Nat := [2, 5, 1, 1, 1, 2, 1, 5, 4]
def baseStart_717108 : Nat := 118140960795 + 717108 * 2 ^ 59
def prefixEnd_717108 : Nat := 4983230072969 + 3 ^ 40 * 717108 * 2
def baseEnd_717108 : Nat := 81826907818774565633797

theorem tailTrace_717108 : CollatzResearch.WordTrace tailWord_717108 prefixEnd_717108 81826907818774565633797 := by
  unfold tailWord_717108
  simp only [CollatzResearch.WordTrace]
  refine ⟨13077538743023831570495989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17436718324031775427327985 13077538743023831570495989)
  ·
    refine ⟨1226019257158484209733999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13077538743023831570495989 1226019257158484209733999)
    ·
      refine ⟨1839028885737726314600999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1226019257158484209733999 1839028885737726314600999)
      ·
        refine ⟨2758543328606589471901499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839028885737726314600999 2758543328606589471901499)
        ·
          refine ⟨4137814992909884207852249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758543328606589471901499 4137814992909884207852249)
          ·
            refine ⟨3103361244682413155889187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4137814992909884207852249 3103361244682413155889187)
            ·
              refine ⟨4655041867023619733833781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3103361244682413155889187 4655041867023619733833781)
              ·
                refine ⟨436410175033464350046917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4655041867023619733833781 436410175033464350046917)
                ·
                  refine ⟨81826907818774565633797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436410175033464350046917 81826907818774565633797)
                  ·
                    rfl

theorem cell22_717108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_717108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717108 prefixEnd_717108 := by exact prefixLift 717108
  have htrace : WordTrace (prefixWord ++ tailWord_717108) baseStart_717108 baseEnd_717108 := by
    simpa [prefixWord, tailWord_717108, baseEnd_717108] using wordTrace_append hprefix tailTrace_717108
  have hstable : (prefixWord ++ tailWord_717108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717108).length < 2 ^ (prefixWord ++ tailWord_717108).sum := by decide
  have hdescent : baseEnd_717108 < baseStart_717108 := by decide
  rcases family_descends (prefixWord ++ tailWord_717108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717140 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_717140 : Nat := 118140960795 + 717140 * 2 ^ 59
def prefixEnd_717140 : Nat := 4983230072969 + 3 ^ 40 * 717140 * 2
def baseEnd_717140 : Nat := 245491677710286280101293

theorem tailTrace_717140 : CollatzResearch.WordTrace tailWord_717140 prefixEnd_717140 245491677710286280101293 := by
  unfold tailWord_717140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13078122310965866303078437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17437496414621155070771249 13078122310965866303078437)
  ·
    refine ⟨2452147933306099931827207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13078122310965866303078437 2452147933306099931827207)
    ·
      refine ⟨3678221899959149897740811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2452147933306099931827207 3678221899959149897740811)
      ·
        refine ⟨5517332849938724846611217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3678221899959149897740811 5517332849938724846611217)
        ·
          refine ⟨4137999637454043634958413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5517332849938724846611217 4137999637454043634958413)
          ·
            refine ⟨1551749864045266363109405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4137999637454043634958413 1551749864045266363109405)
            ·
              refine ⟨581906199016974886166027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1551749864045266363109405 581906199016974886166027)
              ·
                refine ⟨872859298525462329249041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581906199016974886166027 872859298525462329249041)
                ·
                  refine ⟨654644473894096746936781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 872859298525462329249041 654644473894096746936781)
                  ·
                    refine ⟨245491677710286280101293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654644473894096746936781 245491677710286280101293)
                    ·
                      rfl

theorem cell22_717140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_717140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717140 prefixEnd_717140 := by exact prefixLift 717140
  have htrace : WordTrace (prefixWord ++ tailWord_717140) baseStart_717140 baseEnd_717140 := by
    simpa [prefixWord, tailWord_717140, baseEnd_717140] using wordTrace_append hprefix tailTrace_717140
  have hstable : (prefixWord ++ tailWord_717140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717140).length < 2 ^ (prefixWord ++ tailWord_717140).sum := by decide
  have hdescent : baseEnd_717140 < baseStart_717140 := by decide
  rcases family_descends (prefixWord ++ tailWord_717140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717151 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 3, 3]
def baseStart_717151 : Nat := 118140960795 + 717151 * 2 ^ 59
def prefixEnd_717151 : Nat := 4983230072969 + 3 ^ 40 * 717151 * 2
def baseEnd_717151 : Nat := 245495443235085918076259

theorem tailTrace_717151 : CollatzResearch.WordTrace tailWord_717151 prefixEnd_717151 245495443235085918076259 := by
  unfold tailWord_717151
  simp only [CollatzResearch.WordTrace]
  refine ⟨26156645824891881484807307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17437763883261254323204871 26156645824891881484807307)
  ·
    refine ⟨39234968737337822227210961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26156645824891881484807307 39234968737337822227210961)
    ·
      refine ⟨29426226553003366670408221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39234968737337822227210961 29426226553003366670408221)
      ·
        refine ⟨11034834957376262501403083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29426226553003366670408221 11034834957376262501403083)
        ·
          refine ⟨16552252436064393752104625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11034834957376262501403083 16552252436064393752104625)
          ·
            refine ⟨12414189327048295314078469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16552252436064393752104625 12414189327048295314078469)
            ·
              refine ⟨2327660498821555371389713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12414189327048295314078469 2327660498821555371389713)
              ·
                refine ⟨1745745374116166528542285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2327660498821555371389713 1745745374116166528542285)
                ·
                  refine ⟨654654515293562448203357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1745745374116166528542285 654654515293562448203357)
                  ·
                    refine ⟨245495443235085918076259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654654515293562448203357 245495443235085918076259)
                    ·
                      rfl

theorem cell22_717151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3, 3].length) (baseStart_717151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717151 prefixEnd_717151 := by exact prefixLift 717151
  have htrace : WordTrace (prefixWord ++ tailWord_717151) baseStart_717151 baseEnd_717151 := by
    simpa [prefixWord, tailWord_717151, baseEnd_717151] using wordTrace_append hprefix tailTrace_717151
  have hstable : (prefixWord ++ tailWord_717151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717151).length < 2 ^ (prefixWord ++ tailWord_717151).sum := by decide
  have hdescent : baseEnd_717151 < baseStart_717151 := by decide
  rcases family_descends (prefixWord ++ tailWord_717151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717185 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 3, 3]
def baseStart_717185 : Nat := 118140960795 + 717185 * 2 ^ 59
def prefixEnd_717185 : Nat := 4983230072969 + 3 ^ 40 * 717185 * 2
def baseEnd_717185 : Nat := 245507082129921162726155

theorem tailTrace_717185 : CollatzResearch.WordTrace tailWord_717185 prefixEnd_717185 245507082129921162726155 := by
  unfold tailWord_717185
  simp only [CollatzResearch.WordTrace]
  refine ⟨26157885906768705291545009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17438590604512470194363339 26157885906768705291545009)
  ·
    refine ⟨19618414430076528968658757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26157885906768705291545009 19618414430076528968658757)
    ·
      refine ⟨3678452705639349181623517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19618414430076528968658757 3678452705639349181623517)
      ·
        refine ⟨1379419764614755943108819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3678452705639349181623517 1379419764614755943108819)
        ·
          refine ⟨2069129646922133914663229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379419764614755943108819 2069129646922133914663229)
          ·
            refine ⟨775923617595800217998711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2069129646922133914663229 775923617595800217998711)
            ·
              refine ⟨1163885426393700326998067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775923617595800217998711 1163885426393700326998067)
              ·
                refine ⟨1745828139590550490497101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163885426393700326998067 1745828139590550490497101)
                ·
                  refine ⟨654685552346456433936413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1745828139590550490497101 654685552346456433936413)
                  ·
                    refine ⟨245507082129921162726155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654685552346456433936413 245507082129921162726155)
                    ·
                      rfl

theorem cell22_717185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_717185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717185 prefixEnd_717185 := by exact prefixLift 717185
  have htrace : WordTrace (prefixWord ++ tailWord_717185) baseStart_717185 baseEnd_717185 := by
    simpa [prefixWord, tailWord_717185, baseEnd_717185] using wordTrace_append hprefix tailTrace_717185
  have hstable : (prefixWord ++ tailWord_717185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717185).length < 2 ^ (prefixWord ++ tailWord_717185).sum := by decide
  have hdescent : baseEnd_717185 < baseStart_717185 := by decide
  rcases family_descends (prefixWord ++ tailWord_717185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717198 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_717198 : Nat := 118140960795 + 717198 * 2 ^ 59
def prefixEnd_717198 : Nat := 4983230072969 + 3 ^ 40 * 717198 * 2
def baseEnd_717198 : Nat := 81837177431864487383705

theorem tailTrace_717198 : CollatzResearch.WordTrace tailWord_717198 prefixEnd_717198 81837177431864487383705 := by
  unfold tailWord_717198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269795006965201063971031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17438906703814405674512165 3269795006965201063971031)
  ·
    refine ⟨4904692510447801595956547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3269795006965201063971031 4904692510447801595956547)
    ·
      refine ⟨7357038765671702393934821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4904692510447801595956547 7357038765671702393934821)
      ·
        refine ⟨1379444768563444198862779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7357038765671702393934821 1379444768563444198862779)
        ·
          refine ⟨2069167152845166298294169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1379444768563444198862779 2069167152845166298294169)
          ·
            refine ⟨1551875364633874723720627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2069167152845166298294169 1551875364633874723720627)
            ·
              refine ⟨2327813046950812085580941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1551875364633874723720627 2327813046950812085580941)
              ·
                refine ⟨872929892606554532092853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2327813046950812085580941 872929892606554532092853)
                ·
                  refine ⟨81837177431864487383705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 872929892606554532092853 81837177431864487383705)
                  ·
                    rfl

theorem cell22_717198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_717198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717198 prefixEnd_717198 := by exact prefixLift 717198
  have htrace : WordTrace (prefixWord ++ tailWord_717198) baseStart_717198 baseEnd_717198 := by
    simpa [prefixWord, tailWord_717198, baseEnd_717198] using wordTrace_append hprefix tailTrace_717198
  have hstable : (prefixWord ++ tailWord_717198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717198).length < 2 ^ (prefixWord ++ tailWord_717198).sum := by decide
  have hdescent : baseEnd_717198 < baseStart_717198 := by decide
  rcases family_descends (prefixWord ++ tailWord_717198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717209 : List Nat := [1, 2, 1, 2, 1, 4, 2, 1, 8]
def baseStart_717209 : Nat := 118140960795 + 717209 * 2 ^ 59
def prefixEnd_717209 : Nat := 4983230072969 + 3 ^ 40 * 717209 * 2
def baseEnd_717209 : Nat := 81838432606797700042027

theorem tailTrace_717209 : CollatzResearch.WordTrace tailWord_717209 prefixEnd_717209 81838432606797700042027 := by
  unfold tailWord_717209
  simp only [CollatzResearch.WordTrace]
  refine ⟨26158761258681757390418681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17439174172454504926945787 26158761258681757390418681)
  ·
    refine ⟨19619070944011318042814011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26158761258681757390418681 19619070944011318042814011)
    ·
      refine ⟨29428606416016977064221017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19619070944011318042814011 29428606416016977064221017)
      ·
        refine ⟨22071454812012732798165763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29428606416016977064221017 22071454812012732798165763)
        ·
          refine ⟨33107182218019099197248645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22071454812012732798165763 33107182218019099197248645)
          ·
            refine ⟨6207596665878581099484121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33107182218019099197248645 6207596665878581099484121)
            ·
              refine ⟨4655697499408935824613091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6207596665878581099484121 4655697499408935824613091)
              ·
                refine ⟨6983546249113403736919637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4655697499408935824613091 6983546249113403736919637)
                ·
                  refine ⟨81838432606797700042027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6983546249113403736919637 81838432606797700042027)
                  ·
                    rfl

theorem cell22_717209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_717209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717209 prefixEnd_717209 := by exact prefixLift 717209
  have htrace : WordTrace (prefixWord ++ tailWord_717209) baseStart_717209 baseEnd_717209 := by
    simpa [prefixWord, tailWord_717209, baseEnd_717209] using wordTrace_append hprefix tailTrace_717209
  have hstable : (prefixWord ++ tailWord_717209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717209).length < 2 ^ (prefixWord ++ tailWord_717209).sum := by decide
  have hdescent : baseEnd_717209 < baseStart_717209 := by decide
  rcases family_descends (prefixWord ++ tailWord_717209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717258 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 2, 3]
def baseStart_717258 : Nat := 118140960795 + 717258 * 2 ^ 59
def prefixEnd_717258 : Nat := 4983230072969 + 3 ^ 40 * 717258 * 2
def baseEnd_717258 : Nat := 245532071521773305650931

theorem tailTrace_717258 : CollatzResearch.WordTrace tailWord_717258 prefixEnd_717258 245532071521773305650931 := by
  unfold tailWord_717258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6540137108876059689738107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17440365623669492505968285 6540137108876059689738107)
  ·
    refine ⟨9810205663314089534607161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6540137108876059689738107 9810205663314089534607161)
    ·
      refine ⟨7357654247485567150955371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9810205663314089534607161 7357654247485567150955371)
      ·
        refine ⟨11036481371228350726433057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7357654247485567150955371 11036481371228350726433057)
        ·
          refine ⟨8277361028421263044824793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11036481371228350726433057 8277361028421263044824793)
          ·
            refine ⟨6208020771315947283618595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8277361028421263044824793 6208020771315947283618595)
            ·
              refine ⟨9312031156973920925427893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6208020771315947283618595 9312031156973920925427893)
              ·
                refine ⟨873002920966305086758865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9312031156973920925427893 873002920966305086758865)
                ·
                  refine ⟨654752190724728815069149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 873002920966305086758865 654752190724728815069149)
                  ·
                    refine ⟨245532071521773305650931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654752190724728815069149 245532071521773305650931)
                    ·
                      rfl

theorem cell22_717258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_717258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717258 prefixEnd_717258 := by exact prefixLift 717258
  have htrace : WordTrace (prefixWord ++ tailWord_717258) baseStart_717258 baseEnd_717258 := by
    simpa [prefixWord, tailWord_717258, baseEnd_717258] using wordTrace_append hprefix tailTrace_717258
  have hstable : (prefixWord ++ tailWord_717258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717258).length < 2 ^ (prefixWord ++ tailWord_717258).sum := by decide
  have hdescent : baseEnd_717258 < baseStart_717258 := by decide
  rcases family_descends (prefixWord ++ tailWord_717258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717354 : List Nat := [3, 1, 4, 1, 1, 3, 3, 2, 1, 3]
def baseStart_717354 : Nat := 118140960795 + 717354 * 2 ^ 59
def prefixEnd_717354 : Nat := 4983230072969 + 3 ^ 40 * 717354 * 2
def baseEnd_717354 : Nat := 245564934283661055250637

theorem tailTrace_717354 : CollatzResearch.WordTrace tailWord_717354 prefixEnd_717354 245564934283661055250637 := by
  unfold tailWord_717354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6541012460789111788611779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17442699895437631436298077 6541012460789111788611779)
  ·
    refine ⟨9811518691183667682917669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6541012460789111788611779 9811518691183667682917669)
    ·
      refine ⟨1839659754596937690547063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9811518691183667682917669 1839659754596937690547063)
      ·
        refine ⟨2759489631895406535820595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1839659754596937690547063 2759489631895406535820595)
        ·
          refine ⟨4139234447843109803730893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2759489631895406535820595 4139234447843109803730893)
          ·
            refine ⟨1552212917941166176399085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4139234447843109803730893 1552212917941166176399085)
            ·
              refine ⟨582079844227937316149657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1552212917941166176399085 582079844227937316149657)
              ·
                refine ⟨436559883170952987112243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582079844227937316149657 436559883170952987112243)
                ·
                  refine ⟨654839824756429480668365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436559883170952987112243 654839824756429480668365)
                  ·
                    refine ⟨245564934283661055250637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654839824756429480668365 245564934283661055250637)
                    ·
                      rfl

theorem cell22_717354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_717354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717354 prefixEnd_717354 := by exact prefixLift 717354
  have htrace : WordTrace (prefixWord ++ tailWord_717354) baseStart_717354 baseEnd_717354 := by
    simpa [prefixWord, tailWord_717354, baseEnd_717354] using wordTrace_append hprefix tailTrace_717354
  have hstable : (prefixWord ++ tailWord_717354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717354).length < 2 ^ (prefixWord ++ tailWord_717354).sum := by decide
  have hdescent : baseEnd_717354 < baseStart_717354 := by decide
  rcases family_descends (prefixWord ++ tailWord_717354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717391 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 1, 6]
def baseStart_717391 : Nat := 118140960795 + 717391 * 2 ^ 59
def prefixEnd_717391 : Nat := 4983230072969 + 3 ^ 40 * 717391 * 2
def baseEnd_717391 : Nat := 245577600139805292075523

theorem tailTrace_717391 : CollatzResearch.WordTrace tailWord_717391 prefixEnd_717391 245577600139805292075523 := by
  unfold tailWord_717391
  simp only [CollatzResearch.WordTrace]
  refine ⟨26165399344022402473544027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17443599562681601649029351 26165399344022402473544027)
  ·
    refine ⟨39248099016033603710316041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26165399344022402473544027 39248099016033603710316041)
    ·
      refine ⟨29436074262025202782737031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39248099016033603710316041 29436074262025202782737031)
      ·
        refine ⟨44154111393037804174105547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29436074262025202782737031 44154111393037804174105547)
        ·
          refine ⟨66231167089556706261158321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44154111393037804174105547 66231167089556706261158321)
          ·
            refine ⟨49673375317167529695868741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66231167089556706261158321 49673375317167529695868741)
            ·
              refine ⟨9313757871968911817975389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49673375317167529695868741 9313757871968911817975389)
              ·
                refine ⟨3492659201988341931740771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9313757871968911817975389 3492659201988341931740771)
                ·
                  refine ⟨5238988802982512897611157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3492659201988341931740771 5238988802982512897611157)
                  ·
                    refine ⟨245577600139805292075523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5238988802982512897611157 245577600139805292075523)
                    ·
                      rfl

theorem cell22_717391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_717391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717391 prefixEnd_717391 := by exact prefixLift 717391
  have htrace : WordTrace (prefixWord ++ tailWord_717391) baseStart_717391 baseEnd_717391 := by
    simpa [prefixWord, tailWord_717391, baseEnd_717391] using wordTrace_append hprefix tailTrace_717391
  have hstable : (prefixWord ++ tailWord_717391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717391).length < 2 ^ (prefixWord ++ tailWord_717391).sum := by decide
  have hdescent : baseEnd_717391 < baseStart_717391 := by decide
  rcases family_descends (prefixWord ++ tailWord_717391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717393 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_717393 : Nat := 118140960795 + 717393 * 2 ^ 59
def prefixEnd_717393 : Nat := 4983230072969 + 3 ^ 40 * 717393 * 2
def baseEnd_717393 : Nat := 245578284780677953525517

theorem tailTrace_717393 : CollatzResearch.WordTrace tailWord_717393 prefixEnd_717393 245578284780677953525517 := by
  unfold tailWord_717393
  simp only [CollatzResearch.WordTrace]
  refine ⟨26165472290015156815116833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17443648193343437876744555 26165472290015156815116833)
  ·
    refine ⟨19624104217511367611337625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26165472290015156815116833 19624104217511367611337625)
    ·
      refine ⟨14718078163133525708503219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19624104217511367611337625 14718078163133525708503219)
      ·
        refine ⟨22077117244700288562754829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14718078163133525708503219 22077117244700288562754829)
        ·
          refine ⟨8278918966762608211033061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22077117244700288562754829 8278918966762608211033061)
          ·
            refine ⟨1552297306267989039568699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8278918966762608211033061 1552297306267989039568699)
            ·
              refine ⟨2328445959401983559353049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1552297306267989039568699 2328445959401983559353049)
              ·
                refine ⟨1746334469551487669514787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2328445959401983559353049 1746334469551487669514787)
                ·
                  refine ⟨2619501704327231504272181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1746334469551487669514787 2619501704327231504272181)
                  ·
                    refine ⟨245578284780677953525517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2619501704327231504272181 245578284780677953525517)
                    ·
                      rfl

theorem cell22_717393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_717393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717393 prefixEnd_717393 := by exact prefixLift 717393
  have htrace : WordTrace (prefixWord ++ tailWord_717393) baseStart_717393 baseEnd_717393 := by
    simpa [prefixWord, tailWord_717393, baseEnd_717393] using wordTrace_append hprefix tailTrace_717393
  have hstable : (prefixWord ++ tailWord_717393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717393).length < 2 ^ (prefixWord ++ tailWord_717393).sum := by decide
  have hdescent : baseEnd_717393 < baseStart_717393 := by decide
  rcases family_descends (prefixWord ++ tailWord_717393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717408 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_717408 : Nat := 118140960795 + 717408 * 2 ^ 59
def prefixEnd_717408 : Nat := 4983230072969 + 3 ^ 40 * 717408 * 2
def baseEnd_717408 : Nat := 245583419587222914400471

theorem tailTrace_717408 : CollatzResearch.WordTrace tailWord_717408 prefixEnd_717408 245583419587222914400471 := by
  unfold tailWord_717408
  simp only [CollatzResearch.WordTrace]
  refine ⟨13083009692480407188456439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17444012923307209584608585 13083009692480407188456439)
  ·
    refine ⟨19624514538720610782684659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13083009692480407188456439 19624514538720610782684659)
    ·
      refine ⟨29436771808080916174026989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19624514538720610782684659 29436771808080916174026989)
      ·
        refine ⟨11038789428030343565260121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29436771808080916174026989 11038789428030343565260121)
        ·
          refine ⟨8279092071022757673945091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11038789428030343565260121 8279092071022757673945091)
          ·
            refine ⟨12418638106534136510917637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8279092071022757673945091 12418638106534136510917637)
            ·
              refine ⟨2328494644975150595797057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12418638106534136510917637 2328494644975150595797057)
              ·
                refine ⟨1746370983731362946847793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2328494644975150595797057 1746370983731362946847793)
                ·
                  refine ⟨1309778237798522210135845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1746370983731362946847793 1309778237798522210135845)
                  ·
                    refine ⟨245583419587222914400471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1309778237798522210135845 245583419587222914400471)
                    ·
                      rfl

theorem cell22_717408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_717408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717408 prefixEnd_717408 := by exact prefixLift 717408
  have htrace : WordTrace (prefixWord ++ tailWord_717408) baseStart_717408 baseEnd_717408 := by
    simpa [prefixWord, tailWord_717408, baseEnd_717408] using wordTrace_append hprefix tailTrace_717408
  have hstable : (prefixWord ++ tailWord_717408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717408).length < 2 ^ (prefixWord ++ tailWord_717408).sum := by decide
  have hdescent : baseEnd_717408 < baseStart_717408 := by decide
  rcases family_descends (prefixWord ++ tailWord_717408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717472 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 3, 3]
def baseStart_717472 : Nat := 118140960795 + 717472 * 2 ^ 59
def prefixEnd_717472 : Nat := 4983230072969 + 3 ^ 40 * 717472 * 2
def baseEnd_717472 : Nat := 245605328095148080800275

theorem tailTrace_717472 : CollatzResearch.WordTrace tailWord_717472 prefixEnd_717472 245605328095148080800275 := by
  unfold tailWord_717472
  simp only [CollatzResearch.WordTrace]
  refine ⟨13084176828364476653621335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17445569104485968871495113 13084176828364476653621335)
  ·
    refine ⟨19626265242546714980432003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13084176828364476653621335 19626265242546714980432003)
    ·
      refine ⟨29439397863820072470648005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19626265242546714980432003 29439397863820072470648005)
      ·
        refine ⟨5519887099466263588246501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29439397863820072470648005 5519887099466263588246501)
        ·
          refine ⟨1034978831149924422796219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5519887099466263588246501 1034978831149924422796219)
          ·
            refine ⟨1552468246724886634194329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034978831149924422796219 1552468246724886634194329)
            ·
              refine ⟨1164351185043664975645747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1552468246724886634194329 1164351185043664975645747)
              ·
                refine ⟨1746526777565497463468621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164351185043664975645747 1746526777565497463468621)
                ·
                  refine ⟨654947541587061548800733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1746526777565497463468621 654947541587061548800733)
                  ·
                    refine ⟨245605328095148080800275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 654947541587061548800733 245605328095148080800275)
                    ·
                      rfl

theorem cell22_717472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 3, 3].length) (baseStart_717472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717472 prefixEnd_717472 := by exact prefixLift 717472
  have htrace : WordTrace (prefixWord ++ tailWord_717472) baseStart_717472 baseEnd_717472 := by
    simpa [prefixWord, tailWord_717472, baseEnd_717472] using wordTrace_append hprefix tailTrace_717472
  have hstable : (prefixWord ++ tailWord_717472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717472).length < 2 ^ (prefixWord ++ tailWord_717472).sum := by decide
  have hdescent : baseEnd_717472 < baseStart_717472 := by decide
  rcases family_descends (prefixWord ++ tailWord_717472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717560 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 2, 4]
def baseStart_717560 : Nat := 118140960795 + 717560 * 2 ^ 59
def prefixEnd_717560 : Nat := 4983230072969 + 3 ^ 40 * 717560 * 2
def baseEnd_717560 : Nat := 245635452293545184600005

theorem tailTrace_717560 : CollatzResearch.WordTrace tailWord_717560 prefixEnd_717560 245635452293545184600005 := by
  unfold tailWord_717560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13085781640205072168223067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17447708853606762890964089 13085781640205072168223067)
  ·
    refine ⟨19628672460307608252334601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13085781640205072168223067 19628672460307608252334601)
    ·
      refine ⟨14721504345230706189250951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19628672460307608252334601 14721504345230706189250951)
      ·
        refine ⟨22082256517846059283876427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14721504345230706189250951 22082256517846059283876427)
        ·
          refine ⟨33123384776769088925814641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22082256517846059283876427 33123384776769088925814641)
          ·
            refine ⟨24842538582576816694360981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33123384776769088925814641 24842538582576816694360981)
            ·
              refine ⟨1164493996058288282548171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24842538582576816694360981 1164493996058288282548171)
              ·
                refine ⟨1746740994087432423822257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164493996058288282548171 1746740994087432423822257)
                ·
                  refine ⟨1310055745565574317866693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1746740994087432423822257 1310055745565574317866693)
                  ·
                    refine ⟨245635452293545184600005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1310055745565574317866693 245635452293545184600005)
                    ·
                      rfl

theorem cell22_717560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_717560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717560 prefixEnd_717560 := by exact prefixLift 717560
  have htrace : WordTrace (prefixWord ++ tailWord_717560) baseStart_717560 baseEnd_717560 := by
    simpa [prefixWord, tailWord_717560, baseEnd_717560] using wordTrace_append hprefix tailTrace_717560
  have hstable : (prefixWord ++ tailWord_717560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717560).length < 2 ^ (prefixWord ++ tailWord_717560).sum := by decide
  have hdescent : baseEnd_717560 < baseStart_717560 := by decide
  rcases family_descends (prefixWord ++ tailWord_717560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717603 : List Nat := [1, 1, 1, 4, 2, 1, 1, 2, 9]
def baseStart_717603 : Nat := 118140960795 + 717603 * 2 ^ 59
def prefixEnd_717603 : Nat := 4983230072969 + 3 ^ 40 * 717603 * 2
def baseEnd_717603 : Nat := 81883390690769135258291

theorem tailTrace_717603 : CollatzResearch.WordTrace tailWord_717603 prefixEnd_717603 81883390690769135258291 := by
  unfold tailWord_717603
  simp only [CollatzResearch.WordTrace]
  refine ⟨26173131619254362680261463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17448754412836241786840975 26173131619254362680261463)
  ·
    refine ⟨39259697428881544020392195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26173131619254362680261463 39259697428881544020392195)
    ·
      refine ⟨58889546143322316030588293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39259697428881544020392195 58889546143322316030588293)
      ·
        refine ⟨11041789901872934255735305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58889546143322316030588293 11041789901872934255735305)
        ·
          refine ⟨8281342426404700691801479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11041789901872934255735305 8281342426404700691801479)
          ·
            refine ⟨12422013639607051037702219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8281342426404700691801479 12422013639607051037702219)
            ·
              refine ⟨18633020459410576556553329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12422013639607051037702219 18633020459410576556553329)
              ·
                refine ⟨13974765344557932417414997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18633020459410576556553329 13974765344557932417414997)
                ·
                  refine ⟨81883390690769135258291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13974765344557932417414997 81883390690769135258291)
                  ·
                    rfl

theorem cell22_717603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 2, 9].length) (baseStart_717603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717603 prefixEnd_717603 := by exact prefixLift 717603
  have htrace : WordTrace (prefixWord ++ tailWord_717603) baseStart_717603 baseEnd_717603 := by
    simpa [prefixWord, tailWord_717603, baseEnd_717603] using wordTrace_append hprefix tailTrace_717603
  have hstable : (prefixWord ++ tailWord_717603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717603).length < 2 ^ (prefixWord ++ tailWord_717603).sum := by decide
  have hdescent : baseEnd_717603 < baseStart_717603 := by decide
  rcases family_descends (prefixWord ++ tailWord_717603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717624 : List Nat := [2, 1, 2, 1, 3, 2, 4, 3, 1, 3]
def baseStart_717624 : Nat := 118140960795 + 717624 * 2 ^ 59
def prefixEnd_717624 : Nat := 4983230072969 + 3 ^ 40 * 717624 * 2
def baseEnd_717624 : Nat := 245657360801470350999809

theorem tailTrace_717624 : CollatzResearch.WordTrace tailWord_717624 prefixEnd_717624 245657360801470350999809 := by
  unfold tailWord_717624
  simp only [CollatzResearch.WordTrace]
  refine ⟨13086948776089141633387963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17449265034785522177850617 13086948776089141633387963)
  ·
    refine ⟨19630423164133712450081945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13086948776089141633387963 19630423164133712450081945)
    ·
      refine ⟨14722817373100284337561459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19630423164133712450081945 14722817373100284337561459)
      ·
        refine ⟨22084226059650426506342189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14722817373100284337561459 22084226059650426506342189)
        ·
          refine ⟨8281584772368909939878321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22084226059650426506342189 8281584772368909939878321)
          ·
            refine ⟨6211188579276682454908741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8281584772368909939878321 6211188579276682454908741)
            ·
              refine ⟨1164597858614377960295389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6211188579276682454908741 1164597858614377960295389)
              ·
                refine ⟨436724196980391735110771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1164597858614377960295389 436724196980391735110771)
                ·
                  refine ⟨655086295470587602666157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436724196980391735110771 655086295470587602666157)
                  ·
                    refine ⟨245657360801470350999809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 655086295470587602666157 245657360801470350999809)
                    ·
                      rfl

theorem cell22_717624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 3, 1, 3].length) (baseStart_717624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717624 prefixEnd_717624 := by exact prefixLift 717624
  have htrace : WordTrace (prefixWord ++ tailWord_717624) baseStart_717624 baseEnd_717624 := by
    simpa [prefixWord, tailWord_717624, baseEnd_717624] using wordTrace_append hprefix tailTrace_717624
  have hstable : (prefixWord ++ tailWord_717624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717624).length < 2 ^ (prefixWord ++ tailWord_717624).sum := by decide
  have hdescent : baseEnd_717624 < baseStart_717624 := by decide
  rcases family_descends (prefixWord ++ tailWord_717624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717667 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 1, 4]
def baseStart_717667 : Nat := 118140960795 + 717667 * 2 ^ 59
def prefixEnd_717667 : Nat := 4983230072969 + 3 ^ 40 * 717667 * 2
def baseEnd_717667 : Nat := 245672080580232572174677

theorem tailTrace_717667 : CollatzResearch.WordTrace tailWord_717667 prefixEnd_717667 245672080580232572174677 := by
  unfold tailWord_717667
  simp only [CollatzResearch.WordTrace]
  refine ⟨26175465891022501610591255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17450310594015001073727503 26175465891022501610591255)
  ·
    refine ⟨39263198836533752415886883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26175465891022501610591255 39263198836533752415886883)
    ·
      refine ⟨58894798254800628623830325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39263198836533752415886883 58894798254800628623830325)
      ·
        refine ⟨5521387336387558933484093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58894798254800628623830325 5521387336387558933484093)
        ·
          refine ⟨2070520251145334600056535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5521387336387558933484093 2070520251145334600056535)
          ·
            refine ⟨3105780376718001900084803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070520251145334600056535 3105780376718001900084803)
            ·
              refine ⟨4658670565077002850127205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3105780376718001900084803 4658670565077002850127205)
              ·
                refine ⟨873500730951938034398851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4658670565077002850127205 873500730951938034398851)
                ·
                  refine ⟨1310251096427907051598277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873500730951938034398851 1310251096427907051598277)
                  ·
                    refine ⟨245672080580232572174677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1310251096427907051598277 245672080580232572174677)
                    ·
                      rfl

theorem cell22_717667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 4].length) (baseStart_717667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717667 prefixEnd_717667 := by exact prefixLift 717667
  have htrace : WordTrace (prefixWord ++ tailWord_717667) baseStart_717667 baseEnd_717667 := by
    simpa [prefixWord, tailWord_717667, baseEnd_717667] using wordTrace_append hprefix tailTrace_717667
  have hstable : (prefixWord ++ tailWord_717667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717667).length < 2 ^ (prefixWord ++ tailWord_717667).sum := by decide
  have hdescent : baseEnd_717667 < baseStart_717667 := by decide
  rcases family_descends (prefixWord ++ tailWord_717667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717680 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_717680 : Nat := 118140960795 + 717680 * 2 ^ 59
def prefixEnd_717680 : Nat := 4983230072969 + 3 ^ 40 * 717680 * 2
def baseEnd_717680 : Nat := 245676530745904871599637

theorem tailTrace_717680 : CollatzResearch.WordTrace tailWord_717680 prefixEnd_717680 245676530745904871599637 := by
  unfold tailWord_717680
  simp only [CollatzResearch.WordTrace]
  refine ⟨13087970019987702415407247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17450626693316936553876329 13087970019987702415407247)
  ·
    refine ⟨19631955029981553623110871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13087970019987702415407247 19631955029981553623110871)
    ·
      refine ⟨29447932544972330434666307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19631955029981553623110871 29447932544972330434666307)
      ·
        refine ⟨44171898817458495651999461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29447932544972330434666307 44171898817458495651999461)
        ·
          refine ⟨8282231028273467934749899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44171898817458495651999461 8282231028273467934749899)
          ·
            refine ⟨12423346542410201902124849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8282231028273467934749899 12423346542410201902124849)
            ·
              refine ⟨9317509906807651426593637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12423346542410201902124849 9317509906807651426593637)
              ·
                refine ⟨1747033107526434642486307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9317509906807651426593637 1747033107526434642486307)
                ·
                  refine ⟨2620549661289651963729461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747033107526434642486307 2620549661289651963729461)
                  ·
                    refine ⟨245676530745904871599637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2620549661289651963729461 245676530745904871599637)
                    ·
                      rfl

theorem cell22_717680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_717680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717680 prefixEnd_717680 := by exact prefixLift 717680
  have htrace : WordTrace (prefixWord ++ tailWord_717680) baseStart_717680 baseEnd_717680 := by
    simpa [prefixWord, tailWord_717680, baseEnd_717680] using wordTrace_append hprefix tailTrace_717680
  have hstable : (prefixWord ++ tailWord_717680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717680).length < 2 ^ (prefixWord ++ tailWord_717680).sum := by decide
  have hdescent : baseEnd_717680 < baseStart_717680 := by decide
  rcases family_descends (prefixWord ++ tailWord_717680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717695 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 4, 4]
def baseStart_717695 : Nat := 118140960795 + 717695 * 2 ^ 59
def prefixEnd_717695 : Nat := 4983230072969 + 3 ^ 40 * 717695 * 2
def baseEnd_717695 : Nat := 245681665552449832474591

theorem tailTrace_717695 : CollatzResearch.WordTrace tailWord_717695 prefixEnd_717695 245681665552449832474591 := by
  unfold tailWord_717695
  simp only [CollatzResearch.WordTrace]
  refine ⟨26176487134921062392610539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17450991423280708261740359 26176487134921062392610539)
  ·
    refine ⟨39264730702381593588915809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26176487134921062392610539 39264730702381593588915809)
    ·
      refine ⟨29448548026786195191686857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39264730702381593588915809 29448548026786195191686857)
      ·
        refine ⟨22086411020089646393765143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29448548026786195191686857 22086411020089646393765143)
        ·
          refine ⟨33129616530134469590647715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22086411020089646393765143 33129616530134469590647715)
          ·
            refine ⟨49694424795201704385971573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33129616530134469590647715 49694424795201704385971573)
            ·
              refine ⟨4658852324550159786184835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49694424795201704385971573 4658852324550159786184835)
              ·
                refine ⟨6988278486825239679277253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4658852324550159786184835 6988278486825239679277253)
                ·
                  refine ⟨1310302216279732439864485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6988278486825239679277253 1310302216279732439864485)
                  ·
                    refine ⟨245681665552449832474591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1310302216279732439864485 245681665552449832474591)
                    ·
                      rfl

theorem cell22_717695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_717695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717695 prefixEnd_717695 := by exact prefixLift 717695
  have htrace : WordTrace (prefixWord ++ tailWord_717695) baseStart_717695 baseEnd_717695 := by
    simpa [prefixWord, tailWord_717695, baseEnd_717695] using wordTrace_append hprefix tailTrace_717695
  have hstable : (prefixWord ++ tailWord_717695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717695).length < 2 ^ (prefixWord ++ tailWord_717695).sum := by decide
  have hdescent : baseEnd_717695 < baseStart_717695 := by decide
  rcases family_descends (prefixWord ++ tailWord_717695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717699 : List Nat := [1, 1, 1, 3, 4, 1, 5, 2, 4]
def baseStart_717699 : Nat := 118140960795 + 717699 * 2 ^ 59
def prefixEnd_717699 : Nat := 4983230072969 + 3 ^ 40 * 717699 * 2
def baseEnd_717699 : Nat := 81894344944731718458193

theorem tailTrace_717699 : CollatzResearch.WordTrace tailWord_717699 prefixEnd_717699 81894344944731718458193 := by
  unfold tailWord_717699
  simp only [CollatzResearch.WordTrace]
  refine ⟨26176633026906571075756151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17451088684604380717170767 26176633026906571075756151)
  ·
    refine ⟨39264949540359856613634227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26176633026906571075756151 39264949540359856613634227)
    ·
      refine ⟨58897424310539784920451341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39264949540359856613634227 58897424310539784920451341)
      ·
        refine ⟨22086534116452419345169253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58897424310539784920451341 22086534116452419345169253)
        ·
          refine ⟨4141225146834828627219235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22086534116452419345169253 4141225146834828627219235)
          ·
            refine ⟨6211837720252242940828853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4141225146834828627219235 6211837720252242940828853)
            ·
              refine ⟨582359786273647775702705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6211837720252242940828853 582359786273647775702705)
              ·
                refine ⟨436769839705235831777029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582359786273647775702705 436769839705235831777029)
                ·
                  refine ⟨81894344944731718458193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436769839705235831777029 81894344944731718458193)
                  ·
                    rfl

theorem cell22_717699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 2, 4].length) (baseStart_717699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717699 prefixEnd_717699 := by exact prefixLift 717699
  have htrace : WordTrace (prefixWord ++ tailWord_717699) baseStart_717699 baseEnd_717699 := by
    simpa [prefixWord, tailWord_717699, baseEnd_717699] using wordTrace_append hprefix tailTrace_717699
  have hstable : (prefixWord ++ tailWord_717699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717699).length < 2 ^ (prefixWord ++ tailWord_717699).sum := by decide
  have hdescent : baseEnd_717699 < baseStart_717699 := by decide
  rcases family_descends (prefixWord ++ tailWord_717699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717718 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_717718 : Nat := 118140960795 + 717718 * 2 ^ 59
def prefixEnd_717718 : Nat := 4983230072969 + 3 ^ 40 * 717718 * 2
def baseEnd_717718 : Nat := 245689538922485439149521

theorem tailTrace_717718 : CollatzResearch.WordTrace tailWord_717718 prefixEnd_717718 245689538922485439149521 := by
  unfold tailWord_717718
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636082875864858582543613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17451550675891824880465205 1636082875864858582543613)
  ·
    refine ⟨613531078449321968453855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1636082875864858582543613 613531078449321968453855)
    ·
      refine ⟨920296617673982952680783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613531078449321968453855 920296617673982952680783)
      ·
        refine ⟨1380444926510974429021175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920296617673982952680783 1380444926510974429021175)
        ·
          refine ⟨2070667389766461643531763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380444926510974429021175 2070667389766461643531763)
          ·
            refine ⟨3106001084649692465297645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2070667389766461643531763 3106001084649692465297645)
            ·
              refine ⟨1164750406743634674486617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3106001084649692465297645 1164750406743634674486617)
              ·
                refine ⟨873562805057726005864963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1164750406743634674486617 873562805057726005864963)
                ·
                  refine ⟨1310344207586589008797445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873562805057726005864963 1310344207586589008797445)
                  ·
                    refine ⟨245689538922485439149521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1310344207586589008797445 245689538922485439149521)
                    ·
                      rfl

theorem cell22_717718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_717718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717718 prefixEnd_717718 := by exact prefixLift 717718
  have htrace : WordTrace (prefixWord ++ tailWord_717718) baseStart_717718 baseEnd_717718 := by
    simpa [prefixWord, tailWord_717718, baseEnd_717718] using wordTrace_append hprefix tailTrace_717718
  have hstable : (prefixWord ++ tailWord_717718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717718).length < 2 ^ (prefixWord ++ tailWord_717718).sum := by decide
  have hdescent : baseEnd_717718 < baseStart_717718 := by decide
  rcases family_descends (prefixWord ++ tailWord_717718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717729 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 2, 4]
def baseStart_717729 : Nat := 118140960795 + 717729 * 2 ^ 59
def prefixEnd_717729 : Nat := 4983230072969 + 3 ^ 40 * 717729 * 2
def baseEnd_717729 : Nat := 245693304447285077124487

theorem tailTrace_717729 : CollatzResearch.WordTrace tailWord_717729 prefixEnd_717729 245693304447285077124487 := by
  unfold tailWord_717729
  simp only [CollatzResearch.WordTrace]
  refine ⟨26177727216797886199348241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17451818144531924132898827 26177727216797886199348241)
  ·
    refine ⟨19633295412598414649511181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26177727216797886199348241 19633295412598414649511181)
    ·
      refine ⟨7362485779724405493566693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19633295412598414649511181 7362485779724405493566693)
      ·
        refine ⟨1380466083698326030043755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7362485779724405493566693 1380466083698326030043755)
        ·
          refine ⟨2070699125547489045065633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380466083698326030043755 2070699125547489045065633)
          ·
            refine ⟨1553024344160616783799225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2070699125547489045065633 1553024344160616783799225)
            ·
              refine ⟨1164768258120462587849419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553024344160616783799225 1164768258120462587849419)
              ·
                refine ⟨1747152387180693881774129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164768258120462587849419 1747152387180693881774129)
                ·
                  refine ⟨1310364290385520411330597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1747152387180693881774129 1310364290385520411330597)
                  ·
                    refine ⟨245693304447285077124487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1310364290385520411330597 245693304447285077124487)
                    ·
                      rfl

theorem cell22_717729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_717729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717729 prefixEnd_717729 := by exact prefixLift 717729
  have htrace : WordTrace (prefixWord ++ tailWord_717729) baseStart_717729 baseEnd_717729 := by
    simpa [prefixWord, tailWord_717729, baseEnd_717729] using wordTrace_append hprefix tailTrace_717729
  have hstable : (prefixWord ++ tailWord_717729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717729).length < 2 ^ (prefixWord ++ tailWord_717729).sum := by decide
  have hdescent : baseEnd_717729 < baseStart_717729 := by decide
  rcases family_descends (prefixWord ++ tailWord_717729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717748 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_717748 : Nat := 118140960795 + 717748 * 2 ^ 59
def prefixEnd_717748 : Nat := 4983230072969 + 3 ^ 40 * 717748 * 2
def baseEnd_717748 : Nat := 245699808535575360899429

theorem tailTrace_717748 : CollatzResearch.WordTrace tailWord_717748 prefixEnd_717748 245699808535575360899429 := by
  unfold tailWord_717748
  simp only [CollatzResearch.WordTrace]
  refine ⟨13089210101864526222144949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17452280135819368296193265 13089210101864526222144949)
  ·
    refine ⟨1227113447049799333326089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13089210101864526222144949 1227113447049799333326089)
    ·
      refine ⟨920335085287349499994567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1227113447049799333326089 920335085287349499994567)
      ·
        refine ⟨1380502627931024249991851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920335085287349499994567 1380502627931024249991851)
        ·
          refine ⟨2070753941896536374987777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380502627931024249991851 2070753941896536374987777)
          ·
            refine ⟨1553065456422402281240833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2070753941896536374987777 1553065456422402281240833)
            ·
              refine ⟨1164799092316801710930625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553065456422402281240833 1164799092316801710930625)
              ·
                refine ⟨873599319237601283197969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1164799092316801710930625 873599319237601283197969)
                ·
                  refine ⟨655199489428200962398477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 873599319237601283197969 655199489428200962398477)
                  ·
                    refine ⟨245699808535575360899429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 655199489428200962398477 245699808535575360899429)
                    ·
                      rfl

theorem cell22_717748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_717748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717748 prefixEnd_717748 := by exact prefixLift 717748
  have htrace : WordTrace (prefixWord ++ tailWord_717748) baseStart_717748 baseEnd_717748 := by
    simpa [prefixWord, tailWord_717748, baseEnd_717748] using wordTrace_append hprefix tailTrace_717748
  have hstable : (prefixWord ++ tailWord_717748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717748).length < 2 ^ (prefixWord ++ tailWord_717748).sum := by decide
  have hdescent : baseEnd_717748 < baseStart_717748 := by decide
  rcases family_descends (prefixWord ++ tailWord_717748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717750 : List Nat := [5, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_717750 : Nat := 118140960795 + 717750 * 2 ^ 59
def prefixEnd_717750 : Nat := 4983230072969 + 3 ^ 40 * 717750 * 2
def baseEnd_717750 : Nat := 81900164392149340783141

theorem tailTrace_717750 : CollatzResearch.WordTrace tailWord_717750 prefixEnd_717750 81900164392149340783141 := by
  unfold tailWord_717750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636155821857612924116419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17452328766481204523908469 1636155821857612924116419)
  ·
    refine ⟨2454233732786419386174629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1636155821857612924116419 2454233732786419386174629)
    ·
      refine ⟨460168824897453634907743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2454233732786419386174629 460168824897453634907743)
      ·
        refine ⟨690253237346180452361615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460168824897453634907743 690253237346180452361615)
        ·
          refine ⟨1035379856019270678542423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690253237346180452361615 1035379856019270678542423)
          ·
            refine ⟨1553069784028906017813635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035379856019270678542423 1553069784028906017813635)
            ·
              refine ⟨2329604676043359026720453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1553069784028906017813635 2329604676043359026720453)
              ·
                refine ⟨436800876758129817510085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2329604676043359026720453 436800876758129817510085)
                ·
                  refine ⟨81900164392149340783141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436800876758129817510085 81900164392149340783141)
                  ·
                    rfl

theorem cell22_717750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_717750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717750 prefixEnd_717750 := by exact prefixLift 717750
  have htrace : WordTrace (prefixWord ++ tailWord_717750) baseStart_717750 baseEnd_717750 := by
    simpa [prefixWord, tailWord_717750, baseEnd_717750] using wordTrace_append hprefix tailTrace_717750
  have hstable : (prefixWord ++ tailWord_717750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717750).length < 2 ^ (prefixWord ++ tailWord_717750).sum := by decide
  have hdescent : baseEnd_717750 < baseStart_717750 := by decide
  rcases family_descends (prefixWord ++ tailWord_717750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717772 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 5]
def baseStart_717772 : Nat := 118140960795 + 717772 * 2 ^ 59
def prefixEnd_717772 : Nat := 4983230072969 + 3 ^ 40 * 717772 * 2
def baseEnd_717772 : Nat := 81902674742015766099785

theorem tailTrace_717772 : CollatzResearch.WordTrace tailWord_717772 prefixEnd_717772 81902674742015766099785 := by
  unfold tailWord_717772
  simp only [CollatzResearch.WordTrace]
  refine ⟨13089647777821052271581785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17452863703761403028775713 13089647777821052271581785)
  ·
    refine ⟨9817235833365789203686339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13089647777821052271581785 9817235833365789203686339)
    ·
      refine ⟨14725853750048683805529509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9817235833365789203686339 14725853750048683805529509)
      ·
        refine ⟨2761097578134128213536783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14725853750048683805529509 2761097578134128213536783)
        ·
          refine ⟨4141646367201192320305175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2761097578134128213536783 4141646367201192320305175)
          ·
            refine ⟨6212469550801788480457763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4141646367201192320305175 6212469550801788480457763)
            ·
              refine ⟨9318704326202682720686645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6212469550801788480457763 9318704326202682720686645)
              ·
                refine ⟨873628530581501505064373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9318704326202682720686645 873628530581501505064373)
                ·
                  refine ⟨81902674742015766099785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 873628530581501505064373 81902674742015766099785)
                  ·
                    rfl

theorem cell22_717772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_717772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717772 prefixEnd_717772 := by exact prefixLift 717772
  have htrace : WordTrace (prefixWord ++ tailWord_717772) baseStart_717772 baseEnd_717772 := by
    simpa [prefixWord, tailWord_717772, baseEnd_717772] using wordTrace_append hprefix tailTrace_717772
  have hstable : (prefixWord ++ tailWord_717772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717772).length < 2 ^ (prefixWord ++ tailWord_717772).sum := by decide
  have hdescent : baseEnd_717772 < baseStart_717772 := by decide
  rcases family_descends (prefixWord ++ tailWord_717772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717806 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_717806 : Nat := 118140960795 + 717806 * 2 ^ 59
def prefixEnd_717806 : Nat := 4983230072969 + 3 ^ 40 * 717806 * 2
def baseEnd_717806 : Nat := 81906554373627514316417

theorem tailTrace_717806 : CollatzResearch.WordTrace tailWord_717806 prefixEnd_717806 81906554373627514316417 := by
  unfold tailWord_717806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272566954689866043737659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17453690425012618899934181 3272566954689866043737659)
  ·
    refine ⟨4908850432034799065606489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3272566954689866043737659 4908850432034799065606489)
    ·
      refine ⟨3681637824026099299204867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4908850432034799065606489 3681637824026099299204867)
      ·
        refine ⟨5522456736039148948807301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3681637824026099299204867 5522456736039148948807301)
        ·
          refine ⟨1035460638007340427901369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5522456736039148948807301 1035460638007340427901369)
          ·
            refine ⟨776595478505505320926027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035460638007340427901369 776595478505505320926027)
            ·
              refine ⟨1164893217758257981389041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776595478505505320926027 1164893217758257981389041)
              ·
                refine ⟨873669913318693486041781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1164893217758257981389041 873669913318693486041781)
                ·
                  refine ⟨81906554373627514316417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 873669913318693486041781 81906554373627514316417)
                  ·
                    rfl

theorem cell22_717806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_717806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717806 prefixEnd_717806 := by exact prefixLift 717806
  have htrace : WordTrace (prefixWord ++ tailWord_717806) baseStart_717806 baseEnd_717806 := by
    simpa [prefixWord, tailWord_717806, baseEnd_717806] using wordTrace_append hprefix tailTrace_717806
  have hstable : (prefixWord ++ tailWord_717806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717806).length < 2 ^ (prefixWord ++ tailWord_717806).sum := by decide
  have hdescent : baseEnd_717806 < baseStart_717806 := by decide
  rcases family_descends (prefixWord ++ tailWord_717806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717815 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 11]
def baseStart_717815 : Nat := 118140960795 + 717815 * 2 ^ 59
def prefixEnd_717815 : Nat := 4983230072969 + 3 ^ 40 * 717815 * 2
def baseEnd_717815 : Nat := 245722744004809519474223

theorem tailTrace_717815 : CollatzResearch.WordTrace tailWord_717815 prefixEnd_717815 245722744004809519474223 := by
  unfold tailWord_717815
  simp only [CollatzResearch.WordTrace]
  refine ⟨26180863894486322886978899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17453909262990881924652599 26180863894486322886978899)
  ·
    refine ⟨39271295841729484330468349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26180863894486322886978899 39271295841729484330468349)
    ·
      refine ⟨14726735940648556623925631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39271295841729484330468349 14726735940648556623925631)
      ·
        refine ⟨22090103910972834935888447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14726735940648556623925631 22090103910972834935888447)
        ·
          refine ⟨33135155866459252403832671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22090103910972834935888447 33135155866459252403832671)
          ·
            refine ⟨49702733799688878605749007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33135155866459252403832671 49702733799688878605749007)
            ·
              refine ⟨74554100699533317908623511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49702733799688878605749007 74554100699533317908623511)
              ·
                refine ⟨111831151049299976862935267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74554100699533317908623511 111831151049299976862935267)
                ·
                  refine ⟨167746726573949965294402901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111831151049299976862935267 167746726573949965294402901)
                  ·
                    refine ⟨245722744004809519474223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 167746726573949965294402901 245722744004809519474223)
                    ·
                      rfl

theorem cell22_717815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_717815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717815 prefixEnd_717815 := by exact prefixLift 717815
  have htrace : WordTrace (prefixWord ++ tailWord_717815) baseStart_717815 baseEnd_717815 := by
    simpa [prefixWord, tailWord_717815, baseEnd_717815] using wordTrace_append hprefix tailTrace_717815
  have hstable : (prefixWord ++ tailWord_717815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717815).length < 2 ^ (prefixWord ++ tailWord_717815).sum := by decide
  have hdescent : baseEnd_717815 < baseStart_717815 := by decide
  rcases family_descends (prefixWord ++ tailWord_717815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717817 : List Nat := [1, 2, 1, 3, 1, 3, 4, 1, 6]
def baseStart_717817 : Nat := 118140960795 + 717817 * 2 ^ 59
def prefixEnd_717817 : Nat := 4983230072969 + 3 ^ 40 * 717817 * 2
def baseEnd_717817 : Nat := 81907809548560726974739

theorem tailTrace_717817 : CollatzResearch.WordTrace tailWord_717817 prefixEnd_717817 81907809548560726974739 := by
  unfold tailWord_717817
  simp only [CollatzResearch.WordTrace]
  refine ⟨26180936840479077228551705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17453957893652718152367803 26180936840479077228551705)
  ·
    refine ⟨19635702630359307921413779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26180936840479077228551705 19635702630359307921413779)
    ·
      refine ⟨29453553945538961882120669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19635702630359307921413779 29453553945538961882120669)
      ·
        refine ⟨11045082729577110705795251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29453553945538961882120669 11045082729577110705795251)
        ·
          refine ⟨16567624094365666058692877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11045082729577110705795251 16567624094365666058692877)
          ·
            refine ⟨6212859035387124772009829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16567624094365666058692877 6212859035387124772009829)
            ·
              refine ⟨1164911069135085894751843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6212859035387124772009829 1164911069135085894751843)
              ·
                refine ⟨1747366603702628842127765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1164911069135085894751843 1747366603702628842127765)
                ·
                  refine ⟨81907809548560726974739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1747366603702628842127765 81907809548560726974739)
                  ·
                    rfl

theorem cell22_717817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_717817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717817 prefixEnd_717817 := by exact prefixLift 717817
  have htrace : WordTrace (prefixWord ++ tailWord_717817) baseStart_717817 baseEnd_717817 := by
    simpa [prefixWord, tailWord_717817, baseEnd_717817] using wordTrace_append hprefix tailTrace_717817
  have hstable : (prefixWord ++ tailWord_717817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717817).length < 2 ^ (prefixWord ++ tailWord_717817).sum := by decide
  have hdescent : baseEnd_717817 < baseStart_717817 := by decide
  rcases family_descends (prefixWord ++ tailWord_717817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717911 : List Nat := [1, 1, 3, 2, 2, 1, 1, 7, 1, 3]
def baseStart_717911 : Nat := 118140960795 + 717911 * 2 ^ 59
def prefixEnd_717911 : Nat := 4983230072969 + 3 ^ 40 * 717911 * 2
def baseEnd_717911 : Nat := 245755606766697269073929

theorem tailTrace_717911 : CollatzResearch.WordTrace tailWord_717911 prefixEnd_717911 245755606766697269073929 := by
  unfold tailWord_717911
  simp only [CollatzResearch.WordTrace]
  refine ⟨26184365302138531282473587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17456243534759020854982391 26184365302138531282473587)
  ·
    refine ⟨39276547953207796923710381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26184365302138531282473587 39276547953207796923710381)
    ·
      refine ⟨14728705482452923846391393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39276547953207796923710381 14728705482452923846391393)
      ·
        refine ⟨11046529111839692884793545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14728705482452923846391393 11046529111839692884793545)
        ·
          refine ⟨8284896833879769663595159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11046529111839692884793545 8284896833879769663595159)
          ·
            refine ⟨12427345250819654495392739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8284896833879769663595159 12427345250819654495392739)
            ·
              refine ⟨18641017876229481743089109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12427345250819654495392739 18641017876229481743089109)
              ·
                refine ⟨436898856474128478353651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18641017876229481743089109 436898856474128478353651)
                ·
                  refine ⟨655348284711192717530477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436898856474128478353651 655348284711192717530477)
                  ·
                    refine ⟨245755606766697269073929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 655348284711192717530477 245755606766697269073929)
                    ·
                      rfl

theorem cell22_717911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_717911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717911 prefixEnd_717911 := by exact prefixLift 717911
  have htrace : WordTrace (prefixWord ++ tailWord_717911) baseStart_717911 baseEnd_717911 := by
    simpa [prefixWord, tailWord_717911, baseEnd_717911] using wordTrace_append hprefix tailTrace_717911
  have hstable : (prefixWord ++ tailWord_717911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717911).length < 2 ^ (prefixWord ++ tailWord_717911).sum := by decide
  have hdescent : baseEnd_717911 < baseStart_717911 := by decide
  rcases family_descends (prefixWord ++ tailWord_717911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717952 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 8]
def baseStart_717952 : Nat := 118140960795 + 717952 * 2 ^ 59
def prefixEnd_717952 : Nat := 4983230072969 + 3 ^ 40 * 717952 * 2
def baseEnd_717952 : Nat := 81923213968195609599601

theorem tailTrace_717952 : CollatzResearch.WordTrace tailWord_717952 prefixEnd_717952 81923213968195609599601 := by
  unfold tailWord_717952
  simp only [CollatzResearch.WordTrace]
  refine ⟨13092930347494997642358055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17457240463326663523144073 13092930347494997642358055)
  ·
    refine ⟨19639395521242496463537083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13092930347494997642358055 19639395521242496463537083)
    ·
      refine ⟨29459093281863744695305625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19639395521242496463537083 29459093281863744695305625)
      ·
        refine ⟨22094319961397808521479219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29459093281863744695305625 22094319961397808521479219)
        ·
          refine ⟨33141479942096712782218829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22094319961397808521479219 33141479942096712782218829)
          ·
            refine ⟨12428054978286267293332061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33141479942096712782218829 12428054978286267293332061)
            ·
              refine ⟨4660520616857350234999523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12428054978286267293332061 4660520616857350234999523)
              ·
                refine ⟨6990780925286025352499285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660520616857350234999523 6990780925286025352499285)
                ·
                  refine ⟨81923213968195609599601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6990780925286025352499285 81923213968195609599601)
                  ·
                    rfl

theorem cell22_717952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_717952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717952 prefixEnd_717952 := by exact prefixLift 717952
  have htrace : WordTrace (prefixWord ++ tailWord_717952) baseStart_717952 baseEnd_717952 := by
    simpa [prefixWord, tailWord_717952, baseEnd_717952] using wordTrace_append hprefix tailTrace_717952
  have hstable : (prefixWord ++ tailWord_717952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717952).length < 2 ^ (prefixWord ++ tailWord_717952).sum := by decide
  have hdescent : baseEnd_717952 < baseStart_717952 := by decide
  rcases family_descends (prefixWord ++ tailWord_717952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717967 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 7, 5]
def baseStart_717967 : Nat := 118140960795 + 717967 * 2 ^ 59
def prefixEnd_717967 : Nat := 4983230072969 + 3 ^ 40 * 717967 * 2
def baseEnd_717967 : Nat := 245774776711131789673757

theorem tailTrace_717967 : CollatzResearch.WordTrace tailWord_717967 prefixEnd_717967 245774776711131789673757 := by
  unfold tailWord_717967
  simp only [CollatzResearch.WordTrace]
  refine ⟨26186407789935652846512155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17457605193290435231008103 26186407789935652846512155)
  ·
    refine ⟨39279611684903479269768233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26186407789935652846512155 39279611684903479269768233)
    ·
      refine ⟨29459708763677609452326175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39279611684903479269768233 29459708763677609452326175)
      ·
        refine ⟨44189563145516414178489263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29459708763677609452326175 44189563145516414178489263)
        ·
          refine ⟨66284344718274621267733895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44189563145516414178489263 66284344718274621267733895)
          ·
            refine ⟨99426517077411931901600843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66284344718274621267733895 99426517077411931901600843)
            ·
              refine ⟨149139775616117897852401265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99426517077411931901600843 149139775616117897852401265)
              ·
                refine ⟨111854831712088423389300949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149139775616117897852401265 111854831712088423389300949)
                ·
                  refine ⟨2621597618252072423186741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 111854831712088423389300949 2621597618252072423186741)
                  ·
                    refine ⟨245774776711131789673757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2621597618252072423186741 245774776711131789673757)
                    ·
                      rfl

theorem cell22_717967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_717967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717967 prefixEnd_717967 := by exact prefixLift 717967
  have htrace : WordTrace (prefixWord ++ tailWord_717967) baseStart_717967 baseEnd_717967 := by
    simpa [prefixWord, tailWord_717967, baseEnd_717967] using wordTrace_append hprefix tailTrace_717967
  have hstable : (prefixWord ++ tailWord_717967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717967).length < 2 ^ (prefixWord ++ tailWord_717967).sum := by decide
  have hdescent : baseEnd_717967 < baseStart_717967 := by decide
  rcases family_descends (prefixWord ++ tailWord_717967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_717971 : List Nat := [1, 1, 1, 2, 1, 2, 8, 1, 1, 4]
def baseStart_717971 : Nat := 118140960795 + 717971 * 2 ^ 59
def prefixEnd_717971 : Nat := 4983230072969 + 3 ^ 40 * 717971 * 2
def baseEnd_717971 : Nat := 245776145992877112573745

theorem tailTrace_717971 : CollatzResearch.WordTrace tailWord_717971 prefixEnd_717971 245776145992877112573745 := by
  unfold tailWord_717971
  simp only [CollatzResearch.WordTrace]
  refine ⟨26186553681921161529657767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17457702454614107686438511 26186553681921161529657767)
  ·
    refine ⟨39279830522881742294486651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26186553681921161529657767 39279830522881742294486651)
    ·
      refine ⟨58919745784322613441729977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39279830522881742294486651 58919745784322613441729977)
      ·
        refine ⟨44189809338241960081297483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58919745784322613441729977 44189809338241960081297483)
        ·
          refine ⟨66284714007362940121946225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44189809338241960081297483 66284714007362940121946225)
          ·
            refine ⟨49713535505522205091459669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66284714007362940121946225 49713535505522205091459669)
            ·
              refine ⟨582580494205338340915543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 49713535505522205091459669 582580494205338340915543)
              ·
                refine ⟨873870741308007511373315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582580494205338340915543 873870741308007511373315)
                ·
                  refine ⟨1310806111962011267059973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873870741308007511373315 1310806111962011267059973)
                  ·
                    refine ⟨245776145992877112573745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1310806111962011267059973 245776145992877112573745)
                    ·
                      rfl

theorem cell22_717971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 8, 1, 1, 4].length) (baseStart_717971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_717971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_717971 prefixEnd_717971 := by exact prefixLift 717971
  have htrace : WordTrace (prefixWord ++ tailWord_717971) baseStart_717971 baseEnd_717971 := by
    simpa [prefixWord, tailWord_717971, baseEnd_717971] using wordTrace_append hprefix tailTrace_717971
  have hstable : (prefixWord ++ tailWord_717971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_717971).length < 2 ^ (prefixWord ++ tailWord_717971).sum := by decide
  have hdescent : baseEnd_717971 < baseStart_717971 := by decide
  rcases family_descends (prefixWord ++ tailWord_717971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718001 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 1, 5]
def baseStart_718001 : Nat := 118140960795 + 718001 * 2 ^ 59
def prefixEnd_718001 : Nat := 4983230072969 + 3 ^ 40 * 718001 * 2
def baseEnd_718001 : Nat := 245786415605967034323653

theorem tailTrace_718001 : CollatzResearch.WordTrace tailWord_718001 prefixEnd_718001 245786415605967034323653 := by
  unfold tailWord_718001
  simp only [CollatzResearch.WordTrace]
  refine ⟨26187647871812476653249857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17458431914541651102166571 26187647871812476653249857)
  ·
    refine ⟨19640735903859357489937393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26187647871812476653249857 19640735903859357489937393)
    ·
      refine ⟨14730551927894518117453045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19640735903859357489937393 14730551927894518117453045)
      ·
        refine ⟨1380989243240111073511223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14730551927894518117453045 1380989243240111073511223)
        ·
          refine ⟨2071483864860166610266835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1380989243240111073511223 2071483864860166610266835)
          ·
            refine ⟨3107225797290249915400253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071483864860166610266835 3107225797290249915400253)
            ·
              refine ⟨1165209673983843718275095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3107225797290249915400253 1165209673983843718275095)
              ·
                refine ⟨1747814510975765577412643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165209673983843718275095 1747814510975765577412643)
                ·
                  refine ⟨2621721766463648366118965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1747814510975765577412643 2621721766463648366118965)
                  ·
                    refine ⟨245786415605967034323653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2621721766463648366118965 245786415605967034323653)
                    ·
                      rfl

theorem cell22_718001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_718001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718001 prefixEnd_718001 := by exact prefixLift 718001
  have htrace : WordTrace (prefixWord ++ tailWord_718001) baseStart_718001 baseEnd_718001 := by
    simpa [prefixWord, tailWord_718001, baseEnd_718001] using wordTrace_append hprefix tailTrace_718001
  have hstable : (prefixWord ++ tailWord_718001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718001).length < 2 ^ (prefixWord ++ tailWord_718001).sum := by decide
  have hdescent : baseEnd_718001 < baseStart_718001 := by decide
  rcases family_descends (prefixWord ++ tailWord_718001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718020 : List Nat := [2, 3, 3, 1, 3, 2, 1, 3, 4]
def baseStart_718020 : Nat := 118140960795 + 718020 * 2 ^ 59
def prefixEnd_718020 : Nat := 4983230072969 + 3 ^ 40 * 718020 * 2
def baseEnd_718020 : Nat := 81930973231419106032865

theorem tailTrace_718020 : CollatzResearch.WordTrace tailWord_718020 prefixEnd_718020 81930973231419106032865 := by
  unfold tailWord_718020
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094170429371821449095757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17458893905829095265461009 13094170429371821449095757)
  ·
    refine ⟨4910313911014433043410909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13094170429371821449095757 4910313911014433043410909)
    ·
      refine ⟨1841367716630412391279091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4910313911014433043410909 1841367716630412391279091)
      ·
        refine ⟨2762051574945618586918637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1841367716630412391279091 2762051574945618586918637)
        ·
          refine ⟨1035769340604606970094489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2762051574945618586918637 1035769340604606970094489)
          ·
            refine ⟨776827005453455227570867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1035769340604606970094489 776827005453455227570867)
            ·
              refine ⟨1165240508180182841356301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776827005453455227570867 1165240508180182841356301)
              ·
                refine ⟨436965190567568565508613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1165240508180182841356301 436965190567568565508613)
                ·
                  refine ⟨81930973231419106032865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 436965190567568565508613 81930973231419106032865)
                  ·
                    rfl

theorem cell22_718020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_718020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718020 prefixEnd_718020 := by exact prefixLift 718020
  have htrace : WordTrace (prefixWord ++ tailWord_718020) baseStart_718020 baseEnd_718020 := by
    simpa [prefixWord, tailWord_718020, baseEnd_718020] using wordTrace_append hprefix tailTrace_718020
  have hstable : (prefixWord ++ tailWord_718020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718020).length < 2 ^ (prefixWord ++ tailWord_718020).sum := by decide
  have hdescent : baseEnd_718020 < baseStart_718020 := by decide
  rcases family_descends (prefixWord ++ tailWord_718020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718106 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_718106 : Nat := 118140960795 + 718106 * 2 ^ 59
def prefixEnd_718106 : Nat := 4983230072969 + 3 ^ 40 * 718106 * 2
def baseEnd_718106 : Nat := 245822359251781760448331

theorem tailTrace_718106 : CollatzResearch.WordTrace tailWord_718106 prefixEnd_718106 245822359251781760448331 := by
  unfold tailWord_718106
  simp only [CollatzResearch.WordTrace]
  refine ⟨6547869384108019896455543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17460985024288053057214781 6547869384108019896455543)
  ·
    refine ⟨9821804076162029844683315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6547869384108019896455543 9821804076162029844683315)
    ·
      refine ⟨14732706114243044767024973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9821804076162029844683315 14732706114243044767024973)
      ·
        refine ⟨5524764792841141787634365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14732706114243044767024973 5524764792841141787634365)
        ·
          refine ⟨2071786797315428170362887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5524764792841141787634365 2071786797315428170362887)
          ·
            refine ⟨3107680195973142255544331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2071786797315428170362887 3107680195973142255544331)
            ·
              refine ⟨4661520293959713383316497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3107680195973142255544331 4661520293959713383316497)
              ·
                refine ⟨3496140220469785037487373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4661520293959713383316497 3496140220469785037487373)
                ·
                  refine ⟨1311052582676169389057765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3496140220469785037487373 1311052582676169389057765)
                  ·
                    refine ⟨245822359251781760448331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1311052582676169389057765 245822359251781760448331)
                    ·
                      rfl

theorem cell22_718106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_718106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718106 prefixEnd_718106 := by exact prefixLift 718106
  have htrace : WordTrace (prefixWord ++ tailWord_718106) baseStart_718106 baseEnd_718106 := by
    simpa [prefixWord, tailWord_718106, baseEnd_718106] using wordTrace_append hprefix tailTrace_718106
  have hstable : (prefixWord ++ tailWord_718106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718106).length < 2 ^ (prefixWord ++ tailWord_718106).sum := by decide
  have hdescent : baseEnd_718106 < baseStart_718106 := by decide
  rcases family_descends (prefixWord ++ tailWord_718106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718136 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 4, 3]
def baseStart_718136 : Nat := 118140960795 + 718136 * 2 ^ 59
def prefixEnd_718136 : Nat := 4983230072969 + 3 ^ 40 * 718136 * 2
def baseEnd_718136 : Nat := 245832628864871682198239

theorem tailTrace_718136 : CollatzResearch.WordTrace tailWord_718136 prefixEnd_718136 245832628864871682198239 := by
  unfold tailWord_718136
  simp only [CollatzResearch.WordTrace]
  refine ⟨13096285863161697354707131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17461714484215596472942841 13096285863161697354707131)
  ·
    refine ⟨19644428794742546032060697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13096285863161697354707131 19644428794742546032060697)
    ·
      refine ⟨14733321596056909524045523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19644428794742546032060697 14733321596056909524045523)
      ·
        refine ⟨22099982394085364286068285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14733321596056909524045523 22099982394085364286068285)
        ·
          refine ⟨8287493397782011607275607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22099982394085364286068285 8287493397782011607275607)
          ·
            refine ⟨12431240096673017410913411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8287493397782011607275607 12431240096673017410913411)
            ·
              refine ⟨18646860145009526116370117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12431240096673017410913411 18646860145009526116370117)
              ·
                refine ⟨3496286277189286146819397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18646860145009526116370117 3496286277189286146819397)
                ·
                  refine ⟨655553676972991152528637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3496286277189286146819397 655553676972991152528637)
                  ·
                    refine ⟨245832628864871682198239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 655553676972991152528637 245832628864871682198239)
                    ·
                      rfl

theorem cell22_718136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_718136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718136 prefixEnd_718136 := by exact prefixLift 718136
  have htrace : WordTrace (prefixWord ++ tailWord_718136) baseStart_718136 baseEnd_718136 := by
    simpa [prefixWord, tailWord_718136, baseEnd_718136] using wordTrace_append hprefix tailTrace_718136
  have hstable : (prefixWord ++ tailWord_718136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718136).length < 2 ^ (prefixWord ++ tailWord_718136).sum := by decide
  have hdescent : baseEnd_718136 < baseStart_718136 := by decide
  rcases family_descends (prefixWord ++ tailWord_718136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718138 : List Nat := [3, 1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_718138 : Nat := 118140960795 + 718138 * 2 ^ 59
def prefixEnd_718138 : Nat := 4983230072969 + 3 ^ 40 * 718138 * 2
def baseEnd_718138 : Nat := 81944437835248114549411

theorem tailTrace_718138 : CollatzResearch.WordTrace tailWord_718138 prefixEnd_718138 81944437835248114549411 := by
  unfold tailWord_718138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6548161168079037262746767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17461763114877432700658045 6548161168079037262746767)
  ·
    refine ⟨9822241752118555894120151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6548161168079037262746767 9822241752118555894120151)
    ·
      refine ⟨14733362628177833841180227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9822241752118555894120151 14733362628177833841180227)
      ·
        refine ⟨22100043942266750761770341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14733362628177833841180227 22100043942266750761770341)
        ·
          refine ⟨4143758239175015767831939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22100043942266750761770341 4143758239175015767831939)
          ·
            refine ⟨6215637358762523651747909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4143758239175015767831939 6215637358762523651747909)
            ·
              refine ⟨1165432004767973184702733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6215637358762523651747909 1165432004767973184702733)
              ·
                refine ⟨437037001787989944263525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1165432004767973184702733 437037001787989944263525)
                ·
                  refine ⟨81944437835248114549411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437037001787989944263525 81944437835248114549411)
                  ·
                    rfl

theorem cell22_718138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_718138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718138 prefixEnd_718138 := by exact prefixLift 718138
  have htrace : WordTrace (prefixWord ++ tailWord_718138) baseStart_718138 baseEnd_718138 := by
    simpa [prefixWord, tailWord_718138, baseEnd_718138] using wordTrace_append hprefix tailTrace_718138
  have hstable : (prefixWord ++ tailWord_718138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718138).length < 2 ^ (prefixWord ++ tailWord_718138).sum := by decide
  have hdescent : baseEnd_718138 < baseStart_718138 := by decide
  rcases family_descends (prefixWord ++ tailWord_718138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718140 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 1, 4]
def baseStart_718140 : Nat := 118140960795 + 718140 * 2 ^ 59
def prefixEnd_718140 : Nat := 4983230072969 + 3 ^ 40 * 718140 * 2
def baseEnd_718140 : Nat := 245833998146617005098227

theorem tailTrace_718140 : CollatzResearch.WordTrace tailWord_718140 prefixEnd_718140 245833998146617005098227 := by
  unfold tailWord_718140
  simp only [CollatzResearch.WordTrace]
  refine ⟨13096358809154451696279937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17461811745539268928373249 13096358809154451696279937)
  ·
    refine ⟨9822269106865838772209953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13096358809154451696279937 9822269106865838772209953)
    ·
      refine ⟨7366701830149379079157465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9822269106865838772209953 7366701830149379079157465)
      ·
        refine ⟨5525026372612034309368099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7366701830149379079157465 5525026372612034309368099)
        ·
          refine ⟨8287539558918051464052149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5525026372612034309368099 8287539558918051464052149)
          ·
            refine ⟨776956833648567324754889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8287539558918051464052149 776956833648567324754889)
            ·
              refine ⟨582717625236425493566167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 776956833648567324754889 582717625236425493566167)
              ·
                refine ⟨874076437854638240349251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582717625236425493566167 874076437854638240349251)
                ·
                  refine ⟨1311114656781957360523877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 874076437854638240349251 1311114656781957360523877)
                  ·
                    refine ⟨245833998146617005098227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1311114656781957360523877 245833998146617005098227)
                    ·
                      rfl

theorem cell22_718140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_718140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718140 prefixEnd_718140 := by exact prefixLift 718140
  have htrace : WordTrace (prefixWord ++ tailWord_718140) baseStart_718140 baseEnd_718140 := by
    simpa [prefixWord, tailWord_718140, baseEnd_718140] using wordTrace_append hprefix tailTrace_718140
  have hstable : (prefixWord ++ tailWord_718140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718140).length < 2 ^ (prefixWord ++ tailWord_718140).sum := by decide
  have hdescent : baseEnd_718140 < baseStart_718140 := by decide
  rcases family_descends (prefixWord ++ tailWord_718140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718153 : List Nat := [1, 2, 1, 1, 2, 3, 5, 2, 2, 3]
def baseStart_718153 : Nat := 118140960795 + 718153 * 2 ^ 59
def prefixEnd_718153 : Nat := 4983230072969 + 3 ^ 40 * 718153 * 2
def baseEnd_718153 : Nat := 245838448312289304523187

theorem tailTrace_718153 : CollatzResearch.WordTrace tailWord_718153 prefixEnd_718153 245838448312289304523187 := by
  unfold tailWord_718153
  simp only [CollatzResearch.WordTrace]
  refine ⟨26193191767261806612783113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17462127844841204408522075 26193191767261806612783113)
  ·
    refine ⟨19644893825446354959587335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26193191767261806612783113 19644893825446354959587335)
    ·
      refine ⟨29467340738169532439381003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19644893825446354959587335 29467340738169532439381003)
      ·
        refine ⟨44201011107254298659071505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29467340738169532439381003 44201011107254298659071505)
        ·
          refine ⟨33150758330440723994303629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44201011107254298659071505 33150758330440723994303629)
          ·
            refine ⟨12431534373915271497863861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33150758330440723994303629 12431534373915271497863861)
            ·
              refine ⟨1165456347554556702924737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12431534373915271497863861 1165456347554556702924737)
              ·
                refine ⟨874092260665917527193553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165456347554556702924737 874092260665917527193553)
                ·
                  refine ⟨655569195499438145395165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 874092260665917527193553 655569195499438145395165)
                  ·
                    refine ⟨245838448312289304523187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 655569195499438145395165 245838448312289304523187)
                    ·
                      rfl

theorem cell22_718153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 2, 2, 3].length) (baseStart_718153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718153 prefixEnd_718153 := by exact prefixLift 718153
  have htrace : WordTrace (prefixWord ++ tailWord_718153) baseStart_718153 baseEnd_718153 := by
    simpa [prefixWord, tailWord_718153, baseEnd_718153] using wordTrace_append hprefix tailTrace_718153
  have hstable : (prefixWord ++ tailWord_718153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718153).length < 2 ^ (prefixWord ++ tailWord_718153).sum := by decide
  have hdescent : baseEnd_718153 < baseStart_718153 := by decide
  rcases family_descends (prefixWord ++ tailWord_718153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718211 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 7]
def baseStart_718211 : Nat := 118140960795 + 718211 * 2 ^ 59
def prefixEnd_718211 : Nat := 4983230072969 + 3 ^ 40 * 718211 * 2
def baseEnd_718211 : Nat := 81952767632532162191003

theorem tailTrace_718211 : CollatzResearch.WordTrace tailWord_718211 prefixEnd_718211 81952767632532162191003 := by
  unfold tailWord_718211
  simp only [CollatzResearch.WordTrace]
  refine ⟨26195307201051682518394487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17463538134034455012262991 26195307201051682518394487)
  ·
    refine ⟨39292960801577523777591731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26195307201051682518394487 39292960801577523777591731)
    ·
      refine ⟨58939441202366285666387597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39292960801577523777591731 58939441202366285666387597)
      ·
        refine ⟨22102290450887357124895349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58939441202366285666387597 22102290450887357124895349)
        ·
          refine ⟨2072089729770689730458939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22102290450887357124895349 2072089729770689730458939)
          ·
            refine ⟨3108134594656034595688409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072089729770689730458939 3108134594656034595688409)
            ·
              refine ⟨2331100945992025946766307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3108134594656034595688409 2331100945992025946766307)
              ·
                refine ⟨3496651418988038920149461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331100945992025946766307 3496651418988038920149461)
                ·
                  refine ⟨81952767632532162191003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3496651418988038920149461 81952767632532162191003)
                  ·
                    rfl

theorem cell22_718211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 7].length) (baseStart_718211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718211 prefixEnd_718211 := by exact prefixLift 718211
  have htrace : WordTrace (prefixWord ++ tailWord_718211) baseStart_718211 baseEnd_718211 := by
    simpa [prefixWord, tailWord_718211, baseEnd_718211] using wordTrace_append hprefix tailTrace_718211
  have hstable : (prefixWord ++ tailWord_718211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718211).length < 2 ^ (prefixWord ++ tailWord_718211).sum := by decide
  have hdescent : baseEnd_718211 < baseStart_718211 := by decide
  rcases family_descends (prefixWord ++ tailWord_718211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718215 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 3, 3]
def baseStart_718215 : Nat := 118140960795 + 718215 * 2 ^ 59
def prefixEnd_718215 : Nat := 4983230072969 + 3 ^ 40 * 718215 * 2
def baseEnd_718215 : Nat := 245859672179341809472997

theorem tailTrace_718215 : CollatzResearch.WordTrace tailWord_718215 prefixEnd_718215 245859672179341809472997 := by
  unfold tailWord_718215
  simp only [CollatzResearch.WordTrace]
  refine ⟨26195453093037191201540099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17463635395358127467693399 26195453093037191201540099)
  ·
    refine ⟨39293179639555786802310149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26195453093037191201540099 39293179639555786802310149)
    ·
      refine ⟨7367471182416710025433153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39293179639555786802310149 7367471182416710025433153)
      ·
        refine ⟨5525603386812532519074865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7367471182416710025433153 5525603386812532519074865)
        ·
          refine ⟨4144202540109399389306149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5525603386812532519074865 4144202540109399389306149)
          ·
            refine ⟨777037976270512385494903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4144202540109399389306149 777037976270512385494903)
            ·
              refine ⟨1165556964405768578242355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777037976270512385494903 1165556964405768578242355)
              ·
                refine ⟨1748335446608652867363533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165556964405768578242355 1748335446608652867363533)
                ·
                  refine ⟨655625792478244825261325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1748335446608652867363533 655625792478244825261325)
                  ·
                    refine ⟨245859672179341809472997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 655625792478244825261325 245859672179341809472997)
                    ·
                      rfl

theorem cell22_718215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_718215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718215 prefixEnd_718215 := by exact prefixLift 718215
  have htrace : WordTrace (prefixWord ++ tailWord_718215) baseStart_718215 baseEnd_718215 := by
    simpa [prefixWord, tailWord_718215, baseEnd_718215] using wordTrace_append hprefix tailTrace_718215
  have hstable : (prefixWord ++ tailWord_718215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718215).length < 2 ^ (prefixWord ++ tailWord_718215).sum := by decide
  have hdescent : baseEnd_718215 < baseStart_718215 := by decide
  rcases family_descends (prefixWord ++ tailWord_718215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718322 : List Nat := [3, 2, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_718322 : Nat := 118140960795 + 718322 * 2 ^ 59
def prefixEnd_718322 : Nat := 4983230072969 + 3 ^ 40 * 718322 * 2
def baseEnd_718322 : Nat := 245896300466029197047669

theorem tailTrace_718322 : CollatzResearch.WordTrace tailWord_718322 prefixEnd_718322 245896300466029197047669 := by
  unfold tailWord_718322
  simp only [CollatzResearch.WordTrace]
  refine ⟨6549838925912387118921305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17466237135766365650456813 6549838925912387118921305)
  ·
    refine ⟨4912379194434290339190979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6549838925912387118921305 4912379194434290339190979)
    ·
      refine ⟨7368568791651435508786469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4912379194434290339190979 7368568791651435508786469)
      ·
        refine ⟨1381606648434644157897463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7368568791651435508786469 1381606648434644157897463)
        ·
          refine ⟨2072409972651966236846195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381606648434644157897463 2072409972651966236846195)
          ·
            refine ⟨3108614958977949355269293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2072409972651966236846195 3108614958977949355269293)
            ·
              refine ⟨1165730609616731008225985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3108614958977949355269293 1165730609616731008225985)
              ·
                refine ⟨874297957212548256169489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165730609616731008225985 874297957212548256169489)
                ·
                  refine ⟨655723467909411192127117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 874297957212548256169489 655723467909411192127117)
                  ·
                    refine ⟨245896300466029197047669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 655723467909411192127117 245896300466029197047669)
                    ·
                      rfl

theorem cell22_718322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_718322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718322 prefixEnd_718322 := by exact prefixLift 718322
  have htrace : WordTrace (prefixWord ++ tailWord_718322) baseStart_718322 baseEnd_718322 := by
    simpa [prefixWord, tailWord_718322, baseEnd_718322] using wordTrace_append hprefix tailTrace_718322
  have hstable : (prefixWord ++ tailWord_718322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718322).length < 2 ^ (prefixWord ++ tailWord_718322).sum := by decide
  have hdescent : baseEnd_718322 < baseStart_718322 := by decide
  rcases family_descends (prefixWord ++ tailWord_718322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718367 : List Nat := [1, 1, 2, 4, 1, 1, 5, 3, 1, 3]
def baseStart_718367 : Nat := 118140960795 + 718367 * 2 ^ 59
def prefixEnd_718367 : Nat := 4983230072969 + 3 ^ 40 * 718367 * 2
def baseEnd_718367 : Nat := 245911704885664079672531

theorem tailTrace_718367 : CollatzResearch.WordTrace tailWord_718367 prefixEnd_718367 245911704885664079672531 := by
  unfold tailWord_718367
  simp only [CollatzResearch.WordTrace]
  refine ⟨26200996988486521161073355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17467331325657680774048903 26200996988486521161073355)
  ·
    refine ⟨39301495482729781741610033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26200996988486521161073355 39301495482729781741610033)
    ·
      refine ⟨29476121612047336306207525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39301495482729781741610033 29476121612047336306207525)
      ·
        refine ⟨5526772802258875557413911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29476121612047336306207525 5526772802258875557413911)
        ·
          refine ⟨8290159203388313336120867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5526772802258875557413911 8290159203388313336120867)
          ·
            refine ⟨12435238805082470004181301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8290159203388313336120867 12435238805082470004181301)
            ·
              refine ⟨1165803637976481562891997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12435238805082470004181301 1165803637976481562891997)
              ·
                refine ⟨437176364241180586084499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1165803637976481562891997 437176364241180586084499)
                ·
                  refine ⟨655764546361770879126749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437176364241180586084499 655764546361770879126749)
                  ·
                    refine ⟨245911704885664079672531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 655764546361770879126749 245911704885664079672531)
                    ·
                      rfl

theorem cell22_718367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 3, 1, 3].length) (baseStart_718367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718367 prefixEnd_718367 := by exact prefixLift 718367
  have htrace : WordTrace (prefixWord ++ tailWord_718367) baseStart_718367 baseEnd_718367 := by
    simpa [prefixWord, tailWord_718367, baseEnd_718367] using wordTrace_append hprefix tailTrace_718367
  have hstable : (prefixWord ++ tailWord_718367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718367).length < 2 ^ (prefixWord ++ tailWord_718367).sum := by decide
  have hdescent : baseEnd_718367 < baseStart_718367 := by decide
  rcases family_descends (prefixWord ++ tailWord_718367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718423 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 3, 5]
def baseStart_718423 : Nat := 118140960795 + 718423 * 2 ^ 59
def prefixEnd_718423 : Nat := 4983230072969 + 3 ^ 40 * 718423 * 2
def baseEnd_718423 : Nat := 245930874830098600272359

theorem tailTrace_718423 : CollatzResearch.WordTrace tailWord_718423 prefixEnd_718423 245930874830098600272359 := by
  unfold tailWord_718423
  simp only [CollatzResearch.WordTrace]
  refine ⟨26203039476283642725111923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17468692984189095150074615 26203039476283642725111923)
  ·
    refine ⟨39304559214425464087667885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26203039476283642725111923 39304559214425464087667885)
    ·
      refine ⟨14739209705409549032875457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39304559214425464087667885 14739209705409549032875457)
      ·
        refine ⟨11054407279057161774656593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14739209705409549032875457 11054407279057161774656593)
        ·
          refine ⟨8290805459292871330992445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11054407279057161774656593 8290805459292871330992445)
          ·
            refine ⟨3109052047234826749122167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8290805459292871330992445 3109052047234826749122167)
            ·
              refine ⟨4663578070852240123683251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3109052047234826749122167 4663578070852240123683251)
              ·
                refine ⟨6995367106278360185524877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4663578070852240123683251 6995367106278360185524877)
                ·
                  refine ⟨2623262664854385069571829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6995367106278360185524877 2623262664854385069571829)
                  ·
                    refine ⟨245930874830098600272359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2623262664854385069571829 245930874830098600272359)
                    ·
                      rfl

theorem cell22_718423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_718423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718423 prefixEnd_718423 := by exact prefixLift 718423
  have htrace : WordTrace (prefixWord ++ tailWord_718423) baseStart_718423 baseEnd_718423 := by
    simpa [prefixWord, tailWord_718423, baseEnd_718423] using wordTrace_append hprefix tailTrace_718423
  have hstable : (prefixWord ++ tailWord_718423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718423).length < 2 ^ (prefixWord ++ tailWord_718423).sum := by decide
  have hdescent : baseEnd_718423 < baseStart_718423 := by decide
  rcases family_descends (prefixWord ++ tailWord_718423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718442 : List Nat := [3, 1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_718442 : Nat := 118140960795 + 718442 * 2 ^ 59
def prefixEnd_718442 : Nat := 4983230072969 + 3 ^ 40 * 718442 * 2
def baseEnd_718442 : Nat := 81979126306129628015767

theorem tailTrace_718442 : CollatzResearch.WordTrace tailWord_718442 prefixEnd_718442 81979126306129628015767 := by
  unfold tailWord_718442
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550933115803702242513395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17469154975476539313369053 6550933115803702242513395)
  ·
    refine ⟨9826399673705553363770093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6550933115803702242513395 9826399673705553363770093)
    ·
      refine ⟨3684899877639582511413785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9826399673705553363770093 3684899877639582511413785)
      ·
        refine ⟨2763674908229686883560339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3684899877639582511413785 2763674908229686883560339)
        ·
          refine ⟨4145512362344530325340509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763674908229686883560339 4145512362344530325340509)
          ·
            refine ⟨1554567135879198872002691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4145512362344530325340509 1554567135879198872002691)
            ·
              refine ⟨2331850703818798308004037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554567135879198872002691 2331850703818798308004037)
              ·
                refine ⟨437222006966024682750757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2331850703818798308004037 437222006966024682750757)
                ·
                  refine ⟨81979126306129628015767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437222006966024682750757 81979126306129628015767)
                  ·
                    rfl

theorem cell22_718442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_718442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718442 prefixEnd_718442 := by exact prefixLift 718442
  have htrace : WordTrace (prefixWord ++ tailWord_718442) baseStart_718442 baseEnd_718442 := by
    simpa [prefixWord, tailWord_718442, baseEnd_718442] using wordTrace_append hprefix tailTrace_718442
  have hstable : (prefixWord ++ tailWord_718442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718442).length < 2 ^ (prefixWord ++ tailWord_718442).sum := by decide
  have hdescent : baseEnd_718442 < baseStart_718442 := by decide
  rcases family_descends (prefixWord ++ tailWord_718442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718472 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 1, 6]
def baseStart_718472 : Nat := 118140960795 + 718472 * 2 ^ 59
def prefixEnd_718472 : Nat := 4983230072969 + 3 ^ 40 * 718472 * 2
def baseEnd_718472 : Nat := 245947648531478805797209

theorem tailTrace_718472 : CollatzResearch.WordTrace tailWord_718472 prefixEnd_718472 245947648531478805797209 := by
  unfold tailWord_718472
  simp only [CollatzResearch.WordTrace]
  refine ⟨13102413326553062046822835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17469884435404082729097113 13102413326553062046822835)
  ·
    refine ⟨19653619989829593070234253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13102413326553062046822835 19653619989829593070234253)
    ·
      refine ⟨7370107496186097401337845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19653619989829593070234253 7370107496186097401337845)
      ·
        refine ⟨690947577767446631375423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7370107496186097401337845 690947577767446631375423)
        ·
          refine ⟨1036421366651169947063135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 690947577767446631375423 1036421366651169947063135)
          ·
            refine ⟨1554632049976754920594703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036421366651169947063135 1554632049976754920594703)
            ·
              refine ⟨2331948074965132380892055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554632049976754920594703 2331948074965132380892055)
              ·
                refine ⟨3497922112447698571338083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331948074965132380892055 3497922112447698571338083)
                ·
                  refine ⟨5246883168671547857007125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3497922112447698571338083 5246883168671547857007125)
                  ·
                    refine ⟨245947648531478805797209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5246883168671547857007125 245947648531478805797209)
                    ·
                      rfl

theorem cell22_718472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_718472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718472 prefixEnd_718472 := by exact prefixLift 718472
  have htrace : WordTrace (prefixWord ++ tailWord_718472) baseStart_718472 baseEnd_718472 := by
    simpa [prefixWord, tailWord_718472, baseEnd_718472] using wordTrace_append hprefix tailTrace_718472
  have hstable : (prefixWord ++ tailWord_718472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718472).length < 2 ^ (prefixWord ++ tailWord_718472).sum := by decide
  have hdescent : baseEnd_718472 < baseStart_718472 := by decide
  rcases family_descends (prefixWord ++ tailWord_718472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718543 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 8]
def baseStart_718543 : Nat := 118140960795 + 718543 * 2 ^ 59
def prefixEnd_718543 : Nat := 4983230072969 + 3 ^ 40 * 718543 * 2
def baseEnd_718543 : Nat := 81990651094152762423997

theorem tailTrace_718543 : CollatzResearch.WordTrace tailWord_718543 prefixEnd_718543 81990651094152762423997 := by
  unfold tailWord_718543
  simp only [CollatzResearch.WordTrace]
  refine ⟨26207416235848903219480283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17471610823899268812986855 26207416235848903219480283)
  ·
    refine ⟨39311124353773354829220425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26207416235848903219480283 39311124353773354829220425)
    ·
      refine ⟨29483343265330016121915319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39311124353773354829220425 29483343265330016121915319)
      ·
        refine ⟨44225014897995024182872979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29483343265330016121915319 44225014897995024182872979)
        ·
          refine ⟨66337522346992536274309469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44225014897995024182872979 66337522346992536274309469)
          ·
            refine ⟨24876570880122201102866051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66337522346992536274309469 24876570880122201102866051)
            ·
              refine ⟨37314856320183301654299077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24876570880122201102866051 37314856320183301654299077)
              ·
                refine ⟨6996535560034369060181077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37314856320183301654299077 6996535560034369060181077)
                ·
                  refine ⟨81990651094152762423997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6996535560034369060181077 81990651094152762423997)
                  ·
                    rfl

theorem cell22_718543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 8].length) (baseStart_718543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718543 prefixEnd_718543 := by exact prefixLift 718543
  have htrace : WordTrace (prefixWord ++ tailWord_718543) baseStart_718543 baseEnd_718543 := by
    simpa [prefixWord, tailWord_718543, baseEnd_718543] using wordTrace_append hprefix tailTrace_718543
  have hstable : (prefixWord ++ tailWord_718543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718543).length < 2 ^ (prefixWord ++ tailWord_718543).sum := by decide
  have hdescent : baseEnd_718543 < baseStart_718543 := by decide
  rcases family_descends (prefixWord ++ tailWord_718543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718560 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 6]
def baseStart_718560 : Nat := 118140960795 + 718560 * 2 ^ 59
def prefixEnd_718560 : Nat := 4983230072969 + 3 ^ 40 * 718560 * 2
def baseEnd_718560 : Nat := 81992590909958636532313

theorem tailTrace_718560 : CollatzResearch.WordTrace tailWord_718560 prefixEnd_718560 81992590909958636532313 := by
  unfold tailWord_718560
  simp only [CollatzResearch.WordTrace]
  refine ⟨13104018138393657561424567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17472024184524876748566089 13104018138393657561424567)
  ·
    refine ⟨19656027207590486342136851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13104018138393657561424567 19656027207590486342136851)
    ·
      refine ⟨29484040811385729513205277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19656027207590486342136851 29484040811385729513205277)
      ·
        refine ⟨11056515304269648567451979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29484040811385729513205277 11056515304269648567451979)
        ·
          refine ⟨16584772956404472851177969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11056515304269648567451979 16584772956404472851177969)
          ·
            refine ⟨12438579717303354638383477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16584772956404472851177969 12438579717303354638383477)
            ·
              refine ⟨1166116848497189497348451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12438579717303354638383477 1166116848497189497348451)
              ·
                refine ⟨1749175272745784246022677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166116848497189497348451 1749175272745784246022677)
                ·
                  refine ⟨81992590909958636532313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1749175272745784246022677 81992590909958636532313)
                  ·
                    rfl

theorem cell22_718560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_718560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718560 prefixEnd_718560 := by exact prefixLift 718560
  have htrace : WordTrace (prefixWord ++ tailWord_718560) baseStart_718560 baseEnd_718560 := by
    simpa [prefixWord, tailWord_718560, baseEnd_718560] using wordTrace_append hprefix tailTrace_718560
  have hstable : (prefixWord ++ tailWord_718560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718560).length < 2 ^ (prefixWord ++ tailWord_718560).sum := by decide
  have hdescent : baseEnd_718560 < baseStart_718560 := by decide
  rcases family_descends (prefixWord ++ tailWord_718560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718575 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 1, 5]
def baseStart_718575 : Nat := 118140960795 + 718575 * 2 ^ 59
def prefixEnd_718575 : Nat := 4983230072969 + 3 ^ 40 * 718575 * 2
def baseEnd_718575 : Nat := 245982907536420870471893

theorem tailTrace_718575 : CollatzResearch.WordTrace tailWord_718575 prefixEnd_718575 245982907536420870471893 := by
  unfold tailWord_718575
  simp only [CollatzResearch.WordTrace]
  refine ⟨26208583371732972684645179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17472388914488648456430119 26208583371732972684645179)
  ·
    refine ⟨39312875057599459026967769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26208583371732972684645179 39312875057599459026967769)
    ·
      refine ⟨29484656293199594270225827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39312875057599459026967769 29484656293199594270225827)
      ·
        refine ⟨44226984439799391405338741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29484656293199594270225827 44226984439799391405338741)
        ·
          refine ⟨4146279791231192944250507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44226984439799391405338741 4146279791231192944250507)
          ·
            refine ⟨6219419686846789416375761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4146279791231192944250507 6219419686846789416375761)
            ·
              refine ⟨4664564765135092062281821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6219419686846789416375761 4664564765135092062281821)
              ·
                refine ⟨1749211786925659523355683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4664564765135092062281821 1749211786925659523355683)
                ·
                  refine ⟨2623817680388489285033525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749211786925659523355683 2623817680388489285033525)
                  ·
                    refine ⟨245982907536420870471893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2623817680388489285033525 245982907536420870471893)
                    ·
                      rfl

theorem cell22_718575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_718575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718575 prefixEnd_718575 := by exact prefixLift 718575
  have htrace : WordTrace (prefixWord ++ tailWord_718575) baseStart_718575 baseEnd_718575 := by
    simpa [prefixWord, tailWord_718575, baseEnd_718575] using wordTrace_append hprefix tailTrace_718575
  have hstable : (prefixWord ++ tailWord_718575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718575).length < 2 ^ (prefixWord ++ tailWord_718575).sum := by decide
  have hdescent : baseEnd_718575 < baseStart_718575 := by decide
  rcases family_descends (prefixWord ++ tailWord_718575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718594 : List Nat := [3, 4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_718594 : Nat := 118140960795 + 718594 * 2 ^ 59
def prefixEnd_718594 : Nat := 4983230072969 + 3 ^ 40 * 718594 * 2
def baseEnd_718594 : Nat := 81996470541570384748945

theorem tailTrace_718594 : CollatzResearch.WordTrace tailWord_718594 prefixEnd_718594 81996470541570384748945 := by
  unfold tailWord_718594
  simp only [CollatzResearch.WordTrace]
  refine ⟨6552319089666034732396709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17472850905776092619724557 6552319089666034732396709)
  ·
    refine ⟨1228559829312381512324383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6552319089666034732396709 1228559829312381512324383)
    ·
      refine ⟨1842839743968572268486575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1228559829312381512324383 1842839743968572268486575)
      ·
        refine ⟨2764259615952858402729863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842839743968572268486575 2764259615952858402729863)
        ·
          refine ⟨4146389423929287604094795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2764259615952858402729863 4146389423929287604094795)
          ·
            refine ⟨6219584135893931406142193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4146389423929287604094795 6219584135893931406142193)
            ·
              refine ⟨4664688101920448554606645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6219584135893931406142193 4664688101920448554606645)
              ·
                refine ⟨437314509555042051994373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4664688101920448554606645 437314509555042051994373)
                ·
                  refine ⟨81996470541570384748945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437314509555042051994373 81996470541570384748945)
                  ·
                    rfl

theorem cell22_718594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_718594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718594 prefixEnd_718594 := by exact prefixLift 718594
  have htrace : WordTrace (prefixWord ++ tailWord_718594) baseStart_718594 baseEnd_718594 := by
    simpa [prefixWord, tailWord_718594, baseEnd_718594] using wordTrace_append hprefix tailTrace_718594
  have hstable : (prefixWord ++ tailWord_718594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718594).length < 2 ^ (prefixWord ++ tailWord_718594).sum := by decide
  have hdescent : baseEnd_718594 < baseStart_718594 := by decide
  rcases family_descends (prefixWord ++ tailWord_718594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718665 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 4, 5]
def baseStart_718665 : Nat := 118140960795 + 718665 * 2 ^ 59
def prefixEnd_718665 : Nat := 4983230072969 + 3 ^ 40 * 718665 * 2
def baseEnd_718665 : Nat := 246013716375690635721617

theorem tailTrace_718665 : CollatzResearch.WordTrace tailWord_718665 prefixEnd_718665 246013716375690635721617 := by
  unfold tailWord_718665
  simp only [CollatzResearch.WordTrace]
  refine ⟨26211865941406918055421449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17474577294271278703614299 26211865941406918055421449)
  ·
    refine ⟨19658899456055188541566087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26211865941406918055421449 19658899456055188541566087)
    ·
      refine ⟨29488349184082782812349131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19658899456055188541566087 29488349184082782812349131)
      ·
        refine ⟨44232523776124174218523697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29488349184082782812349131 44232523776124174218523697)
        ·
          refine ⟨33174392832093130663892773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44232523776124174218523697 33174392832093130663892773)
          ·
            refine ⟨6220198656017461999479895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33174392832093130663892773 6220198656017461999479895)
            ·
              refine ⟨9330297984026192999219843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6220198656017461999479895 9330297984026192999219843)
              ·
                refine ⟨13995446976039289498829765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9330297984026192999219843 13995446976039289498829765)
                ·
                  refine ⟨2624146308007366781030581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13995446976039289498829765 2624146308007366781030581)
                  ·
                    refine ⟨246013716375690635721617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2624146308007366781030581 246013716375690635721617)
                    ·
                      rfl

theorem cell22_718665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_718665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718665 prefixEnd_718665 := by exact prefixLift 718665
  have htrace : WordTrace (prefixWord ++ tailWord_718665) baseStart_718665 baseEnd_718665 := by
    simpa [prefixWord, tailWord_718665, baseEnd_718665] using wordTrace_append hprefix tailTrace_718665
  have hstable : (prefixWord ++ tailWord_718665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718665).length < 2 ^ (prefixWord ++ tailWord_718665).sum := by decide
  have hdescent : baseEnd_718665 < baseStart_718665 := by decide
  rcases family_descends (prefixWord ++ tailWord_718665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718759 : List Nat := [1, 1, 6, 1, 2, 1, 1, 3, 2, 4]
def baseStart_718759 : Nat := 118140960795 + 718759 * 2 ^ 59
def prefixEnd_718759 : Nat := 4983230072969 + 3 ^ 40 * 718759 * 2
def baseEnd_718759 : Nat := 246045894496705723871329

theorem tailTrace_718759 : CollatzResearch.WordTrace tailWord_718759 prefixEnd_718759 246045894496705723871329 := by
  unfold tailWord_718759
  simp only [CollatzResearch.WordTrace]
  refine ⟨26215294403066372109343331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17476862935377581406228887 26215294403066372109343331)
  ·
    refine ⟨39322941604599558164014997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26215294403066372109343331 39322941604599558164014997)
    ·
      refine ⟨1843262887715604288938203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39322941604599558164014997 1843262887715604288938203)
      ·
        refine ⟨2764894331573406433407305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843262887715604288938203 2764894331573406433407305)
        ·
          refine ⟨2073670748680054825055479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2764894331573406433407305 2073670748680054825055479)
          ·
            refine ⟨3110506123020082237583219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073670748680054825055479 3110506123020082237583219)
            ·
              refine ⟨4665759184530123356374829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3110506123020082237583219 4665759184530123356374829)
              ·
                refine ⟨1749659694198796258640561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4665759184530123356374829 1749659694198796258640561)
                ·
                  refine ⟨1312244770649097193980421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1749659694198796258640561 1312244770649097193980421)
                  ·
                    refine ⟨246045894496705723871329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1312244770649097193980421 246045894496705723871329)
                    ·
                      rfl

theorem cell22_718759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_718759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718759 prefixEnd_718759 := by exact prefixLift 718759
  have htrace : WordTrace (prefixWord ++ tailWord_718759) baseStart_718759 baseEnd_718759 := by
    simpa [prefixWord, tailWord_718759, baseEnd_718759] using wordTrace_append hprefix tailTrace_718759
  have hstable : (prefixWord ++ tailWord_718759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718759).length < 2 ^ (prefixWord ++ tailWord_718759).sum := by decide
  have hdescent : baseEnd_718759 < baseStart_718759 := by decide
  rcases family_descends (prefixWord ++ tailWord_718759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718774 : List Nat := [5, 1, 4, 12]
def baseStart_718774 : Nat := 118140960795 + 718774 * 2 ^ 59
def prefixEnd_718774 : Nat := 4983230072969 + 3 ^ 40 * 718774 * 2
def baseEnd_718774 : Nat := 337518558715021515427

theorem tailTrace_718774 : CollatzResearch.WordTrace tailWord_718774 prefixEnd_718774 337518558715021515427 := by
  unfold tailWord_718774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1638490093625751854446211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17477227665341353114092917 1638490093625751854446211)
  ·
    refine ⟨2457735140438627781669317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1638490093625751854446211 2457735140438627781669317)
    ·
      refine ⟨460825338832242709062997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2457735140438627781669317 460825338832242709062997)
      ·
        refine ⟨337518558715021515427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 460825338832242709062997 337518558715021515427)
        ·
          rfl

theorem cell22_718774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 12].length) (baseStart_718774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718774 prefixEnd_718774 := by exact prefixLift 718774
  have htrace : WordTrace (prefixWord ++ tailWord_718774) baseStart_718774 baseEnd_718774 := by
    simpa [prefixWord, tailWord_718774, baseEnd_718774] using wordTrace_append hprefix tailTrace_718774
  have hstable : (prefixWord ++ tailWord_718774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718774).length < 2 ^ (prefixWord ++ tailWord_718774).sum := by decide
  have hdescent : baseEnd_718774 < baseStart_718774 := by decide
  rcases family_descends (prefixWord ++ tailWord_718774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718780 : List Nat := [2, 2, 2, 5, 1, 2, 2, 2, 4]
def baseStart_718780 : Nat := 118140960795 + 718780 * 2 ^ 59
def prefixEnd_718780 : Nat := 4983230072969 + 3 ^ 40 * 718780 * 2
def baseEnd_718780 : Nat := 82017694408622889698755

theorem tailTrace_718780 : CollatzResearch.WordTrace tailWord_718780 prefixEnd_718780 82017694408622889698755 := by
  unfold tailWord_718780
  simp only [CollatzResearch.WordTrace]
  refine ⟨13108030167995146347928897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17477373557326861797238529 13108030167995146347928897)
  ·
    refine ⟨9831022625996359760946673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13108030167995146347928897 9831022625996359760946673)
    ·
      refine ⟨7373266969497269820710005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9831022625996359760946673 7373266969497269820710005)
      ·
        refine ⟨691243778390369045691563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7373266969497269820710005 691243778390369045691563)
        ·
          refine ⟨1036865667585553568537345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691243778390369045691563 1036865667585553568537345)
          ·
            refine ⟨777649250689165176403009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1036865667585553568537345 777649250689165176403009)
            ·
              refine ⟨583236938016873882302257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777649250689165176403009 583236938016873882302257)
              ·
                refine ⟨437427703512655411726693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583236938016873882302257 437427703512655411726693)
                ·
                  refine ⟨82017694408622889698755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437427703512655411726693 82017694408622889698755)
                  ·
                    rfl

theorem cell22_718780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_718780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718780 prefixEnd_718780 := by exact prefixLift 718780
  have htrace : WordTrace (prefixWord ++ tailWord_718780) baseStart_718780 baseEnd_718780 := by
    simpa [prefixWord, tailWord_718780, baseEnd_718780] using wordTrace_append hprefix tailTrace_718780
  have hstable : (prefixWord ++ tailWord_718780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718780).length < 2 ^ (prefixWord ++ tailWord_718780).sum := by decide
  have hdescent : baseEnd_718780 < baseStart_718780 := by decide
  rcases family_descends (prefixWord ++ tailWord_718780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718879 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 6, 3]
def baseStart_718879 : Nat := 118140960795 + 718879 * 2 ^ 59
def prefixEnd_718879 : Nat := 4983230072969 + 3 ^ 40 * 718879 * 2
def baseEnd_718879 : Nat := 246086972949065410870961

theorem tailTrace_718879 : CollatzResearch.WordTrace tailWord_718879 prefixEnd_718879 246086972949065410870961 := by
  unfold tailWord_718879
  simp only [CollatzResearch.WordTrace]
  refine ⟨26219671162631632603711691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17479780775087755069141127 26219671162631632603711691)
  ·
    refine ⟨39329506743947448905567537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26219671162631632603711691 39329506743947448905567537)
    ·
      refine ⟨29497130057960586679175653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39329506743947448905567537 29497130057960586679175653)
      ·
        refine ⟨5530711885867610002345435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29497130057960586679175653 5530711885867610002345435)
        ·
          refine ⟨8296067828801415003518153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5530711885867610002345435 8296067828801415003518153)
          ·
            refine ⟨6222050871601061252638615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8296067828801415003518153 6222050871601061252638615)
            ·
              refine ⟨9333076307401591878957923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6222050871601061252638615 9333076307401591878957923)
              ·
                refine ⟨13999614461102387818436885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9333076307401591878957923 13999614461102387818436885)
                ·
                  refine ⟨656231927864174428989229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13999614461102387818436885 656231927864174428989229)
                  ·
                    refine ⟨246086972949065410870961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 656231927864174428989229 246086972949065410870961)
                    ·
                      rfl

theorem cell22_718879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 3].length) (baseStart_718879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718879 prefixEnd_718879 := by exact prefixLift 718879
  have htrace : WordTrace (prefixWord ++ tailWord_718879) baseStart_718879 baseEnd_718879 := by
    simpa [prefixWord, tailWord_718879, baseEnd_718879] using wordTrace_append hprefix tailTrace_718879
  have hstable : (prefixWord ++ tailWord_718879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718879).length < 2 ^ (prefixWord ++ tailWord_718879).sum := by decide
  have hdescent : baseEnd_718879 < baseStart_718879 := by decide
  rcases family_descends (prefixWord ++ tailWord_718879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718898 : List Nat := [3, 2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_718898 : Nat := 118140960795 + 718898 * 2 ^ 59
def prefixEnd_718898 : Nat := 4983230072969 + 3 ^ 40 * 718898 * 2
def baseEnd_718898 : Nat := 82031159012451898215301

theorem tailTrace_718898 : CollatzResearch.WordTrace tailWord_718898 prefixEnd_718898 82031159012451898215301 := by
  unfold tailWord_718898
  simp only [CollatzResearch.WordTrace]
  refine ⟨6555091037390699712163337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17480242766375199232435565 6555091037390699712163337)
  ·
    refine ⟨4916318278043024784122503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6555091037390699712163337 4916318278043024784122503)
    ·
      refine ⟨7374477417064537176183755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4916318278043024784122503 7374477417064537176183755)
      ·
        refine ⟨11061716125596805764275633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7374477417064537176183755 11061716125596805764275633)
        ·
          refine ⟨8296287094197604323206725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11061716125596805764275633 8296287094197604323206725)
          ·
            refine ⟨1555553830162050810601261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8296287094197604323206725 1555553830162050810601261)
            ·
              refine ⟨583332686310769053975473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1555553830162050810601261 583332686310769053975473)
              ·
                refine ⟨437499514733076790481605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583332686310769053975473 437499514733076790481605)
                ·
                  refine ⟨82031159012451898215301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 437499514733076790481605 82031159012451898215301)
                  ·
                    rfl

theorem cell22_718898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_718898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718898 prefixEnd_718898 := by exact prefixLift 718898
  have htrace : WordTrace (prefixWord ++ tailWord_718898) baseStart_718898 baseEnd_718898 := by
    simpa [prefixWord, tailWord_718898, baseEnd_718898] using wordTrace_append hprefix tailTrace_718898
  have hstable : (prefixWord ++ tailWord_718898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718898).length < 2 ^ (prefixWord ++ tailWord_718898).sum := by decide
  have hdescent : baseEnd_718898 < baseStart_718898 := by decide
  rcases family_descends (prefixWord ++ tailWord_718898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718909 : List Nat := [1, 4, 1, 3, 1, 1, 4, 7]
def baseStart_718909 : Nat := 118140960795 + 718909 * 2 ^ 59
def prefixEnd_718909 : Nat := 4983230072969 + 3 ^ 40 * 718909 * 2
def baseEnd_718909 : Nat := 27344138062461703624541

theorem tailTrace_718909 : CollatzResearch.WordTrace tailWord_718909 prefixEnd_718909 27344138062461703624541 := by
  unfold tailWord_718909
  simp only [CollatzResearch.WordTrace]
  refine ⟨26220765352522947727303781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17480510235015298484869187 26220765352522947727303781)
  ·
    refine ⟨4916393503598052698869459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26220765352522947727303781 4916393503598052698869459)
    ·
      refine ⟨7374590255397079048304189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4916393503598052698869459 7374590255397079048304189)
      ·
        refine ⟨2765471345773904643114071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7374590255397079048304189 2765471345773904643114071)
        ·
          refine ⟨4148207018660856964671107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2765471345773904643114071 4148207018660856964671107)
          ·
            refine ⟨6222310527991285447006661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4148207018660856964671107 6222310527991285447006661)
            ·
              refine ⟨1166683223998366021313749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6222310527991285447006661 1166683223998366021313749)
              ·
                refine ⟨27344138062461703624541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1166683223998366021313749 27344138062461703624541)
                ·
                  rfl

theorem cell22_718909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 7].length) (baseStart_718909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718909 prefixEnd_718909 := by exact prefixLift 718909
  have htrace : WordTrace (prefixWord ++ tailWord_718909) baseStart_718909 baseEnd_718909 := by
    simpa [prefixWord, tailWord_718909, baseEnd_718909] using wordTrace_append hprefix tailTrace_718909
  have hstable : (prefixWord ++ tailWord_718909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718909).length < 2 ^ (prefixWord ++ tailWord_718909).sum := by decide
  have hdescent : baseEnd_718909 < baseStart_718909 := by decide
  rcases family_descends (prefixWord ++ tailWord_718909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718913 : List Nat := [1, 2, 5, 1, 2, 2, 1, 3, 2, 3]
def baseStart_718913 : Nat := 118140960795 + 718913 * 2 ^ 59
def prefixEnd_718913 : Nat := 4983230072969 + 3 ^ 40 * 718913 * 2
def baseEnd_718913 : Nat := 246098611843900655520857

theorem tailTrace_718913 : CollatzResearch.WordTrace tailWord_718913 prefixEnd_718913 246098611843900655520857 := by
  unfold tailWord_718913
  simp only [CollatzResearch.WordTrace]
  refine ⟨26220911244508456410449393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17480607496338970940299595 26220911244508456410449393)
  ·
    refine ⟨19665683433381342307837045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26220911244508456410449393 19665683433381342307837045)
    ·
      refine ⟨1843657821879500841359723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19665683433381342307837045 1843657821879500841359723)
      ·
        refine ⟨2765486732819251262039585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843657821879500841359723 2765486732819251262039585)
        ·
          refine ⟨2074115049614438446529689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765486732819251262039585 2074115049614438446529689)
          ·
            refine ⟨1555586287210828834897267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2074115049614438446529689 1555586287210828834897267)
            ·
              refine ⟨2333379430816243252345901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1555586287210828834897267 2333379430816243252345901)
              ·
                refine ⟨875017286556091219629713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2333379430816243252345901 875017286556091219629713)
                ·
                  refine ⟨656262964917068414722285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 875017286556091219629713 656262964917068414722285)
                  ·
                    refine ⟨246098611843900655520857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 656262964917068414722285 246098611843900655520857)
                    ·
                      rfl

theorem cell22_718913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_718913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718913 prefixEnd_718913 := by exact prefixLift 718913
  have htrace : WordTrace (prefixWord ++ tailWord_718913) baseStart_718913 baseEnd_718913 := by
    simpa [prefixWord, tailWord_718913, baseEnd_718913] using wordTrace_append hprefix tailTrace_718913
  have hstable : (prefixWord ++ tailWord_718913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718913).length < 2 ^ (prefixWord ++ tailWord_718913).sum := by decide
  have hdescent : baseEnd_718913 < baseStart_718913 := by decide
  rcases family_descends (prefixWord ++ tailWord_718913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718969 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 1, 7]
def baseStart_718969 : Nat := 118140960795 + 718969 * 2 ^ 59
def prefixEnd_718969 : Nat := 4983230072969 + 3 ^ 40 * 718969 * 2
def baseEnd_718969 : Nat := 246117781788335176120685

theorem tailTrace_718969 : CollatzResearch.WordTrace tailWord_718969 prefixEnd_718969 246117781788335176120685 := by
  unfold tailWord_718969
  simp only [CollatzResearch.WordTrace]
  refine ⟨26222953732305577974487961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17481969154870385316325307 26222953732305577974487961)
  ·
    refine ⟨19667215299229183480865971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26222953732305577974487961 19667215299229183480865971)
    ·
      refine ⟨29500822948843775221298957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19667215299229183480865971 29500822948843775221298957)
      ·
        refine ⟨11062808605816415707987109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29500822948843775221298957 11062808605816415707987109)
        ·
          refine ⟨2074276613590577945247583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11062808605816415707987109 2074276613590577945247583)
          ·
            refine ⟨3111414920385866917871375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2074276613590577945247583 3111414920385866917871375)
            ·
              refine ⟨4667122380578800376807063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111414920385866917871375 4667122380578800376807063)
              ·
                refine ⟨7000683570868200565210595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4667122380578800376807063 7000683570868200565210595)
                ·
                  refine ⟨10501025356302300847815893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7000683570868200565210595 10501025356302300847815893)
                  ·
                    refine ⟨246117781788335176120685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10501025356302300847815893 246117781788335176120685)
                    ·
                      rfl

theorem cell22_718969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_718969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718969 prefixEnd_718969 := by exact prefixLift 718969
  have htrace : WordTrace (prefixWord ++ tailWord_718969) baseStart_718969 baseEnd_718969 := by
    simpa [prefixWord, tailWord_718969, baseEnd_718969] using wordTrace_append hprefix tailTrace_718969
  have hstable : (prefixWord ++ tailWord_718969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718969).length < 2 ^ (prefixWord ++ tailWord_718969).sum := by decide
  have hdescent : baseEnd_718969 < baseStart_718969 := by decide
  rcases family_descends (prefixWord ++ tailWord_718969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_718998 : List Nat := [5, 3, 2, 1, 2, 1, 1, 2, 2, 3]
def baseStart_718998 : Nat := 118140960795 + 718998 * 2 ^ 59
def prefixEnd_718998 : Nat := 4983230072969 + 3 ^ 40 * 718998 * 2
def baseEnd_718998 : Nat := 246127709080988767145597

theorem tailTrace_718998 : CollatzResearch.WordTrace tailWord_718998 prefixEnd_718998 246127709080988767145597 := by
  unfold tailWord_718998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1639000715575032245455853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 17482674299467010618195765 1639000715575032245455853)
  ·
    refine ⟨614625268340637092045945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1639000715575032245455853 614625268340637092045945)
    ·
      refine ⟨460968951255477819034459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 614625268340637092045945 460968951255477819034459)
      ·
        refine ⟨691453426883216728551689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460968951255477819034459 691453426883216728551689)
        ·
          refine ⟨518590070162412546413767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 691453426883216728551689 518590070162412546413767)
          ·
            refine ⟨777885105243618819620651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518590070162412546413767 777885105243618819620651)
            ·
              refine ⟨1166827657865428229430977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777885105243618819620651 1166827657865428229430977)
              ·
                refine ⟨875120743399071172073233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166827657865428229430977 875120743399071172073233)
                ·
                  refine ⟨656340557549303379054925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 875120743399071172073233 656340557549303379054925)
                  ·
                    refine ⟨246127709080988767145597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 656340557549303379054925 246127709080988767145597)
                    ·
                      rfl

theorem cell22_718998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_718998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_718998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_718998 prefixEnd_718998 := by exact prefixLift 718998
  have htrace : WordTrace (prefixWord ++ tailWord_718998) baseStart_718998 baseEnd_718998 := by
    simpa [prefixWord, tailWord_718998, baseEnd_718998] using wordTrace_append hprefix tailTrace_718998
  have hstable : (prefixWord ++ tailWord_718998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_718998).length < 2 ^ (prefixWord ++ tailWord_718998).sum := by decide
  have hdescent : baseEnd_718998 < baseStart_718998 := by decide
  rcases family_descends (prefixWord ++ tailWord_718998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719022 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_719022 : Nat := 118140960795 + 719022 * 2 ^ 59
def prefixEnd_719022 : Nat := 4983230072969 + 3 ^ 40 * 719022 * 2
def baseEnd_719022 : Nat := 82045308257153568181841

theorem tailTrace_719022 : CollatzResearch.WordTrace tailWord_719022 prefixEnd_719022 82045308257153568181841 := by
  unfold tailWord_719022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278110850139196003270915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 17483257867409045350778213 3278110850139196003270915)
  ·
    refine ⟨4917166275208794004906373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3278110850139196003270915 4917166275208794004906373)
    ·
      refine ⟨921968676601648875919945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4917166275208794004906373 921968676601648875919945)
      ·
        refine ⟨691476507451236656939959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 921968676601648875919945 691476507451236656939959)
        ·
          refine ⟨1037214761176854985409939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691476507451236656939959 1037214761176854985409939)
          ·
            refine ⟨1555822141765282478114909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037214761176854985409939 1555822141765282478114909)
            ·
              refine ⟨583433303161980929293091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1555822141765282478114909 583433303161980929293091)
              ·
                refine ⟨875149954742971393939637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583433303161980929293091 875149954742971393939637)
                ·
                  refine ⟨82045308257153568181841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 875149954742971393939637 82045308257153568181841)
                  ·
                    rfl

theorem cell22_719022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_719022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719022 prefixEnd_719022 := by exact prefixLift 719022
  have htrace : WordTrace (prefixWord ++ tailWord_719022) baseStart_719022 baseEnd_719022 := by
    simpa [prefixWord, tailWord_719022, baseEnd_719022] using wordTrace_append hprefix tailTrace_719022
  have hstable : (prefixWord ++ tailWord_719022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719022).length < 2 ^ (prefixWord ++ tailWord_719022).sum := by decide
  have hdescent : baseEnd_719022 < baseStart_719022 := by decide
  rcases family_descends (prefixWord ++ tailWord_719022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719031 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 1, 5]
def baseStart_719031 : Nat := 118140960795 + 719031 * 2 ^ 59
def prefixEnd_719031 : Nat := 4983230072969 + 3 ^ 40 * 719031 * 2
def baseEnd_719031 : Nat := 246139005655387681070495

theorem tailTrace_719031 : CollatzResearch.WordTrace tailWord_719031 prefixEnd_719031 246139005655387681070495 := by
  unfold tailWord_719031
  simp only [CollatzResearch.WordTrace]
  refine ⟨26225215058080962563244947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17483476705387308375496631 26225215058080962563244947)
  ·
    refine ⟨39337822587121443844867421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26225215058080962563244947 39337822587121443844867421)
    ·
      refine ⟨14751683470170541441825283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39337822587121443844867421 14751683470170541441825283)
      ·
        refine ⟨22127525205255812162737925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14751683470170541441825283 22127525205255812162737925)
        ·
          refine ⟨4148910975985464780513361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22127525205255812162737925 4148910975985464780513361)
          ·
            refine ⟨3111683231989098585385021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4148910975985464780513361 3111683231989098585385021)
            ·
              refine ⟨1166881211995911969519383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3111683231989098585385021 1166881211995911969519383)
              ·
                refine ⟨1750321817993867954279075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1166881211995911969519383 1750321817993867954279075)
                ·
                  refine ⟨2625482726990801931418613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750321817993867954279075 2625482726990801931418613)
                  ·
                    refine ⟨246139005655387681070495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2625482726990801931418613 246139005655387681070495)
                    ·
                      rfl

theorem cell22_719031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_719031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719031 prefixEnd_719031 := by exact prefixLift 719031
  have htrace : WordTrace (prefixWord ++ tailWord_719031) baseStart_719031 baseEnd_719031 := by
    simpa [prefixWord, tailWord_719031, baseEnd_719031] using wordTrace_append hprefix tailTrace_719031
  have hstable : (prefixWord ++ tailWord_719031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719031).length < 2 ^ (prefixWord ++ tailWord_719031).sum := by decide
  have hdescent : baseEnd_719031 < baseStart_719031 := by decide
  rcases family_descends (prefixWord ++ tailWord_719031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719127 : List Nat := [1, 1, 3, 4, 1, 2, 4, 2, 1, 3]
def baseStart_719127 : Nat := 118140960795 + 719127 * 2 ^ 59
def prefixEnd_719127 : Nat := 4983230072969 + 3 ^ 40 * 719127 * 2
def baseEnd_719127 : Nat := 246171868417275430670201

theorem tailTrace_719127 : CollatzResearch.WordTrace tailWord_719127 prefixEnd_719127 246171868417275430670201 := by
  unfold tailWord_719127
  simp only [CollatzResearch.WordTrace]
  refine ⟨26228716465733170958739635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17485810977155447305826423 26228716465733170958739635)
  ·
    refine ⟨39343074698599756438109453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26228716465733170958739635 39343074698599756438109453)
    ·
      refine ⟨14753653011974908664291045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39343074698599756438109453 14753653011974908664291045)
      ·
        refine ⟨2766309939745295374554571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14753653011974908664291045 2766309939745295374554571)
        ·
          refine ⟨4149464909617943061831857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2766309939745295374554571 4149464909617943061831857)
          ·
            refine ⟨3112098682213457296373893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4149464909617943061831857 3112098682213457296373893)
            ·
              refine ⟨583518502915023243070105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3112098682213457296373893 583518502915023243070105)
              ·
                refine ⟨437638877186267432302579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583518502915023243070105 437638877186267432302579)
                ·
                  refine ⟨656458315779401148453869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437638877186267432302579 656458315779401148453869)
                  ·
                    refine ⟨246171868417275430670201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 656458315779401148453869 246171868417275430670201)
                    ·
                      rfl

theorem cell22_719127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_719127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719127 prefixEnd_719127 := by exact prefixLift 719127
  have htrace : WordTrace (prefixWord ++ tailWord_719127) baseStart_719127 baseEnd_719127 := by
    simpa [prefixWord, tailWord_719127, baseEnd_719127] using wordTrace_append hprefix tailTrace_719127
  have hstable : (prefixWord ++ tailWord_719127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719127).length < 2 ^ (prefixWord ++ tailWord_719127).sum := by decide
  have hdescent : baseEnd_719127 < baseStart_719127 := by decide
  rcases family_descends (prefixWord ++ tailWord_719127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719138 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_719138 : Nat := 118140960795 + 719138 * 2 ^ 59
def prefixEnd_719138 : Nat := 4983230072969 + 3 ^ 40 * 719138 * 2
def baseEnd_719138 : Nat := 246175633942075068645167

theorem tailTrace_719138 : CollatzResearch.WordTrace tailWord_719138 prefixEnd_719138 246175633942075068645167 := by
  unfold tailWord_719138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6557279417173329959347517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 17486078445795546558260045 6557279417173329959347517)
  ·
    refine ⟨2458979781439998734755319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6557279417173329959347517 2458979781439998734755319)
    ·
      refine ⟨3688469672159998102132979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2458979781439998734755319 3688469672159998102132979)
      ·
        refine ⟨5532704508239997153199469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3688469672159998102132979 5532704508239997153199469)
        ·
          refine ⟨2074764190589998932449801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5532704508239997153199469 2074764190589998932449801)
          ·
            refine ⟨1556073142942499199337351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2074764190589998932449801 1556073142942499199337351)
            ·
              refine ⟨2334109714413748799006027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1556073142942499199337351 2334109714413748799006027)
              ·
                refine ⟨3501164571620623198509041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2334109714413748799006027 3501164571620623198509041)
                ·
                  refine ⟨2625873428715467398881781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3501164571620623198509041 2625873428715467398881781)
                  ·
                    refine ⟨246175633942075068645167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2625873428715467398881781 246175633942075068645167)
                    ·
                      rfl

theorem cell22_719138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_719138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719138 prefixEnd_719138 := by exact prefixLift 719138
  have htrace : WordTrace (prefixWord ++ tailWord_719138) baseStart_719138 baseEnd_719138 := by
    simpa [prefixWord, tailWord_719138, baseEnd_719138] using wordTrace_append hprefix tailTrace_719138
  have hstable : (prefixWord ++ tailWord_719138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719138).length < 2 ^ (prefixWord ++ tailWord_719138).sum := by decide
  have hdescent : baseEnd_719138 < baseStart_719138 := by decide
  rcases family_descends (prefixWord ++ tailWord_719138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719183 : List Nat := [1, 1, 2, 1, 1, 2, 1, 8, 2, 3]
def baseStart_719183 : Nat := 118140960795 + 719183 * 2 ^ 59
def prefixEnd_719183 : Nat := 4983230072969 + 3 ^ 40 * 719183 * 2
def baseEnd_719183 : Nat := 246191038361709951270029

theorem tailTrace_719183 : CollatzResearch.WordTrace tailWord_719183 prefixEnd_719183 246191038361709951270029 := by
  unfold tailWord_719183
  simp only [CollatzResearch.WordTrace]
  refine ⟨26230758953530292522778203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 17487172635686861681852135 26230758953530292522778203)
  ·
    refine ⟨39346138430295438784167305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26230758953530292522778203 39346138430295438784167305)
    ·
      refine ⟨29509603822721579088125479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39346138430295438784167305 29509603822721579088125479)
      ·
        refine ⟨44264405734082368632188219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29509603822721579088125479 44264405734082368632188219)
        ·
          refine ⟨66396608601123552948282329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44264405734082368632188219 66396608601123552948282329)
          ·
            refine ⟨49797456450842664711211747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66396608601123552948282329 49797456450842664711211747)
            ·
              refine ⟨74696184676263997066817621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49797456450842664711211747 74696184676263997066817621)
              ·
                refine ⟨875345914174968715626769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 74696184676263997066817621 875345914174968715626769)
                ·
                  refine ⟨656509435631226536720077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 875345914174968715626769 656509435631226536720077)
                  ·
                    refine ⟨246191038361709951270029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 656509435631226536720077 246191038361709951270029)
                    ·
                      rfl

theorem cell22_719183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 2, 3].length) (baseStart_719183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719183 prefixEnd_719183 := by exact prefixLift 719183
  have htrace : WordTrace (prefixWord ++ tailWord_719183) baseStart_719183 baseEnd_719183 := by
    simpa [prefixWord, tailWord_719183, baseEnd_719183] using wordTrace_append hprefix tailTrace_719183
  have hstable : (prefixWord ++ tailWord_719183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719183).length < 2 ^ (prefixWord ++ tailWord_719183).sum := by decide
  have hdescent : baseEnd_719183 < baseStart_719183 := by decide
  rcases family_descends (prefixWord ++ tailWord_719183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_719200 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 1, 5]
def baseStart_719200 : Nat := 118140960795 + 719200 * 2 ^ 59
def prefixEnd_719200 : Nat := 4983230072969 + 3 ^ 40 * 719200 * 2
def baseEnd_719200 : Nat := 246196857809127573594977

theorem tailTrace_719200 : CollatzResearch.WordTrace tailWord_719200 prefixEnd_719200 246196857809127573594977 := by
  unfold tailWord_719200
  simp only [CollatzResearch.WordTrace]
  refine ⟨13115689497234352213073527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 17487585996312469617431369 13115689497234352213073527)
  ·
    refine ⟨19673534245851528319610291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13115689497234352213073527 19673534245851528319610291)
    ·
      refine ⟨29510301368777292479415437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19673534245851528319610291 29510301368777292479415437)
      ·
        refine ⟨11066363013291484679780789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29510301368777292479415437 11066363013291484679780789)
        ·
          refine ⟨1037471532496076688729449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11066363013291484679780789 1037471532496076688729449)
          ·
            refine ⟨778103649372057516547087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037471532496076688729449 778103649372057516547087)
            ·
              refine ⟨1167155474058086274820631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778103649372057516547087 1167155474058086274820631)
              ·
                refine ⟨1750733211087129412230947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1167155474058086274820631 1750733211087129412230947)
                ·
                  refine ⟨2626099816630694118346421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1750733211087129412230947 2626099816630694118346421)
                  ·
                    refine ⟨246196857809127573594977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2626099816630694118346421 246196857809127573594977)
                    ·
                      rfl

theorem cell22_719200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 1, 5].length) (baseStart_719200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_719200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_719200 prefixEnd_719200 := by exact prefixLift 719200
  have htrace : WordTrace (prefixWord ++ tailWord_719200) baseStart_719200 baseEnd_719200 := by
    simpa [prefixWord, tailWord_719200, baseEnd_719200] using wordTrace_append hprefix tailTrace_719200
  have hstable : (prefixWord ++ tailWord_719200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_719200).length < 2 ^ (prefixWord ++ tailWord_719200).sum := by decide
  have hdescent : baseEnd_719200 < baseStart_719200 := by decide
  rcases family_descends (prefixWord ++ tailWord_719200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
