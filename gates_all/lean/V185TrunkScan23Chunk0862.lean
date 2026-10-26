import V185TrunkScan23Chunk0861

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5101246 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_5101246 : Nat := 118140960795 + 5101246 * 2 ^ 59
def prefixEnd_5101246 : Nat := 4983230072969 + 3 ^ 40 * 5101246 * 2
def baseEnd_5101246 : Nat := 2619391134825653585264803

theorem tailTrace_5101246 : CollatzResearch.WordTrace tailWord_5101246 prefixEnd_5101246 2619391134825653585264803 := by
  unfold tailWord_5101246
  simp only [CollatzResearch.WordTrace]
  refine ⟨23257215859633055037533449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124038484584709626866845061 23257215859633055037533449)
  ·
    refine ⟨17442911894724791278150087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23257215859633055037533449 17442911894724791278150087)
    ·
      refine ⟨26164367842087186917225131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17442911894724791278150087 26164367842087186917225131)
      ·
        refine ⟨39246551763130780375837697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26164367842087186917225131 39246551763130780375837697)
        ·
          refine ⟨29434913822348085281878273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39246551763130780375837697 29434913822348085281878273)
          ·
            refine ⟨22076185366761063961408705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29434913822348085281878273 22076185366761063961408705)
            ·
              refine ⟨16557139025070797971056529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22076185366761063961408705 16557139025070797971056529)
              ·
                refine ⟨12417854268803098478292397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16557139025070797971056529 12417854268803098478292397)
                ·
                  refine ⟨4656695350801161929359649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12417854268803098478292397 4656695350801161929359649)
                  ·
                    refine ⟨3492521513100871447019737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4656695350801161929359649 3492521513100871447019737)
                    ·
                      refine ⟨2619391134825653585264803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3492521513100871447019737 2619391134825653585264803)
                      ·
                        rfl

theorem cell23_5101246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_5101246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101246 prefixEnd_5101246 := by exact prefixLift 5101246
  have htrace : WordTrace (prefixWord ++ tailWord_5101246) baseStart_5101246 baseEnd_5101246 := by
    simpa [prefixWord, tailWord_5101246, baseEnd_5101246] using wordTrace_append hprefix tailTrace_5101246
  have hstable : (prefixWord ++ tailWord_5101246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101246).length < 2 ^ (prefixWord ++ tailWord_5101246).sum := by decide
  have hdescent : baseEnd_5101246 < baseStart_5101246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101262 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_5101262 : Nat := 118140960795 + 5101262 * 2 ^ 59
def prefixEnd_5101262 : Nat := 4983230072969 + 3 ^ 40 * 5101262 * 2
def baseEnd_5101262 : Nat := 2619399350516125522664729

theorem tailTrace_5101262 : CollatzResearch.WordTrace tailWord_5101262 prefixEnd_5101262 2619399350516125522664729 := by
  unfold tailWord_5101262
  simp only [CollatzResearch.WordTrace]
  refine ⟨23257288805625809379106255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124038873630004316688566693 23257288805625809379106255)
  ·
    refine ⟨34885933208438714068659383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23257288805625809379106255 34885933208438714068659383)
    ·
      refine ⟨52328899812658071102989075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34885933208438714068659383 52328899812658071102989075)
      ·
        refine ⟨78493349718987106654483613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52328899812658071102989075 78493349718987106654483613)
        ·
          refine ⟨29435006144620164995431355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78493349718987106654483613 29435006144620164995431355)
          ·
            refine ⟨44152509216930247493147033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29435006144620164995431355 44152509216930247493147033)
            ·
              refine ⟨33114381912697685619860275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44152509216930247493147033 33114381912697685619860275)
              ·
                refine ⟨49671572869046528429790413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33114381912697685619860275 49671572869046528429790413)
                ·
                  refine ⟨18626839825892448161171405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49671572869046528429790413 18626839825892448161171405)
                  ·
                    refine ⟨6985064934709668060439277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18626839825892448161171405 6985064934709668060439277)
                    ·
                      refine ⟨2619399350516125522664729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6985064934709668060439277 2619399350516125522664729)
                      ·
                        rfl

theorem cell23_5101262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_5101262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101262 prefixEnd_5101262 := by exact prefixLift 5101262
  have htrace : WordTrace (prefixWord ++ tailWord_5101262) baseStart_5101262 baseEnd_5101262 := by
    simpa [prefixWord, tailWord_5101262, baseEnd_5101262] using wordTrace_append hprefix tailTrace_5101262
  have hstable : (prefixWord ++ tailWord_5101262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101262).length < 2 ^ (prefixWord ++ tailWord_5101262).sum := by decide
  have hdescent : baseEnd_5101262 < baseStart_5101262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101279 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 2, 1, 3]
def baseStart_5101279 : Nat := 118140960795 + 5101279 * 2 ^ 59
def prefixEnd_5101279 : Nat := 4983230072969 + 3 ^ 40 * 5101279 * 2
def baseEnd_5101279 : Nat := 2619408079687251956152151

theorem tailTrace_5101279 : CollatzResearch.WordTrace tailWord_5101279 prefixEnd_5101279 2619408079687251956152151 := by
  unfold tailWord_5101279
  simp only [CollatzResearch.WordTrace]
  refine ⟨186058930485944886936218891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124039286990629924624145927 186058930485944886936218891)
  ·
    refine ⟨279088395728917330404328337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186058930485944886936218891 279088395728917330404328337)
    ·
      refine ⟨209316296796687997803246253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279088395728917330404328337 209316296796687997803246253)
      ·
        refine ⟨78493611298757999176217345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209316296796687997803246253 78493611298757999176217345)
        ·
          refine ⟨58870208474068499382163009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78493611298757999176217345 58870208474068499382163009)
          ·
            refine ⟨44152656355551374536622257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58870208474068499382163009 44152656355551374536622257)
            ·
              refine ⟨33114492266663530902466693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44152656355551374536622257 33114492266663530902466693)
              ·
                refine ⟨6208967299999412044212505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33114492266663530902466693 6208967299999412044212505)
                ·
                  refine ⟨4656725474999559033159379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6208967299999412044212505 4656725474999559033159379)
                  ·
                    refine ⟨6985088212499338549739069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4656725474999559033159379 6985088212499338549739069)
                    ·
                      refine ⟨2619408079687251956152151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6985088212499338549739069 2619408079687251956152151)
                      ·
                        rfl

theorem cell23_5101279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_5101279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101279 prefixEnd_5101279 := by exact prefixLift 5101279
  have htrace : WordTrace (prefixWord ++ tailWord_5101279) baseStart_5101279 baseEnd_5101279 := by
    simpa [prefixWord, tailWord_5101279, baseEnd_5101279] using wordTrace_append hprefix tailTrace_5101279
  have hstable : (prefixWord ++ tailWord_5101279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101279).length < 2 ^ (prefixWord ++ tailWord_5101279).sum := by decide
  have hdescent : baseEnd_5101279 < baseStart_5101279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101295 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 1, 8]
def baseStart_5101295 : Nat := 118140960795 + 5101295 * 2 ^ 59
def prefixEnd_5101295 : Nat := 4983230072969 + 3 ^ 40 * 5101295 * 2
def baseEnd_5101295 : Nat := 873138765125907964517359

theorem tailTrace_5101295 : CollatzResearch.WordTrace tailWord_5101295 prefixEnd_5101295 873138765125907964517359 := by
  unfold tailWord_5101295
  simp only [CollatzResearch.WordTrace]
  refine ⟨186059514053886921668801339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124039676035924614445867559 186059514053886921668801339)
  ·
    refine ⟨279089271080830382503202009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186059514053886921668801339 279089271080830382503202009)
    ·
      refine ⟨209316953310622786877401507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279089271080830382503202009 209316953310622786877401507)
      ·
        refine ⟨313975429965934180316102261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209316953310622786877401507 313975429965934180316102261)
        ·
          refine ⟨29435196559306329404634587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 313975429965934180316102261 29435196559306329404634587)
          ·
            refine ⟨44152794838959494106951881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29435196559306329404634587 44152794838959494106951881)
            ·
              refine ⟨33114596129219620580213911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44152794838959494106951881 33114596129219620580213911)
              ·
                refine ⟨49671894193829430870320867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33114596129219620580213911 49671894193829430870320867)
                ·
                  refine ⟨74507841290744146305481301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49671894193829430870320867 74507841290744146305481301)
                  ·
                    refine ⟨873138765125907964517359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74507841290744146305481301 873138765125907964517359)
                    ·
                      rfl

theorem cell23_5101295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 8].length) (baseStart_5101295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101295 prefixEnd_5101295 := by exact prefixLift 5101295
  have htrace : WordTrace (prefixWord ++ tailWord_5101295) baseStart_5101295 baseEnd_5101295 := by
    simpa [prefixWord, tailWord_5101295, baseEnd_5101295] using wordTrace_append hprefix tailTrace_5101295
  have hstable : (prefixWord ++ tailWord_5101295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101295).length < 2 ^ (prefixWord ++ tailWord_5101295).sum := by decide
  have hdescent : baseEnd_5101295 < baseStart_5101295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101300 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_5101300 : Nat := 118140960795 + 5101300 * 2 ^ 59
def prefixEnd_5101300 : Nat := 4983230072969 + 3 ^ 40 * 5101300 * 2
def baseEnd_5101300 : Nat := 2619418862780996373989555

theorem tailTrace_5101300 : CollatzResearch.WordTrace tailWord_5101300 prefixEnd_5101300 2619418862780996373989555 := by
  unfold tailWord_5101300
  simp only [CollatzResearch.WordTrace]
  refine ⟨93029848209434403761366677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124039797612579205015155569 93029848209434403761366677)
  ·
    refine ⟨4360774134817237676314063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 93029848209434403761366677 4360774134817237676314063)
    ·
      refine ⟨6541161202225856514471095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4360774134817237676314063 6541161202225856514471095)
      ·
        refine ⟨9811741803338784771706643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6541161202225856514471095 9811741803338784771706643)
        ·
          refine ⟨14717612705008177157559965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9811741803338784771706643 14717612705008177157559965)
          ·
            refine ⟨5519104764378066434084987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14717612705008177157559965 5519104764378066434084987)
            ·
              refine ⟨8278657146567099651127481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519104764378066434084987 8278657146567099651127481)
              ·
                refine ⟨6208992859925324738345611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8278657146567099651127481 6208992859925324738345611)
                ·
                  refine ⟨9313489289887987107518417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6208992859925324738345611 9313489289887987107518417)
                  ·
                    refine ⟨6985116967415990330638813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9313489289887987107518417 6985116967415990330638813)
                    ·
                      refine ⟨2619418862780996373989555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6985116967415990330638813 2619418862780996373989555)
                      ·
                        rfl

theorem cell23_5101300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_5101300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101300 prefixEnd_5101300 := by exact prefixLift 5101300
  have htrace : WordTrace (prefixWord ++ tailWord_5101300) baseStart_5101300 baseEnd_5101300 := by
    simpa [prefixWord, tailWord_5101300, baseEnd_5101300] using wordTrace_append hprefix tailTrace_5101300
  have hstable : (prefixWord ++ tailWord_5101300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101300).length < 2 ^ (prefixWord ++ tailWord_5101300).sum := by decide
  have hdescent : baseEnd_5101300 < baseStart_5101300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101322 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_5101322 : Nat := 118140960795 + 5101322 * 2 ^ 59
def prefixEnd_5101322 : Nat := 4983230072969 + 3 ^ 40 * 5101322 * 2
def baseEnd_5101322 : Nat := 2619430159355395287914453

theorem tailTrace_5101322 : CollatzResearch.WordTrace tailWord_5101322 prefixEnd_5101322 2619430159355395287914453 := by
  unfold tailWord_5101322
  simp only [CollatzResearch.WordTrace]
  refine ⟨46515124706197276320008555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124040332549859403520022813 46515124706197276320008555)
  ·
    refine ⟨69772687059295914480012833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46515124706197276320008555 69772687059295914480012833)
    ·
      refine ⟨52329515294471935860009625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69772687059295914480012833 52329515294471935860009625)
      ·
        refine ⟨39247136470853951895007219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52329515294471935860009625 39247136470853951895007219)
        ·
          refine ⟨58870704706280927842510829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39247136470853951895007219 58870704706280927842510829)
          ·
            refine ⟨22076514264855347940941561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58870704706280927842510829 22076514264855347940941561)
            ·
              refine ⟨16557385698641510955706171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22076514264855347940941561 16557385698641510955706171)
              ·
                refine ⟨24836078547962266433559257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16557385698641510955706171 24836078547962266433559257)
                ·
                  refine ⟨18627058910971699825169443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24836078547962266433559257 18627058910971699825169443)
                  ·
                    refine ⟨27940588366457549737754165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18627058910971699825169443 27940588366457549737754165)
                    ·
                      refine ⟨2619430159355395287914453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27940588366457549737754165 2619430159355395287914453)
                      ·
                        rfl

theorem cell23_5101322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_5101322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101322 prefixEnd_5101322 := by exact prefixLift 5101322
  have htrace : WordTrace (prefixWord ++ tailWord_5101322) baseStart_5101322 baseEnd_5101322 := by
    simpa [prefixWord, tailWord_5101322, baseEnd_5101322] using wordTrace_append hprefix tailTrace_5101322
  have hstable : (prefixWord ++ tailWord_5101322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101322).length < 2 ^ (prefixWord ++ tailWord_5101322).sum := by decide
  have hdescent : baseEnd_5101322 < baseStart_5101322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101336 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 2, 2, 2]
def baseStart_5101336 : Nat := 118140960795 + 5101336 * 2 ^ 59
def prefixEnd_5101336 : Nat := 4983230072969 + 3 ^ 40 * 5101336 * 2
def baseEnd_5101336 : Nat := 2619437348084558233139389

theorem tailTrace_5101336 : CollatzResearch.WordTrace tailWord_5101336 prefixEnd_5101336 2619437348084558233139389 := by
  unfold tailWord_5101336
  simp only [CollatzResearch.WordTrace]
  refine ⟨93030504723369192835521931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124040672964492257114029241 93030504723369192835521931)
  ·
    refine ⟨139545757085053789253282897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93030504723369192835521931 139545757085053789253282897)
    ·
      refine ⟨104659317813790341939962173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139545757085053789253282897 104659317813790341939962173)
      ·
        refine ⟨39247244180171378227485815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104659317813790341939962173 39247244180171378227485815)
        ·
          refine ⟨58870866270257067341228723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39247244180171378227485815 58870866270257067341228723)
          ·
            refine ⟨88306299405385601011843085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58870866270257067341228723 88306299405385601011843085)
            ·
              refine ⟨33114862277019600379441157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88306299405385601011843085 33114862277019600379441157)
              ·
                refine ⟨6209036676941175071145217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33114862277019600379441157 6209036676941175071145217)
                ·
                  refine ⟨4656777507705881303358913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6209036676941175071145217 4656777507705881303358913)
                  ·
                    refine ⟨3492583130779410977519185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4656777507705881303358913 3492583130779410977519185)
                    ·
                      refine ⟨2619437348084558233139389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3492583130779410977519185 2619437348084558233139389)
                      ·
                        rfl

theorem cell23_5101336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_5101336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101336 prefixEnd_5101336 := by exact prefixLift 5101336
  have htrace : WordTrace (prefixWord ++ tailWord_5101336) baseStart_5101336 baseEnd_5101336 := by
    simpa [prefixWord, tailWord_5101336, baseEnd_5101336] using wordTrace_append hprefix tailTrace_5101336
  have hstable : (prefixWord ++ tailWord_5101336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101336).length < 2 ^ (prefixWord ++ tailWord_5101336).sum := by decide
  have hdescent : baseEnd_5101336 < baseStart_5101336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101392 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 4]
def baseStart_5101392 : Nat := 118140960795 + 5101392 * 2 ^ 59
def prefixEnd_5101392 : Nat := 4983230072969 + 3 ^ 40 * 5101392 * 2
def baseEnd_5101392 : Nat := 2619466103001210014039131

theorem tailTrace_5101392 : CollatzResearch.WordTrace tailWord_5101392 prefixEnd_5101392 2619466103001210014039131 := by
  unfold tailWord_5101392
  simp only [CollatzResearch.WordTrace]
  refine ⟨93031525967267753617541215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124042034623023671490054953 93031525967267753617541215)
  ·
    refine ⟨139547288950901630426311823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93031525967267753617541215 139547288950901630426311823)
    ·
      refine ⟨209320933426352445639467735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139547288950901630426311823 209320933426352445639467735)
      ·
        refine ⟨313981400139528668459201603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209320933426352445639467735 313981400139528668459201603)
        ·
          refine ⟨470972100209293002688802405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313981400139528668459201603 470972100209293002688802405)
          ·
            refine ⟨88307268789242438004150451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 470972100209293002688802405 88307268789242438004150451)
            ·
              refine ⟨132460903183863657006225677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88307268789242438004150451 132460903183863657006225677)
              ·
                refine ⟨49672838693948871377334629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132460903183863657006225677 49672838693948871377334629)
                ·
                  refine ⟨9313657255115413383250243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49672838693948871377334629 9313657255115413383250243)
                  ·
                    refine ⟨13970485882673120074875365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9313657255115413383250243 13970485882673120074875365)
                    ·
                      refine ⟨2619466103001210014039131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13970485882673120074875365 2619466103001210014039131)
                      ·
                        rfl

theorem cell23_5101392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_5101392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101392 prefixEnd_5101392 := by exact prefixLift 5101392
  have htrace : WordTrace (prefixWord ++ tailWord_5101392) baseStart_5101392 baseEnd_5101392 := by
    simpa [prefixWord, tailWord_5101392, baseEnd_5101392] using wordTrace_append hprefix tailTrace_5101392
  have hstable : (prefixWord ++ tailWord_5101392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101392).length < 2 ^ (prefixWord ++ tailWord_5101392).sum := by decide
  have hdescent : baseEnd_5101392 < baseStart_5101392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101409 : List Nat := [1, 2, 3, 1, 1, 1, 3, 3, 2, 4, 2]
def baseStart_5101409 : Nat := 118140960795 + 5101409 * 2 ^ 59
def prefixEnd_5101409 : Nat := 4983230072969 + 3 ^ 40 * 5101409 * 2
def baseEnd_5101409 : Nat := 2619474832172336447526553

theorem tailTrace_5101409 : CollatzResearch.WordTrace tailWord_5101409 prefixEnd_5101409 2619474832172336447526553 := by
  unfold tailWord_5101409
  simp only [CollatzResearch.WordTrace]
  refine ⟨186063671975473919138451281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124042447983649279425634187 186063671975473919138451281)
  ·
    refine ⟨139547753981605439353838461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186063671975473919138451281 139547753981605439353838461)
    ·
      refine ⟨52330407743102039757689423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139547753981605439353838461 52330407743102039757689423)
      ·
        refine ⟨78495611614653059636534135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52330407743102039757689423 78495611614653059636534135)
        ·
          refine ⟨117743417421979589454801203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78495611614653059636534135 117743417421979589454801203)
          ·
            refine ⟨176615126132969384182201805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117743417421979589454801203 176615126132969384182201805)
            ·
              refine ⟨66230672299863519068325677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176615126132969384182201805 66230672299863519068325677)
              ·
                refine ⟨24836502112448819650622129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66230672299863519068325677 24836502112448819650622129)
                ·
                  refine ⟨18627376584336614737966597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24836502112448819650622129 18627376584336614737966597)
                  ·
                    refine ⟨3492633109563115263368737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18627376584336614737966597 3492633109563115263368737)
                    ·
                      refine ⟨2619474832172336447526553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3492633109563115263368737 2619474832172336447526553)
                      ·
                        rfl

theorem cell23_5101409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_5101409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101409 prefixEnd_5101409 := by exact prefixLift 5101409
  have htrace : WordTrace (prefixWord ++ tailWord_5101409) baseStart_5101409 baseEnd_5101409 := by
    simpa [prefixWord, tailWord_5101409, baseEnd_5101409] using wordTrace_append hprefix tailTrace_5101409
  have hstable : (prefixWord ++ tailWord_5101409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101409).length < 2 ^ (prefixWord ++ tailWord_5101409).sum := by decide
  have hdescent : baseEnd_5101409 < baseStart_5101409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101429 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_5101429 : Nat := 118140960795 + 5101429 * 2 ^ 59
def prefixEnd_5101429 : Nat := 4983230072969 + 3 ^ 40 * 5101429 * 2
def baseEnd_5101429 : Nat := 2619485101785426369276461

theorem tailTrace_5101429 : CollatzResearch.WordTrace tailWord_5101429 prefixEnd_5101429 2619485101785426369276461 := by
  unfold tailWord_5101429
  simp only [CollatzResearch.WordTrace]
  refine ⟨186064401435401462554179341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124042934290267641702786227 186064401435401462554179341)
  ·
    refine ⟨69774150538275548457817253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186064401435401462554179341 69774150538275548457817253)
    ·
      refine ⟨13082653225926665335840735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69774150538275548457817253 13082653225926665335840735)
      ·
        refine ⟨19623979838889998003761103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13082653225926665335840735 19623979838889998003761103)
        ·
          refine ⟨29435969758334997005641655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19623979838889998003761103 29435969758334997005641655)
          ·
            refine ⟨44153954637502495508462483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29435969758334997005641655 44153954637502495508462483)
            ·
              refine ⟨66230931956253743262693725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44153954637502495508462483 66230931956253743262693725)
              ·
                refine ⟨24836599483595153723510147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66230931956253743262693725 24836599483595153723510147)
                ·
                  refine ⟨37254899225392730585265221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24836599483595153723510147 37254899225392730585265221)
                  ·
                    refine ⟨6985293604761136984737229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37254899225392730585265221 6985293604761136984737229)
                    ·
                      refine ⟨2619485101785426369276461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6985293604761136984737229 2619485101785426369276461)
                      ·
                        rfl

theorem cell23_5101429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_5101429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101429 prefixEnd_5101429 := by exact prefixLift 5101429
  have htrace : WordTrace (prefixWord ++ tailWord_5101429) baseStart_5101429 baseEnd_5101429 := by
    simpa [prefixWord, tailWord_5101429, baseEnd_5101429] using wordTrace_append hprefix tailTrace_5101429
  have hstable : (prefixWord ++ tailWord_5101429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101429).length < 2 ^ (prefixWord ++ tailWord_5101429).sum := by decide
  have hdescent : baseEnd_5101429 < baseStart_5101429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101466 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 6]
def baseStart_5101466 : Nat := 118140960795 + 5101466 * 2 ^ 59
def prefixEnd_5101466 : Nat := 4983230072969 + 3 ^ 40 * 5101466 * 2
def baseEnd_5101466 : Nat := 291056011174404747168199

theorem tailTrace_5101466 : CollatzResearch.WordTrace tailWord_5101466 prefixEnd_5101466 291056011174404747168199 := by
  unfold tailWord_5101466
  simp only [CollatzResearch.WordTrace]
  refine ⟨46516437734066854468319063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124043833957511611915517501 46516437734066854468319063)
  ·
    refine ⟨69774656601100281702478595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46516437734066854468319063 69774656601100281702478595)
    ·
      refine ⟨104661984901650422553717893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69774656601100281702478595 104661984901650422553717893)
      ·
        refine ⟨19624122169059454228822105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104661984901650422553717893 19624122169059454228822105)
        ·
          refine ⟨14718091626794590671616579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19624122169059454228822105 14718091626794590671616579)
          ·
            refine ⟨22077137440191886007424869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14718091626794590671616579 22077137440191886007424869)
            ·
              refine ⟨4139463270035978626392163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22077137440191886007424869 4139463270035978626392163)
              ·
                refine ⟨6209194905053967939588245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4139463270035978626392163 6209194905053967939588245)
                ·
                  refine ⟨291056011174404747168199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6209194905053967939588245 291056011174404747168199)
                  ·
                    rfl

theorem cell23_5101466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_5101466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101466 prefixEnd_5101466 := by exact prefixLift 5101466
  have htrace : WordTrace (prefixWord ++ tailWord_5101466) baseStart_5101466 baseEnd_5101466 := by
    simpa [prefixWord, tailWord_5101466, baseEnd_5101466] using wordTrace_append hprefix tailTrace_5101466
  have hstable : (prefixWord ++ tailWord_5101466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101466).length < 2 ^ (prefixWord ++ tailWord_5101466).sum := by decide
  have hdescent : baseEnd_5101466 < baseStart_5101466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101480 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5101480 : Nat := 118140960795 + 5101480 * 2 ^ 59
def prefixEnd_5101480 : Nat := 4983230072969 + 3 ^ 40 * 5101480 * 2
def baseEnd_5101480 : Nat := 2619511289298805669738727

theorem tailTrace_5101480 : CollatzResearch.WordTrace tailWord_5101480 prefixEnd_5101480 2619511289298805669738727 := by
  unfold tailWord_5101480
  simp only [CollatzResearch.WordTrace]
  refine ⟨93033130779108349132142947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124044174372144465509523929 93033130779108349132142947)
  ·
    refine ⟨139549696168662523698214421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93033130779108349132142947 139549696168662523698214421)
    ·
      refine ⟨6541392007906055798353801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139549696168662523698214421 6541392007906055798353801)
      ·
        refine ⟨4906044005929541848765351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6541392007906055798353801 4906044005929541848765351)
        ·
          refine ⟨7359066008894312773148027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4906044005929541848765351 7359066008894312773148027)
          ·
            refine ⟨11038599013341469159722041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7359066008894312773148027 11038599013341469159722041)
            ·
              refine ⟨8278949260006101869791531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11038599013341469159722041 8278949260006101869791531)
              ·
                refine ⟨12418423890009152804687297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8278949260006101869791531 12418423890009152804687297)
                ·
                  refine ⟨9313817917506864603515473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12418423890009152804687297 9313817917506864603515473)
                  ·
                    refine ⟨6985363438130148452636605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9313817917506864603515473 6985363438130148452636605)
                    ·
                      refine ⟨2619511289298805669738727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6985363438130148452636605 2619511289298805669738727)
                      ·
                        rfl

theorem cell23_5101480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5101480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101480 prefixEnd_5101480 := by exact prefixLift 5101480
  have htrace : WordTrace (prefixWord ++ tailWord_5101480) baseStart_5101480 baseEnd_5101480 := by
    simpa [prefixWord, tailWord_5101480, baseEnd_5101480] using wordTrace_append hprefix tailTrace_5101480
  have hstable : (prefixWord ++ tailWord_5101480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101480).length < 2 ^ (prefixWord ++ tailWord_5101480).sum := by decide
  have hdescent : baseEnd_5101480 < baseStart_5101480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101496 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 1, 5]
def baseStart_5101496 : Nat := 118140960795 + 5101496 * 2 ^ 59
def prefixEnd_5101496 : Nat := 4983230072969 + 3 ^ 40 * 5101496 * 2
def baseEnd_5101496 : Nat := 873173168329759202379551

theorem tailTrace_5101496 : CollatzResearch.WordTrace tailWord_5101496 prefixEnd_5101496 873173168329759202379551 := by
  unfold tailWord_5101496
  simp only [CollatzResearch.WordTrace]
  refine ⟨93033422563079366498434171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124044563417439155331245561 93033422563079366498434171)
  ·
    refine ⟨139550133844619049747651257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93033422563079366498434171 139550133844619049747651257)
    ·
      refine ⟨104662600383464287310738443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139550133844619049747651257 104662600383464287310738443)
      ·
        refine ⟨156993900575196430966107665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104662600383464287310738443 156993900575196430966107665)
        ·
          refine ⟨117745425431397323224580749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156993900575196430966107665 117745425431397323224580749)
          ·
            refine ⟨44154534536773996209217781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117745425431397323224580749 44154534536773996209217781)
            ·
              refine ⟨4139487612822562144614167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44154534536773996209217781 4139487612822562144614167)
              ·
                refine ⟨6209231419233843216921251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4139487612822562144614167 6209231419233843216921251)
                ·
                  refine ⟨9313847128850764825381877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6209231419233843216921251 9313847128850764825381877)
                  ·
                    refine ⟨873173168329759202379551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9313847128850764825381877 873173168329759202379551)
                    ·
                      rfl

theorem cell23_5101496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_5101496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101496 prefixEnd_5101496 := by exact prefixLift 5101496
  have htrace : WordTrace (prefixWord ++ tailWord_5101496) baseStart_5101496 baseEnd_5101496 := by
    simpa [prefixWord, tailWord_5101496, baseEnd_5101496] using wordTrace_append hprefix tailTrace_5101496
  have hstable : (prefixWord ++ tailWord_5101496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101496).length < 2 ^ (prefixWord ++ tailWord_5101496).sum := by decide
  have hdescent : baseEnd_5101496 < baseStart_5101496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101519 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 3]
def baseStart_5101519 : Nat := 118140960795 + 5101519 * 2 ^ 59
def prefixEnd_5101519 : Nat := 4983230072969 + 3 ^ 40 * 5101519 * 2
def baseEnd_5101519 : Nat := 2619531315044331017151047

theorem tailTrace_5101519 : CollatzResearch.WordTrace tailWord_5101519 prefixEnd_5101519 2619531315044331017151047 := by
  unfold tailWord_5101519
  simp only [CollatzResearch.WordTrace]
  refine ⟨186067684005075407924955611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124045122670050271949970407 186067684005075407924955611)
  ·
    refine ⟨279101526007613111887433417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186067684005075407924955611 279101526007613111887433417)
    ·
      refine ⟨209326144505709833915575063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279101526007613111887433417 209326144505709833915575063)
      ·
        refine ⟨313989216758564750873362595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209326144505709833915575063 313989216758564750873362595)
        ·
          refine ⟨470983825137847126310043893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313989216758564750873362595 470983825137847126310043893)
          ·
            refine ⟨44154733606673168091566615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 470983825137847126310043893 44154733606673168091566615)
            ·
              refine ⟨66232100410009752137349923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44154733606673168091566615 66232100410009752137349923)
              ·
                refine ⟨99348150615014628206024885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66232100410009752137349923 99348150615014628206024885)
                ·
                  refine ⟨9313889120157621394314833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99348150615014628206024885 9313889120157621394314833)
                  ·
                    refine ⟨6985416840118216045736125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9313889120157621394314833 6985416840118216045736125)
                    ·
                      refine ⟨2619531315044331017151047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6985416840118216045736125 2619531315044331017151047)
                      ·
                        rfl

theorem cell23_5101519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 3].length) (baseStart_5101519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101519 prefixEnd_5101519 := by exact prefixLift 5101519
  have htrace : WordTrace (prefixWord ++ tailWord_5101519) baseStart_5101519 baseEnd_5101519 := by
    simpa [prefixWord, tailWord_5101519, baseEnd_5101519] using wordTrace_append hprefix tailTrace_5101519
  have hstable : (prefixWord ++ tailWord_5101519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101519).length < 2 ^ (prefixWord ++ tailWord_5101519).sum := by decide
  have hdescent : baseEnd_5101519 < baseStart_5101519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101550 : List Nat := [4, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_5101550 : Nat := 118140960795 + 5101550 * 2 ^ 59
def prefixEnd_5101550 : Nat := 4983230072969 + 3 ^ 40 * 5101550 * 2
def baseEnd_5101550 : Nat := 2619547232944620395863405

theorem tailTrace_5101550 : CollatzResearch.WordTrace tailWord_5101550 prefixEnd_5101550 2619547232944620395863405 := by
  unfold tailWord_5101550
  simp only [CollatzResearch.WordTrace]
  refine ⟨23258601833495387527416763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124045876445308733479556069 23258601833495387527416763)
  ·
    refine ⟨34887902750243081291125145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23258601833495387527416763 34887902750243081291125145)
    ·
      refine ⟨26165927062682310968343859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34887902750243081291125145 26165927062682310968343859)
      ·
        refine ⟨39248890594023466452515789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26165927062682310968343859 39248890594023466452515789)
        ·
          refine ⟨14718333972758799919693421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39248890594023466452515789 14718333972758799919693421)
          ·
            refine ⟨5519375239784549969885033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14718333972758799919693421 5519375239784549969885033)
            ·
              refine ⟨4139531429838412477413775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5519375239784549969885033 4139531429838412477413775)
              ·
                refine ⟨6209297144757618716120663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4139531429838412477413775 6209297144757618716120663)
                ·
                  refine ⟨9313945717136428074180995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6209297144757618716120663 9313945717136428074180995)
                  ·
                    refine ⟨13970918575704642111271493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9313945717136428074180995 13970918575704642111271493)
                    ·
                      refine ⟨2619547232944620395863405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13970918575704642111271493 2619547232944620395863405)
                      ·
                        rfl

theorem cell23_5101550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_5101550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101550 prefixEnd_5101550 := by exact prefixLift 5101550
  have htrace : WordTrace (prefixWord ++ tailWord_5101550) baseStart_5101550 baseEnd_5101550 := by
    simpa [prefixWord, tailWord_5101550, baseEnd_5101550] using wordTrace_append hprefix tailTrace_5101550
  have hstable : (prefixWord ++ tailWord_5101550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101550).length < 2 ^ (prefixWord ++ tailWord_5101550).sum := by decide
  have hdescent : baseEnd_5101550 < baseStart_5101550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101553 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 1, 2, 3]
def baseStart_5101553 : Nat := 118140960795 + 5101553 * 2 ^ 59
def prefixEnd_5101553 : Nat := 4983230072969 + 3 ^ 40 * 5101553 * 2
def baseEnd_5101553 : Nat := 2619548773386583884125891

theorem tailTrace_5101553 : CollatzResearch.WordTrace tailWord_5101553 prefixEnd_5101553 2619548773386583884125891 := by
  unfold tailWord_5101553
  simp only [CollatzResearch.WordTrace]
  refine ⟨186068924086952231731693313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124045949391301487821128875 186068924086952231731693313)
  ·
    refine ⟨139551693065214173798769985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186068924086952231731693313 139551693065214173798769985)
    ·
      refine ⟨104663769798910630349077489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139551693065214173798769985 104663769798910630349077489)
      ·
        refine ⟨78497827349182972761808117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104663769798910630349077489 78497827349182972761808117)
        ·
          refine ⟨7359171313985903696419511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78497827349182972761808117 7359171313985903696419511)
          ·
            refine ⟨11038756970978855544629267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7359171313985903696419511 11038756970978855544629267)
            ·
              refine ⟨16558135456468283316943901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11038756970978855544629267 16558135456468283316943901)
              ·
                refine ⟨6209300796175606243853963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16558135456468283316943901 6209300796175606243853963)
                ·
                  refine ⟨9313951194263409365780945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6209300796175606243853963 9313951194263409365780945)
                  ·
                    refine ⟨6985463395697557024335709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9313951194263409365780945 6985463395697557024335709)
                    ·
                      refine ⟨2619548773386583884125891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6985463395697557024335709 2619548773386583884125891)
                      ·
                        rfl

theorem cell23_5101553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 2, 3].length) (baseStart_5101553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101553 prefixEnd_5101553 := by exact prefixLift 5101553
  have htrace : WordTrace (prefixWord ++ tailWord_5101553) baseStart_5101553 baseEnd_5101553 := by
    simpa [prefixWord, tailWord_5101553, baseEnd_5101553] using wordTrace_append hprefix tailTrace_5101553
  have hstable : (prefixWord ++ tailWord_5101553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101553).length < 2 ^ (prefixWord ++ tailWord_5101553).sum := by decide
  have hdescent : baseEnd_5101553 < baseStart_5101553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101610 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_5101610 : Nat := 118140960795 + 5101610 * 2 ^ 59
def prefixEnd_5101610 : Nat := 4983230072969 + 3 ^ 40 * 5101610 * 2
def baseEnd_5101610 : Nat := 2619578041783890161113129

theorem tailTrace_5101610 : CollatzResearch.WordTrace tailWord_5101610 prefixEnd_5101610 2619578041783890161113129 := by
  unfold tailWord_5101610
  simp only [CollatzResearch.WordTrace]
  refine ⟨46517750761936432616629571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124047335365163820311012189 46517750761936432616629571)
  ·
    refine ⟨69776626142904648924944357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46517750761936432616629571 69776626142904648924944357)
    ·
      refine ⟨13083117401794621673427067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69776626142904648924944357 13083117401794621673427067)
      ·
        refine ⟨19624676102691932510140601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13083117401794621673427067 19624676102691932510140601)
        ·
          refine ⟨14718507077018949382605451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19624676102691932510140601 14718507077018949382605451)
          ·
            refine ⟨22077760615528424073908177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14718507077018949382605451 22077760615528424073908177)
            ·
              refine ⟨16558320461646318055431133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22077760615528424073908177 16558320461646318055431133)
              ·
                refine ⟨6209370173117369270786675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16558320461646318055431133 6209370173117369270786675)
                ·
                  refine ⟨9314055259676053906180013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6209370173117369270786675 9314055259676053906180013)
                  ·
                    refine ⟨3492770722378520214817505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9314055259676053906180013 3492770722378520214817505)
                    ·
                      refine ⟨2619578041783890161113129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3492770722378520214817505 2619578041783890161113129)
                      ·
                        rfl

theorem cell23_5101610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_5101610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101610 prefixEnd_5101610 := by exact prefixLift 5101610
  have htrace : WordTrace (prefixWord ++ tailWord_5101610) baseStart_5101610 baseEnd_5101610 := by
    simpa [prefixWord, tailWord_5101610, baseEnd_5101610] using wordTrace_append hprefix tailTrace_5101610
  have hstable : (prefixWord ++ tailWord_5101610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101610).length < 2 ^ (prefixWord ++ tailWord_5101610).sum := by decide
  have hdescent : baseEnd_5101610 < baseStart_5101610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101619 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 4]
def baseStart_5101619 : Nat := 118140960795 + 5101619 * 2 ^ 59
def prefixEnd_5101619 : Nat := 4983230072969 + 3 ^ 40 * 5101619 * 2
def baseEnd_5101619 : Nat := 2619582663109780625900587

theorem tailTrace_5101619 : CollatzResearch.WordTrace tailWord_5101619 prefixEnd_5101619 2619582663109780625900587 := by
  unfold tailWord_5101619
  simp only [CollatzResearch.WordTrace]
  refine ⟨186071331304713125003595911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124047554203142083335730607 186071331304713125003595911)
  ·
    refine ⟨279106996957069687505393867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186071331304713125003595911 279106996957069687505393867)
    ·
      refine ⟨418660495435604531258090801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279106996957069687505393867 418660495435604531258090801)
      ·
        refine ⟨313995371576703398443568101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418660495435604531258090801 313995371576703398443568101)
        ·
          refine ⟨58874132170631887208169019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313995371576703398443568101 58874132170631887208169019)
          ·
            refine ⟨88311198255947830812253529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58874132170631887208169019 88311198255947830812253529)
            ·
              refine ⟨66233398691960873109190147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88311198255947830812253529 66233398691960873109190147)
              ·
                refine ⟨99350098037941309663785221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66233398691960873109190147 99350098037941309663785221)
                ·
                  refine ⟨18628143382113995561959729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99350098037941309663785221 18628143382113995561959729)
                  ·
                    refine ⟨13971107536585496671469797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18628143382113995561959729 13971107536585496671469797)
                    ·
                      refine ⟨2619582663109780625900587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13971107536585496671469797 2619582663109780625900587)
                      ·
                        rfl

theorem cell23_5101619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_5101619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101619 prefixEnd_5101619 := by exact prefixLift 5101619
  have htrace : WordTrace (prefixWord ++ tailWord_5101619) baseStart_5101619 baseEnd_5101619 := by
    simpa [prefixWord, tailWord_5101619, baseEnd_5101619] using wordTrace_append hprefix tailTrace_5101619
  have hstable : (prefixWord ++ tailWord_5101619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101619).length < 2 ^ (prefixWord ++ tailWord_5101619).sum := by decide
  have hdescent : baseEnd_5101619 < baseStart_5101619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101623 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 4, 2, 2]
def baseStart_5101623 : Nat := 118140960795 + 5101623 * 2 ^ 59
def prefixEnd_5101623 : Nat := 4983230072969 + 3 ^ 40 * 5101623 * 2
def baseEnd_5101623 : Nat := 2619584717032398610250569

theorem tailTrace_5101623 : CollatzResearch.WordTrace tailWord_5101623 prefixEnd_5101623 2619584717032398610250569 := by
  unfold tailWord_5101623
  simp only [CollatzResearch.WordTrace]
  refine ⟨186071477196698633686741523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124047651464465755791161015 186071477196698633686741523)
  ·
    refine ⟨279107215795047950530112285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186071477196698633686741523 279107215795047950530112285)
    ·
      refine ⟨104665205923142981448792107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279107215795047950530112285 104665205923142981448792107)
      ·
        refine ⟨156997808884714472173188161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104665205923142981448792107 156997808884714472173188161)
        ·
          refine ⟨117748356663535854129891121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156997808884714472173188161 117748356663535854129891121)
          ·
            refine ⟨88311267497651890597418341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117748356663535854129891121 88311267497651890597418341)
            ·
              refine ⟨16558362655809729487015939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88311267497651890597418341 16558362655809729487015939)
              ·
                refine ⟨24837543983714594230523909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16558362655809729487015939 24837543983714594230523909)
                ·
                  refine ⟨4657039496946486418223233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24837543983714594230523909 4657039496946486418223233)
                  ·
                    refine ⟨3492779622709864813667425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4657039496946486418223233 3492779622709864813667425)
                    ·
                      refine ⟨2619584717032398610250569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3492779622709864813667425 2619584717032398610250569)
                      ·
                        rfl

theorem cell23_5101623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 2, 2].length) (baseStart_5101623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101623 prefixEnd_5101623 := by exact prefixLift 5101623
  have htrace : WordTrace (prefixWord ++ tailWord_5101623) baseStart_5101623 baseEnd_5101623 := by
    simpa [prefixWord, tailWord_5101623, baseEnd_5101623] using wordTrace_append hprefix tailTrace_5101623
  have hstable : (prefixWord ++ tailWord_5101623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101623).length < 2 ^ (prefixWord ++ tailWord_5101623).sum := by decide
  have hdescent : baseEnd_5101623 < baseStart_5101623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101676 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 2, 5]
def baseStart_5101676 : Nat := 118140960795 + 5101676 * 2 ^ 59
def prefixEnd_5101676 : Nat := 4983230072969 + 3 ^ 40 * 5101676 * 2
def baseEnd_5101676 : Nat := 873203977169028967629275

theorem tailTrace_5101676 : CollatzResearch.WordTrace tailWord_5101676 prefixEnd_5101676 873203977169028967629275 := by
  unfold tailWord_5101676
  simp only [CollatzResearch.WordTrace]
  refine ⟨93036705132753311869210441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124048940177004415825613921 93036705132753311869210441)
  ·
    refine ⟨69777528849564983901907831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93036705132753311869210441 69777528849564983901907831)
    ·
      refine ⟨104666293274347475852861747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69777528849564983901907831 104666293274347475852861747)
      ·
        refine ⟨156999439911521213779292621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104666293274347475852861747 156999439911521213779292621)
        ·
          refine ⟨58874789966820455167234733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156999439911521213779292621 58874789966820455167234733)
          ·
            refine ⟨22078046237557670687713025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58874789966820455167234733 22078046237557670687713025)
            ·
              refine ⟨16558534678168253015784769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22078046237557670687713025 16558534678168253015784769)
              ·
                refine ⟨12418901008626189761838577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16558534678168253015784769 12418901008626189761838577)
                ·
                  refine ⟨9314175756469642321378933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12418901008626189761838577 9314175756469642321378933)
                  ·
                    refine ⟨873203977169028967629275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9314175756469642321378933 873203977169028967629275)
                    ·
                      rfl

theorem cell23_5101676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_5101676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101676 prefixEnd_5101676 := by exact prefixLift 5101676
  have htrace : WordTrace (prefixWord ++ tailWord_5101676) baseStart_5101676 baseEnd_5101676 := by
    simpa [prefixWord, tailWord_5101676, baseEnd_5101676] using wordTrace_append hprefix tailTrace_5101676
  have hstable : (prefixWord ++ tailWord_5101676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101676).length < 2 ^ (prefixWord ++ tailWord_5101676).sum := by decide
  have hdescent : baseEnd_5101676 < baseStart_5101676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101680 : List Nat := [2, 1, 1, 1, 5, 4, 2, 2, 5]
def baseStart_5101680 : Nat := 118140960795 + 5101680 * 2 ^ 59
def prefixEnd_5101680 : Nat := 4983230072969 + 3 ^ 40 * 5101680 * 2
def baseEnd_5101680 : Nat := 291068220603300543026423

theorem tailTrace_5101680 : CollatzResearch.WordTrace tailWord_5101680 prefixEnd_5101680 291068220603300543026423 := by
  unfold tailWord_5101680
  simp only [CollatzResearch.WordTrace]
  refine ⟨93036778078746066210783247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124049037438328088281044329 93036778078746066210783247)
  ·
    refine ⟨139555167118119099316174871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93036778078746066210783247 139555167118119099316174871)
    ·
      refine ⟨209332750677178648974262307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139555167118119099316174871 209332750677178648974262307)
      ·
        refine ⟨313999126015767973461393461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209332750677178648974262307 313999126015767973461393461)
        ·
          refine ⟨29437418063978247512005637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 313999126015767973461393461 29437418063978247512005637)
          ·
            refine ⟨5519515886995921408501057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29437418063978247512005637 5519515886995921408501057)
            ·
              refine ⟨4139636915246941056375793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5519515886995921408501057 4139636915246941056375793)
              ·
                refine ⟨3104727686435205792281845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4139636915246941056375793 3104727686435205792281845)
                ·
                  refine ⟨291068220603300543026423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3104727686435205792281845 291068220603300543026423)
                  ·
                    rfl

theorem cell23_5101680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 5].length) (baseStart_5101680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101680 prefixEnd_5101680 := by exact prefixLift 5101680
  have htrace : WordTrace (prefixWord ++ tailWord_5101680) baseStart_5101680 baseEnd_5101680 := by
    simpa [prefixWord, tailWord_5101680, baseEnd_5101680] using wordTrace_append hprefix tailTrace_5101680
  have hstable : (prefixWord ++ tailWord_5101680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101680).length < 2 ^ (prefixWord ++ tailWord_5101680).sum := by decide
  have hdescent : baseEnd_5101680 < baseStart_5101680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101710 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_5101710 : Nat := 118140960795 + 5101710 * 2 ^ 59
def prefixEnd_5101710 : Nat := 4983230072969 + 3 ^ 40 * 5101710 * 2
def baseEnd_5101710 : Nat := 873209796616446589954223

theorem tailTrace_5101710 : CollatzResearch.WordTrace tailWord_5101710 prefixEnd_5101710 873209796616446589954223 := by
  unfold tailWord_5101710
  simp only [CollatzResearch.WordTrace]
  refine ⟨23259331293422930943144823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124049766898255631696772389 23259331293422930943144823)
  ·
    refine ⟨34888996940134396414717235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23259331293422930943144823 34888996940134396414717235)
    ·
      refine ⟨52333495410201594622075853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34888996940134396414717235 52333495410201594622075853)
      ·
        refine ⟨19625060778825597983278445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52333495410201594622075853 19625060778825597983278445)
        ·
          refine ⟨7359397792059599243729417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19625060778825597983278445 7359397792059599243729417)
          ·
            refine ⟨5519548344044699432797063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7359397792059599243729417 5519548344044699432797063)
            ·
              refine ⟨8279322516067049149195595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519548344044699432797063 8279322516067049149195595)
              ·
                refine ⟨12418983774100573723793393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8279322516067049149195595 12418983774100573723793393)
                ·
                  refine ⟨9314237830575430292845045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12418983774100573723793393 9314237830575430292845045)
                  ·
                    refine ⟨873209796616446589954223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9314237830575430292845045 873209796616446589954223)
                    ·
                      rfl

theorem cell23_5101710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_5101710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101710 prefixEnd_5101710 := by exact prefixLift 5101710
  have htrace : WordTrace (prefixWord ++ tailWord_5101710) baseStart_5101710 baseEnd_5101710 := by
    simpa [prefixWord, tailWord_5101710, baseEnd_5101710] using wordTrace_append hprefix tailTrace_5101710
  have hstable : (prefixWord ++ tailWord_5101710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101710).length < 2 ^ (prefixWord ++ tailWord_5101710).sum := by decide
  have hdescent : baseEnd_5101710 < baseStart_5101710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101730 : List Nat := [3, 3, 1, 3, 1, 1, 1, 2, 2, 4, 2]
def baseStart_5101730 : Nat := 118140960795 + 5101730 * 2 ^ 59
def prefixEnd_5101730 : Nat := 4983230072969 + 3 ^ 40 * 5101730 * 2
def baseEnd_5101730 : Nat := 2619639659462429691612577

theorem tailTrace_5101730 : CollatzResearch.WordTrace tailWord_5101730 prefixEnd_5101730 2619639659462429691612577 := by
  unfold tailWord_5101730
  simp only [CollatzResearch.WordTrace]
  refine ⟨46518844951827747740221661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124050253204873993973924429 46518844951827747740221661)
  ·
    refine ⟨17444566856935405402583123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46518844951827747740221661 17444566856935405402583123)
    ·
      refine ⟨26166850285403108103874685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17444566856935405402583123 26166850285403108103874685)
      ·
        refine ⟨9812568857026165538953007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26166850285403108103874685 9812568857026165538953007)
        ·
          refine ⟨14718853285539248308429511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9812568857026165538953007 14718853285539248308429511)
          ·
            refine ⟨22078279928308872462644267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14718853285539248308429511 22078279928308872462644267)
            ·
              refine ⟨33117419892463308693966401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22078279928308872462644267 33117419892463308693966401)
              ·
                refine ⟨24838064919347481520474801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33117419892463308693966401 24838064919347481520474801)
                ·
                  refine ⟨18628548689510611140356101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24838064919347481520474801 18628548689510611140356101)
                  ·
                    refine ⟨3492852879283239588816769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18628548689510611140356101 3492852879283239588816769)
                    ·
                      refine ⟨2619639659462429691612577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3492852879283239588816769 2619639659462429691612577)
                      ·
                        rfl

theorem cell23_5101730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_5101730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101730 prefixEnd_5101730 := by exact prefixLift 5101730
  have htrace : WordTrace (prefixWord ++ tailWord_5101730) baseStart_5101730 baseEnd_5101730 := by
    simpa [prefixWord, tailWord_5101730, baseEnd_5101730] using wordTrace_append hprefix tailTrace_5101730
  have hstable : (prefixWord ++ tailWord_5101730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101730).length < 2 ^ (prefixWord ++ tailWord_5101730).sum := by decide
  have hdescent : baseEnd_5101730 < baseStart_5101730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101753 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 6]
def baseStart_5101753 : Nat := 118140960795 + 5101753 * 2 ^ 59
def prefixEnd_5101753 : Nat := 4983230072969 + 3 ^ 40 * 5101753 * 2
def baseEnd_5101753 : Nat := 291072385501942566847219

theorem tailTrace_5101753 : CollatzResearch.WordTrace tailWord_5101753 prefixEnd_5101753 291072385501942566847219 := by
  unfold tailWord_5101753
  simp only [CollatzResearch.WordTrace]
  refine ⟨186076218686227665888973913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124050812457485110592649275 186076218686227665888973913)
  ·
    refine ⟨139557164014670749416730435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186076218686227665888973913 139557164014670749416730435)
    ·
      refine ⟨209335746022006124125095653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139557164014670749416730435 209335746022006124125095653)
      ·
        refine ⟨39250452379126148273455435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209335746022006124125095653 39250452379126148273455435)
        ·
          refine ⟨58875678568689222410183153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39250452379126148273455435 58875678568689222410183153)
          ·
            refine ⟨44156758926516916807637365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58875678568689222410183153 44156758926516916807637365)
            ·
              refine ⟨4139696149360960950716003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44156758926516916807637365 4139696149360960950716003)
              ·
                refine ⟨6209544224041441426074005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4139696149360960950716003 6209544224041441426074005)
                ·
                  refine ⟨291072385501942566847219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6209544224041441426074005 291072385501942566847219)
                  ·
                    rfl

theorem cell23_5101753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 6].length) (baseStart_5101753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101753 prefixEnd_5101753 := by exact prefixLift 5101753
  have htrace : WordTrace (prefixWord ++ tailWord_5101753) baseStart_5101753 baseEnd_5101753 := by
    simpa [prefixWord, tailWord_5101753, baseEnd_5101753] using wordTrace_append hprefix tailTrace_5101753
  have hstable : (prefixWord ++ tailWord_5101753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101753).length < 2 ^ (prefixWord ++ tailWord_5101753).sum := by decide
  have hdescent : baseEnd_5101753 < baseStart_5101753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101797 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 3, 1, 3]
def baseStart_5101797 : Nat := 118140960795 + 5101797 * 2 ^ 59
def prefixEnd_5101797 : Nat := 4983230072969 + 3 ^ 40 * 5101797 * 2
def baseEnd_5101797 : Nat := 2619674062666280929474769

theorem tailTrace_5101797 : CollatzResearch.WordTrace tailWord_5101797 prefixEnd_5101797 2619674062666280929474769 := by
  unfold tailWord_5101797
  simp only [CollatzResearch.WordTrace]
  refine ⟨186077823498068261403575645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124051882332045507602383763 186077823498068261403575645)
  ·
    refine ⟨69779183811775598026340867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186077823498068261403575645 69779183811775598026340867)
    ·
      refine ⟨104668775717663397039511301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69779183811775598026340867 104668775717663397039511301)
      ·
        refine ⟨19625395447061886944908369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104668775717663397039511301 19625395447061886944908369)
        ·
          refine ⟨14719046585296415208681277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19625395447061886944908369 14719046585296415208681277)
          ·
            refine ⟨5519642469486155703255479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14719046585296415208681277 5519642469486155703255479)
            ·
              refine ⟨8279463704229233554883219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519642469486155703255479 8279463704229233554883219)
              ·
                refine ⟨12419195556343850332324829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8279463704229233554883219 12419195556343850332324829)
                ·
                  refine ⟨4657198333628943874621811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12419195556343850332324829 4657198333628943874621811)
                  ·
                    refine ⟨6985797500443415811932717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4657198333628943874621811 6985797500443415811932717)
                    ·
                      refine ⟨2619674062666280929474769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6985797500443415811932717 2619674062666280929474769)
                      ·
                        rfl

theorem cell23_5101797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_5101797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101797 prefixEnd_5101797 := by exact prefixLift 5101797
  have htrace : WordTrace (prefixWord ++ tailWord_5101797) baseStart_5101797 baseEnd_5101797 := by
    simpa [prefixWord, tailWord_5101797, baseEnd_5101797] using wordTrace_append hprefix tailTrace_5101797
  have hstable : (prefixWord ++ tailWord_5101797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101797).length < 2 ^ (prefixWord ++ tailWord_5101797).sum := by decide
  have hdescent : baseEnd_5101797 < baseStart_5101797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101816 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_5101816 : Nat := 118140960795 + 5101816 * 2 ^ 59
def prefixEnd_5101816 : Nat := 4983230072969 + 3 ^ 40 * 5101816 * 2
def baseEnd_5101816 : Nat := 2619683818798716355137181

theorem tailTrace_5101816 : CollatzResearch.WordTrace tailWord_5101816 prefixEnd_5101816 2619683818798716355137181 := by
  unfold tailWord_5101816
  simp only [CollatzResearch.WordTrace]
  refine ⟨93039258242499713824258651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124052344323332951765678201 93039258242499713824258651)
  ·
    refine ⟨139558887363749570736387977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93039258242499713824258651 139558887363749570736387977)
    ·
      refine ⟨104669165522812178052290983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139558887363749570736387977 104669165522812178052290983)
      ·
        refine ⟨157003748284218267078436475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104669165522812178052290983 157003748284218267078436475)
        ·
          refine ⟨235505622426327400617654713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157003748284218267078436475 235505622426327400617654713)
          ·
            refine ⟨176629216819745550463241035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235505622426327400617654713 176629216819745550463241035)
            ·
              refine ⟨264943825229618325694861553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176629216819745550463241035 264943825229618325694861553)
              ·
                refine ⟨198707868922213744271146165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264943825229618325694861553 198707868922213744271146165)
                ·
                  refine ⟨18628862711457538525419953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198707868922213744271146165 18628862711457538525419953)
                  ·
                    refine ⟨13971647033593153894064965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18628862711457538525419953 13971647033593153894064965)
                    ·
                      refine ⟨2619683818798716355137181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13971647033593153894064965 2619683818798716355137181)
                      ·
                        rfl

theorem cell23_5101816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_5101816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101816 prefixEnd_5101816 := by exact prefixLift 5101816
  have htrace : WordTrace (prefixWord ++ tailWord_5101816) baseStart_5101816 baseEnd_5101816 := by
    simpa [prefixWord, tailWord_5101816, baseEnd_5101816] using wordTrace_append hprefix tailTrace_5101816
  have hstable : (prefixWord ++ tailWord_5101816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101816).length < 2 ^ (prefixWord ++ tailWord_5101816).sum := by decide
  have hdescent : baseEnd_5101816 < baseStart_5101816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101820 : List Nat := [2, 2, 2, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_5101820 : Nat := 118140960795 + 5101820 * 2 ^ 59
def prefixEnd_5101820 : Nat := 4983230072969 + 3 ^ 40 * 5101820 * 2
def baseEnd_5101820 : Nat := 2619685872721334339487163

theorem tailTrace_5101820 : CollatzResearch.WordTrace tailWord_5101820 prefixEnd_5101820 2619685872721334339487163 := by
  unfold tailWord_5101820
  simp only [CollatzResearch.WordTrace]
  refine ⟨93039331188492468165831457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124052441584656624221108609 93039331188492468165831457)
  ·
    refine ⟨69779498391369351124373593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93039331188492468165831457 69779498391369351124373593)
    ·
      refine ⟨52334623793527013343280195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69779498391369351124373593 52334623793527013343280195)
      ·
        refine ⟨78501935690290520014920293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52334623793527013343280195 78501935690290520014920293)
        ·
          refine ⟨14719112941929472502797555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78501935690290520014920293 14719112941929472502797555)
          ·
            refine ⟨22078669412894208754196333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14719112941929472502797555 22078669412894208754196333)
            ·
              refine ⟨8279501029835328282823625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22078669412894208754196333 8279501029835328282823625)
              ·
                refine ⟨6209625772376496212117719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8279501029835328282823625 6209625772376496212117719)
                ·
                  refine ⟨9314438658564744318176579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6209625772376496212117719 9314438658564744318176579)
                  ·
                    refine ⟨13971657987847116477264869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9314438658564744318176579 13971657987847116477264869)
                    ·
                      refine ⟨2619685872721334339487163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13971657987847116477264869 2619685872721334339487163)
                      ·
                        rfl

theorem cell23_5101820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_5101820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101820 prefixEnd_5101820 := by exact prefixLift 5101820
  have htrace : WordTrace (prefixWord ++ tailWord_5101820) baseStart_5101820 baseEnd_5101820 := by
    simpa [prefixWord, tailWord_5101820, baseEnd_5101820] using wordTrace_append hprefix tailTrace_5101820
  have hstable : (prefixWord ++ tailWord_5101820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101820).length < 2 ^ (prefixWord ++ tailWord_5101820).sum := by decide
  have hdescent : baseEnd_5101820 < baseStart_5101820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101823 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 3]
def baseStart_5101823 : Nat := 118140960795 + 5101823 * 2 ^ 59
def prefixEnd_5101823 : Nat := 4983230072969 + 3 ^ 40 * 5101823 * 2
def baseEnd_5101823 : Nat := 2619687413163297827749649

theorem tailTrace_5101823 : CollatzResearch.WordTrace tailWord_5101823 prefixEnd_5101823 2619687413163297827749649 := by
  unfold tailWord_5101823
  simp only [CollatzResearch.WordTrace]
  refine ⟨186078771795974067844022123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124052514530649378562681415 186078771795974067844022123)
  ·
    refine ⟨279118157693961101766033185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186078771795974067844022123 279118157693961101766033185)
    ·
      refine ⟨209338618270470826324524889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279118157693961101766033185 209338618270470826324524889)
      ·
        refine ⟨157003963702853119743393667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209338618270470826324524889 157003963702853119743393667)
        ·
          refine ⟨235505945554279679615090501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157003963702853119743393667 235505945554279679615090501)
          ·
            refine ⟨44157364791427439927829469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235505945554279679615090501 44157364791427439927829469)
            ·
              refine ⟨16559011796785289972936051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44157364791427439927829469 16559011796785289972936051)
              ·
                refine ⟨24838517695177934959404077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16559011796785289972936051 24838517695177934959404077)
                ·
                  refine ⟨9314444135691725609776529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24838517695177934959404077 9314444135691725609776529)
                  ·
                    refine ⟨6985833101768794207332397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9314444135691725609776529 6985833101768794207332397)
                    ·
                      refine ⟨2619687413163297827749649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6985833101768794207332397 2619687413163297827749649)
                      ·
                        rfl

theorem cell23_5101823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_5101823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101823 prefixEnd_5101823 := by exact prefixLift 5101823
  have htrace : WordTrace (prefixWord ++ tailWord_5101823) baseStart_5101823 baseEnd_5101823 := by
    simpa [prefixWord, tailWord_5101823, baseEnd_5101823] using wordTrace_append hprefix tailTrace_5101823
  have hstable : (prefixWord ++ tailWord_5101823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101823).length < 2 ^ (prefixWord ++ tailWord_5101823).sum := by decide
  have hdescent : baseEnd_5101823 < baseStart_5101823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101833 : List Nat := [1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 4]
def baseStart_5101833 : Nat := 118140960795 + 5101833 * 2 ^ 59
def prefixEnd_5101833 : Nat := 4983230072969 + 3 ^ 40 * 5101833 * 2
def baseEnd_5101833 : Nat := 2619692547969842788624603

theorem tailTrace_5101833 : CollatzResearch.WordTrace tailWord_5101833 prefixEnd_5101833 2619692547969842788624603 := by
  unfold tailWord_5101833
  simp only [CollatzResearch.WordTrace]
  refine ⟨186079136525937839551886153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124052757683958559701257435 186079136525937839551886153)
  ·
    refine ⟨139559352394453379663914615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186079136525937839551886153 139559352394453379663914615)
    ·
      refine ⟨209339028591680069495871923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139559352394453379663914615 209339028591680069495871923)
      ·
        refine ⟨314008542887520104243807885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209339028591680069495871923 314008542887520104243807885)
        ·
          refine ⟨117753203582820039091427957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314008542887520104243807885 117753203582820039091427957)
          ·
            refine ⟨11039362835889378664821371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117753203582820039091427957 11039362835889378664821371)
            ·
              refine ⟨16559044253834067997232057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11039362835889378664821371 16559044253834067997232057)
              ·
                refine ⟨12419283190375550997924043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16559044253834067997232057 12419283190375550997924043)
                ·
                  refine ⟨18628924785563326496886065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12419283190375550997924043 18628924785563326496886065)
                  ·
                    refine ⟨13971693589172494872664549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18628924785563326496886065 13971693589172494872664549)
                    ·
                      refine ⟨2619692547969842788624603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13971693589172494872664549 2619692547969842788624603)
                      ·
                        rfl

theorem cell23_5101833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_5101833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101833 prefixEnd_5101833 := by exact prefixLift 5101833
  have htrace : WordTrace (prefixWord ++ tailWord_5101833) baseStart_5101833 baseEnd_5101833 := by
    simpa [prefixWord, tailWord_5101833, baseEnd_5101833] using wordTrace_append hprefix tailTrace_5101833
  have hstable : (prefixWord ++ tailWord_5101833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101833).length < 2 ^ (prefixWord ++ tailWord_5101833).sum := by decide
  have hdescent : baseEnd_5101833 < baseStart_5101833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101880 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 3, 3, 2]
def baseStart_5101880 : Nat := 118140960795 + 5101880 * 2 ^ 59
def prefixEnd_5101880 : Nat := 4983230072969 + 3 ^ 40 * 5101880 * 2
def baseEnd_5101880 : Nat := 2619716681560604104736887

theorem tailTrace_5101880 : CollatzResearch.WordTrace tailWord_5101880 prefixEnd_5101880 2619716681560604104736887 := by
  unfold tailWord_5101880
  simp only [CollatzResearch.WordTrace]
  refine ⟨93040425378383783289423547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124053900504511711052564729 93040425378383783289423547)
  ·
    refine ⟨139560638067575674934135321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93040425378383783289423547 139560638067575674934135321)
    ·
      refine ⟨104670478550681756200601491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139560638067575674934135321 104670478550681756200601491)
      ·
        refine ⟨157005717826022634300902237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104670478550681756200601491 157005717826022634300902237)
        ·
          refine ⟨58877144184758487862838339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157005717826022634300902237 58877144184758487862838339)
          ·
            refine ⟨88315716277137731794257509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58877144184758487862838339 88315716277137731794257509)
            ·
              refine ⟨16559196801963324711423283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88315716277137731794257509 16559196801963324711423283)
              ·
                refine ⟨24838795202944987067134925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16559196801963324711423283 24838795202944987067134925)
                ·
                  refine ⟨9314548201104370150175597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24838795202944987067134925 9314548201104370150175597)
                  ·
                    refine ⟨3492955575414138806315849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9314548201104370150175597 3492955575414138806315849)
                    ·
                      refine ⟨2619716681560604104736887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3492955575414138806315849 2619716681560604104736887)
                      ·
                        rfl

theorem cell23_5101880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_5101880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101880 prefixEnd_5101880 := by exact prefixLift 5101880
  have htrace : WordTrace (prefixWord ++ tailWord_5101880) baseStart_5101880 baseEnd_5101880 := by
    simpa [prefixWord, tailWord_5101880, baseEnd_5101880] using wordTrace_append hprefix tailTrace_5101880
  have hstable : (prefixWord ++ tailWord_5101880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101880).length < 2 ^ (prefixWord ++ tailWord_5101880).sum := by decide
  have hdescent : baseEnd_5101880 < baseStart_5101880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101918 : List Nat := [4, 4, 2, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_5101918 : Nat := 118140960795 + 5101918 * 2 ^ 59
def prefixEnd_5101918 : Nat := 4983230072969 + 3 ^ 40 * 5101918 * 2
def baseEnd_5101918 : Nat := 2619736193825474956061713

theorem tailTrace_5101918 : CollatzResearch.WordTrace tailWord_5101918 prefixEnd_5101918 2619736193825474956061713 := by
  unfold tailWord_5101918
  simp only [CollatzResearch.WordTrace]
  refine ⟨23260279591328737383591301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124054824487086599379153605 23260279591328737383591301)
  ·
    refine ⟨4361302423374138259423369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23260279591328737383591301 4361302423374138259423369)
    ·
      refine ⟨3270976817530603694567527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4361302423374138259423369 3270976817530603694567527)
      ·
        refine ⟨4906465226295905541851291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270976817530603694567527 4906465226295905541851291)
        ·
          refine ⟨7359697839443858312776937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4906465226295905541851291 7359697839443858312776937)
          ·
            refine ⟨5519773379582893734582703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7359697839443858312776937 5519773379582893734582703)
            ·
              refine ⟨8279660069374340601874055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519773379582893734582703 8279660069374340601874055)
              ·
                refine ⟨12419490104061510902811083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8279660069374340601874055 12419490104061510902811083)
                ·
                  refine ⟨18629235156092266354216625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12419490104061510902811083 18629235156092266354216625)
                  ·
                    refine ⟨13971926367069199765662469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18629235156092266354216625 13971926367069199765662469)
                    ·
                      refine ⟨2619736193825474956061713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13971926367069199765662469 2619736193825474956061713)
                      ·
                        rfl

theorem cell23_5101918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_5101918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101918 prefixEnd_5101918 := by exact prefixLift 5101918
  have htrace : WordTrace (prefixWord ++ tailWord_5101918) baseStart_5101918 baseEnd_5101918 := by
    simpa [prefixWord, tailWord_5101918, baseEnd_5101918] using wordTrace_append hprefix tailTrace_5101918
  have hstable : (prefixWord ++ tailWord_5101918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101918).length < 2 ^ (prefixWord ++ tailWord_5101918).sum := by decide
  have hdescent : baseEnd_5101918 < baseStart_5101918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101923 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 4]
def baseStart_5101923 : Nat := 118140960795 + 5101923 * 2 ^ 59
def prefixEnd_5101923 : Nat := 4983230072969 + 3 ^ 40 * 5101923 * 2
def baseEnd_5101923 : Nat := 2619738761228747436499189

theorem tailTrace_5101923 : CollatzResearch.WordTrace tailWord_5101923 prefixEnd_5101923 2619738761228747436499189 := by
  unfold tailWord_5101923
  simp only [CollatzResearch.WordTrace]
  refine ⟨186082419095611784922662423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124054946063741189948441615 186082419095611784922662423)
  ·
    refine ⟨279123628643417677383993635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186082419095611784922662423 279123628643417677383993635)
    ·
      refine ⟨418685442965126516075990453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279123628643417677383993635 418685442965126516075990453)
      ·
        refine ⟨39251760277980610882124105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 418685442965126516075990453 39251760277980610882124105)
        ·
          refine ⟨29438820208485458161593079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39251760277980610882124105 29438820208485458161593079)
          ·
            refine ⟨44158230312728187242389619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29438820208485458161593079 44158230312728187242389619)
            ·
              refine ⟨66237345469092280863584429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44158230312728187242389619 66237345469092280863584429)
              ·
                refine ⟨24839004550909605323844161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66237345469092280863584429 24839004550909605323844161)
                ·
                  refine ⟨18629253413182203992883121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24839004550909605323844161 18629253413182203992883121)
                  ·
                    refine ⟨13971940059886652994662341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18629253413182203992883121 13971940059886652994662341)
                    ·
                      refine ⟨2619738761228747436499189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13971940059886652994662341 2619738761228747436499189)
                      ·
                        rfl

theorem cell23_5101923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_5101923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101923 prefixEnd_5101923 := by exact prefixLift 5101923
  have htrace : WordTrace (prefixWord ++ tailWord_5101923) baseStart_5101923 baseEnd_5101923 := by
    simpa [prefixWord, tailWord_5101923, baseEnd_5101923] using wordTrace_append hprefix tailTrace_5101923
  have hstable : (prefixWord ++ tailWord_5101923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101923).length < 2 ^ (prefixWord ++ tailWord_5101923).sum := by decide
  have hdescent : baseEnd_5101923 < baseStart_5101923 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101927 : List Nat := [1, 1, 5, 1, 3, 1, 3, 1, 1, 4, 2]
def baseStart_5101927 : Nat := 118140960795 + 5101927 * 2 ^ 59
def prefixEnd_5101927 : Nat := 4983230072969 + 3 ^ 40 * 5101927 * 2
def baseEnd_5101927 : Nat := 2619740815151365420849171

theorem tailTrace_5101927 : CollatzResearch.WordTrace tailWord_5101927 prefixEnd_5101927 2619740815151365420849171 := by
  unfold tailWord_5101927
  simp only [CollatzResearch.WordTrace]
  refine ⟨186082564987597293605808035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124055043325064862403872023 186082564987597293605808035)
  ·
    refine ⟨279123847481395940408712053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186082564987597293605808035 279123847481395940408712053)
    ·
      refine ⟨26167860701380869413316755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 279123847481395940408712053 26167860701380869413316755)
      ·
        refine ⟨39251791052071304119975133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26167860701380869413316755 39251791052071304119975133)
        ·
          refine ⟨14719421644526739044990675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39251791052071304119975133 14719421644526739044990675)
          ·
            refine ⟨22079132466790108567486013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14719421644526739044990675 22079132466790108567486013)
            ·
              refine ⟨8279674675046290712807255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22079132466790108567486013 8279674675046290712807255)
              ·
                refine ⟨12419512012569436069210883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8279674675046290712807255 12419512012569436069210883)
                ·
                  refine ⟨18629268018854154103816325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12419512012569436069210883 18629268018854154103816325)
                  ·
                    refine ⟨3492987753535153894465561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18629268018854154103816325 3492987753535153894465561)
                    ·
                      refine ⟨2619740815151365420849171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3492987753535153894465561 2619740815151365420849171)
                      ·
                        rfl

theorem cell23_5101927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_5101927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101927 prefixEnd_5101927 := by exact prefixLift 5101927
  have htrace : WordTrace (prefixWord ++ tailWord_5101927) baseStart_5101927 baseEnd_5101927 := by
    simpa [prefixWord, tailWord_5101927, baseEnd_5101927] using wordTrace_append hprefix tailTrace_5101927
  have hstable : (prefixWord ++ tailWord_5101927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101927).length < 2 ^ (prefixWord ++ tailWord_5101927).sum := by decide
  have hdescent : baseEnd_5101927 < baseStart_5101927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101933 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 7]
def baseStart_5101933 : Nat := 118140960795 + 5101933 * 2 ^ 59
def prefixEnd_5101933 : Nat := 4983230072969 + 3 ^ 40 * 5101933 * 2
def baseEnd_5101933 : Nat := 291082655115032488597127

theorem tailTrace_5101933 : CollatzResearch.WordTrace tailWord_5101933 prefixEnd_5101933 291082655115032488597127 := by
  unfold tailWord_5101933
  simp only [CollatzResearch.WordTrace]
  refine ⟨186082783825575556630526453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124055189217050371087017635 186082783825575556630526453)
  ·
    refine ⟨17445260983647708434111855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186082783825575556630526453 17445260983647708434111855)
    ·
      refine ⟨26167891475471562651167783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17445260983647708434111855 26167891475471562651167783)
      ·
        refine ⟨39251837213207343976751675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26167891475471562651167783 39251837213207343976751675)
        ·
          refine ⟨58877755819811015965127513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39251837213207343976751675 58877755819811015965127513)
          ·
            refine ⟨44158316864858261973845635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58877755819811015965127513 44158316864858261973845635)
            ·
              refine ⟨66237475297287392960768453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44158316864858261973845635 66237475297287392960768453)
              ·
                refine ⟨12419526618241386180144085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66237475297287392960768453 12419526618241386180144085)
                ·
                  refine ⟨291082655115032488597127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12419526618241386180144085 291082655115032488597127)
                  ·
                    rfl

theorem cell23_5101933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_5101933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101933 prefixEnd_5101933 := by exact prefixLift 5101933
  have htrace : WordTrace (prefixWord ++ tailWord_5101933) baseStart_5101933 baseEnd_5101933 := by
    simpa [prefixWord, tailWord_5101933, baseEnd_5101933] using wordTrace_append hprefix tailTrace_5101933
  have hstable : (prefixWord ++ tailWord_5101933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101933).length < 2 ^ (prefixWord ++ tailWord_5101933).sum := by decide
  have hdescent : baseEnd_5101933 < baseStart_5101933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101943 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 3]
def baseStart_5101943 : Nat := 118140960795 + 5101943 * 2 ^ 59
def prefixEnd_5101943 : Nat := 4983230072969 + 3 ^ 40 * 5101943 * 2
def baseEnd_5101943 : Nat := 2619749030841837358249097

theorem tailTrace_5101943 : CollatzResearch.WordTrace tailWord_5101943 prefixEnd_5101943 2619749030841837358249097 := by
  unfold tailWord_5101943
  simp only [CollatzResearch.WordTrace]
  refine ⟨186083148555539328338390483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124055432370359552225593655 186083148555539328338390483)
  ·
    refine ⟨279124722833308992507585725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186083148555539328338390483 279124722833308992507585725)
    ·
      refine ⟨104671771062490872190344647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279124722833308992507585725 104671771062490872190344647)
      ·
        refine ⟨157007656593736308285516971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104671771062490872190344647 157007656593736308285516971)
        ·
          refine ⟨235511484890604462428275457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157007656593736308285516971 235511484890604462428275457)
          ·
            refine ⟨176633613667953346821206593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235511484890604462428275457 176633613667953346821206593)
            ·
              refine ⟨132475210250965010115904945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176633613667953346821206593 132475210250965010115904945)
              ·
                refine ⟨99356407688223757586928709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132475210250965010115904945 99356407688223757586928709)
                ·
                  refine ⟨18629326441541954547549133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99356407688223757586928709 18629326441541954547549133)
                  ·
                    refine ⟨6985997415578232955330925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18629326441541954547549133 6985997415578232955330925)
                    ·
                      refine ⟨2619749030841837358249097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6985997415578232955330925 2619749030841837358249097)
                      ·
                        rfl

theorem cell23_5101943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_5101943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101943 prefixEnd_5101943 := by exact prefixLift 5101943
  have htrace : WordTrace (prefixWord ++ tailWord_5101943) baseStart_5101943 baseEnd_5101943 := by
    simpa [prefixWord, tailWord_5101943, baseEnd_5101943] using wordTrace_append hprefix tailTrace_5101943
  have hstable : (prefixWord ++ tailWord_5101943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101943).length < 2 ^ (prefixWord ++ tailWord_5101943).sum := by decide
  have hdescent : baseEnd_5101943 < baseStart_5101943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5101963 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 4, 5]
def baseStart_5101963 : Nat := 118140960795 + 5101963 * 2 ^ 59
def prefixEnd_5101963 : Nat := 4983230072969 + 3 ^ 40 * 5101963 * 2
def baseEnd_5101963 : Nat := 873253100151642426666335

theorem tailTrace_5101963 : CollatzResearch.WordTrace tailWord_5101963 prefixEnd_5101963 873253100151642426666335 := by
  unfold tailWord_5101963
  simp only [CollatzResearch.WordTrace]
  refine ⟨186083878015466871754118543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124055918676977914502745695 186083878015466871754118543)
  ·
    refine ⟨279125817023200307631177815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186083878015466871754118543 279125817023200307631177815)
    ·
      refine ⟨418688725534800461446766723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279125817023200307631177815 418688725534800461446766723)
      ·
        refine ⟨628033088302200692170150085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418688725534800461446766723 628033088302200692170150085)
        ·
          refine ⟨117756204056662629781903141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 628033088302200692170150085 117756204056662629781903141)
          ·
            refine ⟨22079288260624243084106839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117756204056662629781903141 22079288260624243084106839)
            ·
              refine ⟨33118932390936364626160259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22079288260624243084106839 33118932390936364626160259)
              ·
                refine ⟨49678398586404546939240389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33118932390936364626160259 49678398586404546939240389)
                ·
                  refine ⟨9314699734950852551107573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49678398586404546939240389 9314699734950852551107573)
                  ·
                    refine ⟨873253100151642426666335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9314699734950852551107573 873253100151642426666335)
                    ·
                      rfl

theorem cell23_5101963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 5].length) (baseStart_5101963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5101963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5101963 prefixEnd_5101963 := by exact prefixLift 5101963
  have htrace : WordTrace (prefixWord ++ tailWord_5101963) baseStart_5101963 baseEnd_5101963 := by
    simpa [prefixWord, tailWord_5101963, baseEnd_5101963] using wordTrace_append hprefix tailTrace_5101963
  have hstable : (prefixWord ++ tailWord_5101963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5101963).length < 2 ^ (prefixWord ++ tailWord_5101963).sum := by decide
  have hdescent : baseEnd_5101963 < baseStart_5101963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5101963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102061 : List Nat := [1, 5, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_5102061 : Nat := 118140960795 + 5102061 * 2 ^ 59
def prefixEnd_5102061 : Nat := 4983230072969 + 3 ^ 40 * 5102061 * 2
def baseEnd_5102061 : Nat := 873269873853022632191185

theorem tailTrace_5102061 : CollatzResearch.WordTrace tailWord_5102061 prefixEnd_5102061 873269873853022632191185 := by
  unfold tailWord_5102061
  simp only [CollatzResearch.WordTrace]
  refine ⟨186087452369111834491186037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124058301579407889660790691 186087452369111834491186037)
  ·
    refine ⟨17445698659604234483548691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186087452369111834491186037 17445698659604234483548691)
    ·
      refine ⟨26168547989406351725323037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17445698659604234483548691 26168547989406351725323037)
      ·
        refine ⟨9813205496027381896996139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26168547989406351725323037 9813205496027381896996139)
        ·
          refine ⟨14719808244041072845494209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9813205496027381896996139 14719808244041072845494209)
          ·
            refine ⟨11039856183030804634120657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14719808244041072845494209 11039856183030804634120657)
            ·
              refine ⟨8279892137273103475590493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11039856183030804634120657 8279892137273103475590493)
              ·
                refine ⟨3104959551477413803346435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8279892137273103475590493 3104959551477413803346435)
                ·
                  refine ⟨4657439327216120705019653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3104959551477413803346435 4657439327216120705019653)
                  ·
                    refine ⟨873269873853022632191185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4657439327216120705019653 873269873853022632191185)
                    ·
                      rfl

theorem cell23_5102061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_5102061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102061 prefixEnd_5102061 := by exact prefixLift 5102061
  have htrace : WordTrace (prefixWord ++ tailWord_5102061) baseStart_5102061 baseEnd_5102061 := by
    simpa [prefixWord, tailWord_5102061, baseEnd_5102061] using wordTrace_append hprefix tailTrace_5102061
  have hstable : (prefixWord ++ tailWord_5102061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102061).length < 2 ^ (prefixWord ++ tailWord_5102061).sum := by decide
  have hdescent : baseEnd_5102061 < baseStart_5102061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102063 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 5]
def baseStart_5102063 : Nat := 118140960795 + 5102063 * 2 ^ 59
def prefixEnd_5102063 : Nat := 4983230072969 + 3 ^ 40 * 5102063 * 2
def baseEnd_5102063 : Nat := 2619810648520376888748545

theorem tailTrace_5102063 : CollatzResearch.WordTrace tailWord_5102063 prefixEnd_5102063 2619810648520376888748545 := by
  unfold tailWord_5102063
  simp only [CollatzResearch.WordTrace]
  refine ⟨186087525315104588832758843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124058350210069725888505895 186087525315104588832758843)
  ·
    refine ⟨279131287972656883249138265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186087525315104588832758843 279131287972656883249138265)
    ·
      refine ⟨209348465979492662436853699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279131287972656883249138265 209348465979492662436853699)
      ·
        refine ⟨314022698969238993655280549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209348465979492662436853699 314022698969238993655280549)
        ·
          refine ⟨58879256056732311310365103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 314022698969238993655280549 58879256056732311310365103)
          ·
            refine ⟨88318884085098466965547655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58879256056732311310365103 88318884085098466965547655)
            ·
              refine ⟨132478326127647700448321483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88318884085098466965547655 132478326127647700448321483)
              ·
                refine ⟨198717489191471550672482225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132478326127647700448321483 198717489191471550672482225)
                ·
                  refine ⟨149038116893603663004361669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198717489191471550672482225 149038116893603663004361669)
                  ·
                    refine ⟨27944646917550686813317813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149038116893603663004361669 27944646917550686813317813)
                    ·
                      refine ⟨2619810648520376888748545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27944646917550686813317813 2619810648520376888748545)
                      ·
                        rfl

theorem cell23_5102063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_5102063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102063 prefixEnd_5102063 := by exact prefixLift 5102063
  have htrace : WordTrace (prefixWord ++ tailWord_5102063) baseStart_5102063 baseEnd_5102063 := by
    simpa [prefixWord, tailWord_5102063, baseEnd_5102063] using wordTrace_append hprefix tailTrace_5102063
  have hstable : (prefixWord ++ tailWord_5102063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102063).length < 2 ^ (prefixWord ++ tailWord_5102063).sum := by decide
  have hdescent : baseEnd_5102063 < baseStart_5102063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102077 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 4, 3, 2]
def baseStart_5102077 : Nat := 118140960795 + 5102077 * 2 ^ 59
def prefixEnd_5102077 : Nat := 4983230072969 + 3 ^ 40 * 5102077 * 2
def baseEnd_5102077 : Nat := 2619817837249539833973481

theorem tailTrace_5102077 : CollatzResearch.WordTrace tailWord_5102077 prefixEnd_5102077 2619817837249539833973481 := by
  unfold tailWord_5102077
  simp only [CollatzResearch.WordTrace]
  refine ⟨186088035937053869223768485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124058690624702579482512323 186088035937053869223768485)
  ·
    refine ⟨34891506738197600479456591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186088035937053869223768485 34891506738197600479456591)
    ·
      refine ⟨52337260107296400719184887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34891506738197600479456591 52337260107296400719184887)
      ·
        refine ⟨78505890160944601078777331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52337260107296400719184887 78505890160944601078777331)
        ·
          refine ⟨117758835241416901618165997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78505890160944601078777331 117758835241416901618165997)
          ·
            refine ⟨44159563215531338106812249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117758835241416901618165997 44159563215531338106812249)
            ·
              refine ⟨33119672411648503580109187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44159563215531338106812249 33119672411648503580109187)
              ·
                refine ⟨49679508617472755370163781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33119672411648503580109187 49679508617472755370163781)
                ·
                  refine ⟨9314907865776141631905709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49679508617472755370163781 9314907865776141631905709)
                  ·
                    refine ⟨3493090449666053111964641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9314907865776141631905709 3493090449666053111964641)
                    ·
                      refine ⟨2619817837249539833973481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493090449666053111964641 2619817837249539833973481)
                      ·
                        rfl

theorem cell23_5102077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_5102077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102077 prefixEnd_5102077 := by exact prefixLift 5102077
  have htrace : WordTrace (prefixWord ++ tailWord_5102077) baseStart_5102077 baseEnd_5102077 := by
    simpa [prefixWord, tailWord_5102077, baseEnd_5102077] using wordTrace_append hprefix tailTrace_5102077
  have hstable : (prefixWord ++ tailWord_5102077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102077).length < 2 ^ (prefixWord ++ tailWord_5102077).sum := by decide
  have hdescent : baseEnd_5102077 < baseStart_5102077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102084 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 3, 1, 3]
def baseStart_5102084 : Nat := 118140960795 + 5102084 * 2 ^ 59
def prefixEnd_5102084 : Nat := 4983230072969 + 3 ^ 40 * 5102084 * 2
def baseEnd_5102084 : Nat := 2619821431614121306585949

theorem tailTrace_5102084 : CollatzResearch.WordTrace tailWord_5102084 prefixEnd_5102084 2619821431614121306585949 := by
  unfold tailWord_5102084
  simp only [CollatzResearch.WordTrace]
  refine ⟨93044145624014254709636653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124058860832019006279515537 93044145624014254709636653)
  ·
    refine ⟨34891554609005345516113745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93044145624014254709636653 34891554609005345516113745)
    ·
      refine ⟨26168665956754009137085309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34891554609005345516113745 26168665956754009137085309)
      ·
        refine ⟨9813249733782753426406991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26168665956754009137085309 9813249733782753426406991)
        ·
          refine ⟨14719874600674130139610487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9813249733782753426406991 14719874600674130139610487)
          ·
            refine ⟨22079811901011195209415731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14719874600674130139610487 22079811901011195209415731)
            ·
              refine ⟨33119717851516792814123597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22079811901011195209415731 33119717851516792814123597)
              ·
                refine ⟨12419894194318797305296349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33119717851516792814123597 12419894194318797305296349)
                ·
                  refine ⟨4657460322869548989486131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12419894194318797305296349 4657460322869548989486131)
                  ·
                    refine ⟨6986190484304323484229197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4657460322869548989486131 6986190484304323484229197)
                    ·
                      refine ⟨2619821431614121306585949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6986190484304323484229197 2619821431614121306585949)
                      ·
                        rfl

theorem cell23_5102084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_5102084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102084 prefixEnd_5102084 := by exact prefixLift 5102084
  have htrace : WordTrace (prefixWord ++ tailWord_5102084) baseStart_5102084 baseEnd_5102084 := by
    simpa [prefixWord, tailWord_5102084, baseEnd_5102084] using wordTrace_append hprefix tailTrace_5102084
  have hstable : (prefixWord ++ tailWord_5102084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102084).length < 2 ^ (prefixWord ++ tailWord_5102084).sum := by decide
  have hdescent : baseEnd_5102084 < baseStart_5102084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102134 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_5102134 : Nat := 118140960795 + 5102134 * 2 ^ 59
def prefixEnd_5102134 : Nat := 4983230072969 + 3 ^ 40 * 5102134 * 2
def baseEnd_5102134 : Nat := 873282368548948703653573

theorem tailTrace_5102134 : CollatzResearch.WordTrace tailWord_5102134 prefixEnd_5102134 873282368548948703653573 := by
  unfold tailWord_5102134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11630632181115460497412091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124060076598564911972395637 11630632181115460497412091)
  ·
    refine ⟨17445948271673190746118137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11630632181115460497412091 17445948271673190746118137)
    ·
      refine ⟨13084461203754893059588603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17445948271673190746118137 13084461203754893059588603)
      ·
        refine ⟨19626691805632339589382905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13084461203754893059588603 19626691805632339589382905)
        ·
          refine ⟨14720018854224254692037179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19626691805632339589382905 14720018854224254692037179)
          ·
            refine ⟨22080028281336382038055769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14720018854224254692037179 22080028281336382038055769)
            ·
              refine ⟨16560021211002286528541827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22080028281336382038055769 16560021211002286528541827)
              ·
                refine ⟨24840031816503429792812741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16560021211002286528541827 24840031816503429792812741)
                ·
                  refine ⟨4657505965594393086152389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24840031816503429792812741 4657505965594393086152389)
                  ·
                    refine ⟨873282368548948703653573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4657505965594393086152389 873282368548948703653573)
                    ·
                      rfl

theorem cell23_5102134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_5102134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102134 prefixEnd_5102134 := by exact prefixLift 5102134
  have htrace : WordTrace (prefixWord ++ tailWord_5102134) baseStart_5102134 baseEnd_5102134 := by
    simpa [prefixWord, tailWord_5102134, baseEnd_5102134] using wordTrace_append hprefix tailTrace_5102134
  have hstable : (prefixWord ++ tailWord_5102134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102134).length < 2 ^ (prefixWord ++ tailWord_5102134).sum := by decide
  have hdescent : baseEnd_5102134 < baseStart_5102134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102141 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 3, 2, 2]
def baseStart_5102141 : Nat := 118140960795 + 5102141 * 2 ^ 59
def prefixEnd_5102141 : Nat := 4983230072969 + 3 ^ 40 * 5102141 * 2
def baseEnd_5102141 : Nat := 2619850700011427583573187

theorem tailTrace_5102141 : CollatzResearch.WordTrace tailWord_5102141 prefixEnd_5102141 2619850700011427583573187 := by
  unfold tailWord_5102141
  simp only [CollatzResearch.WordTrace]
  refine ⟨186090370208822008154098277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124060246805881338769398851 186090370208822008154098277)
  ·
    refine ⟨34891944414154126528893427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186090370208822008154098277 34891944414154126528893427)
    ·
      refine ⟨52337916621231189793340141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34891944414154126528893427 52337916621231189793340141)
      ·
        refine ⟨19626718732961696172502553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52337916621231189793340141 19626718732961696172502553)
        ·
          refine ⟨14720039049721272129376915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19626718732961696172502553 14720039049721272129376915)
          ·
            refine ⟨22080058574581908194065373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14720039049721272129376915 22080058574581908194065373)
            ·
              refine ⟨8280021965468215572774515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22080058574581908194065373 8280021965468215572774515)
              ·
                refine ⟨12420032948202323359161773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8280021965468215572774515 12420032948202323359161773)
                ·
                  refine ⟨4657512355575871259685665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12420032948202323359161773 4657512355575871259685665)
                  ·
                    refine ⟨3493134266681903444764249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4657512355575871259685665 3493134266681903444764249)
                    ·
                      refine ⟨2619850700011427583573187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493134266681903444764249 2619850700011427583573187)
                      ·
                        rfl

theorem cell23_5102141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_5102141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102141 prefixEnd_5102141 := by exact prefixLift 5102141
  have htrace : WordTrace (prefixWord ++ tailWord_5102141) baseStart_5102141 baseEnd_5102141 := by
    simpa [prefixWord, tailWord_5102141, baseEnd_5102141] using wordTrace_append hprefix tailTrace_5102141
  have hstable : (prefixWord ++ tailWord_5102141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102141).length < 2 ^ (prefixWord ++ tailWord_5102141).sum := by decide
  have hdescent : baseEnd_5102141 < baseStart_5102141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102151 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 2, 4]
def baseStart_5102151 : Nat := 118140960795 + 5102151 * 2 ^ 59
def prefixEnd_5102151 : Nat := 4983230072969 + 3 ^ 40 * 5102151 * 2
def baseEnd_5102151 : Nat := 873285278272657514816047

theorem tailTrace_5102151 : CollatzResearch.WordTrace tailWord_5102151 prefixEnd_5102151 873285278272657514816047 := by
  unfold tailWord_5102151
  simp only [CollatzResearch.WordTrace]
  refine ⟨186090734938785779861962307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124060489959190519907974871 186090734938785779861962307)
  ·
    refine ⟨279136102408178669792943461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186090734938785779861962307 279136102408178669792943461)
    ·
      refine ⟨52338019201533500586176899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279136102408178669792943461 52338019201533500586176899)
      ·
        refine ⟨78507028802300250879265349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52338019201533500586176899 78507028802300250879265349)
        ·
          refine ⟨14720067900431297039862253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78507028802300250879265349 14720067900431297039862253)
          ·
            refine ⟨5520025462661736389948345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14720067900431297039862253 5520025462661736389948345)
            ·
              refine ⟨4140019096996302292461259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5520025462661736389948345 4140019096996302292461259)
              ·
                refine ⟨6210028645494453438691889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140019096996302292461259 6210028645494453438691889)
                ·
                  refine ⟨4657521484120840079018917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6210028645494453438691889 4657521484120840079018917)
                  ·
                    refine ⟨873285278272657514816047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4657521484120840079018917 873285278272657514816047)
                    ·
                      rfl

theorem cell23_5102151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 2, 4].length) (baseStart_5102151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102151 prefixEnd_5102151 := by exact prefixLift 5102151
  have htrace : WordTrace (prefixWord ++ tailWord_5102151) baseStart_5102151 baseEnd_5102151 := by
    simpa [prefixWord, tailWord_5102151, baseEnd_5102151] using wordTrace_append hprefix tailTrace_5102151
  have hstable : (prefixWord ++ tailWord_5102151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102151).length < 2 ^ (prefixWord ++ tailWord_5102151).sum := by decide
  have hdescent : baseEnd_5102151 < baseStart_5102151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102178 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5102178 : Nat := 118140960795 + 5102178 * 2 ^ 59
def prefixEnd_5102178 : Nat := 4983230072969 + 3 ^ 40 * 5102178 * 2
def baseEnd_5102178 : Nat := 2619869698795643938810517

theorem tailTrace_5102178 : CollatzResearch.WordTrace tailWord_5102178 prefixEnd_5102178 2619869698795643938810517 := by
  unfold tailWord_5102178
  simp only [CollatzResearch.WordTrace]
  refine ⟨46522929927421990868298797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124061146473125308982130125 46522929927421990868298797)
  ·
    refine ⟨17446098722783246575612049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46522929927421990868298797 17446098722783246575612049)
    ·
      refine ⟨13084574042087434931709037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17446098722783246575612049 13084574042087434931709037)
      ·
        refine ⟨4906715265782788099390889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13084574042087434931709037 4906715265782788099390889)
        ·
          refine ⟨3680036449337091074543167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4906715265782788099390889 3680036449337091074543167)
          ·
            refine ⟨5520054674005636611814751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3680036449337091074543167 5520054674005636611814751)
            ·
              refine ⟨8280082011008454917722127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520054674005636611814751 8280082011008454917722127)
              ·
                refine ⟨12420123016512682376583191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8280082011008454917722127 12420123016512682376583191)
                ·
                  refine ⟨18630184524769023564874787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12420123016512682376583191 18630184524769023564874787)
                  ·
                    refine ⟨27945276787153535347312181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18630184524769023564874787 27945276787153535347312181)
                    ·
                      refine ⟨2619869698795643938810517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27945276787153535347312181 2619869698795643938810517)
                      ·
                        rfl

theorem cell23_5102178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5102178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102178 prefixEnd_5102178 := by exact prefixLift 5102178
  have htrace : WordTrace (prefixWord ++ tailWord_5102178) baseStart_5102178 baseEnd_5102178 := by
    simpa [prefixWord, tailWord_5102178, baseEnd_5102178] using wordTrace_append hprefix tailTrace_5102178
  have hstable : (prefixWord ++ tailWord_5102178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102178).length < 2 ^ (prefixWord ++ tailWord_5102178).sum := by decide
  have hdescent : baseEnd_5102178 < baseStart_5102178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102192 : List Nat := [2, 1, 1, 1, 8, 1, 2, 2, 1, 2, 2]
def baseStart_5102192 : Nat := 118140960795 + 5102192 * 2 ^ 59
def prefixEnd_5102192 : Nat := 4983230072969 + 3 ^ 40 * 5102192 * 2
def baseEnd_5102192 : Nat := 2619876887524806884035453

theorem tailTrace_5102192 : CollatzResearch.WordTrace tailWord_5102192 prefixEnd_5102192 2619876887524806884035453 := by
  unfold tailWord_5102192
  simp only [CollatzResearch.WordTrace]
  refine ⟨93046115165818621932102415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124061486887758162576136553 93046115165818621932102415)
  ·
    refine ⟨139569172748727932898153623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93046115165818621932102415 139569172748727932898153623)
    ·
      refine ⟨209353759123091899347230435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139569172748727932898153623 209353759123091899347230435)
      ·
        refine ⟨314030638684637849020845653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209353759123091899347230435 314030638684637849020845653)
        ·
          refine ⟨3680046547085599793213035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 314030638684637849020845653 3680046547085599793213035)
          ·
            refine ⟨5520069820628399689819553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3680046547085599793213035 5520069820628399689819553)
            ·
              refine ⟨4140052365471299767364665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5520069820628399689819553 4140052365471299767364665)
              ·
                refine ⟨3105039274103474825523499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4140052365471299767364665 3105039274103474825523499)
                ·
                  refine ⟨4657558911155212238285249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105039274103474825523499 4657558911155212238285249)
                  ·
                    refine ⟨3493169183366409178713937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4657558911155212238285249 3493169183366409178713937)
                    ·
                      refine ⟨2619876887524806884035453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493169183366409178713937 2619876887524806884035453)
                      ·
                        rfl

theorem cell23_5102192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 2, 1, 2, 2].length) (baseStart_5102192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102192 prefixEnd_5102192 := by exact prefixLift 5102192
  have htrace : WordTrace (prefixWord ++ tailWord_5102192) baseStart_5102192 baseEnd_5102192 := by
    simpa [prefixWord, tailWord_5102192, baseEnd_5102192] using wordTrace_append hprefix tailTrace_5102192
  have hstable : (prefixWord ++ tailWord_5102192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102192).length < 2 ^ (prefixWord ++ tailWord_5102192).sum := by decide
  have hdescent : baseEnd_5102192 < baseStart_5102192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102254 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_5102254 : Nat := 118140960795 + 5102254 * 2 ^ 59
def prefixEnd_5102254 : Nat := 4983230072969 + 3 ^ 40 * 5102254 * 2
def baseEnd_5102254 : Nat := 291100969258376182384463

theorem tailTrace_5102254 : CollatzResearch.WordTrace tailWord_5102254 prefixEnd_5102254 291100969258376182384463 := by
  unfold tailWord_5102254
  simp only [CollatzResearch.WordTrace]
  refine ⟨23261811457176578556620227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124062994438275085635307877 23261811457176578556620227)
  ·
    refine ⟨34892717185764867834930341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23261811457176578556620227 34892717185764867834930341)
    ·
      refine ⟨6542384472330912719049439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34892717185764867834930341 6542384472330912719049439)
      ·
        refine ⟨9813576708496369078574159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6542384472330912719049439 9813576708496369078574159)
        ·
          refine ⟨14720365062744553617861239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9813576708496369078574159 14720365062744553617861239)
          ·
            refine ⟨22080547594116830426791859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14720365062744553617861239 22080547594116830426791859)
            ·
              refine ⟨33120821391175245640187789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22080547594116830426791859 33120821391175245640187789)
              ·
                refine ⟨12420308021690717115070421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33120821391175245640187789 12420308021690717115070421)
                ·
                  refine ⟨291100969258376182384463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12420308021690717115070421 291100969258376182384463)
                  ·
                    rfl

theorem cell23_5102254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_5102254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102254 prefixEnd_5102254 := by exact prefixLift 5102254
  have htrace : WordTrace (prefixWord ++ tailWord_5102254) baseStart_5102254 baseEnd_5102254 := by
    simpa [prefixWord, tailWord_5102254, baseEnd_5102254] using wordTrace_append hprefix tailTrace_5102254
  have hstable : (prefixWord ++ tailWord_5102254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102254).length < 2 ^ (prefixWord ++ tailWord_5102254).sum := by decide
  have hdescent : baseEnd_5102254 < baseStart_5102254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102365 : List Nat := [1, 4, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_5102365 : Nat := 118140960795 + 5102365 * 2 ^ 59
def prefixEnd_5102365 : Nat := 4983230072969 + 3 ^ 40 * 5102365 * 2
def baseEnd_5102365 : Nat := 873321906559344902390719

theorem tailTrace_5102365 : CollatzResearch.WordTrace tailWord_5102365 prefixEnd_5102365 873321906559344902390719 := by
  unfold tailWord_5102365
  simp only [CollatzResearch.WordTrace]
  refine ⟨186098540160010494410252549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124065693440006996273501699 186098540160010494410252549)
  ·
    refine ⟨34893476280001967701922353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186098540160010494410252549 34893476280001967701922353)
    ·
      refine ⟨26170107210001475776441765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34893476280001967701922353 26170107210001475776441765)
      ·
        refine ⟨4906895101875276708082831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26170107210001475776441765 4906895101875276708082831)
        ·
          refine ⟨7360342652812915062124247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4906895101875276708082831 7360342652812915062124247)
          ·
            refine ⟨11040513979219372593186371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7360342652812915062124247 11040513979219372593186371)
            ·
              refine ⟨16560770968829058889779557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11040513979219372593186371 16560770968829058889779557)
              ·
                refine ⟨3105144556655448541833667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16560770968829058889779557 3105144556655448541833667)
                ·
                  refine ⟨4657716834983172812750501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105144556655448541833667 4657716834983172812750501)
                  ·
                    refine ⟨873321906559344902390719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4657716834983172812750501 873321906559344902390719)
                    ·
                      rfl

theorem cell23_5102365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_5102365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102365 prefixEnd_5102365 := by exact prefixLift 5102365
  have htrace : WordTrace (prefixWord ++ tailWord_5102365) baseStart_5102365 baseEnd_5102365 := by
    simpa [prefixWord, tailWord_5102365, baseEnd_5102365] using wordTrace_append hprefix tailTrace_5102365
  have hstable : (prefixWord ++ tailWord_5102365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102365).length < 2 ^ (prefixWord ++ tailWord_5102365).sum := by decide
  have hdescent : baseEnd_5102365 < baseStart_5102365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102398 : List Nat := [4, 2, 1, 2, 3, 1, 1, 1, 1, 5, 2]
def baseStart_5102398 : Nat := 118140960795 + 5102398 * 2 ^ 59
def prefixEnd_5102398 : Nat := 4983230072969 + 3 ^ 40 * 5102398 * 2
def baseEnd_5102398 : Nat := 2619982664539633078059505

theorem tailTrace_5102398 : CollatzResearch.WordTrace tailWord_5102398 prefixEnd_5102398 2619982664539633078059505 := by
  unfold tailWord_5102398
  simp only [CollatzResearch.WordTrace]
  refine ⟨23262467971111367630775481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124066495845927294030802565 23262467971111367630775481)
  ·
    refine ⟨17446850978333525723081611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23262467971111367630775481 17446850978333525723081611)
    ·
      refine ⟨26170276467500288584622417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17446850978333525723081611 26170276467500288584622417)
      ·
        refine ⟨19627707350625216438466813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26170276467500288584622417 19627707350625216438466813)
        ·
          refine ⟨7360390256484456164425055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19627707350625216438466813 7360390256484456164425055)
          ·
            refine ⟨11040585384726684246637583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7360390256484456164425055 11040585384726684246637583)
            ·
              refine ⟨16560878077090026369956375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11040585384726684246637583 16560878077090026369956375)
              ·
                refine ⟨24841317115635039554934563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16560878077090026369956375 24841317115635039554934563)
                ·
                  refine ⟨37261975673452559332401845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24841317115635039554934563 37261975673452559332401845)
                  ·
                    refine ⟨3493310219386177437412673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37261975673452559332401845 3493310219386177437412673)
                    ·
                      refine ⟨2619982664539633078059505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493310219386177437412673 2619982664539633078059505)
                      ·
                        rfl

theorem cell23_5102398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_5102398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102398 prefixEnd_5102398 := by exact prefixLift 5102398
  have htrace : WordTrace (prefixWord ++ tailWord_5102398) baseStart_5102398 baseEnd_5102398 := by
    simpa [prefixWord, tailWord_5102398, baseEnd_5102398] using wordTrace_append hprefix tailTrace_5102398
  have hstable : (prefixWord ++ tailWord_5102398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102398).length < 2 ^ (prefixWord ++ tailWord_5102398).sum := by decide
  have hdescent : baseEnd_5102398 < baseStart_5102398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102407 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 6]
def baseStart_5102407 : Nat := 118140960795 + 5102407 * 2 ^ 59
def prefixEnd_5102407 : Nat := 4983230072969 + 3 ^ 40 * 5102407 * 2
def baseEnd_5102407 : Nat := 2619987285865523542846963

theorem tailTrace_5102407 : CollatzResearch.WordTrace tailWord_5102407 prefixEnd_5102407 2619987285865523542846963 := by
  unfold tailWord_5102407
  simp only [CollatzResearch.WordTrace]
  refine ⟨186100072025858335583281475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124066714683905557055520983 186100072025858335583281475)
  ·
    refine ⟨279150108038787503374922213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186100072025858335583281475 279150108038787503374922213)
    ·
      refine ⟨52340645257272656882797915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279150108038787503374922213 52340645257272656882797915)
      ·
        refine ⟨78510967885908985324196873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52340645257272656882797915 78510967885908985324196873)
        ·
          refine ⟨58883225914431738993147655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78510967885908985324196873 58883225914431738993147655)
          ·
            refine ⟨88324838871647608489721483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58883225914431738993147655 88324838871647608489721483)
            ·
              refine ⟨132487258307471412734582225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88324838871647608489721483 132487258307471412734582225)
              ·
                refine ⟨99365443730603559550936669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132487258307471412734582225 99365443730603559550936669)
                ·
                  refine ⟨37262041398976334831601251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99365443730603559550936669 37262041398976334831601251)
                  ·
                    refine ⟨55893062098464502247401877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37262041398976334831601251 55893062098464502247401877)
                    ·
                      refine ⟨2619987285865523542846963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55893062098464502247401877 2619987285865523542846963)
                      ·
                        rfl

theorem cell23_5102407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_5102407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102407 prefixEnd_5102407 := by exact prefixLift 5102407
  have htrace : WordTrace (prefixWord ++ tailWord_5102407) baseStart_5102407 baseEnd_5102407 := by
    simpa [prefixWord, tailWord_5102407, baseEnd_5102407] using wordTrace_append hprefix tailTrace_5102407
  have hstable : (prefixWord ++ tailWord_5102407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102407).length < 2 ^ (prefixWord ++ tailWord_5102407).sum := by decide
  have hdescent : baseEnd_5102407 < baseStart_5102407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102447 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 2, 7]
def baseStart_5102447 : Nat := 118140960795 + 5102447 * 2 ^ 59
def prefixEnd_5102447 : Nat := 4983230072969 + 3 ^ 40 * 5102447 * 2
def baseEnd_5102447 : Nat := 873335941697234462115593

theorem tailTrace_5102447 : CollatzResearch.WordTrace tailWord_5102447 prefixEnd_5102447 873335941697234462115593 := by
  unfold tailWord_5102447
  simp only [CollatzResearch.WordTrace]
  refine ⟨186101530945713422414737595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124067687297142281609825063 186101530945713422414737595)
  ·
    refine ⟨279152296418570133622106393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186101530945713422414737595 279152296418570133622106393)
    ·
      refine ⟨209364222313927600216579795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279152296418570133622106393 209364222313927600216579795)
      ·
        refine ⟨314046333470891400324869693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209364222313927600216579795 314046333470891400324869693)
        ·
          refine ⟨117767375051584275121826135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314046333470891400324869693 117767375051584275121826135)
          ·
            refine ⟨176651062577376412682739203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117767375051584275121826135 176651062577376412682739203)
            ·
              refine ⟨264976593866064619024108805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176651062577376412682739203 264976593866064619024108805)
              ·
                refine ⟨49683111349887116067020401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264976593866064619024108805 49683111349887116067020401)
                ·
                  refine ⟨37262333512415337050265301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49683111349887116067020401 37262333512415337050265301)
                  ·
                    refine ⟨873335941697234462115593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37262333512415337050265301 873335941697234462115593)
                    ·
                      rfl

theorem cell23_5102447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 7].length) (baseStart_5102447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102447 prefixEnd_5102447 := by exact prefixLift 5102447
  have htrace : WordTrace (prefixWord ++ tailWord_5102447) baseStart_5102447 baseEnd_5102447 := by
    simpa [prefixWord, tailWord_5102447, baseEnd_5102447] using wordTrace_append hprefix tailTrace_5102447
  have hstable : (prefixWord ++ tailWord_5102447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102447).length < 2 ^ (prefixWord ++ tailWord_5102447).sum := by decide
  have hdescent : baseEnd_5102447 < baseStart_5102447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102461 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_5102461 : Nat := 118140960795 + 5102461 * 2 ^ 59
def prefixEnd_5102461 : Nat := 4983230072969 + 3 ^ 40 * 5102461 * 2
def baseEnd_5102461 : Nat := 2620015013820866331571715

theorem tailTrace_5102461 : CollatzResearch.WordTrace tailWord_5102461 prefixEnd_5102461 2620015013820866331571715 := by
  unfold tailWord_5102461
  simp only [CollatzResearch.WordTrace]
  refine ⟨186102041567662702805747237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124068027711775135203831491 186102041567662702805747237)
  ·
    refine ⟨34894132793936756776077607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186102041567662702805747237 34894132793936756776077607)
    ·
      refine ⟨52341199190905135164116411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34894132793936756776077607 52341199190905135164116411)
      ·
        refine ⟨78511798786357702746174617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52341199190905135164116411 78511798786357702746174617)
        ·
          refine ⟨58883849089768277059630963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78511798786357702746174617 58883849089768277059630963)
          ·
            refine ⟨88325773634652415589446445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58883849089768277059630963 88325773634652415589446445)
            ·
              refine ⟨33122165112994655846042417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88325773634652415589446445 33122165112994655846042417)
              ·
                refine ⟨24841623834745991884531813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33122165112994655846042417 24841623834745991884531813)
                ·
                  refine ⟨4657804469014873478349715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24841623834745991884531813 4657804469014873478349715)
                  ·
                    refine ⟨6986706703522310217524573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4657804469014873478349715 6986706703522310217524573)
                    ·
                      refine ⟨2620015013820866331571715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6986706703522310217524573 2620015013820866331571715)
                      ·
                        rfl

theorem cell23_5102461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_5102461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102461 prefixEnd_5102461 := by exact prefixLift 5102461
  have htrace : WordTrace (prefixWord ++ tailWord_5102461) baseStart_5102461 baseEnd_5102461 := by
    simpa [prefixWord, tailWord_5102461, baseEnd_5102461] using wordTrace_append hprefix tailTrace_5102461
  have hstable : (prefixWord ++ tailWord_5102461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102461).length < 2 ^ (prefixWord ++ tailWord_5102461).sum := by decide
  have hdescent : baseEnd_5102461 < baseStart_5102461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102495 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 2, 1, 3]
def baseStart_5102495 : Nat := 118140960795 + 5102495 * 2 ^ 59
def prefixEnd_5102495 : Nat := 4983230072969 + 3 ^ 40 * 5102495 * 2
def baseEnd_5102495 : Nat := 2620032472163119198546559

theorem tailTrace_5102495 : CollatzResearch.WordTrace tailWord_5102495 prefixEnd_5102495 2620032472163119198546559 := by
  unfold tailWord_5102495
  simp only [CollatzResearch.WordTrace]
  refine ⟨186103281649539526612484939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124068854433026351074989959 186103281649539526612484939)
  ·
    refine ⟨279154922474309289918727409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186103281649539526612484939 279154922474309289918727409)
    ·
      refine ⟨209366191855731967439045557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279154922474309289918727409 209366191855731967439045557)
      ·
        refine ⟨19628080486474871947410521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 209366191855731967439045557 19628080486474871947410521)
        ·
          refine ⟨14721060364856153960557891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19628080486474871947410521 14721060364856153960557891)
          ·
            refine ⟨22081590547284230940836837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14721060364856153960557891 22081590547284230940836837)
            ·
              refine ⟨4140298227615793301406907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22081590547284230940836837 4140298227615793301406907)
              ·
                refine ⟨6210447341423689952110361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140298227615793301406907 6210447341423689952110361)
                ·
                  refine ⟨4657835506067767464082771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6210447341423689952110361 4657835506067767464082771)
                  ·
                    refine ⟨6986753259101651196124157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4657835506067767464082771 6986753259101651196124157)
                    ·
                      refine ⟨2620032472163119198546559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6986753259101651196124157 2620032472163119198546559)
                      ·
                        rfl

theorem cell23_5102495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_5102495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102495 prefixEnd_5102495 := by exact prefixLift 5102495
  have htrace : WordTrace (prefixWord ++ tailWord_5102495) baseStart_5102495 baseEnd_5102495 := by
    simpa [prefixWord, tailWord_5102495, baseEnd_5102495] using wordTrace_append hprefix tailTrace_5102495
  have hstable : (prefixWord ++ tailWord_5102495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102495).length < 2 ^ (prefixWord ++ tailWord_5102495).sum := by decide
  have hdescent : baseEnd_5102495 < baseStart_5102495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102514 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4]
def baseStart_5102514 : Nat := 118140960795 + 5102514 * 2 ^ 59
def prefixEnd_5102514 : Nat := 4983230072969 + 3 ^ 40 * 5102514 * 2
def baseEnd_5102514 : Nat := 2620042228295554624208971

theorem tailTrace_5102514 : CollatzResearch.WordTrace tailWord_5102514 prefixEnd_5102514 2620042228295554624208971 := by
  unfold tailWord_5102514
  simp only [CollatzResearch.WordTrace]
  refine ⟨46525993659117673214356649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124069316424313795238284397 46525993659117673214356649)
  ·
    refine ⟨34894495244338254910767487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46525993659117673214356649 34894495244338254910767487)
    ·
      refine ⟨52341742866507382366151231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34894495244338254910767487 52341742866507382366151231)
      ·
        refine ⟨78512614299761073549226847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52341742866507382366151231 78512614299761073549226847)
        ·
          refine ⟨117768921449641610323840271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78512614299761073549226847 117768921449641610323840271)
          ·
            refine ⟨176653382174462415485760407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117768921449641610323840271 176653382174462415485760407)
            ·
              refine ⟨264980073261693623228640611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176653382174462415485760407 264980073261693623228640611)
              ·
                refine ⟨397470109892540434842960917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264980073261693623228640611 397470109892540434842960917)
                ·
                  refine ⟨18631411401212832883263793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 397470109892540434842960917 18631411401212832883263793)
                  ·
                    refine ⟨13973558550909624662447845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18631411401212832883263793 13973558550909624662447845)
                    ·
                      refine ⟨2620042228295554624208971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13973558550909624662447845 2620042228295554624208971)
                      ·
                        rfl

theorem cell23_5102514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_5102514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102514 prefixEnd_5102514 := by exact prefixLift 5102514
  have htrace : WordTrace (prefixWord ++ tailWord_5102514) baseStart_5102514 baseEnd_5102514 := by
    simpa [prefixWord, tailWord_5102514, baseEnd_5102514] using wordTrace_append hprefix tailTrace_5102514
  have hstable : (prefixWord ++ tailWord_5102514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102514).length < 2 ^ (prefixWord ++ tailWord_5102514).sum := by decide
  have hdescent : baseEnd_5102514 < baseStart_5102514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102561 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 4, 5, 2]
def baseStart_5102561 : Nat := 118140960795 + 5102561 * 2 ^ 59
def prefixEnd_5102561 : Nat := 4983230072969 + 3 ^ 40 * 5102561 * 2
def baseEnd_5102561 : Nat := 2620066361886315940321255

theorem tailTrace_5102561 : CollatzResearch.WordTrace tailWord_5102561 prefixEnd_5102561 2620066361886315940321255 := by
  unfold tailWord_5102561
  simp only [CollatzResearch.WordTrace]
  refine ⟨186105688867300419884387537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124070459244866946589591691 186105688867300419884387537)
  ·
    refine ⟨139579266650475314913290653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186105688867300419884387537 139579266650475314913290653)
    ·
      refine ⟨52342224993928243092483995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139579266650475314913290653 52342224993928243092483995)
      ·
        refine ⟨78513337490892364638725993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52342224993928243092483995 78513337490892364638725993)
        ·
          refine ⟨58885003118169273479044495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78513337490892364638725993 58885003118169273479044495)
          ·
            refine ⟨88327504677253910218566743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58885003118169273479044495 88327504677253910218566743)
            ·
              refine ⟨132491257015880865327850115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88327504677253910218566743 132491257015880865327850115)
              ·
                refine ⟨198736885523821297991775173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132491257015880865327850115 198736885523821297991775173)
                ·
                  refine ⟨37263166035716493373457845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198736885523821297991775173 37263166035716493373457845)
                  ·
                    refine ⟨3493421815848421253761673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37263166035716493373457845 3493421815848421253761673)
                    ·
                      refine ⟨2620066361886315940321255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493421815848421253761673 2620066361886315940321255)
                      ·
                        rfl

theorem cell23_5102561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_5102561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102561 prefixEnd_5102561 := by exact prefixLift 5102561
  have htrace : WordTrace (prefixWord ++ tailWord_5102561) baseStart_5102561 baseEnd_5102561 := by
    simpa [prefixWord, tailWord_5102561, baseEnd_5102561] using wordTrace_append hprefix tailTrace_5102561
  have hstable : (prefixWord ++ tailWord_5102561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102561).length < 2 ^ (prefixWord ++ tailWord_5102561).sum := by decide
  have hdescent : baseEnd_5102561 < baseStart_5102561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102564 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_5102564 : Nat := 118140960795 + 5102564 * 2 ^ 59
def prefixEnd_5102564 : Nat := 4983230072969 + 3 ^ 40 * 5102564 * 2
def baseEnd_5102564 : Nat := 2620067902328279428583741

theorem tailTrace_5102564 : CollatzResearch.WordTrace tailWord_5102564 prefixEnd_5102564 2620067902328279428583741 := by
  unfold tailWord_5102564
  simp only [CollatzResearch.WordTrace]
  refine ⟨93052899143144775698373373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124070532190859700931164497 93052899143144775698373373)
  ·
    refine ⟨34894837178679290886890015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93052899143144775698373373 34894837178679290886890015)
    ·
      refine ⟨52342255768018936330335023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34894837178679290886890015 52342255768018936330335023)
      ·
        refine ⟨78513383652028404495502535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52342255768018936330335023 78513383652028404495502535)
        ·
          refine ⟨117770075478042606743253803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78513383652028404495502535 117770075478042606743253803)
          ·
            refine ⟨176655113217063910114880705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117770075478042606743253803 176655113217063910114880705)
            ·
              refine ⟨132491334912797932586160529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176655113217063910114880705 132491334912797932586160529)
              ·
                refine ⟨99368501184598449439620397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132491334912797932586160529 99368501184598449439620397)
                ·
                  refine ⟨37263187944224418539857649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99368501184598449439620397 37263187944224418539857649)
                  ·
                    refine ⟨27947390958168313904893237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37263187944224418539857649 27947390958168313904893237)
                    ·
                      refine ⟨2620067902328279428583741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27947390958168313904893237 2620067902328279428583741)
                      ·
                        rfl

theorem cell23_5102564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_5102564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102564 prefixEnd_5102564 := by exact prefixLift 5102564
  have htrace : WordTrace (prefixWord ++ tailWord_5102564) baseStart_5102564 baseEnd_5102564 := by
    simpa [prefixWord, tailWord_5102564, baseEnd_5102564] using wordTrace_append hprefix tailTrace_5102564
  have hstable : (prefixWord ++ tailWord_5102564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102564).length < 2 ^ (prefixWord ++ tailWord_5102564).sum := by decide
  have hdescent : baseEnd_5102564 < baseStart_5102564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102628 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_5102628 : Nat := 118140960795 + 5102628 * 2 ^ 59
def prefixEnd_5102628 : Nat := 4983230072969 + 3 ^ 40 * 5102628 * 2
def baseEnd_5102628 : Nat := 2620100765090167178183447

theorem tailTrace_5102628 : CollatzResearch.WordTrace tailWord_5102628 prefixEnd_5102628 2620100765090167178183447 := by
  unfold tailWord_5102628
  simp only [CollatzResearch.WordTrace]
  refine ⟨93054066279028845163538269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124072088372038460218051025 93054066279028845163538269)
  ·
    refine ⟨34895274854635816936326851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93054066279028845163538269 34895274854635816936326851)
    ·
      refine ⟨52342912281953725404490277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34895274854635816936326851 52342912281953725404490277)
      ·
        refine ⟨9814296052866323513341927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52342912281953725404490277 9814296052866323513341927)
        ·
          refine ⟨14721444079299485270012891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9814296052866323513341927 14721444079299485270012891)
          ·
            refine ⟨22082166118949227905019337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14721444079299485270012891 22082166118949227905019337)
            ·
              refine ⟨16561624589211920928764503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22082166118949227905019337 16561624589211920928764503)
              ·
                refine ⟨24842436883817881393146755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16561624589211920928764503 24842436883817881393146755)
                ·
                  refine ⟨37263655325726822089720133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24842436883817881393146755 37263655325726822089720133)
                  ·
                    refine ⟨6986935373573779141822525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37263655325726822089720133 6986935373573779141822525)
                    ·
                      refine ⟨2620100765090167178183447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6986935373573779141822525 2620100765090167178183447)
                      ·
                        rfl

theorem cell23_5102628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_5102628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102628 prefixEnd_5102628 := by exact prefixLift 5102628
  have htrace : WordTrace (prefixWord ++ tailWord_5102628) baseStart_5102628 baseEnd_5102628 := by
    simpa [prefixWord, tailWord_5102628, baseEnd_5102628] using wordTrace_append hprefix tailTrace_5102628
  have hstable : (prefixWord ++ tailWord_5102628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102628).length < 2 ^ (prefixWord ++ tailWord_5102628).sum := by decide
  have hdescent : baseEnd_5102628 < baseStart_5102628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102652 : List Nat := [2, 2, 2, 2, 2, 3, 3, 2, 1, 4]
def baseStart_5102652 : Nat := 118140960795 + 5102652 * 2 ^ 59
def prefixEnd_5102652 : Nat := 4983230072969 + 3 ^ 40 * 5102652 * 2
def baseEnd_5102652 : Nat := 873371029541958361427779

theorem tailTrace_5102652 : CollatzResearch.WordTrace tailWord_5102652 prefixEnd_5102652 873371029541958361427779 := by
  unfold tailWord_5102652
  simp only [CollatzResearch.WordTrace]
  refine ⟨93054503954985371212975105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124072671939980494950633473 93054503954985371212975105)
  ·
    refine ⟨69790877966239028409731329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93054503954985371212975105 69790877966239028409731329)
    ·
      refine ⟨52343158474679271307298497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69790877966239028409731329 52343158474679271307298497)
      ·
        refine ⟨39257368856009453480473873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52343158474679271307298497 39257368856009453480473873)
        ·
          refine ⟨29443026642007090110355405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39257368856009453480473873 29443026642007090110355405)
          ·
            refine ⟨11041134990752658791383277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29443026642007090110355405 11041134990752658791383277)
            ·
              refine ⟨4140425621532247046768729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11041134990752658791383277 4140425621532247046768729)
              ·
                refine ⟨3105319216149185285076547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4140425621532247046768729 3105319216149185285076547)
                ·
                  refine ⟨4657978824223777927614821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105319216149185285076547 4657978824223777927614821)
                  ·
                    refine ⟨873371029541958361427779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4657978824223777927614821 873371029541958361427779)
                    ·
                      rfl

theorem cell23_5102652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 1, 4].length) (baseStart_5102652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102652 prefixEnd_5102652 := by exact prefixLift 5102652
  have htrace : WordTrace (prefixWord ++ tailWord_5102652) baseStart_5102652 baseEnd_5102652 := by
    simpa [prefixWord, tailWord_5102652, baseEnd_5102652] using wordTrace_append hprefix tailTrace_5102652
  have hstable : (prefixWord ++ tailWord_5102652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102652).length < 2 ^ (prefixWord ++ tailWord_5102652).sum := by decide
  have hdescent : baseEnd_5102652 < baseStart_5102652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102668 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 6, 3, 2]
def baseStart_5102668 : Nat := 118140960795 + 5102668 * 2 ^ 59
def prefixEnd_5102668 : Nat := 4983230072969 + 3 ^ 40 * 5102668 * 2
def baseEnd_5102668 : Nat := 2620121304316347021683263

theorem tailTrace_5102668 : CollatzResearch.WordTrace tailWord_5102668 prefixEnd_5102668 2620121304316347021683263 := by
  unfold tailWord_5102668
  simp only [CollatzResearch.WordTrace]
  refine ⟨93054795738956388579266329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124073060985275184772355105 93054795738956388579266329)
  ·
    refine ⟨69791096804217291434449747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93054795738956388579266329 69791096804217291434449747)
    ·
      refine ⟨104686645206325937151674621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69791096804217291434449747 104686645206325937151674621)
      ·
        refine ⟨39257491952372226431877983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104686645206325937151674621 39257491952372226431877983)
        ·
          refine ⟨58886237928558339647816975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39257491952372226431877983 58886237928558339647816975)
          ·
            refine ⟨88329356892837509471725463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58886237928558339647816975 88329356892837509471725463)
            ·
              refine ⟨132494035339256264207588195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88329356892837509471725463 132494035339256264207588195)
              ·
                refine ⟨198741053008884396311382293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132494035339256264207588195 198741053008884396311382293)
                ·
                  refine ⟨9315986859791456077096045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 198741053008884396311382293 9315986859791456077096045)
                  ·
                    refine ⟨3493495072421796028911017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9315986859791456077096045 3493495072421796028911017)
                    ·
                      refine ⟨2620121304316347021683263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493495072421796028911017 2620121304316347021683263)
                      ·
                        rfl

theorem cell23_5102668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_5102668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102668 prefixEnd_5102668 := by exact prefixLift 5102668
  have htrace : WordTrace (prefixWord ++ tailWord_5102668) baseStart_5102668 baseEnd_5102668 := by
    simpa [prefixWord, tailWord_5102668, baseEnd_5102668] using wordTrace_append hprefix tailTrace_5102668
  have hstable : (prefixWord ++ tailWord_5102668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102668).length < 2 ^ (prefixWord ++ tailWord_5102668).sum := by decide
  have hdescent : baseEnd_5102668 < baseStart_5102668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102695 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 1, 5]
def baseStart_5102695 : Nat := 118140960795 + 5102695 * 2 ^ 59
def prefixEnd_5102695 : Nat := 4983230072969 + 3 ^ 40 * 5102695 * 2
def baseEnd_5102695 : Nat := 873378389431339472015213

theorem tailTrace_5102695 : CollatzResearch.WordTrace tailWord_5102695 prefixEnd_5102695 873378389431339472015213 := by
  unfold tailWord_5102695
  simp only [CollatzResearch.WordTrace]
  refine ⟨186110576248814960769765539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124073717499209973846510359 186110576248814960769765539)
  ·
    refine ⟨279165864373222441154648309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186110576248814960769765539 279165864373222441154648309)
    ·
      refine ⟨26171799784989603858248279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 279165864373222441154648309 26171799784989603858248279)
      ·
        refine ⟨39257699677484405787372419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26171799784989603858248279 39257699677484405787372419)
        ·
          refine ⟨58886549516226608681058629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39257699677484405787372419 58886549516226608681058629)
          ·
            refine ⟨11041228034292489127698493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58886549516226608681058629 11041228034292489127698493)
            ·
              refine ⟨4140460512859683422886935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11041228034292489127698493 4140460512859683422886935)
              ·
                refine ⟨6210690769289525134330403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140460512859683422886935 6210690769289525134330403)
                ·
                  refine ⟨9316036153934287701495605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6210690769289525134330403 9316036153934287701495605)
                  ·
                    refine ⟨873378389431339472015213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9316036153934287701495605 873378389431339472015213)
                    ·
                      rfl

theorem cell23_5102695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_5102695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102695 prefixEnd_5102695 := by exact prefixLift 5102695
  have htrace : WordTrace (prefixWord ++ tailWord_5102695) baseStart_5102695 baseEnd_5102695 := by
    simpa [prefixWord, tailWord_5102695, baseEnd_5102695] using wordTrace_append hprefix tailTrace_5102695
  have hstable : (prefixWord ++ tailWord_5102695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102695).length < 2 ^ (prefixWord ++ tailWord_5102695).sum := by decide
  have hdescent : baseEnd_5102695 < baseStart_5102695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102711 : List Nat := [1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 4]
def baseStart_5102711 : Nat := 118140960795 + 5102711 * 2 ^ 59
def prefixEnd_5102711 : Nat := 4983230072969 + 3 ^ 40 * 5102711 * 2
def baseEnd_5102711 : Nat := 2620143383984490353445565

theorem tailTrace_5102711 : CollatzResearch.WordTrace tailWord_5102711 prefixEnd_5102711 2620143383984490353445565 := by
  unfold tailWord_5102711
  simp only [CollatzResearch.WordTrace]
  refine ⟨186111159816756995502347987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124074106544504663668231991 186111159816756995502347987)
  ·
    refine ⟨279166739725135493253521981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186111159816756995502347987 279166739725135493253521981)
    ·
      refine ⟨104687527396925809970070743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279166739725135493253521981 104687527396925809970070743)
      ·
        refine ⟨157031291095388714955106115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104687527396925809970070743 157031291095388714955106115)
        ·
          refine ⟨235546936643083072432659173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157031291095388714955106115 235546936643083072432659173)
          ·
            refine ⟨44165050620578076081123595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235546936643083072432659173 44165050620578076081123595)
            ·
              refine ⟨66247575930867114121685393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44165050620578076081123595 66247575930867114121685393)
              ·
                refine ⟨49685681948150335591264045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66247575930867114121685393 49685681948150335591264045)
                ·
                  refine ⟨18632130730556375846724017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49685681948150335591264045 18632130730556375846724017)
                  ·
                    refine ⟨13974098047917281885043013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18632130730556375846724017 13974098047917281885043013)
                    ·
                      refine ⟨2620143383984490353445565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13974098047917281885043013 2620143383984490353445565)
                      ·
                        rfl

theorem cell23_5102711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_5102711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102711 prefixEnd_5102711 := by exact prefixLift 5102711
  have htrace : WordTrace (prefixWord ++ tailWord_5102711) baseStart_5102711 baseEnd_5102711 := by
    simpa [prefixWord, tailWord_5102711, baseEnd_5102711] using wordTrace_append hprefix tailTrace_5102711
  have hstable : (prefixWord ++ tailWord_5102711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102711).length < 2 ^ (prefixWord ++ tailWord_5102711).sum := by decide
  have hdescent : baseEnd_5102711 < baseStart_5102711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102749 : List Nat := [1, 4, 2, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_5102749 : Nat := 118140960795 + 5102749 * 2 ^ 59
def prefixEnd_5102749 : Nat := 4983230072969 + 3 ^ 40 * 5102749 * 2
def baseEnd_5102749 : Nat := 2620162896249361204770391

theorem tailTrace_5102749 : CollatzResearch.WordTrace tailWord_5102749 prefixEnd_5102749 2620162896249361204770391 := by
  unfold tailWord_5102749
  simp only [CollatzResearch.WordTrace]
  refine ⟨186112545790619327992231301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124075030527079551994820867 186112545790619327992231301)
  ·
    refine ⟨34896102335741123998543369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186112545790619327992231301 34896102335741123998543369)
    ·
      refine ⟨26172076751805842998907527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34896102335741123998543369 26172076751805842998907527)
      ·
        refine ⟨39258115127708764498361291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26172076751805842998907527 39258115127708764498361291)
        ·
          refine ⟨58887172691563146747541937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39258115127708764498361291 58887172691563146747541937)
          ·
            refine ⟨44165379518672360060656453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58887172691563146747541937 44165379518672360060656453)
            ·
              refine ⟨8281008659751067511373085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44165379518672360060656453 8281008659751067511373085)
              ·
                refine ⟨3105378247406650316764907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8281008659751067511373085 3105378247406650316764907)
                ·
                  refine ⟨4658067371109975475147361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105378247406650316764907 4658067371109975475147361)
                  ·
                    refine ⟨3493550528332481606360521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4658067371109975475147361 3493550528332481606360521)
                    ·
                      refine ⟨2620162896249361204770391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493550528332481606360521 2620162896249361204770391)
                      ·
                        rfl

theorem cell23_5102749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_5102749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102749 prefixEnd_5102749 := by exact prefixLift 5102749
  have htrace : WordTrace (prefixWord ++ tailWord_5102749) baseStart_5102749 baseEnd_5102749 := by
    simpa [prefixWord, tailWord_5102749, baseEnd_5102749] using wordTrace_append hprefix tailTrace_5102749
  have hstable : (prefixWord ++ tailWord_5102749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102749).length < 2 ^ (prefixWord ++ tailWord_5102749).sum := by decide
  have hdescent : baseEnd_5102749 < baseStart_5102749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102771 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 4]
def baseStart_5102771 : Nat := 118140960795 + 5102771 * 2 ^ 59
def prefixEnd_5102771 : Nat := 4983230072969 + 3 ^ 40 * 5102771 * 2
def baseEnd_5102771 : Nat := 2620174192823760118695289

theorem tailTrace_5102771 : CollatzResearch.WordTrace tailWord_5102771 prefixEnd_5102771 2620174192823760118695289 := by
  unfold tailWord_5102771
  simp only [CollatzResearch.WordTrace]
  refine ⟨186113348196539625749532167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124075565464359750499688111 186113348196539625749532167)
  ·
    refine ⟨279170022294809438624298251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186113348196539625749532167 279170022294809438624298251)
    ·
      refine ⟨418755033442214157936447377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279170022294809438624298251 418755033442214157936447377)
      ·
        refine ⟨314066275081660618452335533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418755033442214157936447377 314066275081660618452335533)
        ·
          refine ⟨117774853155622731919625825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314066275081660618452335533 117774853155622731919625825)
          ·
            refine ⟨88331139866717048939719369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117774853155622731919625825 88331139866717048939719369)
            ·
              refine ⟨66248354900037786704789527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88331139866717048939719369 66248354900037786704789527)
              ·
                refine ⟨99372532350056680057184291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66248354900037786704789527 99372532350056680057184291)
                ·
                  refine ⟨149058798525085020085776437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99372532350056680057184291 149058798525085020085776437)
                  ·
                    refine ⟨13974262361726720633041541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149058798525085020085776437 13974262361726720633041541)
                    ·
                      refine ⟨2620174192823760118695289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13974262361726720633041541 2620174192823760118695289)
                      ·
                        rfl

theorem cell23_5102771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_5102771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102771 prefixEnd_5102771 := by exact prefixLift 5102771
  have htrace : WordTrace (prefixWord ++ tailWord_5102771) baseStart_5102771 baseEnd_5102771 := by
    simpa [prefixWord, tailWord_5102771, baseEnd_5102771] using wordTrace_append hprefix tailTrace_5102771
  have hstable : (prefixWord ++ tailWord_5102771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102771).length < 2 ^ (prefixWord ++ tailWord_5102771).sum := by decide
  have hdescent : baseEnd_5102771 < baseStart_5102771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102782 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_5102782 : Nat := 118140960795 + 5102782 * 2 ^ 59
def prefixEnd_5102782 : Nat := 4983230072969 + 3 ^ 40 * 5102782 * 2
def baseEnd_5102782 : Nat := 2620179841110959575657739

theorem tailTrace_5102782 : CollatzResearch.WordTrace tailWord_5102782 prefixEnd_5102782 2620179841110959575657739 := by
  unfold tailWord_5102782
  simp only [CollatzResearch.WordTrace]
  refine ⟨23264218674937471828522825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124075832932999849752121733 23264218674937471828522825)
  ·
    refine ⟨17448164006203103871392119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23264218674937471828522825 17448164006203103871392119)
    ·
      refine ⟨26172246009304655807088179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17448164006203103871392119 26172246009304655807088179)
      ·
        refine ⟨39258369013956983710632269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26172246009304655807088179 39258369013956983710632269)
        ·
          refine ⟨14721888380233868891487101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39258369013956983710632269 14721888380233868891487101)
          ·
            refine ⟨5520708142587700834307663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14721888380233868891487101 5520708142587700834307663)
            ·
              refine ⟨8281062213881551251461495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520708142587700834307663 8281062213881551251461495)
              ·
                refine ⟨12421593320822326877192243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8281062213881551251461495 12421593320822326877192243)
                ·
                  refine ⟨18632389981233490315788365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12421593320822326877192243 18632389981233490315788365)
                  ·
                    refine ⟨6987146242962558868420637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18632389981233490315788365 6987146242962558868420637)
                    ·
                      refine ⟨2620179841110959575657739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6987146242962558868420637 2620179841110959575657739)
                      ·
                        rfl

theorem cell23_5102782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_5102782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102782 prefixEnd_5102782 := by exact prefixLift 5102782
  have htrace : WordTrace (prefixWord ++ tailWord_5102782) baseStart_5102782 baseEnd_5102782 := by
    simpa [prefixWord, tailWord_5102782, baseEnd_5102782] using wordTrace_append hprefix tailTrace_5102782
  have hstable : (prefixWord ++ tailWord_5102782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102782).length < 2 ^ (prefixWord ++ tailWord_5102782).sum := by decide
  have hdescent : baseEnd_5102782 < baseStart_5102782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102786 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_5102786 : Nat := 118140960795 + 5102786 * 2 ^ 59
def prefixEnd_5102786 : Nat := 4983230072969 + 3 ^ 40 * 5102786 * 2
def baseEnd_5102786 : Nat := 2620181895033577560007721

theorem tailTrace_5102786 : CollatzResearch.WordTrace tailWord_5102786 prefixEnd_5102786 2620181895033577560007721 := by
  unfold tailWord_5102786
  simp only [CollatzResearch.WordTrace]
  refine ⟨46528473822871320827832053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124075930194323522207552141 46528473822871320827832053)
  ·
    refine ⟨4362044420894186327609255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46528473822871320827832053 4362044420894186327609255)
    ·
      refine ⟨6543066631341279491413883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4362044420894186327609255 6543066631341279491413883)
      ·
        refine ⟨9814599947011919237120825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6543066631341279491413883 9814599947011919237120825)
        ·
          refine ⟨7360949960258939427840619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9814599947011919237120825 7360949960258939427840619)
          ·
            refine ⟨11041424940388409141760929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7360949960258939427840619 11041424940388409141760929)
            ·
              refine ⟨8281068705291306856320697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11041424940388409141760929 8281068705291306856320697)
              ·
                refine ⟨6210801528968480142240523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8281068705291306856320697 6210801528968480142240523)
                ·
                  refine ⟨9316202293452720213360785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6210801528968480142240523 9316202293452720213360785)
                  ·
                    refine ⟨6987151720089540160020589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9316202293452720213360785 6987151720089540160020589)
                    ·
                      refine ⟨2620181895033577560007721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6987151720089540160020589 2620181895033577560007721)
                      ·
                        rfl

theorem cell23_5102786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_5102786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102786 prefixEnd_5102786 := by exact prefixLift 5102786
  have htrace : WordTrace (prefixWord ++ tailWord_5102786) baseStart_5102786 baseEnd_5102786 := by
    simpa [prefixWord, tailWord_5102786, baseEnd_5102786] using wordTrace_append hprefix tailTrace_5102786
  have hstable : (prefixWord ++ tailWord_5102786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102786).length < 2 ^ (prefixWord ++ tailWord_5102786).sum := by decide
  have hdescent : baseEnd_5102786 < baseStart_5102786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102791 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_5102791 : Nat := 118140960795 + 5102791 * 2 ^ 59
def prefixEnd_5102791 : Nat := 4983230072969 + 3 ^ 40 * 5102791 * 2
def baseEnd_5102791 : Nat := 2620184462436850040445197

theorem tailTrace_5102791 : CollatzResearch.WordTrace tailWord_5102791 prefixEnd_5102791 2620184462436850040445197 := by
  unfold tailWord_5102791
  simp only [CollatzResearch.WordTrace]
  refine ⟨186114077656467169165260227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124076051770978112776840151 186114077656467169165260227)
  ·
    refine ⟨279171116484700753747890341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186114077656467169165260227 279171116484700753747890341)
    ·
      refine ⟨52344584340881391327729439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279171116484700753747890341 52344584340881391327729439)
      ·
        refine ⟨78516876511322086991594159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52344584340881391327729439 78516876511322086991594159)
        ·
          refine ⟨117775314766983130487391239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78516876511322086991594159 117775314766983130487391239)
          ·
            refine ⟨176662972150474695731086859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117775314766983130487391239 176662972150474695731086859)
            ·
              refine ⟨264994458225712043596630289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176662972150474695731086859 264994458225712043596630289)
              ·
                refine ⟨198745843669284032697472717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264994458225712043596630289 198745843669284032697472717)
                ·
                  refine ⟨74529691375981512261552269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198745843669284032697472717 74529691375981512261552269)
                  ·
                    refine ⟨27948634265993067098082101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74529691375981512261552269 27948634265993067098082101)
                    ·
                      refine ⟨2620184462436850040445197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27948634265993067098082101 2620184462436850040445197)
                      ·
                        rfl

theorem cell23_5102791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_5102791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102791 prefixEnd_5102791 := by exact prefixLift 5102791
  have htrace : WordTrace (prefixWord ++ tailWord_5102791) baseStart_5102791 baseEnd_5102791 := by
    simpa [prefixWord, tailWord_5102791, baseEnd_5102791] using wordTrace_append hprefix tailTrace_5102791
  have hstable : (prefixWord ++ tailWord_5102791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102791).length < 2 ^ (prefixWord ++ tailWord_5102791).sum := by decide
  have hdescent : baseEnd_5102791 < baseStart_5102791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102828 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 7]
def baseStart_5102828 : Nat := 118140960795 + 5102828 * 2 ^ 59
def prefixEnd_5102828 : Nat := 4983230072969 + 3 ^ 40 * 5102828 * 2
def baseEnd_5102828 : Nat := 291133717913451821742503

theorem tailTrace_5102828 : CollatzResearch.WordTrace tailWord_5102828 prefixEnd_5102828 291133717913451821742503 := by
  unfold tailWord_5102828
  simp only [CollatzResearch.WordTrace]
  refine ⟨93057713578666562242178569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124076951438222082989571425 93057713578666562242178569)
  ·
    refine ⟨69793285183999921681633927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93057713578666562242178569 69793285183999921681633927)
    ·
      refine ⟨104689927775999882522450891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69793285183999921681633927 104689927775999882522450891)
      ·
        refine ⟨157034891663999823783676337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104689927775999882522450891 157034891663999823783676337)
        ·
          refine ⟨117776168747999867837757253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157034891663999823783676337 117776168747999867837757253)
          ·
            refine ⟨22083031640249975219579485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117776168747999867837757253 22083031640249975219579485)
            ·
              refine ⟨8281136865093740707342307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22083031640249975219579485 8281136865093740707342307)
              ·
                refine ⟨12421705297640611061013461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8281136865093740707342307 12421705297640611061013461)
                ·
                  refine ⟨291133717913451821742503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12421705297640611061013461 291133717913451821742503)
                  ·
                    rfl

theorem cell23_5102828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 7].length) (baseStart_5102828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102828 prefixEnd_5102828 := by exact prefixLift 5102828
  have htrace : WordTrace (prefixWord ++ tailWord_5102828) baseStart_5102828 baseEnd_5102828 := by
    simpa [prefixWord, tailWord_5102828, baseEnd_5102828] using wordTrace_append hprefix tailTrace_5102828
  have hstable : (prefixWord ++ tailWord_5102828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102828).length < 2 ^ (prefixWord ++ tailWord_5102828).sum := by decide
  have hdescent : baseEnd_5102828 < baseStart_5102828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102879 : List Nat := [1, 1, 2, 4, 4, 2, 2, 2, 5]
def baseStart_5102879 : Nat := 118140960795 + 5102879 * 2 ^ 59
def prefixEnd_5102879 : Nat := 4983230072969 + 3 ^ 40 * 5102879 * 2
def baseEnd_5102879 : Nat := 291136627637160632904977

theorem tailTrace_5102879 : CollatzResearch.WordTrace tailWord_5102879 prefixEnd_5102879 291136627637160632904977 := by
  unfold tailWord_5102879
  simp only [CollatzResearch.WordTrace]
  refine ⟨186117287280148360194463691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124078191520098906796309127 186117287280148360194463691)
  ·
    refine ⟨279175930920222540291695537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186117287280148360194463691 279175930920222540291695537)
    ·
      refine ⟨209381948190166905218771653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279175930920222540291695537 209381948190166905218771653)
      ·
        refine ⟨39259115285656294728519685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209381948190166905218771653 39259115285656294728519685)
        ·
          refine ⟨7361084116060555261597441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39259115285656294728519685 7361084116060555261597441)
          ·
            refine ⟨5520813087045416446198081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7361084116060555261597441 5520813087045416446198081)
            ·
              refine ⟨4140609815284062334648561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5520813087045416446198081 4140609815284062334648561)
              ·
                refine ⟨3105457361463046750986421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4140609815284062334648561 3105457361463046750986421)
                ·
                  refine ⟨291136627637160632904977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3105457361463046750986421 291136627637160632904977)
                  ·
                    rfl

theorem cell23_5102879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 5].length) (baseStart_5102879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102879 prefixEnd_5102879 := by exact prefixLift 5102879
  have htrace : WordTrace (prefixWord ++ tailWord_5102879) baseStart_5102879 baseEnd_5102879 := by
    simpa [prefixWord, tailWord_5102879, baseEnd_5102879] using wordTrace_append hprefix tailTrace_5102879
  have hstable : (prefixWord ++ tailWord_5102879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102879).length < 2 ^ (prefixWord ++ tailWord_5102879).sum := by decide
  have hdescent : baseEnd_5102879 < baseStart_5102879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102909 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_5102909 : Nat := 118140960795 + 5102909 * 2 ^ 59
def prefixEnd_5102909 : Nat := 4983230072969 + 3 ^ 40 * 5102909 * 2
def baseEnd_5102909 : Nat := 873415017718026859589885

theorem tailTrace_5102909 : CollatzResearch.WordTrace tailWord_5102909 prefixEnd_5102909 873415017718026859589885 := by
  unfold tailWord_5102909
  simp only [CollatzResearch.WordTrace]
  refine ⟨186118381470039675318055781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124078920980026450212037187 186118381470039675318055781)
  ·
    refine ⟨34897196525632439122135459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186118381470039675318055781 34897196525632439122135459)
    ·
      refine ⟨52345794788448658683203189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34897196525632439122135459 52345794788448658683203189)
      ·
        refine ⟨4907418261417061751550299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52345794788448658683203189 4907418261417061751550299)
        ·
          refine ⟨7361127392125592627325449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907418261417061751550299 7361127392125592627325449)
          ·
            refine ⟨5520845544094194470494087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7361127392125592627325449 5520845544094194470494087)
            ·
              refine ⟨8281268316141291705741131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520845544094194470494087 8281268316141291705741131)
              ·
                refine ⟨12421902474211937558611697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8281268316141291705741131 12421902474211937558611697)
                ·
                  refine ⟨9316426855658953168958773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12421902474211937558611697 9316426855658953168958773)
                  ·
                    refine ⟨873415017718026859589885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9316426855658953168958773 873415017718026859589885)
                    ·
                      rfl

theorem cell23_5102909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_5102909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102909 prefixEnd_5102909 := by exact prefixLift 5102909
  have htrace : WordTrace (prefixWord ++ tailWord_5102909) baseStart_5102909 baseEnd_5102909 := by
    simpa [prefixWord, tailWord_5102909, baseEnd_5102909] using wordTrace_append hprefix tailTrace_5102909
  have hstable : (prefixWord ++ tailWord_5102909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102909).length < 2 ^ (prefixWord ++ tailWord_5102909).sum := by decide
  have hdescent : baseEnd_5102909 < baseStart_5102909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102935 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 6]
def baseStart_5102935 : Nat := 118140960795 + 5102935 * 2 ^ 59
def prefixEnd_5102935 : Nat := 4983230072969 + 3 ^ 40 * 5102935 * 2
def baseEnd_5102935 : Nat := 291139822627899719671615

theorem tailTrace_5102935 : CollatzResearch.WordTrace tailWord_5102935 prefixEnd_5102935 291139822627899719671615 := by
  unfold tailWord_5102935
  simp only [CollatzResearch.WordTrace]
  refine ⟨186119329767945481758502259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124079553178630321172334839 186119329767945481758502259)
  ·
    refine ⟨279178994651918222637753389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186119329767945481758502259 279178994651918222637753389)
    ·
      refine ⟨104692122994469333489157521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279178994651918222637753389 104692122994469333489157521)
      ·
        refine ⟨78519092245852000116868141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104692122994469333489157521 78519092245852000116868141)
        ·
          refine ⟨29444659592194500043825553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78519092245852000116868141 29444659592194500043825553)
          ·
            refine ⟨22083494694145875032869165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29444659592194500043825553 22083494694145875032869165)
            ·
              refine ⟨8281310510304703137325937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22083494694145875032869165 8281310510304703137325937)
              ·
                refine ⟨6210982882728527352994453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8281310510304703137325937 6210982882728527352994453)
                ·
                  refine ⟨291139822627899719671615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6210982882728527352994453 291139822627899719671615)
                  ·
                    rfl

theorem cell23_5102935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 6].length) (baseStart_5102935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102935 prefixEnd_5102935 := by exact prefixLift 5102935
  have htrace : WordTrace (prefixWord ++ tailWord_5102935) baseStart_5102935 baseEnd_5102935 := by
    simpa [prefixWord, tailWord_5102935, baseEnd_5102935] using wordTrace_append hprefix tailTrace_5102935
  have hstable : (prefixWord ++ tailWord_5102935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102935).length < 2 ^ (prefixWord ++ tailWord_5102935).sum := by decide
  have hdescent : baseEnd_5102935 < baseStart_5102935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102938 : List Nat := [3, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_5102938 : Nat := 118140960795 + 5102938 * 2 ^ 59
def prefixEnd_5102938 : Nat := 4983230072969 + 3 ^ 40 * 5102938 * 2
def baseEnd_5102938 : Nat := 2620259944093060965307021

theorem tailTrace_5102938 : CollatzResearch.WordTrace tailWord_5102938 prefixEnd_5102938 2620259944093060965307021 := by
  unfold tailWord_5102938
  simp only [CollatzResearch.WordTrace]
  refine ⟨46529859796733653317715367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124079626124623075513907645 46529859796733653317715367)
  ·
    refine ⟨69794789695100479976573051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46529859796733653317715367 69794789695100479976573051)
    ·
      refine ⟨104692184542650719964859577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69794789695100479976573051 104692184542650719964859577)
      ·
        refine ⟨78519138406988039973644683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104692184542650719964859577 78519138406988039973644683)
        ·
          refine ⟨117778707610482059960467025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78519138406988039973644683 117778707610482059960467025)
          ·
            refine ⟨88334030707861544970350269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117778707610482059960467025 88334030707861544970350269)
            ·
              refine ⟨33125261515448079363881351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88334030707861544970350269 33125261515448079363881351)
              ·
                refine ⟨49687892273172119045822027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33125261515448079363881351 49687892273172119045822027)
                ·
                  refine ⟨74531838409758178568733041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49687892273172119045822027 74531838409758178568733041)
                  ·
                    refine ⟨55898878807318633926549781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74531838409758178568733041 55898878807318633926549781)
                    ·
                      refine ⟨2620259944093060965307021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55898878807318633926549781 2620259944093060965307021)
                      ·
                        rfl

theorem cell23_5102938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_5102938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102938 prefixEnd_5102938 := by exact prefixLift 5102938
  have htrace : WordTrace (prefixWord ++ tailWord_5102938) baseStart_5102938 baseEnd_5102938 := by
    simpa [prefixWord, tailWord_5102938, baseEnd_5102938] using wordTrace_append hprefix tailTrace_5102938
  have hstable : (prefixWord ++ tailWord_5102938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102938).length < 2 ^ (prefixWord ++ tailWord_5102938).sum := by decide
  have hdescent : baseEnd_5102938 < baseStart_5102938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102962 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 3, 1, 3]
def baseStart_5102962 : Nat := 118140960795 + 5102962 * 2 ^ 59
def prefixEnd_5102962 : Nat := 4983230072969 + 3 ^ 40 * 5102962 * 2
def baseEnd_5102962 : Nat := 2620272267628768871406911

theorem tailTrace_5102962 : CollatzResearch.WordTrace tailWord_5102962 prefixEnd_5102962 2620272267628768871406911 := by
  unfold tailWord_5102962
  simp only [CollatzResearch.WordTrace]
  refine ⟨46530078634711916342433785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124080209692565110246490093 46530078634711916342433785)
  ·
    refine ⟨34897558976033937256825339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46530078634711916342433785 34897558976033937256825339)
    ·
      refine ⟨52346338464050905885238009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34897558976033937256825339 52346338464050905885238009)
      ·
        refine ⟨39259753848038179413928507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52346338464050905885238009 39259753848038179413928507)
        ·
          refine ⟨58889630772057269120892761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39259753848038179413928507 58889630772057269120892761)
          ·
            refine ⟨44167223079042951840669571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58889630772057269120892761 44167223079042951840669571)
            ·
              refine ⟨66250834618564427761004357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44167223079042951840669571 66250834618564427761004357)
              ·
                refine ⟨12422031490980830205188317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66250834618564427761004357 12422031490980830205188317)
                ·
                  refine ⟨4658261809117811326945619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12422031490980830205188317 4658261809117811326945619)
                  ·
                    refine ⟨6987392713676716990418429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4658261809117811326945619 6987392713676716990418429)
                    ·
                      refine ⟨2620272267628768871406911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6987392713676716990418429 2620272267628768871406911)
                      ·
                        rfl

theorem cell23_5102962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_5102962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102962 prefixEnd_5102962 := by exact prefixLift 5102962
  have htrace : WordTrace (prefixWord ++ tailWord_5102962) baseStart_5102962 baseEnd_5102962 := by
    simpa [prefixWord, tailWord_5102962, baseEnd_5102962] using wordTrace_append hprefix tailTrace_5102962
  have hstable : (prefixWord ++ tailWord_5102962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102962).length < 2 ^ (prefixWord ++ tailWord_5102962).sum := by decide
  have hdescent : baseEnd_5102962 < baseStart_5102962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102968 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_5102968 : Nat := 118140960795 + 5102968 * 2 ^ 59
def prefixEnd_5102968 : Nat := 4983230072969 + 3 ^ 40 * 5102968 * 2
def baseEnd_5102968 : Nat := 2620275348512695847931883

theorem tailTrace_5102968 : CollatzResearch.WordTrace tailWord_5102968 prefixEnd_5102968 2620275348512695847931883 := by
  unfold tailWord_5102968
  simp only [CollatzResearch.WordTrace]
  refine ⟨93060266688412964197226779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124080355584550618929635705 93060266688412964197226779)
  ·
    refine ⟨139590400032619446295840169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93060266688412964197226779 139590400032619446295840169)
    ·
      refine ⟨104692800024464584721880127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139590400032619446295840169 104692800024464584721880127)
      ·
        refine ⟨157039200036696877082820191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104692800024464584721880127 157039200036696877082820191)
        ·
          refine ⟨235558800055045315624230287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157039200036696877082820191 235558800055045315624230287)
          ·
            refine ⟨353338200082567973436345431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235558800055045315624230287 353338200082567973436345431)
            ·
              refine ⟨530007300123851960154518147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353338200082567973436345431 530007300123851960154518147)
              ·
                refine ⟨795010950185777940231777221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530007300123851960154518147 795010950185777940231777221)
                ·
                  refine ⟨149064553159833363793458229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 795010950185777940231777221 149064553159833363793458229)
                  ·
                    refine ⟨13974801858734377855636709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149064553159833363793458229 13974801858734377855636709)
                    ·
                      refine ⟨2620275348512695847931883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13974801858734377855636709 2620275348512695847931883)
                      ·
                        rfl

theorem cell23_5102968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_5102968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102968 prefixEnd_5102968 := by exact prefixLift 5102968
  have htrace : WordTrace (prefixWord ++ tailWord_5102968) baseStart_5102968 baseEnd_5102968 := by
    simpa [prefixWord, tailWord_5102968, baseEnd_5102968] using wordTrace_append hprefix tailTrace_5102968
  have hstable : (prefixWord ++ tailWord_5102968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102968).length < 2 ^ (prefixWord ++ tailWord_5102968).sum := by decide
  have hdescent : baseEnd_5102968 < baseStart_5102968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102972 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 2, 3, 2]
def baseStart_5102972 : Nat := 118140960795 + 5102972 * 2 ^ 59
def prefixEnd_5102972 : Nat := 4983230072969 + 3 ^ 40 * 5102972 * 2
def baseEnd_5102972 : Nat := 2620277402435313832281865

theorem tailTrace_5102972 : CollatzResearch.WordTrace tailWord_5102972 prefixEnd_5102972 2620277402435313832281865 := by
  unfold tailWord_5102972
  simp only [CollatzResearch.WordTrace]
  refine ⟨93060339634405718538799585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124080452845874291385066113 93060339634405718538799585)
  ·
    refine ⟨69795254725804288904099689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93060339634405718538799585 69795254725804288904099689)
    ·
      refine ⟨52346441044353216678074767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69795254725804288904099689 52346441044353216678074767)
      ·
        refine ⟨78519661566529825017112151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52346441044353216678074767 78519661566529825017112151)
        ·
          refine ⟨117779492349794737525668227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78519661566529825017112151 117779492349794737525668227)
          ·
            refine ⟨176669238524692106288502341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117779492349794737525668227 176669238524692106288502341)
            ·
              refine ⟨33125482223379769929094189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176669238524692106288502341 33125482223379769929094189)
              ·
                refine ⟨12422055833767413723410321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33125482223379769929094189 12422055833767413723410321)
                ·
                  refine ⟨9316541875325560292557741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12422055833767413723410321 9316541875325560292557741)
                  ·
                    refine ⟨3493703203247085109709153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9316541875325560292557741 3493703203247085109709153)
                    ·
                      refine ⟨2620277402435313832281865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493703203247085109709153 2620277402435313832281865)
                      ·
                        rfl

theorem cell23_5102972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 2, 3, 2].length) (baseStart_5102972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102972 prefixEnd_5102972 := by exact prefixLift 5102972
  have htrace : WordTrace (prefixWord ++ tailWord_5102972) baseStart_5102972 baseEnd_5102972 := by
    simpa [prefixWord, tailWord_5102972, baseEnd_5102972] using wordTrace_append hprefix tailTrace_5102972
  have hstable : (prefixWord ++ tailWord_5102972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102972).length < 2 ^ (prefixWord ++ tailWord_5102972).sum := by decide
  have hdescent : baseEnd_5102972 < baseStart_5102972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5102996 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_5102996 : Nat := 118140960795 + 5102996 * 2 ^ 59
def prefixEnd_5102996 : Nat := 4983230072969 + 3 ^ 40 * 5102996 * 2
def baseEnd_5102996 : Nat := 2620289725971021738381755

theorem tailTrace_5102996 : CollatzResearch.WordTrace tailWord_5102996 prefixEnd_5102996 2620289725971021738381755 := by
  unfold tailWord_5102996
  simp only [CollatzResearch.WordTrace]
  refine ⟨93060777310362244588236421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124081036413816326117648561 93060777310362244588236421)
  ·
    refine ⟨17448895745692920860294329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93060777310362244588236421 17448895745692920860294329)
    ·
      refine ⟨13086671809269690645220747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17448895745692920860294329 13086671809269690645220747)
      ·
        refine ⟨19630007713904535967831121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13086671809269690645220747 19630007713904535967831121)
        ·
          refine ⟨14722505785428401975873341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19630007713904535967831121 14722505785428401975873341)
          ·
            refine ⟨5520939669535650740952503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14722505785428401975873341 5520939669535650740952503)
            ·
              refine ⟨8281409504303476111428755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520939669535650740952503 8281409504303476111428755)
              ·
                refine ⟨12422114256455214167143133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8281409504303476111428755 12422114256455214167143133)
                ·
                  refine ⟨4658292846170705312678675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12422114256455214167143133 4658292846170705312678675)
                  ·
                    refine ⟨6987439269256057969018013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4658292846170705312678675 6987439269256057969018013)
                    ·
                      refine ⟨2620289725971021738381755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6987439269256057969018013 2620289725971021738381755)
                      ·
                        rfl

theorem cell23_5102996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_5102996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5102996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5102996 prefixEnd_5102996 := by exact prefixLift 5102996
  have htrace : WordTrace (prefixWord ++ tailWord_5102996) baseStart_5102996 baseEnd_5102996 := by
    simpa [prefixWord, tailWord_5102996, baseEnd_5102996] using wordTrace_append hprefix tailTrace_5102996
  have hstable : (prefixWord ++ tailWord_5102996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5102996).length < 2 ^ (prefixWord ++ tailWord_5102996).sum := by decide
  have hdescent : baseEnd_5102996 < baseStart_5102996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5102996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103015 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_5103015 : Nat := 118140960795 + 5103015 * 2 ^ 59
def prefixEnd_5103015 : Nat := 4983230072969 + 3 ^ 40 * 5103015 * 2
def baseEnd_5103015 : Nat := 2620299482103457164044167

theorem tailTrace_5103015 : CollatzResearch.WordTrace tailWord_5103015 prefixEnd_5103015 2620299482103457164044167 := by
  unfold tailWord_5103015
  simp only [CollatzResearch.WordTrace]
  refine ⟨186122247607655655421414499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124081498405103770280942999 186122247607655655421414499)
  ·
    refine ⟨279183371411483483132121749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186122247607655655421414499 279183371411483483132121749)
    ·
      refine ⟨13086720534913288271818207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 279183371411483483132121749 13086720534913288271818207)
      ·
        refine ⟨19630080802369932407727311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13086720534913288271818207 19630080802369932407727311)
        ·
          refine ⟨29445121203554898611590967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19630080802369932407727311 29445121203554898611590967)
          ·
            refine ⟨44167681805332347917386451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29445121203554898611590967 44167681805332347917386451)
            ·
              refine ⟨66251522707998521876079677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44167681805332347917386451 66251522707998521876079677)
              ·
                refine ⟨24844321015499445703529879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66251522707998521876079677 24844321015499445703529879)
                ·
                  refine ⟨37266481523249168555294819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24844321015499445703529879 37266481523249168555294819)
                  ·
                    refine ⟨55899722284873752832942229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37266481523249168555294819 55899722284873752832942229)
                    ·
                      refine ⟨2620299482103457164044167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55899722284873752832942229 2620299482103457164044167)
                      ·
                        rfl

theorem cell23_5103015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_5103015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103015 prefixEnd_5103015 := by exact prefixLift 5103015
  have htrace : WordTrace (prefixWord ++ tailWord_5103015) baseStart_5103015 baseEnd_5103015 := by
    simpa [prefixWord, tailWord_5103015, baseEnd_5103015] using wordTrace_append hprefix tailTrace_5103015
  have hstable : (prefixWord ++ tailWord_5103015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103015).length < 2 ^ (prefixWord ++ tailWord_5103015).sum := by decide
  have hdescent : baseEnd_5103015 < baseStart_5103015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103016 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5103016 : Nat := 118140960795 + 5103016 * 2 ^ 59
def prefixEnd_5103016 : Nat := 4983230072969 + 3 ^ 40 * 5103016 * 2
def baseEnd_5103016 : Nat := 873433331861370553377221

theorem tailTrace_5103016 : CollatzResearch.WordTrace tailWord_5103016 prefixEnd_5103016 873433331861370553377221 := by
  unfold tailWord_5103016
  simp only [CollatzResearch.WordTrace]
  refine ⟨93061142040326016296100451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124081522720434688394800601 93061142040326016296100451)
  ·
    refine ⟨139591713060489024444150677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93061142040326016296100451 139591713060489024444150677)
    ·
      refine ⟨6543361549710423020819563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139591713060489024444150677 6543361549710423020819563)
      ·
        refine ⟨9815042324565634531229345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6543361549710423020819563 9815042324565634531229345)
        ·
          refine ⟨7361281743424225898422009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9815042324565634531229345 7361281743424225898422009)
          ·
            refine ⟨5520961307568169423816507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7361281743424225898422009 5520961307568169423816507)
            ·
              refine ⟨8281441961352254135724761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5520961307568169423816507 8281441961352254135724761)
              ·
                refine ⟨6211081471014190601793571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8281441961352254135724761 6211081471014190601793571)
                ·
                  refine ⟨9316622206521285902690357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6211081471014190601793571 9316622206521285902690357)
                  ·
                    refine ⟨873433331861370553377221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9316622206521285902690357 873433331861370553377221)
                    ·
                      rfl

theorem cell23_5103016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5103016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103016 prefixEnd_5103016 := by exact prefixLift 5103016
  have htrace : WordTrace (prefixWord ++ tailWord_5103016) baseStart_5103016 baseEnd_5103016 := by
    simpa [prefixWord, tailWord_5103016, baseEnd_5103016] using wordTrace_append hprefix tailTrace_5103016
  have hstable : (prefixWord ++ tailWord_5103016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103016).length < 2 ^ (prefixWord ++ tailWord_5103016).sum := by decide
  have hdescent : baseEnd_5103016 < baseStart_5103016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103036 : List Nat := [2, 2, 2, 4, 2, 1, 3, 1, 1, 1, 4]
def baseStart_5103036 : Nat := 118140960795 + 5103036 * 2 ^ 59
def prefixEnd_5103036 : Nat := 4983230072969 + 3 ^ 40 * 5103036 * 2
def baseEnd_5103036 : Nat := 2620310265197201581881571

theorem tailTrace_5103036 : CollatzResearch.WordTrace tailWord_5103036 prefixEnd_5103036 2620310265197201581881571 := by
  unfold tailWord_5103036
  simp only [CollatzResearch.WordTrace]
  refine ⟨93061506770289788003964481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124082009027053050671952641 93061506770289788003964481)
  ·
    refine ⟨69796130077717341002973361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93061506770289788003964481 69796130077717341002973361)
    ·
      refine ⟨52347097558288005752230021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69796130077717341002973361 52347097558288005752230021)
      ·
        refine ⟨9815080792179001078543129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52347097558288005752230021 9815080792179001078543129)
        ·
          refine ⟨7361310594134250808907347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9815080792179001078543129 7361310594134250808907347)
          ·
            refine ⟨11041965891201376213361021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7361310594134250808907347 11041965891201376213361021)
            ·
              refine ⟨4140737209200516080010383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11041965891201376213361021 4140737209200516080010383)
              ·
                refine ⟨6211105813800774120015575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140737209200516080010383 6211105813800774120015575)
                ·
                  refine ⟨9316658720701161180023363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6211105813800774120015575 9316658720701161180023363)
                  ·
                    refine ⟨13974988081051741770035045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9316658720701161180023363 13974988081051741770035045)
                    ·
                      refine ⟨2620310265197201581881571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13974988081051741770035045 2620310265197201581881571)
                      ·
                        rfl

theorem cell23_5103036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_5103036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103036 prefixEnd_5103036 := by exact prefixLift 5103036
  have htrace : WordTrace (prefixWord ++ tailWord_5103036) baseStart_5103036 baseEnd_5103036 := by
    simpa [prefixWord, tailWord_5103036, baseEnd_5103036] using wordTrace_append hprefix tailTrace_5103036
  have hstable : (prefixWord ++ tailWord_5103036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103036).length < 2 ^ (prefixWord ++ tailWord_5103036).sum := by decide
  have hdescent : baseEnd_5103036 < baseStart_5103036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103069 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_5103069 : Nat := 118140960795 + 5103069 * 2 ^ 59
def prefixEnd_5103069 : Nat := 4983230072969 + 3 ^ 40 * 5103069 * 2
def baseEnd_5103069 : Nat := 2620327210058799952768919

theorem tailTrace_5103069 : CollatzResearch.WordTrace tailWord_5103069 prefixEnd_5103069 2620327210058799952768919 := by
  unfold tailWord_5103069
  simp only [CollatzResearch.WordTrace]
  refine ⟨186124217149460022643880261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124082811432973348429253507 186124217149460022643880261)
  ·
    refine ⟨34898290715523754245727549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186124217149460022643880261 34898290715523754245727549)
    ·
      refine ⟨13086859018321407842147831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34898290715523754245727549 13086859018321407842147831)
      ·
        refine ⟨19630288527482111763221747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13086859018321407842147831 19630288527482111763221747)
        ·
          refine ⟨29445432791223167644832621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19630288527482111763221747 29445432791223167644832621)
          ·
            refine ⟨11042037296708687866812233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29445432791223167644832621 11042037296708687866812233)
            ·
              refine ⟨8281527972531515900109175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11042037296708687866812233 8281527972531515900109175)
              ·
                refine ⟨12422291958797273850163763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8281527972531515900109175 12422291958797273850163763)
                ·
                  refine ⟨18633437938195910775245645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12422291958797273850163763 18633437938195910775245645)
                  ·
                    refine ⟨6987539226823466540717117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18633437938195910775245645 6987539226823466540717117)
                    ·
                      refine ⟨2620327210058799952768919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6987539226823466540717117 2620327210058799952768919)
                      ·
                        rfl

theorem cell23_5103069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_5103069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103069 prefixEnd_5103069 := by exact prefixLift 5103069
  have htrace : WordTrace (prefixWord ++ tailWord_5103069) baseStart_5103069 baseEnd_5103069 := by
    simpa [prefixWord, tailWord_5103069, baseEnd_5103069] using wordTrace_append hprefix tailTrace_5103069
  have hstable : (prefixWord ++ tailWord_5103069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103069).length < 2 ^ (prefixWord ++ tailWord_5103069).sum := by decide
  have hdescent : baseEnd_5103069 < baseStart_5103069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103079 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 3, 3, 2]
def baseStart_5103079 : Nat := 118140960795 + 5103079 * 2 ^ 59
def prefixEnd_5103079 : Nat := 4983230072969 + 3 ^ 40 * 5103079 * 2
def baseEnd_5103079 : Nat := 2620332344865344913643873

theorem tailTrace_5103079 : CollatzResearch.WordTrace tailWord_5103079 prefixEnd_5103079 2620332344865344913643873 := by
  unfold tailWord_5103079
  simp only [CollatzResearch.WordTrace]
  refine ⟨186124581879423794351744291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124083054586282529567829527 186124581879423794351744291)
  ·
    refine ⟨279186872819135691527616437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186124581879423794351744291 279186872819135691527616437)
    ·
      refine ⟨26173769326793971080714041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 279186872819135691527616437 26173769326793971080714041)
      ·
        refine ⟨19630326995095478310535531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26173769326793971080714041 19630326995095478310535531)
        ·
          refine ⟨29445490492643217465803297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19630326995095478310535531 29445490492643217465803297)
          ·
            refine ⟨22084117869482413099352473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29445490492643217465803297 22084117869482413099352473)
            ·
              refine ⟨16563088402111809824514355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22084117869482413099352473 16563088402111809824514355)
              ·
                refine ⟨24844632603167714736771533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16563088402111809824514355 24844632603167714736771533)
                ·
                  refine ⟨9316737226187893026289325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24844632603167714736771533 9316737226187893026289325)
                  ·
                    refine ⟨3493776459820459884858497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9316737226187893026289325 3493776459820459884858497)
                    ·
                      refine ⟨2620332344865344913643873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493776459820459884858497 2620332344865344913643873)
                      ·
                        rfl

theorem cell23_5103079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_5103079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103079 prefixEnd_5103079 := by exact prefixLift 5103079
  have htrace : WordTrace (prefixWord ++ tailWord_5103079) baseStart_5103079 baseEnd_5103079 := by
    simpa [prefixWord, tailWord_5103079, baseEnd_5103079] using wordTrace_append hprefix tailTrace_5103079
  have hstable : (prefixWord ++ tailWord_5103079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103079).length < 2 ^ (prefixWord ++ tailWord_5103079).sum := by decide
  have hdescent : baseEnd_5103079 < baseStart_5103079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103095 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 3]
def baseStart_5103095 : Nat := 118140960795 + 5103095 * 2 ^ 59
def prefixEnd_5103095 : Nat := 4983230072969 + 3 ^ 40 * 5103095 * 2
def baseEnd_5103095 : Nat := 2620340560555816851043799

theorem tailTrace_5103095 : CollatzResearch.WordTrace tailWord_5103095 prefixEnd_5103095 2620340560555816851043799 := by
  unfold tailWord_5103095
  simp only [CollatzResearch.WordTrace]
  refine ⟨186125165447365829084326739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124083443631577219389551159 186125165447365829084326739)
  ·
    refine ⟨279187748171048743626490109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186125165447365829084326739 279187748171048743626490109)
    ·
      refine ⟨104695405564143278859933791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279187748171048743626490109 104695405564143278859933791)
      ·
        refine ⟨157043108346214918289900687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104695405564143278859933791 157043108346214918289900687)
        ·
          refine ⟨235564662519322377434851031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157043108346214918289900687 235564662519322377434851031)
          ·
            refine ⟨353346993778983566152276547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235564662519322377434851031 353346993778983566152276547)
            ·
              refine ⟨530020490668475349228414821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353346993778983566152276547 530020490668475349228414821)
              ·
                refine ⟨99378842000339127980327779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530020490668475349228414821 99378842000339127980327779)
                ·
                  refine ⟨149068263000508691970491669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99378842000339127980327779 149068263000508691970491669)
                  ·
                    refine ⟨6987574828148844936116797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 149068263000508691970491669 6987574828148844936116797)
                    ·
                      refine ⟨2620340560555816851043799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6987574828148844936116797 2620340560555816851043799)
                      ·
                        rfl

theorem cell23_5103095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_5103095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103095 prefixEnd_5103095 := by exact prefixLift 5103095
  have htrace : WordTrace (prefixWord ++ tailWord_5103095) baseStart_5103095 baseEnd_5103095 := by
    simpa [prefixWord, tailWord_5103095, baseEnd_5103095] using wordTrace_append hprefix tailTrace_5103095
  have hstable : (prefixWord ++ tailWord_5103095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103095).length < 2 ^ (prefixWord ++ tailWord_5103095).sum := by decide
  have hdescent : baseEnd_5103095 < baseStart_5103095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103096 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 1, 3, 2]
def baseStart_5103096 : Nat := 118140960795 + 5103096 * 2 ^ 59
def prefixEnd_5103096 : Nat := 4983230072969 + 3 ^ 40 * 5103096 * 2
def baseEnd_5103096 : Nat := 2620341074036471347131295

theorem tailTrace_5103096 : CollatzResearch.WordTrace tailWord_5103096 prefixEnd_5103096 2620341074036471347131295 := by
  unfold tailWord_5103096
  simp only [CollatzResearch.WordTrace]
  refine ⟨93062600960181103127556571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124083467946908137503408761 93062600960181103127556571)
  ·
    refine ⟨139593901440271654691334857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93062600960181103127556571 139593901440271654691334857)
    ·
      refine ⟨104695426080203741018501143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139593901440271654691334857 104695426080203741018501143)
      ·
        refine ⟨157043139120305611527751715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104695426080203741018501143 157043139120305611527751715)
        ·
          refine ⟨235564708680458417291627573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157043139120305611527751715 235564708680458417291627573)
          ·
            refine ⟨22084191438792976621090085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 235564708680458417291627573 22084191438792976621090085)
            ·
              refine ⟨4140785894773683116454391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22084191438792976621090085 4140785894773683116454391)
              ·
                refine ⟨6211178842160524674681587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140785894773683116454391 6211178842160524674681587)
                ·
                  refine ⟨9316768263240787012022381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6211178842160524674681587 9316768263240787012022381)
                  ·
                    refine ⟨3493788098715295129508393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9316768263240787012022381 3493788098715295129508393)
                    ·
                      refine ⟨2620341074036471347131295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493788098715295129508393 2620341074036471347131295)
                      ·
                        rfl

theorem cell23_5103096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_5103096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103096 prefixEnd_5103096 := by exact prefixLift 5103096
  have htrace : WordTrace (prefixWord ++ tailWord_5103096) baseStart_5103096 baseEnd_5103096 := by
    simpa [prefixWord, tailWord_5103096, baseEnd_5103096] using wordTrace_append hprefix tailTrace_5103096
  have hstable : (prefixWord ++ tailWord_5103096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103096).length < 2 ^ (prefixWord ++ tailWord_5103096).sum := by decide
  have hdescent : baseEnd_5103096 < baseStart_5103096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103152 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 1, 7, 2]
def baseStart_5103152 : Nat := 118140960795 + 5103152 * 2 ^ 59
def prefixEnd_5103152 : Nat := 4983230072969 + 3 ^ 40 * 5103152 * 2
def baseEnd_5103152 : Nat := 2620369828953123128031037

theorem tailTrace_5103152 : CollatzResearch.WordTrace tailWord_5103152 prefixEnd_5103152 2620369828953123128031037 := by
  unfold tailWord_5103152
  simp only [CollatzResearch.WordTrace]
  refine ⟨93063622204079663909575855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124084829605439551879434473 93063622204079663909575855)
  ·
    refine ⟨139595433306119495864363783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93063622204079663909575855 139595433306119495864363783)
    ·
      refine ⟨209393149959179243796545675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139595433306119495864363783 209393149959179243796545675)
      ·
        refine ⟨314089724938768865694818513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209393149959179243796545675 314089724938768865694818513)
        ·
          refine ⟨235567293704076649271113885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314089724938768865694818513 235567293704076649271113885)
          ·
            refine ⟨88337735139028743476667707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235567293704076649271113885 88337735139028743476667707)
            ·
              refine ⟨132506602708543115215001561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88337735139028743476667707 132506602708543115215001561)
              ·
                refine ⟨99379952031407336411251171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132506602708543115215001561 99379952031407336411251171)
                ·
                  refine ⟨149069928047111004616876757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99379952031407336411251171 149069928047111004616876757)
                  ·
                    refine ⟨3493826438604164170708049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 149069928047111004616876757 3493826438604164170708049)
                    ·
                      refine ⟨2620369828953123128031037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493826438604164170708049 2620369828953123128031037)
                      ·
                        rfl

theorem cell23_5103152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 1, 7, 2].length) (baseStart_5103152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103152 prefixEnd_5103152 := by exact prefixLift 5103152
  have htrace : WordTrace (prefixWord ++ tailWord_5103152) baseStart_5103152 baseEnd_5103152 := by
    simpa [prefixWord, tailWord_5103152, baseEnd_5103152] using wordTrace_append hprefix tailTrace_5103152
  have hstable : (prefixWord ++ tailWord_5103152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103152).length < 2 ^ (prefixWord ++ tailWord_5103152).sum := by decide
  have hdescent : baseEnd_5103152 < baseStart_5103152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103162 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_5103162 : Nat := 118140960795 + 5103162 * 2 ^ 59
def prefixEnd_5103162 : Nat := 4983230072969 + 3 ^ 40 * 5103162 * 2
def baseEnd_5103162 : Nat := 873458321253222696301997

theorem tailTrace_5103162 : CollatzResearch.WordTrace tailWord_5103162 prefixEnd_5103162 873458321253222696301997 := by
  unfold tailWord_5103162
  simp only [CollatzResearch.WordTrace]
  refine ⟨46531902284530774881753935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124085072758748733018010493 46531902284530774881753935)
  ·
    refine ⟨69797853426796162322630903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46531902284530774881753935 69797853426796162322630903)
    ·
      refine ⟨104696780140194243483946355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69797853426796162322630903 104696780140194243483946355)
      ·
        refine ⟨157045170210291365225919533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104696780140194243483946355 157045170210291365225919533)
        ·
          refine ⟨58891938828859261959719825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157045170210291365225919533 58891938828859261959719825)
          ·
            refine ⟨44168954121644446469789869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58891938828859261959719825 44168954121644446469789869)
            ·
              refine ⟨16563357795616667426171201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44168954121644446469789869 16563357795616667426171201)
              ·
                refine ⟨12422518346712500569628401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16563357795616667426171201 12422518346712500569628401)
                ·
                  refine ⟨9316888760034375427221301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12422518346712500569628401 9316888760034375427221301)
                  ·
                    refine ⟨873458321253222696301997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9316888760034375427221301 873458321253222696301997)
                    ·
                      rfl

theorem cell23_5103162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_5103162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103162 prefixEnd_5103162 := by exact prefixLift 5103162
  have htrace : WordTrace (prefixWord ++ tailWord_5103162) baseStart_5103162 baseEnd_5103162 := by
    simpa [prefixWord, tailWord_5103162, baseEnd_5103162] using wordTrace_append hprefix tailTrace_5103162
  have hstable : (prefixWord ++ tailWord_5103162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103162).length < 2 ^ (prefixWord ++ tailWord_5103162).sum := by decide
  have hdescent : baseEnd_5103162 < baseStart_5103162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103169 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_5103169 : Nat := 118140960795 + 5103169 * 2 ^ 59
def prefixEnd_5103169 : Nat := 4983230072969 + 3 ^ 40 * 5103169 * 2
def baseEnd_5103169 : Nat := 2620378558124249561518459

theorem tailTrace_5103169 : CollatzResearch.WordTrace tailWord_5103169 prefixEnd_5103169 2620378558124249561518459 := by
  unfold tailWord_5103169
  simp only [CollatzResearch.WordTrace]
  refine ⟨186127864449097739722520561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124085242966065159815013707 186127864449097739722520561)
  ·
    refine ⟨139595898336823304791890421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186127864449097739722520561 139595898336823304791890421)
    ·
      refine ⟨13087115469077184824239727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139595898336823304791890421 13087115469077184824239727)
      ·
        refine ⟨19630673203615777236359591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13087115469077184824239727 19630673203615777236359591)
        ·
          refine ⟨29446009805423665854539387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19630673203615777236359591 29446009805423665854539387)
          ·
            refine ⟨44169014708135498781809081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29446009805423665854539387 44169014708135498781809081)
            ·
              refine ⟨33126761031101624086356811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44169014708135498781809081 33126761031101624086356811)
              ·
                refine ⟨49690141546652436129535217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33126761031101624086356811 49690141546652436129535217)
                ·
                  refine ⟨37267606159989327097151413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49690141546652436129535217 37267606159989327097151413)
                  ·
                    refine ⟨3493838077498999415357945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37267606159989327097151413 3493838077498999415357945)
                    ·
                      refine ⟨2620378558124249561518459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3493838077498999415357945 2620378558124249561518459)
                      ·
                        rfl

theorem cell23_5103169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_5103169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103169 prefixEnd_5103169 := by exact prefixLift 5103169
  have htrace : WordTrace (prefixWord ++ tailWord_5103169) baseStart_5103169 baseEnd_5103169 := by
    simpa [prefixWord, tailWord_5103169, baseEnd_5103169] using wordTrace_append hprefix tailTrace_5103169
  have hstable : (prefixWord ++ tailWord_5103169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103169).length < 2 ^ (prefixWord ++ tailWord_5103169).sum := by decide
  have hdescent : baseEnd_5103169 < baseStart_5103169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103182 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_5103182 : Nat := 118140960795 + 5103182 * 2 ^ 59
def prefixEnd_5103182 : Nat := 4983230072969 + 3 ^ 40 * 5103182 * 2
def baseEnd_5103182 : Nat := 2620385233372758010655899

theorem tailTrace_5103182 : CollatzResearch.WordTrace tailWord_5103182 prefixEnd_5103182 2620385233372758010655899 := by
  unfold tailWord_5103182
  simp only [CollatzResearch.WordTrace]
  refine ⟨23266042324756330367842975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124085559065367095295162533 23266042324756330367842975)
  ·
    refine ⟨34899063487134495551764463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23266042324756330367842975 34899063487134495551764463)
    ·
      refine ⟨52348595230701743327646695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34899063487134495551764463 52348595230701743327646695)
      ·
        refine ⟨78522892846052614991470043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52348595230701743327646695 78522892846052614991470043)
        ·
          refine ⟨117784339269078922487205065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78522892846052614991470043 117784339269078922487205065)
          ·
            refine ⟨88338254451809191865403799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117784339269078922487205065 88338254451809191865403799)
            ·
              refine ⟨132507381677713787798105699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88338254451809191865403799 132507381677713787798105699)
              ·
                refine ⟨198761072516570681697158549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132507381677713787798105699 198761072516570681697158549)
                ·
                  refine ⟨9316925274214250704554307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 198761072516570681697158549 9316925274214250704554307)
                  ·
                    refine ⟨13975387911321376056831461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9316925274214250704554307 13975387911321376056831461)
                    ·
                      refine ⟨2620385233372758010655899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13975387911321376056831461 2620385233372758010655899)
                      ·
                        rfl

theorem cell23_5103182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_5103182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103182 prefixEnd_5103182 := by exact prefixLift 5103182
  have htrace : WordTrace (prefixWord ++ tailWord_5103182) baseStart_5103182 baseEnd_5103182 := by
    simpa [prefixWord, tailWord_5103182, baseEnd_5103182] using wordTrace_append hprefix tailTrace_5103182
  have hstable : (prefixWord ++ tailWord_5103182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103182).length < 2 ^ (prefixWord ++ tailWord_5103182).sum := by decide
  have hdescent : baseEnd_5103182 < baseStart_5103182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103192 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 5, 4]
def baseStart_5103192 : Nat := 118140960795 + 5103192 * 2 ^ 59
def prefixEnd_5103192 : Nat := 4983230072969 + 3 ^ 40 * 5103192 * 2
def baseEnd_5103192 : Nat := 873463456059767657176951

theorem tailTrace_5103192 : CollatzResearch.WordTrace tailWord_5103192 prefixEnd_5103192 873463456059767657176951 := by
  unfold tailWord_5103192
  simp only [CollatzResearch.WordTrace]
  refine ⟨93064351664007207325303915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124085802218676276433738553 93064351664007207325303915)
  ·
    refine ⟨139596527496010810987955873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93064351664007207325303915 139596527496010810987955873)
    ·
      refine ⟨104697395622008108240966905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139596527496010810987955873 104697395622008108240966905)
      ·
        refine ⟨78523046716506081180725179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104697395622008108240966905 78523046716506081180725179)
        ·
          refine ⟨117784570074759121771087769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78523046716506081180725179 117784570074759121771087769)
          ·
            refine ⟨88338427556069341328315827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117784570074759121771087769 88338427556069341328315827)
            ·
              refine ⟨132507641334104011992473741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88338427556069341328315827 132507641334104011992473741)
              ·
                refine ⟨49690365500289004497177653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132507641334104011992473741 49690365500289004497177653)
                ·
                  refine ⟨4658471765652094171610405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49690365500289004497177653 4658471765652094171610405)
                  ·
                    refine ⟨873463456059767657176951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4658471765652094171610405 873463456059767657176951)
                    ·
                      rfl

theorem cell23_5103192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_5103192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103192 prefixEnd_5103192 := by exact prefixLift 5103192
  have htrace : WordTrace (prefixWord ++ tailWord_5103192) baseStart_5103192 baseEnd_5103192 := by
    simpa [prefixWord, tailWord_5103192, baseEnd_5103192] using wordTrace_append hprefix tailTrace_5103192
  have hstable : (prefixWord ++ tailWord_5103192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103192).length < 2 ^ (prefixWord ++ tailWord_5103192).sum := by decide
  have hdescent : baseEnd_5103192 < baseStart_5103192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103282 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_5103282 : Nat := 118140960795 + 5103282 * 2 ^ 59
def prefixEnd_5103282 : Nat := 4983230072969 + 3 ^ 40 * 5103282 * 2
def baseEnd_5103282 : Nat := 873478860479402539801813

theorem tailTrace_5103282 : CollatzResearch.WordTrace tailWord_5103282 prefixEnd_5103282 873478860479402539801813 := by
  unfold tailWord_5103282
  simp only [CollatzResearch.WordTrace]
  refine ⟨46532996474422090005346025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124087990598458906680922733 46532996474422090005346025)
  ·
    refine ⟨34899747355816567504009519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46532996474422090005346025 34899747355816567504009519)
    ·
      refine ⟨52349621033724851256014279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34899747355816567504009519 52349621033724851256014279)
      ·
        refine ⟨78524431550587276884021419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52349621033724851256014279 78524431550587276884021419)
        ·
          refine ⟨117786647325880915326032129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78524431550587276884021419 117786647325880915326032129)
          ·
            refine ⟨88339985494410686494524097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117786647325880915326032129 88339985494410686494524097)
            ·
              refine ⟨66254989120808014870893073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88339985494410686494524097 66254989120808014870893073)
              ·
                refine ⟨49691241840606011153169805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66254989120808014870893073 49691241840606011153169805)
                ·
                  refine ⟨18634215690227254182438677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49691241840606011153169805 18634215690227254182438677)
                  ·
                    refine ⟨873478860479402539801813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18634215690227254182438677 873478860479402539801813)
                    ·
                      rfl

theorem cell23_5103282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_5103282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103282 prefixEnd_5103282 := by exact prefixLift 5103282
  have htrace : WordTrace (prefixWord ++ tailWord_5103282) baseStart_5103282 baseEnd_5103282 := by
    simpa [prefixWord, tailWord_5103282, baseEnd_5103282] using wordTrace_append hprefix tailTrace_5103282
  have hstable : (prefixWord ++ tailWord_5103282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103282).length < 2 ^ (prefixWord ++ tailWord_5103282).sum := by decide
  have hdescent : baseEnd_5103282 < baseStart_5103282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103316 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_5103316 : Nat := 118140960795 + 5103316 * 2 ^ 59
def prefixEnd_5103316 : Nat := 4983230072969 + 3 ^ 40 * 5103316 * 2
def baseEnd_5103316 : Nat := 873484679926820162126761

theorem tailTrace_5103316 : CollatzResearch.WordTrace tailWord_5103316 prefixEnd_5103316 873484679926820162126761 := by
  unfold tailWord_5103316
  simp only [CollatzResearch.WordTrace]
  refine ⟨93066612989782591914060901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124088817319710122552081201 93066612989782591914060901)
  ·
    refine ⟨17449989935584235983886419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93066612989782591914060901 17449989935584235983886419)
    ·
      refine ⟨26174984903376353975829629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17449989935584235983886419 26174984903376353975829629)
      ·
        refine ⟨9815619338766132740936111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26174984903376353975829629 9815619338766132740936111)
        ·
          refine ⟨14723429008149199111404167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9815619338766132740936111 14723429008149199111404167)
          ·
            refine ⟨22085143512223798667106251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14723429008149199111404167 22085143512223798667106251)
            ·
              refine ⟨33127715268335698000659377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22085143512223798667106251 33127715268335698000659377)
              ·
                refine ⟨24845786451251773500494533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33127715268335698000659377 24845786451251773500494533)
                ·
                  refine ⟨4658584959609707531342725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24845786451251773500494533 4658584959609707531342725)
                  ·
                    refine ⟨873484679926820162126761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4658584959609707531342725 873484679926820162126761)
                    ·
                      rfl

theorem cell23_5103316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_5103316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103316 prefixEnd_5103316 := by exact prefixLift 5103316
  have htrace : WordTrace (prefixWord ++ tailWord_5103316) baseStart_5103316 baseEnd_5103316 := by
    simpa [prefixWord, tailWord_5103316, baseEnd_5103316] using wordTrace_append hprefix tailTrace_5103316
  have hstable : (prefixWord ++ tailWord_5103316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103316).length < 2 ^ (prefixWord ++ tailWord_5103316).sum := by decide
  have hdescent : baseEnd_5103316 < baseStart_5103316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103329 : List Nat := [1, 2, 3, 1, 5, 2, 9]
def baseStart_5103329 : Nat := 118140960795 + 5103329 * 2 ^ 59
def prefixEnd_5103329 : Nat := 4983230072969 + 3 ^ 40 * 5103329 * 2
def baseEnd_5103329 : Nat := 32351366852209493031083

theorem tailTrace_5103329 : CollatzResearch.WordTrace tailWord_5103329 prefixEnd_5103329 32351366852209493031083 := by
  unfold tailWord_5103329
  simp only [CollatzResearch.WordTrace]
  refine ⟨186133700128518087048345041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124089133419012058032230027 186133700128518087048345041)
  ·
    refine ⟨139600275096388565286258781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186133700128518087048345041 139600275096388565286258781)
    ·
      refine ⟨52350103161145711982347043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139600275096388565286258781 52350103161145711982347043)
      ·
        refine ⟨78525154741718567973520565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52350103161145711982347043 78525154741718567973520565)
        ·
          refine ⟨7361733257036115747517553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78525154741718567973520565 7361733257036115747517553)
          ·
            refine ⟨5521299942777086810638165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7361733257036115747517553 5521299942777086810638165)
            ·
              refine ⟨32351366852209493031083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5521299942777086810638165 32351366852209493031083)
              ·
                rfl

theorem cell23_5103329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 9].length) (baseStart_5103329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103329 prefixEnd_5103329 := by exact prefixLift 5103329
  have htrace : WordTrace (prefixWord ++ tailWord_5103329) baseStart_5103329 baseEnd_5103329 := by
    simpa [prefixWord, tailWord_5103329, baseEnd_5103329] using wordTrace_append hprefix tailTrace_5103329
  have hstable : (prefixWord ++ tailWord_5103329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103329).length < 2 ^ (prefixWord ++ tailWord_5103329).sum := by decide
  have hdescent : baseEnd_5103329 < baseStart_5103329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103350 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_5103350 : Nat := 118140960795 + 5103350 * 2 ^ 59
def prefixEnd_5103350 : Nat := 4983230072969 + 3 ^ 40 * 5103350 * 2
def baseEnd_5103350 : Nat := 873490499374237784451709

theorem tailTrace_5103350 : CollatzResearch.WordTrace tailWord_5103350 prefixEnd_5103350 873490499374237784451709 := by
  unfold tailWord_5103350
  simp only [CollatzResearch.WordTrace]
  refine ⟨11633404128840125477178719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124089644040961338423239669 11633404128840125477178719)
  ·
    refine ⟨17450106193260188215768079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11633404128840125477178719 17450106193260188215768079)
    ·
      refine ⟨26175159289890282323652119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17450106193260188215768079 26175159289890282323652119)
      ·
        refine ⟨39262738934835423485478179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26175159289890282323652119 39262738934835423485478179)
        ·
          refine ⟨58894108402253135228217269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39262738934835423485478179 58894108402253135228217269)
          ·
            refine ⟨5521322662711231427645369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58894108402253135228217269 5521322662711231427645369)
            ·
              refine ⟨4140991997033423570734027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5521322662711231427645369 4140991997033423570734027)
              ·
                refine ⟨6211487995550135356101041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4140991997033423570734027 6211487995550135356101041)
                ·
                  refine ⟨4658615996662601517075781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6211487995550135356101041 4658615996662601517075781)
                  ·
                    refine ⟨873490499374237784451709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4658615996662601517075781 873490499374237784451709)
                    ·
                      rfl

theorem cell23_5103350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_5103350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103350 prefixEnd_5103350 := by exact prefixLift 5103350
  have htrace : WordTrace (prefixWord ++ tailWord_5103350) baseStart_5103350 baseEnd_5103350 := by
    simpa [prefixWord, tailWord_5103350, baseEnd_5103350] using wordTrace_append hprefix tailTrace_5103350
  have hstable : (prefixWord ++ tailWord_5103350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103350).length < 2 ^ (prefixWord ++ tailWord_5103350).sum := by decide
  have hdescent : baseEnd_5103350 < baseStart_5103350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103352 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_5103352 : Nat := 118140960795 + 5103352 * 2 ^ 59
def prefixEnd_5103352 : Nat := 4983230072969 + 3 ^ 40 * 5103352 * 2
def baseEnd_5103352 : Nat := 2620472525084022345530117

theorem tailTrace_5103352 : CollatzResearch.WordTrace tailWord_5103352 prefixEnd_5103352 2620472525084022345530117 := by
  unfold tailWord_5103352
  simp only [CollatzResearch.WordTrace]
  refine ⟨93067269503717380988216155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124089692671623174650954873 93067269503717380988216155)
  ·
    refine ⟨139600904255576071482324233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93067269503717380988216155 139600904255576071482324233)
    ·
      refine ⟨104700678191682053611743175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139600904255576071482324233 104700678191682053611743175)
      ·
        refine ⟨157051017287523080417614763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104700678191682053611743175 157051017287523080417614763)
        ·
          refine ⟨235576525931284620626422145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157051017287523080417614763 235576525931284620626422145)
          ·
            refine ⟨176682394448463465469816609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235576525931284620626422145 176682394448463465469816609)
            ·
              refine ⟨132511795836347599102362457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176682394448463465469816609 132511795836347599102362457)
              ·
                refine ⟨99383846877260699326771843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132511795836347599102362457 99383846877260699326771843)
                ·
                  refine ⟨149075770315891048990157765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99383846877260699326771843 149075770315891048990157765)
                  ·
                    refine ⟨27951706934229571685654581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149075770315891048990157765 27951706934229571685654581)
                    ·
                      refine ⟨2620472525084022345530117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27951706934229571685654581 2620472525084022345530117)
                      ·
                        rfl

theorem cell23_5103352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_5103352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103352 prefixEnd_5103352 := by exact prefixLift 5103352
  have htrace : WordTrace (prefixWord ++ tailWord_5103352) baseStart_5103352 baseEnd_5103352 := by
    simpa [prefixWord, tailWord_5103352, baseEnd_5103352] using wordTrace_append hprefix tailTrace_5103352
  have hstable : (prefixWord ++ tailWord_5103352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103352).length < 2 ^ (prefixWord ++ tailWord_5103352).sum := by decide
  have hdescent : baseEnd_5103352 < baseStart_5103352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103409 : List Nat := [1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_5103409 : Nat := 118140960795 + 5103409 * 2 ^ 59
def prefixEnd_5103409 : Nat := 4983230072969 + 3 ^ 40 * 5103409 * 2
def baseEnd_5103409 : Nat := 2620501793481328622517355

theorem tailTrace_5103409 : CollatzResearch.WordTrace tailWord_5103409 prefixEnd_5103409 2620501793481328622517355 := by
  unfold tailWord_5103409
  simp only [CollatzResearch.WordTrace]
  refine ⟨186136617968228260711257281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124091078645485507140838187 186136617968228260711257281)
  ·
    refine ⟨139602463476171195533442961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186136617968228260711257281 139602463476171195533442961)
    ·
      refine ⟨104701847607128396650082221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139602463476171195533442961 104701847607128396650082221)
      ·
        refine ⟨39263192852673148743780833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104701847607128396650082221 39263192852673148743780833)
        ·
          refine ⟨29447394639504861557835625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39263192852673148743780833 29447394639504861557835625)
          ·
            refine ⟨22085545979628646168376719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29447394639504861557835625 22085545979628646168376719)
            ·
              refine ⟨33128318969442969252565079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22085545979628646168376719 33128318969442969252565079)
              ·
                refine ⟨49692478454164453878847619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33128318969442969252565079 49692478454164453878847619)
                ·
                  refine ⟨74538717681246680818271429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49692478454164453878847619 74538717681246680818271429)
                  ·
                    refine ⟨13976009565233752653425893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74538717681246680818271429 13976009565233752653425893)
                    ·
                      refine ⟨2620501793481328622517355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13976009565233752653425893 2620501793481328622517355)
                      ·
                        rfl

theorem cell23_5103409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_5103409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103409 prefixEnd_5103409 := by exact prefixLift 5103409
  have htrace : WordTrace (prefixWord ++ tailWord_5103409) baseStart_5103409 baseEnd_5103409 := by
    simpa [prefixWord, tailWord_5103409, baseEnd_5103409] using wordTrace_append hprefix tailTrace_5103409
  have hstable : (prefixWord ++ tailWord_5103409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103409).length < 2 ^ (prefixWord ++ tailWord_5103409).sum := by decide
  have hdescent : baseEnd_5103409 < baseStart_5103409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103429 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 1, 5, 3]
def baseStart_5103429 : Nat := 118140960795 + 5103429 * 2 ^ 59
def prefixEnd_5103429 : Nat := 4983230072969 + 3 ^ 40 * 5103429 * 2
def baseEnd_5103429 : Nat := 2620512063094418544267263

theorem tailTrace_5103429 : CollatzResearch.WordTrace tailWord_5103429 prefixEnd_5103429 2620512063094418544267263 := by
  unfold tailWord_5103429
  simp only [CollatzResearch.WordTrace]
  refine ⟨186137347428155804126985341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124091564952103869417990227 186137347428155804126985341)
  ·
    refine ⟨69801505285558426547619503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186137347428155804126985341 69801505285558426547619503)
    ·
      refine ⟨104702257928337639821429255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69801505285558426547619503 104702257928337639821429255)
      ·
        refine ⟨157053386892506459732143883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104702257928337639821429255 157053386892506459732143883)
        ·
          refine ⟨235580080338759689598215825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157053386892506459732143883 235580080338759689598215825)
          ·
            refine ⟨176685060254069767198661869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235580080338759689598215825 176685060254069767198661869)
            ·
              refine ⟨66256897595276162699498201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176685060254069767198661869 66256897595276162699498201)
              ·
                refine ⟨49692673196457122024623651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66256897595276162699498201 49692673196457122024623651)
                ·
                  refine ⟨74539009794685683036935477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49692673196457122024623651 74539009794685683036935477)
                  ·
                    refine ⟨6988032168251782784712701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74539009794685683036935477 6988032168251782784712701)
                    ·
                      refine ⟨2620512063094418544267263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6988032168251782784712701 2620512063094418544267263)
                      ·
                        rfl

theorem cell23_5103429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5, 3].length) (baseStart_5103429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103429 prefixEnd_5103429 := by exact prefixLift 5103429
  have htrace : WordTrace (prefixWord ++ tailWord_5103429) baseStart_5103429 baseEnd_5103429 := by
    simpa [prefixWord, tailWord_5103429, baseEnd_5103429] using wordTrace_append hprefix tailTrace_5103429
  have hstable : (prefixWord ++ tailWord_5103429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103429).length < 2 ^ (prefixWord ++ tailWord_5103429).sum := by decide
  have hdescent : baseEnd_5103429 < baseStart_5103429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103447 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 2, 2, 2]
def baseStart_5103447 : Nat := 118140960795 + 5103447 * 2 ^ 59
def prefixEnd_5103447 : Nat := 4983230072969 + 3 ^ 40 * 5103447 * 2
def baseEnd_5103447 : Nat := 2620521305746199473842181

theorem tailTrace_5103447 : CollatzResearch.WordTrace tailWord_5103447 prefixEnd_5103447 2620521305746199473842181 := by
  unfold tailWord_5103447
  simp only [CollatzResearch.WordTrace]
  refine ⟨186138003942090593201140595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124092002628060395467427063 186138003942090593201140595)
  ·
    refine ⟨279207005913135889801710893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186138003942090593201140595 279207005913135889801710893)
    ·
      refine ⟨104702627217425958675641585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279207005913135889801710893 104702627217425958675641585)
      ·
        refine ⟨78526970413069469006731189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104702627217425958675641585 78526970413069469006731189)
        ·
          refine ⟨7361903476225262719381049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78526970413069469006731189 7361903476225262719381049)
          ·
            refine ⟨5521427607168947039535787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7361903476225262719381049 5521427607168947039535787)
            ·
              refine ⟨8282141410753420559303681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5521427607168947039535787 8282141410753420559303681)
              ·
                refine ⟨6211606058065065419477761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8282141410753420559303681 6211606058065065419477761)
                ·
                  refine ⟨4658704543548799064608321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6211606058065065419477761 4658704543548799064608321)
                  ·
                    refine ⟨3494028407661599298456241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4658704543548799064608321 3494028407661599298456241)
                    ·
                      refine ⟨2620521305746199473842181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494028407661599298456241 2620521305746199473842181)
                      ·
                        rfl

theorem cell23_5103447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 2, 2].length) (baseStart_5103447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103447 prefixEnd_5103447 := by exact prefixLift 5103447
  have htrace : WordTrace (prefixWord ++ tailWord_5103447) baseStart_5103447 baseEnd_5103447 := by
    simpa [prefixWord, tailWord_5103447, baseEnd_5103447] using wordTrace_append hprefix tailTrace_5103447
  have hstable : (prefixWord ++ tailWord_5103447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103447).length < 2 ^ (prefixWord ++ tailWord_5103447).sum := by decide
  have hdescent : baseEnd_5103447 < baseStart_5103447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103449 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 4, 5]
def baseStart_5103449 : Nat := 118140960795 + 5103449 * 2 ^ 59
def prefixEnd_5103449 : Nat := 4983230072969 + 3 ^ 40 * 5103449 * 2
def baseEnd_5103449 : Nat := 873507444235836155339057

theorem tailTrace_5103449 : CollatzResearch.WordTrace tailWord_5103449 prefixEnd_5103449 873507444235836155339057 := by
  unfold tailWord_5103449
  simp only [CollatzResearch.WordTrace]
  refine ⟨186138076888083347542713401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124092051258722231695142267 186138076888083347542713401)
  ·
    refine ⟨139603557666062510657035051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186138076888083347542713401 139603557666062510657035051)
    ·
      refine ⟨209405336499093765985552577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139603557666062510657035051 209405336499093765985552577)
      ·
        refine ⟨157054002374320324489164433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209405336499093765985552577 157054002374320324489164433)
        ·
          refine ⟨117790501780740243366873325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157054002374320324489164433 117790501780740243366873325)
          ·
            refine ⟨44171438167777591262577497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117790501780740243366873325 44171438167777591262577497)
            ·
              refine ⟨33128578625833193446933123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44171438167777591262577497 33128578625833193446933123)
              ·
                refine ⟨49692867938749790170399685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33128578625833193446933123 49692867938749790170399685)
                ·
                  refine ⟨9317412738515585656949941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49692867938749790170399685 9317412738515585656949941)
                  ·
                    refine ⟨873507444235836155339057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9317412738515585656949941 873507444235836155339057)
                    ·
                      rfl

theorem cell23_5103449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_5103449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103449 prefixEnd_5103449 := by exact prefixLift 5103449
  have htrace : WordTrace (prefixWord ++ tailWord_5103449) baseStart_5103449 baseEnd_5103449 := by
    simpa [prefixWord, tailWord_5103449, baseEnd_5103449] using wordTrace_append hprefix tailTrace_5103449
  have hstable : (prefixWord ++ tailWord_5103449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103449).length < 2 ^ (prefixWord ++ tailWord_5103449).sum := by decide
  have hdescent : baseEnd_5103449 < baseStart_5103449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103509 : List Nat := [1, 3, 2, 1, 1, 3, 1, 3, 8]
def baseStart_5103509 : Nat := 118140960795 + 5103509 * 2 ^ 59
def prefixEnd_5103509 : Nat := 4983230072969 + 3 ^ 40 * 5103509 * 2
def baseEnd_5103509 : Nat := 291172571282975359029655

theorem tailTrace_5103509 : CollatzResearch.WordTrace tailWord_5103509 prefixEnd_5103509 291172571282975359029655 := by
  unfold tailWord_5103509
  simp only [CollatzResearch.WordTrace]
  refine ⟨186140265267865977789897581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124093510178577318526598387 186140265267865977789897581)
  ·
    refine ⟨69802599475449741671211593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186140265267865977789897581 69802599475449741671211593)
    ·
      refine ⟨52351949606587306253408695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69802599475449741671211593 52351949606587306253408695)
      ·
        refine ⟨78527924409880959380113043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52351949606587306253408695 78527924409880959380113043)
        ·
          refine ⟨117791886614821439070169565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78527924409880959380113043 117791886614821439070169565)
          ·
            refine ⟨44171957480558039651313587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117791886614821439070169565 44171957480558039651313587)
            ·
              refine ⟨66257936220837059476970381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44171957480558039651313587 66257936220837059476970381)
              ·
                refine ⟨24846726082813897303863893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66257936220837059476970381 24846726082813897303863893)
                ·
                  refine ⟨291172571282975359029655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24846726082813897303863893 291172571282975359029655)
                  ·
                    rfl

theorem cell23_5103509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_5103509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103509 prefixEnd_5103509 := by exact prefixLift 5103509
  have htrace : WordTrace (prefixWord ++ tailWord_5103509) baseStart_5103509 baseEnd_5103509 := by
    simpa [prefixWord, tailWord_5103509, baseEnd_5103509] using wordTrace_append hprefix tailTrace_5103509
  have hstable : (prefixWord ++ tailWord_5103509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103509).length < 2 ^ (prefixWord ++ tailWord_5103509).sum := by decide
  have hdescent : baseEnd_5103509 < baseStart_5103509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103513 : List Nat := [1, 2, 1, 2, 1, 3, 2, 6, 1, 4]
def baseStart_5103513 : Nat := 118140960795 + 5103513 * 2 ^ 59
def prefixEnd_5103513 : Nat := 4983230072969 + 3 ^ 40 * 5103513 * 2
def baseEnd_5103513 : Nat := 873518398489798738538959

theorem tailTrace_5103513 : CollatzResearch.WordTrace tailWord_5103513 prefixEnd_5103513 873518398489798738538959 := by
  unfold tailWord_5103513
  simp only [CollatzResearch.WordTrace]
  refine ⟨186140411159851486473043193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124093607439900990982028795 186140411159851486473043193)
  ·
    refine ⟨139605308369888614854782395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186140411159851486473043193 139605308369888614854782395)
    ·
      refine ⟨209407962554832922282173593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139605308369888614854782395 209407962554832922282173593)
      ·
        refine ⟨157055971916124691711630195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209407962554832922282173593 157055971916124691711630195)
        ·
          refine ⟨235583957874187037567445293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157055971916124691711630195 235583957874187037567445293)
          ·
            refine ⟨88343984202820139087791985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235583957874187037567445293 88343984202820139087791985)
            ·
              refine ⟨66257988152115104315843989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88343984202820139087791985 66257988152115104315843989)
              ·
                refine ⟨3105843194630395514805187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66257988152115104315843989 3105843194630395514805187)
                ·
                  refine ⟨4658764791945593272207781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105843194630395514805187 4658764791945593272207781)
                  ·
                    refine ⟨873518398489798738538959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4658764791945593272207781 873518398489798738538959)
                    ·
                      rfl

theorem cell23_5103513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 1, 4].length) (baseStart_5103513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103513 prefixEnd_5103513 := by exact prefixLift 5103513
  have htrace : WordTrace (prefixWord ++ tailWord_5103513) baseStart_5103513 baseEnd_5103513 := by
    simpa [prefixWord, tailWord_5103513, baseEnd_5103513] using wordTrace_append hprefix tailTrace_5103513
  have hstable : (prefixWord ++ tailWord_5103513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103513).length < 2 ^ (prefixWord ++ tailWord_5103513).sum := by decide
  have hdescent : baseEnd_5103513 < baseStart_5103513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103563 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 2, 3, 2]
def baseStart_5103563 : Nat := 118140960795 + 5103563 * 2 ^ 59
def prefixEnd_5103563 : Nat := 4983230072969 + 3 ^ 40 * 5103563 * 2
def baseEnd_5103563 : Nat := 2620580869502121019991647

theorem tailTrace_5103563 : CollatzResearch.WordTrace tailWord_5103563 prefixEnd_5103563 2620580869502121019991647 := by
  unfold tailWord_5103563
  simp only [CollatzResearch.WordTrace]
  refine ⟨186142234809670345012363343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124094823206446896674908895 186142234809670345012363343)
  ·
    refine ⟨279213352214505517518545015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186142234809670345012363343 279213352214505517518545015)
    ·
      refine ⟨418820028321758276277817523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279213352214505517518545015 418820028321758276277817523)
      ·
        refine ⟨628230042482637414416726285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418820028321758276277817523 628230042482637414416726285)
        ·
          refine ⟨235586265930989030406272357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 628230042482637414416726285 235586265930989030406272357)
          ·
            refine ⟨44172424862060443201176067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235586265930989030406272357 44172424862060443201176067)
            ·
              refine ⟨66258637293090664801764101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44172424862060443201176067 66258637293090664801764101)
              ·
                refine ⟨12423494492454499650330769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66258637293090664801764101 12423494492454499650330769)
                ·
                  refine ⟨9317620869340874737748077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12423494492454499650330769 9317620869340874737748077)
                  ·
                    refine ⟨3494107826002828026655529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9317620869340874737748077 3494107826002828026655529)
                    ·
                      refine ⟨2620580869502121019991647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494107826002828026655529 2620580869502121019991647)
                      ·
                        rfl

theorem cell23_5103563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 3, 2].length) (baseStart_5103563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103563 prefixEnd_5103563 := by exact prefixLift 5103563
  have htrace : WordTrace (prefixWord ++ tailWord_5103563) baseStart_5103563 baseEnd_5103563 := by
    simpa [prefixWord, tailWord_5103563, baseEnd_5103563] using wordTrace_append hprefix tailTrace_5103563
  have hstable : (prefixWord ++ tailWord_5103563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103563).length < 2 ^ (prefixWord ++ tailWord_5103563).sum := by decide
  have hdescent : baseEnd_5103563 < baseStart_5103563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103576 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_5103576 : Nat := 118140960795 + 5103576 * 2 ^ 59
def prefixEnd_5103576 : Nat := 4983230072969 + 3 ^ 40 * 5103576 * 2
def baseEnd_5103576 : Nat := 2620587544750629469129087

theorem tailTrace_5103576 : CollatzResearch.WordTrace tailWord_5103576 prefixEnd_5103576 2620587544750629469129087 := by
  unfold tailWord_5103576
  simp only [CollatzResearch.WordTrace]
  refine ⟨93071354479311624116293291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124095139305748832155057721 93071354479311624116293291)
  ·
    refine ⟨139607031718967436174439937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93071354479311624116293291 139607031718967436174439937)
    ·
      refine ⟨104705273789225577130829953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139607031718967436174439937 104705273789225577130829953)
      ·
        refine ⟨78528955341919182848122465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104705273789225577130829953 78528955341919182848122465)
        ·
          refine ⟨58896716506439387136091849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78528955341919182848122465 58896716506439387136091849)
          ·
            refine ⟨44172537379829540352068887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58896716506439387136091849 44172537379829540352068887)
            ·
              refine ⟨66258806069744310528103331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44172537379829540352068887 66258806069744310528103331)
              ·
                refine ⟨99388209104616465792154997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66258806069744310528103331 99388209104616465792154997)
                ·
                  refine ⟨9317644603557793668014531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99388209104616465792154997 9317644603557793668014531)
                  ·
                    refine ⟨13976466905336690502021797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9317644603557793668014531 13976466905336690502021797)
                    ·
                      refine ⟨2620587544750629469129087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13976466905336690502021797 2620587544750629469129087)
                      ·
                        rfl

theorem cell23_5103576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_5103576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103576 prefixEnd_5103576 := by exact prefixLift 5103576
  have htrace : WordTrace (prefixWord ++ tailWord_5103576) baseStart_5103576 baseEnd_5103576 := by
    simpa [prefixWord, tailWord_5103576, baseEnd_5103576] using wordTrace_append hprefix tailTrace_5103576
  have hstable : (prefixWord ++ tailWord_5103576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103576).length < 2 ^ (prefixWord ++ tailWord_5103576).sum := by decide
  have hdescent : baseEnd_5103576 < baseStart_5103576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103597 : List Nat := [1, 5, 1, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5103597 : Nat := 118140960795 + 5103597 * 2 ^ 59
def prefixEnd_5103597 : Nat := 4983230072969 + 3 ^ 40 * 5103597 * 2
def baseEnd_5103597 : Nat := 2620598327844373886966491

theorem tailTrace_5103597 : CollatzResearch.WordTrace tailWord_5103597 prefixEnd_5103597 2620598327844373886966491 := by
  unfold tailWord_5103597
  simp only [CollatzResearch.WordTrace]
  refine ⟨186143474891547168819101045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124095649927698112546067363 186143474891547168819101045)
  ·
    refine ⟨17450950771082547076790723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186143474891547168819101045 17450950771082547076790723)
    ·
      refine ⟨26176426156623820615186085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17450950771082547076790723 26176426156623820615186085)
      ·
        refine ⟨4908079904366966365347391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26176426156623820615186085 4908079904366966365347391)
        ·
          refine ⟨7362119856550449548021087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4908079904366966365347391 7362119856550449548021087)
          ·
            refine ⟨11043179784825674322031631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7362119856550449548021087 11043179784825674322031631)
            ·
              refine ⟨16564769677238511483047447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11043179784825674322031631 16564769677238511483047447)
              ·
                refine ⟨24847154515857767224571171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16564769677238511483047447 24847154515857767224571171)
                ·
                  refine ⟨37270731773786650836856757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24847154515857767224571171 37270731773786650836856757)
                  ·
                    refine ⟨3494131103792498515955321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37270731773786650836856757 3494131103792498515955321)
                    ·
                      refine ⟨2620598327844373886966491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494131103792498515955321 2620598327844373886966491)
                      ·
                        rfl

theorem cell23_5103597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5103597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103597 prefixEnd_5103597 := by exact prefixLift 5103597
  have htrace : WordTrace (prefixWord ++ tailWord_5103597) baseStart_5103597 baseEnd_5103597 := by
    simpa [prefixWord, tailWord_5103597, baseEnd_5103597] using wordTrace_append hprefix tailTrace_5103597
  have hstable : (prefixWord ++ tailWord_5103597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103597).length < 2 ^ (prefixWord ++ tailWord_5103597).sum := by decide
  have hdescent : baseEnd_5103597 < baseStart_5103597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103627 : List Nat := [1, 1, 1, 1, 6, 1, 1, 6, 1, 2, 2]
def baseStart_5103627 : Nat := 118140960795 + 5103627 * 2 ^ 59
def prefixEnd_5103627 : Nat := 4983230072969 + 3 ^ 40 * 5103627 * 2
def baseEnd_5103627 : Nat := 2620613732264008769591353

theorem tailTrace_5103627 : CollatzResearch.WordTrace tailWord_5103627 prefixEnd_5103627 2620613732264008769591353 := by
  unfold tailWord_5103627
  simp only [CollatzResearch.WordTrace]
  refine ⟨186144569081438483942693135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124096379387625655961795423 186144569081438483942693135)
  ·
    refine ⟨279216853622157725914039703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186144569081438483942693135 279216853622157725914039703)
    ·
      refine ⟨418825280433236588871059555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279216853622157725914039703 418825280433236588871059555)
      ·
        refine ⟨628237920649854883306589333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418825280433236588871059555 628237920649854883306589333)
        ·
          refine ⟨29448652530461947654996375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 628237920649854883306589333 29448652530461947654996375)
          ·
            refine ⟨44172978795692921482494563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29448652530461947654996375 44172978795692921482494563)
            ·
              refine ⟨66259468193539382223741845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44172978795692921482494563 66259468193539382223741845)
              ·
                refine ⟨3105912571572158541737899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66259468193539382223741845 3105912571572158541737899)
                ·
                  refine ⟨4658868857358237812606849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105912571572158541737899 4658868857358237812606849)
                  ·
                    refine ⟨3494151643018678359455137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4658868857358237812606849 3494151643018678359455137)
                    ·
                      refine ⟨2620613732264008769591353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494151643018678359455137 2620613732264008769591353)
                      ·
                        rfl

theorem cell23_5103627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 1, 2, 2].length) (baseStart_5103627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103627 prefixEnd_5103627 := by exact prefixLift 5103627
  have htrace : WordTrace (prefixWord ++ tailWord_5103627) baseStart_5103627 baseEnd_5103627 := by
    simpa [prefixWord, tailWord_5103627, baseEnd_5103627] using wordTrace_append hprefix tailTrace_5103627
  have hstable : (prefixWord ++ tailWord_5103627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103627).length < 2 ^ (prefixWord ++ tailWord_5103627).sum := by decide
  have hdescent : baseEnd_5103627 < baseStart_5103627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103637 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 2, 4]
def baseStart_5103637 : Nat := 118140960795 + 5103637 * 2 ^ 59
def prefixEnd_5103637 : Nat := 4983230072969 + 3 ^ 40 * 5103637 * 2
def baseEnd_5103637 : Nat := 873539622356851243488769

theorem tailTrace_5103637 : CollatzResearch.WordTrace tailWord_5103637 prefixEnd_5103637 873539622356851243488769 := by
  unfold tailWord_5103637
  simp only [CollatzResearch.WordTrace]
  refine ⟨186144933811402255650557165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124096622540934837100371443 186144933811402255650557165)
  ·
    refine ⟨69804350179275845868958937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186144933811402255650557165 69804350179275845868958937)
    ·
      refine ⟨52353262634456884401719203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69804350179275845868958937 52353262634456884401719203)
      ·
        refine ⟨78529893951685326602578805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52353262634456884401719203 78529893951685326602578805)
        ·
          refine ⟨7362177557970499368991763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78529893951685326602578805 7362177557970499368991763)
          ·
            refine ⟨11043266336955749053487645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7362177557970499368991763 11043266336955749053487645)
            ·
              refine ⟨4141224876358405895057867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11043266336955749053487645 4141224876358405895057867)
              ·
                refine ⟨6211837314537608842586801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141224876358405895057867 6211837314537608842586801)
                ·
                  refine ⟨4658877985903206631940101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6211837314537608842586801 4658877985903206631940101)
                  ·
                    refine ⟨873539622356851243488769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4658877985903206631940101 873539622356851243488769)
                    ·
                      rfl

theorem cell23_5103637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_5103637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103637 prefixEnd_5103637 := by exact prefixLift 5103637
  have htrace : WordTrace (prefixWord ++ tailWord_5103637) baseStart_5103637 baseEnd_5103637 := by
    simpa [prefixWord, tailWord_5103637, baseEnd_5103637] using wordTrace_append hprefix tailTrace_5103637
  have hstable : (prefixWord ++ tailWord_5103637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103637).length < 2 ^ (prefixWord ++ tailWord_5103637).sum := by decide
  have hdescent : baseEnd_5103637 < baseStart_5103637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103678 : List Nat := [4, 2, 1, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_5103678 : Nat := 118140960795 + 5103678 * 2 ^ 59
def prefixEnd_5103678 : Nat := 4983230072969 + 3 ^ 40 * 5103678 * 2
def baseEnd_5103678 : Nat := 2620639919777388070053619

theorem tailTrace_5103678 : CollatzResearch.WordTrace tailWord_5103678 prefixEnd_5103678 2620639919777388070053619 := by
  unfold tailWord_5103678
  simp only [CollatzResearch.WordTrace]
  refine ⟨23268303650531714956599961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124097619469502479768533125 23268303650531714956599961)
  ·
    refine ⟨17451227737898786217449971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23268303650531714956599961 17451227737898786217449971)
    ·
      refine ⟨26176841606848179326174957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17451227737898786217449971 26176841606848179326174957)
      ·
        refine ⟨9816315602568067247315609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26176841606848179326174957 9816315602568067247315609)
        ·
          refine ⟨7362236701926050435486707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9816315602568067247315609 7362236701926050435486707)
          ·
            refine ⟨11043355052889075653230061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7362236701926050435486707 11043355052889075653230061)
            ·
              refine ⟨4141258144833403369961273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11043355052889075653230061 4141258144833403369961273)
              ·
                refine ⟨3105943608625052527470955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4141258144833403369961273 3105943608625052527470955)
                ·
                  refine ⟨4658915412937578791206433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3105943608625052527470955 4658915412937578791206433)
                  ·
                    refine ⟨3494186559703184093404825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4658915412937578791206433 3494186559703184093404825)
                    ·
                      refine ⟨2620639919777388070053619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494186559703184093404825 2620639919777388070053619)
                      ·
                        rfl

theorem cell23_5103678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_5103678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103678 prefixEnd_5103678 := by exact prefixLift 5103678
  have htrace : WordTrace (prefixWord ++ tailWord_5103678) baseStart_5103678 baseEnd_5103678 := by
    simpa [prefixWord, tailWord_5103678, baseEnd_5103678] using wordTrace_append hprefix tailTrace_5103678
  have hstable : (prefixWord ++ tailWord_5103678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103678).length < 2 ^ (prefixWord ++ tailWord_5103678).sum := by decide
  have hdescent : baseEnd_5103678 < baseStart_5103678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103683 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 5, 4, 2]
def baseStart_5103683 : Nat := 118140960795 + 5103683 * 2 ^ 59
def prefixEnd_5103683 : Nat := 4983230072969 + 3 ^ 40 * 5103683 * 2
def baseEnd_5103683 : Nat := 2620642487180660550491095

theorem tailTrace_5103683 : CollatzResearch.WordTrace tailWord_5103683 prefixEnd_5103683 2620642487180660550491095 := by
  unfold tailWord_5103683
  simp only [CollatzResearch.WordTrace]
  refine ⟨186146611569235605506731703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124097741046157070337821135 186146611569235605506731703)
  ·
    refine ⟨279219917353853408260097555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186146611569235605506731703 279219917353853408260097555)
    ·
      refine ⟨418829876030780112390146333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279219917353853408260097555 418829876030780112390146333)
      ·
        refine ⟨157061203511542542146304875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 418829876030780112390146333 157061203511542542146304875)
        ·
          refine ⟨235591805267313813219457313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157061203511542542146304875 235591805267313813219457313)
          ·
            refine ⟨176693853950485359914592985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235591805267313813219457313 176693853950485359914592985)
            ·
              refine ⟨132520390462864019935944739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176693853950485359914592985 132520390462864019935944739)
              ·
                refine ⟨198780585694296029903917109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132520390462864019935944739 198780585694296029903917109)
                ·
                  refine ⟨18635679908840252803492229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 198780585694296029903917109 18635679908840252803492229)
                  ·
                    refine ⟨3494189982907547400654793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18635679908840252803492229 3494189982907547400654793)
                    ·
                      refine ⟨2620642487180660550491095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494189982907547400654793 2620642487180660550491095)
                      ·
                        rfl

theorem cell23_5103683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 4, 2].length) (baseStart_5103683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103683 prefixEnd_5103683 := by exact prefixLift 5103683
  have htrace : WordTrace (prefixWord ++ tailWord_5103683) baseStart_5103683 baseEnd_5103683 := by
    simpa [prefixWord, tailWord_5103683, baseEnd_5103683] using wordTrace_append hprefix tailTrace_5103683
  have hstable : (prefixWord ++ tailWord_5103683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103683).length < 2 ^ (prefixWord ++ tailWord_5103683).sum := by decide
  have hdescent : baseEnd_5103683 < baseStart_5103683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103693 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5103693 : Nat := 118140960795 + 5103693 * 2 ^ 59
def prefixEnd_5103693 : Nat := 4983230072969 + 3 ^ 40 * 5103693 * 2
def baseEnd_5103693 : Nat := 873549207329068503788683

theorem tailTrace_5103693 : CollatzResearch.WordTrace tailWord_5103693 prefixEnd_5103693 873549207329068503788683 := by
  unfold tailWord_5103693
  simp only [CollatzResearch.WordTrace]
  refine ⟨186146976299199377214595733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124097984199466251476397155 186146976299199377214595733)
  ·
    refine ⟨8725639514024970806934175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 186146976299199377214595733 8725639514024970806934175)
    ·
      refine ⟨13088459271037456210401263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8725639514024970806934175 13088459271037456210401263)
      ·
        refine ⟨19632688906556184315601895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13088459271037456210401263 19632688906556184315601895)
        ·
          refine ⟨29449033359834276473402843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19632688906556184315601895 29449033359834276473402843)
          ·
            refine ⟨44173550039751414710104265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29449033359834276473402843 44173550039751414710104265)
            ·
              refine ⟨33130162529813561032578199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44173550039751414710104265 33130162529813561032578199)
              ·
                refine ⟨49695243794720341548867299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33130162529813561032578199 49695243794720341548867299)
                ·
                  refine ⟨74542865692080512323300949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49695243794720341548867299 74542865692080512323300949)
                  ·
                    refine ⟨873549207329068503788683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74542865692080512323300949 873549207329068503788683)
                    ·
                      rfl

theorem cell23_5103693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5103693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103693 prefixEnd_5103693 := by exact prefixLift 5103693
  have htrace : WordTrace (prefixWord ++ tailWord_5103693) baseStart_5103693 baseEnd_5103693 := by
    simpa [prefixWord, tailWord_5103693, baseEnd_5103693] using wordTrace_append hprefix tailTrace_5103693
  have hstable : (prefixWord ++ tailWord_5103693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103693).length < 2 ^ (prefixWord ++ tailWord_5103693).sum := by decide
  have hdescent : baseEnd_5103693 < baseStart_5103693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103694 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3]
def baseStart_5103694 : Nat := 118140960795 + 5103694 * 2 ^ 59
def prefixEnd_5103694 : Nat := 4983230072969 + 3 ^ 40 * 5103694 * 2
def baseEnd_5103694 : Nat := 2620648135467860007453545

theorem tailTrace_5103694 : CollatzResearch.WordTrace tailWord_5103694 prefixEnd_5103694 2620648135467860007453545 := by
  unfold tailWord_5103694
  simp only [CollatzResearch.WordTrace]
  refine ⟨23268376596524469298172767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124098008514797169590254757 23268376596524469298172767)
  ·
    refine ⟨34902564894786703947259151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23268376596524469298172767 34902564894786703947259151)
    ·
      refine ⟨52353847342180055920888727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34902564894786703947259151 52353847342180055920888727)
      ·
        refine ⟨78530771013270083881333091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52353847342180055920888727 78530771013270083881333091)
        ·
          refine ⟨117796156519905125821999637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78530771013270083881333091 117796156519905125821999637)
          ·
            refine ⟨5521694836870552772906233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117796156519905125821999637 5521694836870552772906233)
            ·
              refine ⟨4141271127652914579679675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5521694836870552772906233 4141271127652914579679675)
              ·
                refine ⟨6211906691479371869519513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141271127652914579679675 6211906691479371869519513)
                ·
                  refine ⟨4658930018609528902139635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6211906691479371869519513 4658930018609528902139635)
                  ·
                    refine ⟨6988395027914293353209453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4658930018609528902139635 6988395027914293353209453)
                    ·
                      refine ⟨2620648135467860007453545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6988395027914293353209453 2620648135467860007453545)
                      ·
                        rfl

theorem cell23_5103694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_5103694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103694 prefixEnd_5103694 := by exact prefixLift 5103694
  have htrace : WordTrace (prefixWord ++ tailWord_5103694) baseStart_5103694 baseEnd_5103694 := by
    simpa [prefixWord, tailWord_5103694, baseEnd_5103694] using wordTrace_append hprefix tailTrace_5103694
  have hstable : (prefixWord ++ tailWord_5103694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103694).length < 2 ^ (prefixWord ++ tailWord_5103694).sum := by decide
  have hdescent : baseEnd_5103694 < baseStart_5103694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103700 : List Nat := [2, 4, 1, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_5103700 : Nat := 118140960795 + 5103700 * 2 ^ 59
def prefixEnd_5103700 : Nat := 4983230072969 + 3 ^ 40 * 5103700 * 2
def baseEnd_5103700 : Nat := 2620651216351786983978517

theorem tailTrace_5103700 : CollatzResearch.WordTrace tailWord_5103700 prefixEnd_5103700 2620651216351786983978517 := by
  unfold tailWord_5103700
  simp only [CollatzResearch.WordTrace]
  refine ⟨93073615805087008705050277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124098154406782678273400369 93073615805087008705050277)
  ·
    refine ⟨17451302963453814132196927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93073615805087008705050277 17451302963453814132196927)
    ·
      refine ⟨26176954445180721198295391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17451302963453814132196927 26176954445180721198295391)
      ·
        refine ⟨39265431667771081797443087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26176954445180721198295391 39265431667771081797443087)
        ·
          refine ⟨58898147501656622696164631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39265431667771081797443087 58898147501656622696164631)
          ·
            refine ⟨88347221252484934044246947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58898147501656622696164631 88347221252484934044246947)
            ·
              refine ⟨132520831878727401066370421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88347221252484934044246947 132520831878727401066370421)
              ·
                refine ⟨12423827988630693849972227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132520831878727401066370421 12423827988630693849972227)
                ·
                  refine ⟨18635741982946040774958341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12423827988630693849972227 18635741982946040774958341)
                  ·
                    refine ⟨3494201621802382645304689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18635741982946040774958341 3494201621802382645304689)
                    ·
                      refine ⟨2620651216351786983978517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494201621802382645304689 2620651216351786983978517)
                      ·
                        rfl

theorem cell23_5103700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_5103700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103700 prefixEnd_5103700 := by exact prefixLift 5103700
  have htrace : WordTrace (prefixWord ++ tailWord_5103700) baseStart_5103700 baseEnd_5103700 := by
    simpa [prefixWord, tailWord_5103700, baseEnd_5103700] using wordTrace_append hprefix tailTrace_5103700
  have hstable : (prefixWord ++ tailWord_5103700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103700).length < 2 ^ (prefixWord ++ tailWord_5103700).sum := by decide
  have hdescent : baseEnd_5103700 < baseStart_5103700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103706 : List Nat := [3, 1, 1, 2, 1, 1, 4, 1, 9]
def baseStart_5103706 : Nat := 118140960795 + 5103706 * 2 ^ 59
def prefixEnd_5103706 : Nat := 4983230072969 + 3 ^ 40 * 5103706 * 2
def baseEnd_5103706 : Nat := 291183810803968217833721

theorem tailTrace_5103706 : CollatzResearch.WordTrace tailWord_5103706 prefixEnd_5103706 291183810803968217833721 := by
  unfold tailWord_5103706
  simp only [CollatzResearch.WordTrace]
  refine ⟨46536862612038070108704743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124098300298768186956545981 46536862612038070108704743)
  ·
    refine ⟨69805293918057105163057115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46536862612038070108704743 69805293918057105163057115)
    ·
      refine ⟨104707940877085657744585673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69805293918057105163057115 104707940877085657744585673)
      ·
        refine ⟨78530955657814243308439255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104707940877085657744585673 78530955657814243308439255)
        ·
          refine ⟨117796433486721364962658883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78530955657814243308439255 117796433486721364962658883)
          ·
            refine ⟨176694650230082047443988325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117796433486721364962658883 176694650230082047443988325)
            ·
              refine ⟨33130246918140383895747811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176694650230082047443988325 33130246918140383895747811)
              ·
                refine ⟨49695370377210575843621717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33130246918140383895747811 49695370377210575843621717)
                ·
                  refine ⟨291183810803968217833721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 49695370377210575843621717 291183810803968217833721)
                  ·
                    rfl

theorem cell23_5103706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_5103706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103706 prefixEnd_5103706 := by exact prefixLift 5103706
  have htrace : WordTrace (prefixWord ++ tailWord_5103706) baseStart_5103706 baseEnd_5103706 := by
    simpa [prefixWord, tailWord_5103706, baseEnd_5103706] using wordTrace_append hprefix tailTrace_5103706
  have hstable : (prefixWord ++ tailWord_5103706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103706).length < 2 ^ (prefixWord ++ tailWord_5103706).sum := by decide
  have hdescent : baseEnd_5103706 < baseStart_5103706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103734 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2]
def baseStart_5103734 : Nat := 118140960795 + 5103734 * 2 ^ 59
def prefixEnd_5103734 : Nat := 4983230072969 + 3 ^ 40 * 5103734 * 2
def baseEnd_5103734 : Nat := 2620668674694039850953361

theorem tailTrace_5103734 : CollatzResearch.WordTrace tailWord_5103734 prefixEnd_5103734 2620668674694039850953361 := by
  unfold tailWord_5103734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11634279480753177576052391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124098981128033894144558837 11634279480753177576052391)
  ·
    refine ⟨17451419221129766364078587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11634279480753177576052391 17451419221129766364078587)
    ·
      refine ⟨26177128831694649546117881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17451419221129766364078587 26177128831694649546117881)
      ·
        refine ⟨19632846623770987159588411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26177128831694649546117881 19632846623770987159588411)
        ·
          refine ⟨29449269935656480739382617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19632846623770987159588411 29449269935656480739382617)
          ·
            refine ⟨22086952451742360554536963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29449269935656480739382617 22086952451742360554536963)
            ·
              refine ⟨33130428677613540831805445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22086952451742360554536963 33130428677613540831805445)
              ·
                refine ⟨6211955377052538905963521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33130428677613540831805445 6211955377052538905963521)
                ·
                  refine ⟨4658966532789404179472641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6211955377052538905963521 4658966532789404179472641)
                  ·
                    refine ⟨3494224899592053134604481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4658966532789404179472641 3494224899592053134604481)
                    ·
                      refine ⟨2620668674694039850953361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494224899592053134604481 2620668674694039850953361)
                      ·
                        rfl

theorem cell23_5103734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_5103734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103734 prefixEnd_5103734 := by exact prefixLift 5103734
  have htrace : WordTrace (prefixWord ++ tailWord_5103734) baseStart_5103734 baseEnd_5103734 := by
    simpa [prefixWord, tailWord_5103734, baseEnd_5103734] using wordTrace_append hprefix tailTrace_5103734
  have hstable : (prefixWord ++ tailWord_5103734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103734).length < 2 ^ (prefixWord ++ tailWord_5103734).sum := by decide
  have hdescent : baseEnd_5103734 < baseStart_5103734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103736 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 3, 7]
def baseStart_5103736 : Nat := 118140960795 + 5103736 * 2 ^ 59
def prefixEnd_5103736 : Nat := 4983230072969 + 3 ^ 40 * 5103736 * 2
def baseEnd_5103736 : Nat := 873556567218449614376117

theorem tailTrace_5103736 : CollatzResearch.WordTrace tailWord_5103736 prefixEnd_5103736 873556567218449614376117 := by
  unfold tailWord_5103736
  simp only [CollatzResearch.WordTrace]
  refine ⟨93074272319021797779205531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124099029758695730372274041 93074272319021797779205531)
  ·
    refine ⟨139611408478532696668808297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93074272319021797779205531 139611408478532696668808297)
    ·
      refine ⟨104708556358899522501606223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139611408478532696668808297 104708556358899522501606223)
      ·
        refine ⟨157062834538349283752409335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104708556358899522501606223 157062834538349283752409335)
        ·
          refine ⟨235594251807523925628614003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157062834538349283752409335 235594251807523925628614003)
          ·
            refine ⟨353391377711285888442921005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235594251807523925628614003 353391377711285888442921005)
            ·
              refine ⟨132521766641732208166095377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 353391377711285888442921005 132521766641732208166095377)
              ·
                refine ⟨99391324981299156124571533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132521766641732208166095377 99391324981299156124571533)
                ·
                  refine ⟨37271746867987183546714325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99391324981299156124571533 37271746867987183546714325)
                  ·
                    refine ⟨873556567218449614376117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37271746867987183546714325 873556567218449614376117)
                    ·
                      rfl

theorem cell23_5103736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_5103736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103736 prefixEnd_5103736 := by exact prefixLift 5103736
  have htrace : WordTrace (prefixWord ++ tailWord_5103736) baseStart_5103736 baseEnd_5103736 := by
    simpa [prefixWord, tailWord_5103736, baseEnd_5103736] using wordTrace_append hprefix tailTrace_5103736
  have hstable : (prefixWord ++ tailWord_5103736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103736).length < 2 ^ (prefixWord ++ tailWord_5103736).sum := by decide
  have hdescent : baseEnd_5103736 < baseStart_5103736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103740 : List Nat := [2, 2, 2, 1, 1, 5, 1, 4, 5]
def baseStart_5103740 : Nat := 118140960795 + 5103740 * 2 ^ 59
def prefixEnd_5103740 : Nat := 4983230072969 + 3 ^ 40 * 5103740 * 2
def baseEnd_5103740 : Nat := 291185750619774091942037

theorem tailTrace_5103740 : CollatzResearch.WordTrace tailWord_5103740 prefixEnd_5103740 291185750619774091942037 := by
  unfold tailWord_5103740
  simp only [CollatzResearch.WordTrace]
  refine ⟨93074345265014552120778337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124099127020019402827704449 93074345265014552120778337)
  ·
    refine ⟨69805758948760914090583753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93074345265014552120778337 69805758948760914090583753)
    ·
      refine ⟨52354319211570685567937815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69805758948760914090583753 52354319211570685567937815)
      ·
        refine ⟨78531478817356028351906723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52354319211570685567937815 78531478817356028351906723)
        ·
          refine ⟨117797218226034042527860085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78531478817356028351906723 117797218226034042527860085)
          ·
            refine ⟨11043489208690691486986883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117797218226034042527860085 11043489208690691486986883)
            ·
              refine ⟨16565233813036037230480325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11043489208690691486986883 16565233813036037230480325)
              ·
                refine ⟨3105981339944256980715061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16565233813036037230480325 3105981339944256980715061)
                ·
                  refine ⟨291185750619774091942037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3105981339944256980715061 291185750619774091942037)
                  ·
                    rfl

theorem cell23_5103740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 5].length) (baseStart_5103740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103740 prefixEnd_5103740 := by exact prefixLift 5103740
  have htrace : WordTrace (prefixWord ++ tailWord_5103740) baseStart_5103740 baseEnd_5103740 := by
    simpa [prefixWord, tailWord_5103740, baseEnd_5103740] using wordTrace_append hprefix tailTrace_5103740
  have hstable : (prefixWord ++ tailWord_5103740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103740).length < 2 ^ (prefixWord ++ tailWord_5103740).sum := by decide
  have hdescent : baseEnd_5103740 < baseStart_5103740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103770 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_5103770 : Nat := 118140960795 + 5103770 * 2 ^ 59
def prefixEnd_5103770 : Nat := 4983230072969 + 3 ^ 40 * 5103770 * 2
def baseEnd_5103770 : Nat := 873562386665867236701065

theorem tailTrace_5103770 : CollatzResearch.WordTrace tailWord_5103770 prefixEnd_5103770 873562386665867236701065 := by
  unfold tailWord_5103770
  simp only [CollatzResearch.WordTrace]
  refine ⟨46537446179980104841287191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124099856479946946243432509 46537446179980104841287191)
  ·
    refine ⟨69806169269970157261930787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46537446179980104841287191 69806169269970157261930787)
    ·
      refine ⟨104709253904955235892896181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69806169269970157261930787 104709253904955235892896181)
      ·
        refine ⟨9816492553589553364959017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 104709253904955235892896181 9816492553589553364959017)
        ·
          refine ⟨7362369415192165023719263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9816492553589553364959017 7362369415192165023719263)
          ·
            refine ⟨11043554122788247535578895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7362369415192165023719263 11043554122788247535578895)
            ·
              refine ⟨16565331184182371303368343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11043554122788247535578895 16565331184182371303368343)
              ·
                refine ⟨24847996776273556955052515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16565331184182371303368343 24847996776273556955052515)
                ·
                  refine ⟨37271995164410335432578773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24847996776273556955052515 37271995164410335432578773)
                  ·
                    refine ⟨873562386665867236701065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37271995164410335432578773 873562386665867236701065)
                    ·
                      rfl

theorem cell23_5103770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_5103770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103770 prefixEnd_5103770 := by exact prefixLift 5103770
  have htrace : WordTrace (prefixWord ++ tailWord_5103770) baseStart_5103770 baseEnd_5103770 := by
    simpa [prefixWord, tailWord_5103770, baseEnd_5103770] using wordTrace_append hprefix tailTrace_5103770
  have hstable : (prefixWord ++ tailWord_5103770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103770).length < 2 ^ (prefixWord ++ tailWord_5103770).sum := by decide
  have hdescent : baseEnd_5103770 < baseStart_5103770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103774 : List Nat := [4, 3, 1, 1, 3, 1, 2, 3, 5]
def baseStart_5103774 : Nat := 118140960795 + 5103774 * 2 ^ 59
def prefixEnd_5103774 : Nat := 4983230072969 + 3 ^ 40 * 5103774 * 2
def baseEnd_5103774 : Nat := 291187690435579966050353

theorem tailTrace_5103774 : CollatzResearch.WordTrace tailWord_5103774 prefixEnd_5103774 291187690435579966050353 := by
  unfold tailWord_5103774
  simp only [CollatzResearch.WordTrace]
  refine ⟨23268741326488241006036797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124099953741270618698862917 23268741326488241006036797)
  ·
    refine ⟨8725777997433090377263799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23268741326488241006036797 8725777997433090377263799)
    ·
      refine ⟨13088666996149635565895699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8725777997433090377263799 13088666996149635565895699)
      ·
        refine ⟨19633000494224453348843549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13088666996149635565895699 19633000494224453348843549)
        ·
          refine ⟨7362375185334170005816331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19633000494224453348843549 7362375185334170005816331)
          ·
            refine ⟨11043562778001255008724497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7362375185334170005816331 11043562778001255008724497)
            ·
              refine ⟨8282672083500941256543373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11043562778001255008724497 8282672083500941256543373)
              ·
                refine ⟨3106002031312852971203765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8282672083500941256543373 3106002031312852971203765)
                ·
                  refine ⟨291187690435579966050353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3106002031312852971203765 291187690435579966050353)
                  ·
                    rfl

theorem cell23_5103774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_5103774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103774 prefixEnd_5103774 := by exact prefixLift 5103774
  have htrace : WordTrace (prefixWord ++ tailWord_5103774) baseStart_5103774 baseEnd_5103774 := by
    simpa [prefixWord, tailWord_5103774, baseEnd_5103774] using wordTrace_append hprefix tailTrace_5103774
  have hstable : (prefixWord ++ tailWord_5103774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103774).length < 2 ^ (prefixWord ++ tailWord_5103774).sum := by decide
  have hdescent : baseEnd_5103774 < baseStart_5103774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103800 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 3, 4]
def baseStart_5103800 : Nat := 118140960795 + 5103800 * 2 ^ 59
def prefixEnd_5103800 : Nat := 4983230072969 + 3 ^ 40 * 5103800 * 2
def baseEnd_5103800 : Nat := 873567521472412197576019

theorem tailTrace_5103800 : CollatzResearch.WordTrace tailWord_5103800 prefixEnd_5103800 873567521472412197576019 := by
  unfold tailWord_5103800
  simp only [CollatzResearch.WordTrace]
  refine ⟨93075439454905867244370427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124100585939874489659160569 93075439454905867244370427)
  ·
    refine ⟨139613159182358800866555641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93075439454905867244370427 139613159182358800866555641)
    ·
      refine ⟨104709869386769100649916731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139613159182358800866555641 104709869386769100649916731)
      ·
        refine ⟨157064804080153650974875097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104709869386769100649916731 157064804080153650974875097)
        ·
          refine ⟨117798603060115238231156323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157064804080153650974875097 117798603060115238231156323)
          ·
            refine ⟨176697904590172857346734485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117798603060115238231156323 176697904590172857346734485)
            ·
              refine ⟨8282714277664352688128179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 176697904590172857346734485 8282714277664352688128179)
              ·
                refine ⟨12424071416496529032192269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8282714277664352688128179 12424071416496529032192269)
                ·
                  refine ⟨4659026781186198387072101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12424071416496529032192269 4659026781186198387072101)
                  ·
                    refine ⟨873567521472412197576019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659026781186198387072101 873567521472412197576019)
                    ·
                      rfl

theorem cell23_5103800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_5103800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103800 prefixEnd_5103800 := by exact prefixLift 5103800
  have htrace : WordTrace (prefixWord ++ tailWord_5103800) baseStart_5103800 baseEnd_5103800 := by
    simpa [prefixWord, tailWord_5103800, baseEnd_5103800] using wordTrace_append hprefix tailTrace_5103800
  have hstable : (prefixWord ++ tailWord_5103800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103800).length < 2 ^ (prefixWord ++ tailWord_5103800).sum := by decide
  have hdescent : baseEnd_5103800 < baseStart_5103800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103813 : List Nat := [1, 3, 1, 1, 1, 1, 4, 5, 6]
def baseStart_5103813 : Nat := 118140960795 + 5103813 * 2 ^ 59
def prefixEnd_5103813 : Nat := 4983230072969 + 3 ^ 40 * 5103813 * 2
def baseEnd_5103813 : Nat := 291189915518416115762833

theorem tailTrace_5103813 : CollatzResearch.WordTrace tailWord_5103813 prefixEnd_5103813 291189915518416115762833 := by
  unfold tailWord_5103813
  simp only [CollatzResearch.WordTrace]
  refine ⟨186151353058764637708964093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124100902039176425139309395 186151353058764637708964093)
  ·
    refine ⟨69806757397036739140861535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186151353058764637708964093 69806757397036739140861535)
    ·
      refine ⟨104710136095555108711292303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69806757397036739140861535 104710136095555108711292303)
      ·
        refine ⟨157065204143332663066938455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104710136095555108711292303 157065204143332663066938455)
        ·
          refine ⟨235597806214998994600407683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157065204143332663066938455 235597806214998994600407683)
          ·
            refine ⟨353396709322498491900611525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235597806214998994600407683 353396709322498491900611525)
            ·
              refine ⟨66261882997968467231364661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 353396709322498491900611525 66261882997968467231364661)
              ·
                refine ⟨6212051531059543802940437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66261882997968467231364661 6212051531059543802940437)
                ·
                  refine ⟨291189915518416115762833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6212051531059543802940437 291189915518416115762833)
                  ·
                    rfl

theorem cell23_5103813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 6].length) (baseStart_5103813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103813 prefixEnd_5103813 := by exact prefixLift 5103813
  have htrace : WordTrace (prefixWord ++ tailWord_5103813) baseStart_5103813 baseEnd_5103813 := by
    simpa [prefixWord, tailWord_5103813, baseEnd_5103813] using wordTrace_append hprefix tailTrace_5103813
  have hstable : (prefixWord ++ tailWord_5103813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103813).length < 2 ^ (prefixWord ++ tailWord_5103813).sum := by decide
  have hdescent : baseEnd_5103813 < baseStart_5103813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103823 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 3]
def baseStart_5103823 : Nat := 118140960795 + 5103823 * 2 ^ 59
def prefixEnd_5103823 : Nat := 4983230072969 + 3 ^ 40 * 5103823 * 2
def baseEnd_5103823 : Nat := 2620714374472290002740451

theorem tailTrace_5103823 : CollatzResearch.WordTrace tailWord_5103823 prefixEnd_5103823 2620714374472290002740451 := by
  unfold tailWord_5103823
  simp only [CollatzResearch.WordTrace]
  refine ⟨186151717788728409416828123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124101145192485606277885415 186151717788728409416828123)
  ·
    refine ⟨279227576683092614125242185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186151717788728409416828123 279227576683092614125242185)
    ·
      refine ⟨209420682512319460593931639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279227576683092614125242185 209420682512319460593931639)
      ·
        refine ⟨314131023768479190890897459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209420682512319460593931639 314131023768479190890897459)
        ·
          refine ⟨471196535652718786336346189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314131023768479190890897459 471196535652718786336346189)
          ·
            refine ⟨176698700869769544876129821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 471196535652718786336346189 176698700869769544876129821)
            ·
              refine ⟨66262012826163579328548683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176698700869769544876129821 66262012826163579328548683)
              ·
                refine ⟨99393019239245368992823025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66262012826163579328548683 99393019239245368992823025)
                ·
                  refine ⟨74544764429434026744617269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99393019239245368992823025 74544764429434026744617269)
                  ·
                    refine ⟨6988571665259440007307869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74544764429434026744617269 6988571665259440007307869)
                    ·
                      refine ⟨2620714374472290002740451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6988571665259440007307869 2620714374472290002740451)
                      ·
                        rfl

theorem cell23_5103823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 3].length) (baseStart_5103823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103823 prefixEnd_5103823 := by exact prefixLift 5103823
  have htrace : WordTrace (prefixWord ++ tailWord_5103823) baseStart_5103823 baseEnd_5103823 := by
    simpa [prefixWord, tailWord_5103823, baseEnd_5103823] using wordTrace_append hprefix tailTrace_5103823
  have hstable : (prefixWord ++ tailWord_5103823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103823).length < 2 ^ (prefixWord ++ tailWord_5103823).sum := by decide
  have hdescent : baseEnd_5103823 < baseStart_5103823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103857 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 3, 1, 3]
def baseStart_5103857 : Nat := 118140960795 + 5103857 * 2 ^ 59
def prefixEnd_5103857 : Nat := 4983230072969 + 3 ^ 40 * 5103857 * 2
def baseEnd_5103857 : Nat := 2620731832814542869715295

theorem tailTrace_5103857 : CollatzResearch.WordTrace tailWord_5103857 prefixEnd_5103857 2620731832814542869715295 := by
  unfold tailWord_5103857
  simp only [CollatzResearch.WordTrace]
  refine ⟨186152957870605233223565825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124101971913736822149043883 186152957870605233223565825)
  ·
    refine ⟨139614718402953924917674369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186152957870605233223565825 139614718402953924917674369)
    ·
      refine ⟨104711038802215443688255777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139614718402953924917674369 104711038802215443688255777)
      ·
        refine ⟨78533279101661582766191833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104711038802215443688255777 78533279101661582766191833)
        ·
          refine ⟨58899959326246187074643875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78533279101661582766191833 58899959326246187074643875)
          ·
            refine ⟨88349938989369280611965813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58899959326246187074643875 88349938989369280611965813)
            ·
              refine ⟨8282806780253370057371795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88349938989369280611965813 8282806780253370057371795)
              ·
                refine ⟨12424210170380055086057693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8282806780253370057371795 12424210170380055086057693)
                ·
                  refine ⟨4659078813892520657271635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12424210170380055086057693 4659078813892520657271635)
                  ·
                    refine ⟨6988618220838780985907453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4659078813892520657271635 6988618220838780985907453)
                    ·
                      refine ⟨2620731832814542869715295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6988618220838780985907453 2620731832814542869715295)
                      ·
                        rfl

theorem cell23_5103857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_5103857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103857 prefixEnd_5103857 := by exact prefixLift 5103857
  have htrace : WordTrace (prefixWord ++ tailWord_5103857) baseStart_5103857 baseEnd_5103857 := by
    simpa [prefixWord, tailWord_5103857, baseEnd_5103857] using wordTrace_append hprefix tailTrace_5103857
  have hstable : (prefixWord ++ tailWord_5103857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103857).length < 2 ^ (prefixWord ++ tailWord_5103857).sum := by decide
  have hdescent : baseEnd_5103857 < baseStart_5103857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103903 : List Nat := [1, 1, 2, 4, 3, 12]
def baseStart_5103903 : Nat := 118140960795 + 5103903 * 2 ^ 59
def prefixEnd_5103903 : Nat := 4983230072969 + 3 ^ 40 * 5103903 * 2
def baseEnd_5103903 : Nat := 10785001863887447282881

theorem tailTrace_5103903 : CollatzResearch.WordTrace tailWord_5103903 prefixEnd_5103903 10785001863887447282881 := by
  unfold tailWord_5103903
  simp only [CollatzResearch.WordTrace]
  refine ⟨186154635628438583079740363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124103090418959055386493575 186154635628438583079740363)
  ·
    refine ⟨279231953442657874619610545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186154635628438583079740363 279231953442657874619610545)
    ·
      refine ⟨209423965081993405964707909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279231953442657874619610545 209423965081993405964707909)
      ·
        refine ⟨39266993452873763618382733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209423965081993405964707909 39266993452873763618382733)
        ·
          refine ⟨14725122544827661356893525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39266993452873763618382733 14725122544827661356893525)
          ·
            refine ⟨10785001863887447282881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14725122544827661356893525 10785001863887447282881)
            ·
              rfl

theorem cell23_5103903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 12].length) (baseStart_5103903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103903 prefixEnd_5103903 := by exact prefixLift 5103903
  have htrace : WordTrace (prefixWord ++ tailWord_5103903) baseStart_5103903 baseEnd_5103903 := by
    simpa [prefixWord, tailWord_5103903, baseEnd_5103903] using wordTrace_append hprefix tailTrace_5103903
  have hstable : (prefixWord ++ tailWord_5103903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103903).length < 2 ^ (prefixWord ++ tailWord_5103903).sum := by decide
  have hdescent : baseEnd_5103903 < baseStart_5103903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103907 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 2, 4]
def baseStart_5103907 : Nat := 118140960795 + 5103907 * 2 ^ 59
def prefixEnd_5103907 : Nat := 4983230072969 + 3 ^ 40 * 5103907 * 2
def baseEnd_5103907 : Nat := 873585835615755891363355

theorem tailTrace_5103907 : CollatzResearch.WordTrace tailWord_5103907 prefixEnd_5103907 873585835615755891363355 := by
  unfold tailWord_5103907
  simp only [CollatzResearch.WordTrace]
  refine ⟨186154781520424091762885975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124103187680282727841923983 186154781520424091762885975)
  ·
    refine ⟨279232172280636137644328963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186154781520424091762885975 279232172280636137644328963)
    ·
      refine ⟨418848258420954206466493445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279232172280636137644328963 418848258420954206466493445)
      ·
        refine ⟨78534048453928913712467521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 418848258420954206466493445 78534048453928913712467521)
        ·
          refine ⟨58900536340446685284350641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78534048453928913712467521 58900536340446685284350641)
          ·
            refine ⟨44175402255335013963262981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58900536340446685284350641 44175402255335013963262981)
            ·
              refine ⟨8282887922875315118111809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44175402255335013963262981 8282887922875315118111809)
              ·
                refine ⟨6212165942156486338583857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8282887922875315118111809 6212165942156486338583857)
                ·
                  refine ⟨4659124456617364753937893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212165942156486338583857 4659124456617364753937893)
                  ·
                    refine ⟨873585835615755891363355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659124456617364753937893 873585835615755891363355)
                    ·
                      rfl

theorem cell23_5103907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 4].length) (baseStart_5103907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103907 prefixEnd_5103907 := by exact prefixLift 5103907
  have htrace : WordTrace (prefixWord ++ tailWord_5103907) baseStart_5103907 baseEnd_5103907 := by
    simpa [prefixWord, tailWord_5103907, baseEnd_5103907] using wordTrace_append hprefix tailTrace_5103907
  have hstable : (prefixWord ++ tailWord_5103907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103907).length < 2 ^ (prefixWord ++ tailWord_5103907).sum := by decide
  have hdescent : baseEnd_5103907 < baseStart_5103907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103908 : List Nat := [2, 3, 1, 3, 1, 4, 2, 2, 1, 1, 3]
def baseStart_5103908 : Nat := 118140960795 + 5103908 * 2 ^ 59
def prefixEnd_5103908 : Nat := 4983230072969 + 3 ^ 40 * 5103908 * 2
def baseEnd_5103908 : Nat := 2620758020327922170177561

theorem tailTrace_5103908 : CollatzResearch.WordTrace tailWord_5103908 prefixEnd_5103908 2620758020327922170177561 := by
  unfold tailWord_5103908
  simp only [CollatzResearch.WordTrace]
  refine ⟨93077408996710234466836189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124103211995613645955781585 93077408996710234466836189)
  ·
    refine ⟨34904028373766337925063571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93077408996710234466836189 34904028373766337925063571)
    ·
      refine ⟨52356042560649506887595357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34904028373766337925063571 52356042560649506887595357)
      ·
        refine ⟨19633515960243565082848259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52356042560649506887595357 19633515960243565082848259)
        ·
          refine ⟨29450273940365347624272389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19633515960243565082848259 29450273940365347624272389)
          ·
            refine ⟨5521926363818502679551073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29450273940365347624272389 5521926363818502679551073)
            ·
              refine ⟨4141444772863877009663305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5521926363818502679551073 4141444772863877009663305)
              ·
                refine ⟨3106083579647907757247479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4141444772863877009663305 3106083579647907757247479)
                ·
                  refine ⟨4659125369471861635871219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106083579647907757247479 4659125369471861635871219)
                  ·
                    refine ⟨6988688054207792453806829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4659125369471861635871219 6988688054207792453806829)
                    ·
                      refine ⟨2620758020327922170177561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6988688054207792453806829 2620758020327922170177561)
                      ·
                        rfl

theorem cell23_5103908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_5103908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103908 prefixEnd_5103908 := by exact prefixLift 5103908
  have htrace : WordTrace (prefixWord ++ tailWord_5103908) baseStart_5103908 baseEnd_5103908 := by
    simpa [prefixWord, tailWord_5103908, baseEnd_5103908] using wordTrace_append hprefix tailTrace_5103908
  have hstable : (prefixWord ++ tailWord_5103908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103908).length < 2 ^ (prefixWord ++ tailWord_5103908).sum := by decide
  have hdescent : baseEnd_5103908 < baseStart_5103908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103924 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_5103924 : Nat := 118140960795 + 5103924 * 2 ^ 59
def prefixEnd_5103924 : Nat := 4983230072969 + 3 ^ 40 * 5103924 * 2
def baseEnd_5103924 : Nat := 873588745339464702525829

theorem tailTrace_5103924 : CollatzResearch.WordTrace tailWord_5103924 prefixEnd_5103924 873588745339464702525829 := by
  unfold tailWord_5103924
  simp only [CollatzResearch.WordTrace]
  refine ⟨93077700780681251833127413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124103601040908335777503217 93077700780681251833127413)
  ·
    refine ⟨8726034448188867359355695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93077700780681251833127413 8726034448188867359355695)
    ·
      refine ⟨13089051672283301039033543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8726034448188867359355695 13089051672283301039033543)
      ·
        refine ⟨19633577508424951558550315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13089051672283301039033543 19633577508424951558550315)
        ·
          refine ⟨29450366262637427337825473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19633577508424951558550315 29450366262637427337825473)
          ·
            refine ⟨22087774696978070503369105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29450366262637427337825473 22087774696978070503369105)
            ·
              refine ⟨16565831022733552877526829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22087774696978070503369105 16565831022733552877526829)
              ·
                refine ⟨6212186633525082329072561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16565831022733552877526829 6212186633525082329072561)
                ·
                  refine ⟨4659139975143811746804421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212186633525082329072561 4659139975143811746804421)
                  ·
                    refine ⟨873588745339464702525829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659139975143811746804421 873588745339464702525829)
                    ·
                      rfl

theorem cell23_5103924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_5103924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103924 prefixEnd_5103924 := by exact prefixLift 5103924
  have htrace : WordTrace (prefixWord ++ tailWord_5103924) baseStart_5103924 baseEnd_5103924 := by
    simpa [prefixWord, tailWord_5103924, baseEnd_5103924] using wordTrace_append hprefix tailTrace_5103924
  have hstable : (prefixWord ++ tailWord_5103924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103924).length < 2 ^ (prefixWord ++ tailWord_5103924).sum := by decide
  have hdescent : baseEnd_5103924 < baseStart_5103924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5103981 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_5103981 : Nat := 118140960795 + 5103981 * 2 ^ 59
def prefixEnd_5103981 : Nat := 4983230072969 + 3 ^ 40 * 5103981 * 2
def baseEnd_5103981 : Nat := 2620795504415700384564725

theorem tailTrace_5103981 : CollatzResearch.WordTrace tailWord_5103981 prefixEnd_5103981 2620795504415700384564725 := by
  unfold tailWord_5103981
  simp only [CollatzResearch.WordTrace]
  refine ⟨186157480522156002401079797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124104987014770668267386531 186157480522156002401079797)
  ·
    refine ⟨17452263798952125225101231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 186157480522156002401079797 17452263798952125225101231)
    ·
      refine ⟨26178395698428187837651847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17452263798952125225101231 26178395698428187837651847)
      ·
        refine ⟨39267593547642281756477771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26178395698428187837651847 39267593547642281756477771)
        ·
          refine ⟨58901390321463422634716657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39267593547642281756477771 58901390321463422634716657)
          ·
            refine ⟨44176042741097566976037493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58901390321463422634716657 44176042741097566976037493)
            ·
              refine ⟨4141504006977896904003515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44176042741097566976037493 4141504006977896904003515)
              ·
                refine ⟨6212256010466845356005273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4141504006977896904003515 6212256010466845356005273)
                ·
                  refine ⟨4659192007850134017003955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212256010466845356005273 4659192007850134017003955)
                  ·
                    refine ⟨6988788011775201025505933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4659192007850134017003955 6988788011775201025505933)
                    ·
                      refine ⟨2620795504415700384564725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6988788011775201025505933 2620795504415700384564725)
                      ·
                        rfl

theorem cell23_5103981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_5103981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5103981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5103981 prefixEnd_5103981 := by exact prefixLift 5103981
  have htrace : WordTrace (prefixWord ++ tailWord_5103981) baseStart_5103981 baseEnd_5103981 := by
    simpa [prefixWord, tailWord_5103981, baseEnd_5103981] using wordTrace_append hprefix tailTrace_5103981
  have hstable : (prefixWord ++ tailWord_5103981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5103981).length < 2 ^ (prefixWord ++ tailWord_5103981).sum := by decide
  have hdescent : baseEnd_5103981 < baseStart_5103981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5103981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104004 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_5104004 : Nat := 118140960795 + 5104004 * 2 ^ 59
def prefixEnd_5104004 : Nat := 4983230072969 + 3 ^ 40 * 5104004 * 2
def baseEnd_5104004 : Nat := 2620807314470753794577119

theorem tailTrace_5104004 : CollatzResearch.WordTrace tailWord_5104004 prefixEnd_5104004 2620807314470753794577119 := by
  unfold tailWord_5104004
  simp only [CollatzResearch.WordTrace]
  refine ⟨93079159700536338664583533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124105546267381784886111377 93079159700536338664583533)
  ·
    refine ⟨34904684887701126999218825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93079159700536338664583533 34904684887701126999218825)
    ·
      refine ⟨26178513665775845249414119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34904684887701126999218825 26178513665775845249414119)
      ·
        refine ⟨39267770498663767874121179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26178513665775845249414119 39267770498663767874121179)
        ·
          refine ⟨58901655747995651811181769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39267770498663767874121179 58901655747995651811181769)
          ·
            refine ⟨44176241810996738858386327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58901655747995651811181769 44176241810996738858386327)
            ·
              refine ⟨66264362716495108287579491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44176241810996738858386327 66264362716495108287579491)
              ·
                refine ⟨99396544074742662431369237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66264362716495108287579491 99396544074742662431369237)
                ·
                  refine ⟨4659213003503562301470433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99396544074742662431369237 4659213003503562301470433)
                  ·
                    refine ⟨3494409752627671726102825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4659213003503562301470433 3494409752627671726102825)
                    ·
                      refine ⟨2620807314470753794577119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494409752627671726102825 2620807314470753794577119)
                      ·
                        rfl

theorem cell23_5104004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_5104004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104004 prefixEnd_5104004 := by exact prefixLift 5104004
  have htrace : WordTrace (prefixWord ++ tailWord_5104004) baseStart_5104004 baseEnd_5104004 := by
    simpa [prefixWord, tailWord_5104004, baseEnd_5104004] using wordTrace_append hprefix tailTrace_5104004
  have hstable : (prefixWord ++ tailWord_5104004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104004).length < 2 ^ (prefixWord ++ tailWord_5104004).sum := by decide
  have hdescent : baseEnd_5104004 < baseStart_5104004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104042 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_5104042 : Nat := 118140960795 + 5104042 * 2 ^ 59
def prefixEnd_5104042 : Nat := 4983230072969 + 3 ^ 40 * 5104042 * 2
def baseEnd_5104042 : Nat := 2620826826735624645901945

theorem tailTrace_5104042 : CollatzResearch.WordTrace tailWord_5104042 prefixEnd_5104042 2620826826735624645901945 := by
  unfold tailWord_5104042
  simp only [CollatzResearch.WordTrace]
  refine ⟨46539926343733752454762595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124106470249956673212700253 46539926343733752454762595)
  ·
    refine ⟨69809889515600628682143893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46539926343733752454762595 69809889515600628682143893)
    ·
      refine ⟨3272338571043779469475495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69809889515600628682143893 3272338571043779469475495)
      ·
        refine ⟨4908507856565669204213243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3272338571043779469475495 4908507856565669204213243)
        ·
          refine ⟨7362761784848503806319865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4908507856565669204213243 7362761784848503806319865)
          ·
            refine ⟨5522071338636377854739899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7362761784848503806319865 5522071338636377854739899)
            ·
              refine ⟨8283107007954566782109849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522071338636377854739899 8283107007954566782109849)
              ·
                refine ⟨6212330255965925086582387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8283107007954566782109849 6212330255965925086582387)
                ·
                  refine ⟨9318495383948887629873581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6212330255965925086582387 9318495383948887629873581)
                  ·
                    refine ⟨3494435768980832861202593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9318495383948887629873581 3494435768980832861202593)
                    ·
                      refine ⟨2620826826735624645901945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494435768980832861202593 2620826826735624645901945)
                      ·
                        rfl

theorem cell23_5104042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_5104042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104042 prefixEnd_5104042 := by exact prefixLift 5104042
  have htrace : WordTrace (prefixWord ++ tailWord_5104042) baseStart_5104042 baseEnd_5104042 := by
    simpa [prefixWord, tailWord_5104042, baseEnd_5104042] using wordTrace_append hprefix tailTrace_5104042
  have hstable : (prefixWord ++ tailWord_5104042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104042).length < 2 ^ (prefixWord ++ tailWord_5104042).sum := by decide
  have hdescent : baseEnd_5104042 < baseStart_5104042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104050 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_5104050 : Nat := 118140960795 + 5104050 * 2 ^ 59
def prefixEnd_5104050 : Nat := 4983230072969 + 3 ^ 40 * 5104050 * 2
def baseEnd_5104050 : Nat := 2620830934580860614601907

theorem tailTrace_5104050 : CollatzResearch.WordTrace tailWord_5104050 prefixEnd_5104050 2620830934580860614601907 := by
  unfold tailWord_5104050
  simp only [CollatzResearch.WordTrace]
  refine ⟨46539999289726506796335401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124106664772604018123561069 46539999289726506796335401)
  ·
    refine ⟨34904999467294880097251551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46539999289726506796335401 34904999467294880097251551)
    ·
      refine ⟨52357499200942320145877327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34904999467294880097251551 52357499200942320145877327)
      ·
        refine ⟨78536248801413480218815991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52357499200942320145877327 78536248801413480218815991)
        ·
          refine ⟨117804373202120220328223987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78536248801413480218815991 117804373202120220328223987)
          ·
            refine ⟨176706559803180330492335981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117804373202120220328223987 176706559803180330492335981)
            ·
              refine ⟨66264959926192623934625993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176706559803180330492335981 66264959926192623934625993)
              ·
                refine ⟨49698719944644467950969495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66264959926192623934625993 49698719944644467950969495)
                ·
                  refine ⟨74548079916966701926454243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49698719944644467950969495 74548079916966701926454243)
                  ·
                    refine ⟨111822119875450052889681365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74548079916966701926454243 111822119875450052889681365)
                    ·
                      refine ⟨2620830934580860614601907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111822119875450052889681365 2620830934580860614601907)
                      ·
                        rfl

theorem cell23_5104050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_5104050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104050 prefixEnd_5104050 := by exact prefixLift 5104050
  have htrace : WordTrace (prefixWord ++ tailWord_5104050) baseStart_5104050 baseEnd_5104050 := by
    simpa [prefixWord, tailWord_5104050, baseEnd_5104050] using wordTrace_append hprefix tailTrace_5104050
  have hstable : (prefixWord ++ tailWord_5104050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104050).length < 2 ^ (prefixWord ++ tailWord_5104050).sum := by decide
  have hdescent : baseEnd_5104050 < baseStart_5104050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104057 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 2, 5]
def baseStart_5104057 : Nat := 118140960795 + 5104057 * 2 ^ 59
def prefixEnd_5104057 : Nat := 4983230072969 + 3 ^ 40 * 5104057 * 2
def baseEnd_5104057 : Nat := 873611509648480695738125

theorem tailTrace_5104057 : CollatzResearch.WordTrace tailWord_5104057 prefixEnd_5104057 873611509648480695738125 := by
  unfold tailWord_5104057
  simp only [CollatzResearch.WordTrace]
  refine ⟨186160252469880667380846425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124106834979920444920564283 186160252469880667380846425)
  ·
    refine ⟨139620189352410500535634819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186160252469880667380846425 139620189352410500535634819)
    ·
      refine ⟨209430284028615750803452229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139620189352410500535634819 209430284028615750803452229)
      ·
        refine ⟨39268178255365453275647293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209430284028615750803452229 39268178255365453275647293)
        ·
          refine ⟨14725566845762044978367735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39268178255365453275647293 14725566845762044978367735)
          ·
            refine ⟨22088350268643067467551603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14725566845762044978367735 22088350268643067467551603)
            ·
              refine ⟨33132525402964601201327405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22088350268643067467551603 33132525402964601201327405)
              ·
                refine ⟨12424697026111725450497777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33132525402964601201327405 12424697026111725450497777)
                ·
                  refine ⟨9318522769583794087873333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12424697026111725450497777 9318522769583794087873333)
                  ·
                    refine ⟨873611509648480695738125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9318522769583794087873333 873611509648480695738125)
                    ·
                      rfl

theorem cell23_5104057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_5104057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104057 prefixEnd_5104057 := by exact prefixLift 5104057
  have htrace : WordTrace (prefixWord ++ tailWord_5104057) baseStart_5104057 baseEnd_5104057 := by
    simpa [prefixWord, tailWord_5104057, baseEnd_5104057] using wordTrace_append hprefix tailTrace_5104057
  have hstable : (prefixWord ++ tailWord_5104057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104057).length < 2 ^ (prefixWord ++ tailWord_5104057).sum := by decide
  have hdescent : baseEnd_5104057 < baseStart_5104057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104097 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_5104097 : Nat := 118140960795 + 5104097 * 2 ^ 59
def prefixEnd_5104097 : Nat := 4983230072969 + 3 ^ 40 * 5104097 * 2
def baseEnd_5104097 : Nat := 2620855068171621930714191

theorem tailTrace_5104097 : CollatzResearch.WordTrace tailWord_5104097 prefixEnd_5104097 2620855068171621930714191 := by
  unfold tailWord_5104097
  simp only [CollatzResearch.WordTrace]
  refine ⟨186161711389735754212302545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124107807593157169474868363 186161711389735754212302545)
  ·
    refine ⟨139621283542301815659226909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186161711389735754212302545 139621283542301815659226909)
    ·
      refine ⟨52357981328363180872210091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139621283542301815659226909 52357981328363180872210091)
      ·
        refine ⟨78536971992544771308315137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52357981328363180872210091 78536971992544771308315137)
        ·
          refine ⟨58902728994408578481236353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78536971992544771308315137 58902728994408578481236353)
          ·
            refine ⟨44177046745806433860927265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58902728994408578481236353 44177046745806433860927265)
            ·
              refine ⟨33132785059354825395695449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44177046745806433860927265 33132785059354825395695449)
              ·
                refine ⟨24849588794516119046771587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33132785059354825395695449 24849588794516119046771587)
                ·
                  refine ⟨37274383191774178570157381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24849588794516119046771587 37274383191774178570157381)
                  ·
                    refine ⟨6988946848457658481904509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37274383191774178570157381 6988946848457658481904509)
                    ·
                      refine ⟨2620855068171621930714191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6988946848457658481904509 2620855068171621930714191)
                      ·
                        rfl

theorem cell23_5104097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_5104097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104097 prefixEnd_5104097 := by exact prefixLift 5104097
  have htrace : WordTrace (prefixWord ++ tailWord_5104097) baseStart_5104097 baseEnd_5104097 := by
    simpa [prefixWord, tailWord_5104097, baseEnd_5104097] using wordTrace_append hprefix tailTrace_5104097
  have hstable : (prefixWord ++ tailWord_5104097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104097).length < 2 ^ (prefixWord ++ tailWord_5104097).sum := by decide
  have hdescent : baseEnd_5104097 < baseStart_5104097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104100 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 12]
def baseStart_5104100 : Nat := 118140960795 + 5104100 * 2 ^ 59
def prefixEnd_5104100 : Nat := 4983230072969 + 3 ^ 40 * 5104100 * 2
def baseEnd_5104100 : Nat := 291206289845953935441853

theorem tailTrace_5104100 : CollatzResearch.WordTrace tailWord_5104100 prefixEnd_5104100 291206289845953935441853 := by
  unfold tailWord_5104100
  simp only [CollatzResearch.WordTrace]
  refine ⟨93080910404362442862330877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124107880539149923816441169 93080910404362442862330877)
  ·
    refine ⟨34905341401635916073374079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93080910404362442862330877 34905341401635916073374079)
    ·
      refine ⟨52358012102453874110061119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34905341401635916073374079 52358012102453874110061119)
      ·
        refine ⟨78537018153680811165091679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52358012102453874110061119 78537018153680811165091679)
        ·
          refine ⟨117805527230521216747637519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78537018153680811165091679 117805527230521216747637519)
          ·
            refine ⟨176708290845781825121456279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117805527230521216747637519 176708290845781825121456279)
            ·
              refine ⟨265062436268672737682184419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176708290845781825121456279 265062436268672737682184419)
              ·
                refine ⟨397593654403009106523276629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265062436268672737682184419 397593654403009106523276629)
                ·
                  refine ⟨291206289845953935441853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 397593654403009106523276629 291206289845953935441853)
                  ·
                    rfl

theorem cell23_5104100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_5104100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104100 prefixEnd_5104100 := by exact prefixLift 5104100
  have htrace : WordTrace (prefixWord ++ tailWord_5104100) baseStart_5104100 baseEnd_5104100 := by
    simpa [prefixWord, tailWord_5104100, baseEnd_5104100] using wordTrace_append hprefix tailTrace_5104100
  have hstable : (prefixWord ++ tailWord_5104100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104100).length < 2 ^ (prefixWord ++ tailWord_5104100).sum := by decide
  have hdescent : baseEnd_5104100 < baseStart_5104100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104104 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 3, 4]
def baseStart_5104104 : Nat := 118140960795 + 5104104 * 2 ^ 59
def prefixEnd_5104104 : Nat := 4983230072969 + 3 ^ 40 * 5104104 * 2
def baseEnd_5104104 : Nat := 873619554178734467775553

theorem tailTrace_5104104 : CollatzResearch.WordTrace tailWord_5104104 prefixEnd_5104104 873619554178734467775553 := by
  unfold tailWord_5104104
  simp only [CollatzResearch.WordTrace]
  refine ⟨93080983350355197203903683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124107977800473596271871577 93080983350355197203903683)
  ·
    refine ⟨139621475025532795805855525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93080983350355197203903683 139621475025532795805855525)
    ·
      refine ⟨26179026567287399213597911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139621475025532795805855525 26179026567287399213597911)
      ·
        refine ⟨39268539850931098820396867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26179026567287399213597911 39268539850931098820396867)
        ·
          refine ⟨58902809776396648230595301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39268539850931098820396867 58902809776396648230595301)
          ·
            refine ⟨11044276833074371543236619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58902809776396648230595301 11044276833074371543236619)
            ·
              refine ⟨16566415249611557314854929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11044276833074371543236619 16566415249611557314854929)
              ·
                refine ⟨12424811437208667986141197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16566415249611557314854929 12424811437208667986141197)
                ·
                  refine ⟨4659304288953250494802949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12424811437208667986141197 4659304288953250494802949)
                  ·
                    refine ⟨873619554178734467775553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659304288953250494802949 873619554178734467775553)
                    ·
                      rfl

theorem cell23_5104104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_5104104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104104 prefixEnd_5104104 := by exact prefixLift 5104104
  have htrace : WordTrace (prefixWord ++ tailWord_5104104) baseStart_5104104 baseEnd_5104104 := by
    simpa [prefixWord, tailWord_5104104, baseEnd_5104104] using wordTrace_append hprefix tailTrace_5104104
  have hstable : (prefixWord ++ tailWord_5104104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104104).length < 2 ^ (prefixWord ++ tailWord_5104104).sum := by decide
  have hdescent : baseEnd_5104104 < baseStart_5104104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104154 : List Nat := [3, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2]
def baseStart_5104154 : Nat := 118140960795 + 5104154 * 2 ^ 59
def prefixEnd_5104154 : Nat := 4983230072969 + 3 ^ 40 * 5104154 * 2
def baseEnd_5104154 : Nat := 2620884336568928207701429

theorem tailTrace_5104154 : CollatzResearch.WordTrace tailWord_5104154 prefixEnd_5104154 2620884336568928207701429 := by
  unfold tailWord_5104154
  simp only [CollatzResearch.WordTrace]
  refine ⟨46540947587632313236781879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124109193567019501964751677 46540947587632313236781879)
  ·
    refine ⟨69811421381448469855172819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46540947587632313236781879 69811421381448469855172819)
    ·
      refine ⟨104717132072172704782759229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69811421381448469855172819 104717132072172704782759229)
      ·
        refine ⟨39268924527064764293534711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104717132072172704782759229 39268924527064764293534711)
        ·
          refine ⟨58903386790597146440302067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39268924527064764293534711 58903386790597146440302067)
          ·
            refine ⟨88355080185895719660453101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58903386790597146440302067 88355080185895719660453101)
            ·
              refine ⟨33133155069710894872669913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88355080185895719660453101 33133155069710894872669913)
              ·
                refine ⟨24849866302283171154502435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33133155069710894872669913 24849866302283171154502435)
                ·
                  refine ⟨37274799453424756731753653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24849866302283171154502435 37274799453424756731753653)
                  ·
                    refine ⟨3494512448758570943601905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37274799453424756731753653 3494512448758570943601905)
                    ·
                      refine ⟨2620884336568928207701429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494512448758570943601905 2620884336568928207701429)
                      ·
                        rfl

theorem cell23_5104154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_5104154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104154 prefixEnd_5104154 := by exact prefixLift 5104154
  have htrace : WordTrace (prefixWord ++ tailWord_5104154) baseStart_5104154 baseEnd_5104154 := by
    simpa [prefixWord, tailWord_5104154, baseEnd_5104154] using wordTrace_append hprefix tailTrace_5104154
  have hstable : (prefixWord ++ tailWord_5104154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104154).length < 2 ^ (prefixWord ++ tailWord_5104154).sum := by decide
  have hdescent : baseEnd_5104154 < baseStart_5104154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104177 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 1, 6]
def baseStart_5104177 : Nat := 118140960795 + 5104177 * 2 ^ 59
def prefixEnd_5104177 : Nat := 4983230072969 + 3 ^ 40 * 5104177 * 2
def baseEnd_5104177 : Nat := 873632048874660539237941

theorem tailTrace_5104177 : CollatzResearch.WordTrace tailWord_5104177 prefixEnd_5104177 873632048874660539237941 := by
  unfold tailWord_5104177
  simp only [CollatzResearch.WordTrace]
  refine ⟨186164629229445927875214785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124109752819630618583476523 186164629229445927875214785)
  ·
    refine ⟨139623471922084445906411089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186164629229445927875214785 139623471922084445906411089)
    ·
      refine ⟨104717603941563334429808317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139623471922084445906411089 104717603941563334429808317)
      ·
        refine ⟨39269101478086250411178119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104717603941563334429808317 39269101478086250411178119)
        ·
          refine ⟨58903652217129375616767179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39269101478086250411178119 58903652217129375616767179)
          ·
            refine ⟨88355478325694063425150769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58903652217129375616767179 88355478325694063425150769)
            ·
              refine ⟨66266608744270547568863077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88355478325694063425150769 66266608744270547568863077)
              ·
                refine ⟨12424989139550727669161827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66266608744270547568863077 12424989139550727669161827)
                ·
                  refine ⟨18637483709326091503742741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12424989139550727669161827 18637483709326091503742741)
                  ·
                    refine ⟨873632048874660539237941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18637483709326091503742741 873632048874660539237941)
                    ·
                      rfl

theorem cell23_5104177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_5104177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104177 prefixEnd_5104177 := by exact prefixLift 5104177
  have htrace : WordTrace (prefixWord ++ tailWord_5104177) baseStart_5104177 baseEnd_5104177 := by
    simpa [prefixWord, tailWord_5104177, baseEnd_5104177] using wordTrace_append hprefix tailTrace_5104177
  have hstable : (prefixWord ++ tailWord_5104177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104177).length < 2 ^ (prefixWord ++ tailWord_5104177).sum := by decide
  have hdescent : baseEnd_5104177 < baseStart_5104177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104178 : List Nat := [3, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3]
def baseStart_5104178 : Nat := 118140960795 + 5104178 * 2 ^ 59
def prefixEnd_5104178 : Nat := 4983230072969 + 3 ^ 40 * 5104178 * 2
def baseEnd_5104178 : Nat := 2620896660104636113801319

theorem tailTrace_5104178 : CollatzResearch.WordTrace tailWord_5104178 prefixEnd_5104178 2620896660104636113801319 := by
  unfold tailWord_5104178
  simp only [CollatzResearch.WordTrace]
  refine ⟨46541166425610576261500297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124109777134961536697334125 46541166425610576261500297)
  ·
    refine ⟨34905874819207932196125223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46541166425610576261500297 34905874819207932196125223)
    ·
      refine ⟨52358812228811898294187835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34905874819207932196125223 52358812228811898294187835)
      ·
        refine ⟨78538218343217847441281753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52358812228811898294187835 78538218343217847441281753)
        ·
          refine ⟨58903663757413385580961315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78538218343217847441281753 58903663757413385580961315)
          ·
            refine ⟨88355495636120078371441973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58903663757413385580961315 88355495636120078371441973)
            ·
              refine ⟨8283327715886257347322685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88355495636120078371441973 8283327715886257347322685)
              ·
                refine ⟨3106247893457346505246007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8283327715886257347322685 3106247893457346505246007)
                ·
                  refine ⟨4659371840186019757869011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106247893457346505246007 4659371840186019757869011)
                  ·
                    refine ⟨6989057760279029636803517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4659371840186019757869011 6989057760279029636803517)
                    ·
                      refine ⟨2620896660104636113801319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6989057760279029636803517 2620896660104636113801319)
                      ·
                        rfl

theorem cell23_5104178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_5104178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104178 prefixEnd_5104178 := by exact prefixLift 5104178
  have htrace : WordTrace (prefixWord ++ tailWord_5104178) baseStart_5104178 baseEnd_5104178 := by
    simpa [prefixWord, tailWord_5104178, baseEnd_5104178] using wordTrace_append hprefix tailTrace_5104178
  have hstable : (prefixWord ++ tailWord_5104178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104178).length < 2 ^ (prefixWord ++ tailWord_5104178).sum := by decide
  have hdescent : baseEnd_5104178 < baseStart_5104178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104184 : List Nat := [2, 1, 2, 1, 4, 1, 1, 5, 1, 1, 4]
def baseStart_5104184 : Nat := 118140960795 + 5104184 * 2 ^ 59
def prefixEnd_5104184 : Nat := 4983230072969 + 3 ^ 40 * 5104184 * 2
def baseEnd_5104184 : Nat := 2620899740988563090326291

theorem tailTrace_5104184 : CollatzResearch.WordTrace tailWord_5104184 prefixEnd_5104184 2620899740988563090326291 := by
  unfold tailWord_5104184
  simp only [CollatzResearch.WordTrace]
  refine ⟨93082442270210284035359803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124109923026947045380479737 93082442270210284035359803)
  ·
    refine ⟨139623663405315426053039705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93082442270210284035359803 139623663405315426053039705)
    ·
      refine ⟨104717747553986569539779779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139623663405315426053039705 104717747553986569539779779)
      ·
        refine ⟨157076621330979854309669669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104717747553986569539779779 157076621330979854309669669)
        ·
          refine ⟨29451866499558722683063063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157076621330979854309669669 29451866499558722683063063)
          ·
            refine ⟨44177799749338084024594595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29451866499558722683063063 44177799749338084024594595)
            ·
              refine ⟨66266699624007126036891893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44177799749338084024594595 66266699624007126036891893)
              ·
                refine ⟨6212503089750668065958615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66266699624007126036891893 6212503089750668065958615)
                ·
                  refine ⟨9318754634626002098937923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6212503089750668065958615 9318754634626002098937923)
                  ·
                    refine ⟨13978131951939003148406885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9318754634626002098937923 13978131951939003148406885)
                    ·
                      refine ⟨2620899740988563090326291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13978131951939003148406885 2620899740988563090326291)
                      ·
                        rfl

theorem cell23_5104184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_5104184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104184 prefixEnd_5104184 := by exact prefixLift 5104184
  have htrace : WordTrace (prefixWord ++ tailWord_5104184) baseStart_5104184 baseEnd_5104184 := by
    simpa [prefixWord, tailWord_5104184, baseEnd_5104184] using wordTrace_append hprefix tailTrace_5104184
  have hstable : (prefixWord ++ tailWord_5104184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104184).length < 2 ^ (prefixWord ++ tailWord_5104184).sum := by decide
  have hdescent : baseEnd_5104184 < baseStart_5104184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104197 : List Nat := [1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_5104197 : Nat := 118140960795 + 5104197 * 2 ^ 59
def prefixEnd_5104197 : Nat := 4983230072969 + 3 ^ 40 * 5104197 * 2
def baseEnd_5104197 : Nat := 2620906416237071539463731

theorem tailTrace_5104197 : CollatzResearch.WordTrace tailWord_5104197 prefixEnd_5104197 2620906416237071539463731 := by
  unfold tailWord_5104197
  simp only [CollatzResearch.WordTrace]
  refine ⟨186165358689373471290942845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124110239126248980860628563 186165358689373471290942845)
  ·
    refine ⟨69812009508515051734103567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186165358689373471290942845 69812009508515051734103567)
    ·
      refine ⟨104718014262772577601155351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69812009508515051734103567 104718014262772577601155351)
      ·
        refine ⟨157077021394158866401733027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104718014262772577601155351 157077021394158866401733027)
        ·
          refine ⟨235615532091238299602599541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157077021394158866401733027 235615532091238299602599541)
          ·
            refine ⟨22088956133553590587743707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 235615532091238299602599541 22088956133553590587743707)
            ·
              refine ⟨33133434200330385881615561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22088956133553590587743707 33133434200330385881615561)
              ·
                refine ⟨24850075650247789411211671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33133434200330385881615561 24850075650247789411211671)
                ·
                  refine ⟨37275113475371684116817507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24850075650247789411211671 37275113475371684116817507)
                  ·
                    refine ⟨55912670213057526175226261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37275113475371684116817507 55912670213057526175226261)
                    ·
                      refine ⟨2620906416237071539463731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55912670213057526175226261 2620906416237071539463731)
                      ·
                        rfl

theorem cell23_5104197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_5104197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104197 prefixEnd_5104197 := by exact prefixLift 5104197
  have htrace : WordTrace (prefixWord ++ tailWord_5104197) baseStart_5104197 baseEnd_5104197 := by
    simpa [prefixWord, tailWord_5104197, baseEnd_5104197] using wordTrace_append hprefix tailTrace_5104197
  have hstable : (prefixWord ++ tailWord_5104197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104197).length < 2 ^ (prefixWord ++ tailWord_5104197).sum := by decide
  have hdescent : baseEnd_5104197 < baseStart_5104197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104204 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 3, 2, 3]
def baseStart_5104204 : Nat := 118140960795 + 5104204 * 2 ^ 59
def prefixEnd_5104204 : Nat := 4983230072969 + 3 ^ 40 * 5104204 * 2
def baseEnd_5104204 : Nat := 2620910010601653012076199

theorem tailTrace_5104204 : CollatzResearch.WordTrace tailWord_5104204 prefixEnd_5104204 2620910010601653012076199 := by
  unfold tailWord_5104204
  simp only [CollatzResearch.WordTrace]
  refine ⟨93082807000174055743223833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124110409333565407657631777 93082807000174055743223833)
  ·
    refine ⟨69812105250130541807417875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93082807000174055743223833 69812105250130541807417875)
    ·
      refine ⟨104718157875195812711126813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69812105250130541807417875 104718157875195812711126813)
      ·
        refine ⟨39269309203198429766672555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104718157875195812711126813 39269309203198429766672555)
        ·
          refine ⟨58903963804797644650008833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39269309203198429766672555 58903963804797644650008833)
          ·
            refine ⟨44177972853598233487506625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58903963804797644650008833 44177972853598233487506625)
            ·
              refine ⟨33133479640198675115629969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44177972853598233487506625 33133479640198675115629969)
              ·
                refine ⟨24850109730149006336722477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33133479640198675115629969 24850109730149006336722477)
                ·
                  refine ⟨9318791148805877376270929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24850109730149006336722477 9318791148805877376270929)
                  ·
                    refine ⟨6989093361604408032203197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9318791148805877376270929 6989093361604408032203197)
                    ·
                      refine ⟨2620910010601653012076199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6989093361604408032203197 2620910010601653012076199)
                      ·
                        rfl

theorem cell23_5104204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_5104204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104204 prefixEnd_5104204 := by exact prefixLift 5104204
  have htrace : WordTrace (prefixWord ++ tailWord_5104204) baseStart_5104204 baseEnd_5104204 := by
    simpa [prefixWord, tailWord_5104204, baseEnd_5104204] using wordTrace_append hprefix tailTrace_5104204
  have hstable : (prefixWord ++ tailWord_5104204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104204).length < 2 ^ (prefixWord ++ tailWord_5104204).sum := by decide
  have hdescent : baseEnd_5104204 < baseStart_5104204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104247 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_5104247 : Nat := 118140960795 + 5104247 * 2 ^ 59
def prefixEnd_5104247 : Nat := 4983230072969 + 3 ^ 40 * 5104247 * 2
def baseEnd_5104247 : Nat := 2620932090269796343838501

theorem tailTrace_5104247 : CollatzResearch.WordTrace tailWord_5104247 prefixEnd_5104247 2620932090269796343838501 := by
  unfold tailWord_5104247
  simp only [CollatzResearch.WordTrace]
  refine ⟨186167182339192329830262995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124111454892794886553508663 186167182339192329830262995)
  ·
    refine ⟨279250773508788494745394493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186167182339192329830262995 279250773508788494745394493)
    ·
      refine ⟨104719040065795685529522935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279250773508788494745394493 104719040065795685529522935)
      ·
        refine ⟨157078560098693528294284403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104719040065795685529522935 157078560098693528294284403)
        ·
          refine ⟨235617840148040292441426605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157078560098693528294284403 235617840148040292441426605)
          ·
            refine ⟨88356690055515109665534977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235617840148040292441426605 88356690055515109665534977)
            ·
              refine ⟨66267517541636332249151233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88356690055515109665534977 66267517541636332249151233)
              ·
                refine ⟨49700638156227249186863425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66267517541636332249151233 49700638156227249186863425)
                ·
                  refine ⟨37275478617170436890147569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49700638156227249186863425 37275478617170436890147569)
                  ·
                    refine ⟨27956608962877827667610677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37275478617170436890147569 27956608962877827667610677)
                    ·
                      refine ⟨2620932090269796343838501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27956608962877827667610677 2620932090269796343838501)
                      ·
                        rfl

theorem cell23_5104247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_5104247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104247 prefixEnd_5104247 := by exact prefixLift 5104247
  have htrace : WordTrace (prefixWord ++ tailWord_5104247) baseStart_5104247 baseEnd_5104247 := by
    simpa [prefixWord, tailWord_5104247, baseEnd_5104247] using wordTrace_append hprefix tailTrace_5104247
  have hstable : (prefixWord ++ tailWord_5104247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104247).length < 2 ^ (prefixWord ++ tailWord_5104247).sum := by decide
  have hdescent : baseEnd_5104247 < baseStart_5104247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104261 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 3, 3, 2]
def baseStart_5104261 : Nat := 118140960795 + 5104261 * 2 ^ 59
def prefixEnd_5104261 : Nat := 4983230072969 + 3 ^ 40 * 5104261 * 2
def baseEnd_5104261 : Nat := 2620939278998959289063437

theorem tailTrace_5104261 : CollatzResearch.WordTrace tailWord_5104261 prefixEnd_5104261 2620939278998959289063437 := by
  unfold tailWord_5104261
  simp only [CollatzResearch.WordTrace]
  refine ⟨186167692961141610221272637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124111795307427740147515091 186167692961141610221272637)
  ·
    refine ⟨69812884860428103832977239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186167692961141610221272637 69812884860428103832977239)
    ·
      refine ⟨104719327290642155749465859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69812884860428103832977239 104719327290642155749465859)
      ·
        refine ⟨157078990935963233624198789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104719327290642155749465859 157078990935963233624198789)
        ·
          refine ⟨29452310800493106304537273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 157078990935963233624198789 29452310800493106304537273)
          ·
            refine ⟨22089233100369829728402955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29452310800493106304537273 22089233100369829728402955)
            ·
              refine ⟨33133849650554744592604433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22089233100369829728402955 33133849650554744592604433)
              ·
                refine ⟨24850387237916058444453325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33133849650554744592604433 24850387237916058444453325)
                ·
                  refine ⟨9318895214218521916669997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24850387237916058444453325 9318895214218521916669997)
                  ·
                    refine ⟨3494585705331945718751249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9318895214218521916669997 3494585705331945718751249)
                    ·
                      refine ⟨2620939278998959289063437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494585705331945718751249 2620939278998959289063437)
                      ·
                        rfl

theorem cell23_5104261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 3, 2].length) (baseStart_5104261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104261 prefixEnd_5104261 := by exact prefixLift 5104261
  have htrace : WordTrace (prefixWord ++ tailWord_5104261) baseStart_5104261 baseEnd_5104261 := by
    simpa [prefixWord, tailWord_5104261, baseEnd_5104261] using wordTrace_append hprefix tailTrace_5104261
  have hstable : (prefixWord ++ tailWord_5104261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104261).length < 2 ^ (prefixWord ++ tailWord_5104261).sum := by decide
  have hdescent : baseEnd_5104261 < baseStart_5104261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104302 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_5104302 : Nat := 118140960795 + 5104302 * 2 ^ 59
def prefixEnd_5104302 : Nat := 4983230072969 + 3 ^ 40 * 5104302 * 2
def baseEnd_5104302 : Nat := 2620960331705793628650749

theorem tailTrace_5104302 : CollatzResearch.WordTrace tailWord_5104302 prefixEnd_5104302 2620960331705793628650749 := by
  unfold tailWord_5104302
  simp only [CollatzResearch.WordTrace]
  refine ⟨23271148544249134277939395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124112792235995382815676773 23271148544249134277939395)
  ·
    refine ⟨34906722816373701416909093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23271148544249134277939395 34906722816373701416909093)
    ·
      refine ⟨6545010528070069015670455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34906722816373701416909093 6545010528070069015670455)
      ·
        refine ⟨9817515792105103523505683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6545010528070069015670455 9817515792105103523505683)
        ·
          refine ⟨14726273688157655285258525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9817515792105103523505683 14726273688157655285258525)
          ·
            refine ⟨5522352633059120731971947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14726273688157655285258525 5522352633059120731971947)
            ·
              refine ⟨8283528949588681097957921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5522352633059120731971947 8283528949588681097957921)
              ·
                refine ⟨6212646712191510823468441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8283528949588681097957921 6212646712191510823468441)
                ·
                  refine ⟨4659485034143633117601331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212646712191510823468441 4659485034143633117601331)
                  ·
                    refine ⟨6989227551215449676401997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4659485034143633117601331 6989227551215449676401997)
                    ·
                      refine ⟨2620960331705793628650749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6989227551215449676401997 2620960331705793628650749)
                      ·
                        rfl

theorem cell23_5104302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_5104302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104302 prefixEnd_5104302 := by exact prefixLift 5104302
  have htrace : WordTrace (prefixWord ++ tailWord_5104302) baseStart_5104302 baseEnd_5104302 := by
    simpa [prefixWord, tailWord_5104302, baseEnd_5104302] using wordTrace_append hprefix tailTrace_5104302
  have hstable : (prefixWord ++ tailWord_5104302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104302).length < 2 ^ (prefixWord ++ tailWord_5104302).sum := by decide
  have hdescent : baseEnd_5104302 < baseStart_5104302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104314 : List Nat := [3, 1, 1, 1, 2, 3, 4, 1, 7]
def baseStart_5104314 : Nat := 118140960795 + 5104314 * 2 ^ 59
def prefixEnd_5104314 : Nat := 4983230072969 + 3 ^ 40 * 5104314 * 2
def baseEnd_5104314 : Nat := 291218499274849731300077

theorem tailTrace_5104314 : CollatzResearch.WordTrace tailWord_5104314 prefixEnd_5104314 291218499274849731300077 := by
  unfold tailWord_5104314
  simp only [CollatzResearch.WordTrace]
  refine ⟨46542406507487400068237999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124113084019966400181967997 46542406507487400068237999)
  ·
    refine ⟨69813609761231100102356999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46542406507487400068237999 69813609761231100102356999)
    ·
      refine ⟨104720414641846650153535499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69813609761231100102356999 104720414641846650153535499)
      ·
        refine ⟨157080621962769975230303249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104720414641846650153535499 157080621962769975230303249)
        ·
          refine ⟨117810466472077481422727437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157080621962769975230303249 117810466472077481422727437)
          ·
            refine ⟨44178924927029055533522789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117810466472077481422727437 44178924927029055533522789)
            ·
              refine ⟨8283548423817947912535523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44178924927029055533522789 8283548423817947912535523)
              ·
                refine ⟨12425322635726921868803285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8283548423817947912535523 12425322635726921868803285)
                ·
                  refine ⟨291218499274849731300077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12425322635726921868803285 291218499274849731300077)
                  ·
                    rfl

theorem cell23_5104314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_5104314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104314 prefixEnd_5104314 := by exact prefixLift 5104314
  have htrace : WordTrace (prefixWord ++ tailWord_5104314) baseStart_5104314 baseEnd_5104314 := by
    simpa [prefixWord, tailWord_5104314, baseEnd_5104314] using wordTrace_append hprefix tailTrace_5104314
  have hstable : (prefixWord ++ tailWord_5104314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104314).length < 2 ^ (prefixWord ++ tailWord_5104314).sum := by decide
  have hdescent : baseEnd_5104314 < baseStart_5104314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104344 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 1, 7]
def baseStart_5104344 : Nat := 118140960795 + 5104344 * 2 ^ 59
def prefixEnd_5104344 : Nat := 4983230072969 + 3 ^ 40 * 5104344 * 2
def baseEnd_5104344 : Nat := 873660632631094154775185

theorem tailTrace_5104344 : CollatzResearch.WordTrace tailWord_5104344 prefixEnd_5104344 873660632631094154775185 := by
  unfold tailWord_5104344
  simp only [CollatzResearch.WordTrace]
  refine ⟨93085360109920457698272043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124113813479893943597696057 93085360109920457698272043)
  ·
    refine ⟨139628040164880686547408065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93085360109920457698272043 139628040164880686547408065)
    ·
      refine ⟨104721030123660514910556049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139628040164880686547408065 104721030123660514910556049)
      ·
        refine ⟨78540772592745386182917037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104721030123660514910556049 78540772592745386182917037)
        ·
          refine ⟨29452789722279519818593889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78540772592745386182917037 29452789722279519818593889)
          ·
            refine ⟨22089592291709639863945417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29452789722279519818593889 22089592291709639863945417)
            ·
              refine ⟨16567194218782229897959063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22089592291709639863945417 16567194218782229897959063)
              ·
                refine ⟨24850791328173344846938595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16567194218782229897959063 24850791328173344846938595)
                ·
                  refine ⟨37276186992260017270407893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24850791328173344846938595 37276186992260017270407893)
                  ·
                    refine ⟨873660632631094154775185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37276186992260017270407893 873660632631094154775185)
                    ·
                      rfl

theorem cell23_5104344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_5104344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104344 prefixEnd_5104344 := by exact prefixLift 5104344
  have htrace : WordTrace (prefixWord ++ tailWord_5104344) baseStart_5104344 baseEnd_5104344 := by
    simpa [prefixWord, tailWord_5104344, baseEnd_5104344] using wordTrace_append hprefix tailTrace_5104344
  have hstable : (prefixWord ++ tailWord_5104344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104344).length < 2 ^ (prefixWord ++ tailWord_5104344).sum := by decide
  have hdescent : baseEnd_5104344 < baseStart_5104344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104381 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 1, 6, 2]
def baseStart_5104381 : Nat := 118140960795 + 5104381 * 2 ^ 59
def prefixEnd_5104381 : Nat := 4983230072969 + 3 ^ 40 * 5104381 * 2
def baseEnd_5104381 : Nat := 2621000896677498819562885

theorem tailTrace_5104381 : CollatzResearch.WordTrace tailWord_5104381 prefixEnd_5104381 2621000896677498819562885 := by
  unfold tailWord_5104381
  simp only [CollatzResearch.WordTrace]
  refine ⟨186172069720706870715640997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124114713147137913810427331 186172069720706870715640997)
  ·
    refine ⟨34907263072632538259182687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186172069720706870715640997 34907263072632538259182687)
    ·
      refine ⟨52360894608948807388774031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34907263072632538259182687 52360894608948807388774031)
      ·
        refine ⟨78541341913423211083161047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52360894608948807388774031 78541341913423211083161047)
        ·
          refine ⟨117812012870134816624741571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78541341913423211083161047 117812012870134816624741571)
          ·
            refine ⟨176718019305202224937112357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117812012870134816624741571 176718019305202224937112357)
            ·
              refine ⟨33134628619725417175708567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176718019305202224937112357 33134628619725417175708567)
              ·
                refine ⟨49701942929588125763562851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33134628619725417175708567 49701942929588125763562851)
                ·
                  refine ⟨74552914394382188645344277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49701942929588125763562851 74552914394382188645344277)
                  ·
                    refine ⟨3494667862236665092750513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74552914394382188645344277 3494667862236665092750513)
                    ·
                      refine ⟨2621000896677498819562885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494667862236665092750513 2621000896677498819562885)
                      ·
                        rfl

theorem cell23_5104381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_5104381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104381 prefixEnd_5104381 := by exact prefixLift 5104381
  have htrace : WordTrace (prefixWord ++ tailWord_5104381) baseStart_5104381 baseEnd_5104381 := by
    simpa [prefixWord, tailWord_5104381, baseEnd_5104381] using wordTrace_append hprefix tailTrace_5104381
  have hstable : (prefixWord ++ tailWord_5104381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104381).length < 2 ^ (prefixWord ++ tailWord_5104381).sum := by decide
  have hdescent : baseEnd_5104381 < baseStart_5104381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104401 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 3]
def baseStart_5104401 : Nat := 118140960795 + 5104401 * 2 ^ 59
def prefixEnd_5104401 : Nat := 4983230072969 + 3 ^ 40 * 5104401 * 2
def baseEnd_5104401 : Nat := 2621011166290588741312793

theorem tailTrace_5104401 : CollatzResearch.WordTrace tailWord_5104401 prefixEnd_5104401 2621011166290588741312793 := by
  unfold tailWord_5104401
  simp only [CollatzResearch.WordTrace]
  refine ⟨186172799180634414131369057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124115199453756276087579371 186172799180634414131369057)
  ·
    refine ⟨139629599385475810598526793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186172799180634414131369057 139629599385475810598526793)
    ·
      refine ⟨104722199539106857948895095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139629599385475810598526793 104722199539106857948895095)
      ·
        refine ⟨157083299308660286923342643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104722199539106857948895095 157083299308660286923342643)
        ·
          refine ⟨235624948962990430385013965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157083299308660286923342643 235624948962990430385013965)
          ·
            refine ⟨88359355861121411394380237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235624948962990430385013965 88359355861121411394380237)
            ·
              refine ⟨33134758447920529272892589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88359355861121411394380237 33134758447920529272892589)
              ·
                refine ⟨12425534417970198477334721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33134758447920529272892589 12425534417970198477334721)
                ·
                  refine ⟨9319150813477648858001041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12425534417970198477334721 9319150813477648858001041)
                  ·
                    refine ⟨6989363110108236643500781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9319150813477648858001041 6989363110108236643500781)
                    ·
                      refine ⟨2621011166290588741312793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6989363110108236643500781 2621011166290588741312793)
                      ·
                        rfl

theorem cell23_5104401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_5104401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104401 prefixEnd_5104401 := by exact prefixLift 5104401
  have htrace : WordTrace (prefixWord ++ tailWord_5104401) baseStart_5104401 baseEnd_5104401 := by
    simpa [prefixWord, tailWord_5104401, baseEnd_5104401] using wordTrace_append hprefix tailTrace_5104401
  have hstable : (prefixWord ++ tailWord_5104401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104401).length < 2 ^ (prefixWord ++ tailWord_5104401).sum := by decide
  have hdescent : baseEnd_5104401 < baseStart_5104401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104408 : List Nat := [2, 1, 2, 3, 1, 1, 1, 7, 1, 4]
def baseStart_5104408 : Nat := 118140960795 + 5104408 * 2 ^ 59
def prefixEnd_5104408 : Nat := 4983230072969 + 3 ^ 40 * 5104408 * 2
def baseEnd_5104408 : Nat := 873671586885056737975087

theorem tailTrace_5104408 : CollatzResearch.WordTrace tailWord_5104408 prefixEnd_5104408 873671586885056737975087 := by
  unfold tailWord_5104408
  simp only [CollatzResearch.WordTrace]
  refine ⟨93086527245804527163436939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124115369661072702884582585 93086527245804527163436939)
  ·
    refine ⟨139629790868706790745155409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93086527245804527163436939 139629790868706790745155409)
    ·
      refine ⟨104722343151530093058866557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139629790868706790745155409 104722343151530093058866557)
      ·
        refine ⟨39270878681823784897074959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104722343151530093058866557 39270878681823784897074959)
        ·
          refine ⟨58906318022735677345612439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39270878681823784897074959 58906318022735677345612439)
          ·
            refine ⟨88359477034103516018418659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58906318022735677345612439 88359477034103516018418659)
            ·
              refine ⟨132539215551155274027627989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88359477034103516018418659 132539215551155274027627989)
              ·
                refine ⟨3106387864480201735022531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 132539215551155274027627989 3106387864480201735022531)
                ·
                  refine ⟨4659581796720302602533797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106387864480201735022531 4659581796720302602533797)
                  ·
                    refine ⟨873671586885056737975087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659581796720302602533797 873671586885056737975087)
                    ·
                      rfl

theorem cell23_5104408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_5104408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104408 prefixEnd_5104408 := by exact prefixLift 5104408
  have htrace : WordTrace (prefixWord ++ tailWord_5104408) baseStart_5104408 baseEnd_5104408 := by
    simpa [prefixWord, tailWord_5104408, baseEnd_5104408] using wordTrace_append hprefix tailTrace_5104408
  have hstable : (prefixWord ++ tailWord_5104408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104408).length < 2 ^ (prefixWord ++ tailWord_5104408).sum := by decide
  have hdescent : baseEnd_5104408 < baseStart_5104408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104418 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_5104418 : Nat := 118140960795 + 5104418 * 2 ^ 59
def prefixEnd_5104418 : Nat := 4983230072969 + 3 ^ 40 * 5104418 * 2
def baseEnd_5104418 : Nat := 2621019895461715174800215

theorem tailTrace_5104418 : CollatzResearch.WordTrace tailWord_5104418 prefixEnd_5104418 2621019895461715174800215 := by
  unfold tailWord_5104418
  simp only [CollatzResearch.WordTrace]
  refine ⟨46543354805393206508684477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124115612814381884023158605 46543354805393206508684477)
  ·
    refine ⟨17453758052022452440756679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46543354805393206508684477 17453758052022452440756679)
    ·
      refine ⟨26180637078033678661135019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17453758052022452440756679 26180637078033678661135019)
      ·
        refine ⟨39270955617050517991702529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26180637078033678661135019 39270955617050517991702529)
        ·
          refine ⟨29453216712787888493776897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39270955617050517991702529 29453216712787888493776897)
          ·
            refine ⟨22089912534590916370332673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29453216712787888493776897 22089912534590916370332673)
            ·
              refine ⟨16567434400943187277749505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22089912534590916370332673 16567434400943187277749505)
              ·
                refine ⟨12425575800707390458312129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16567434400943187277749505 12425575800707390458312129)
                ·
                  refine ⟨9319181850530542843734097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12425575800707390458312129 9319181850530542843734097)
                  ·
                    refine ⟨6989386387897907132800573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9319181850530542843734097 6989386387897907132800573)
                    ·
                      refine ⟨2621019895461715174800215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6989386387897907132800573 2621019895461715174800215)
                      ·
                        rfl

theorem cell23_5104418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_5104418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104418 prefixEnd_5104418 := by exact prefixLift 5104418
  have htrace : WordTrace (prefixWord ++ tailWord_5104418) baseStart_5104418 baseEnd_5104418 := by
    simpa [prefixWord, tailWord_5104418, baseEnd_5104418] using wordTrace_append hprefix tailTrace_5104418
  have hstable : (prefixWord ++ tailWord_5104418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104418).length < 2 ^ (prefixWord ++ tailWord_5104418).sum := by decide
  have hdescent : baseEnd_5104418 < baseStart_5104418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104421 : List Nat := [1, 3, 1, 2, 3, 1, 4, 2, 6]
def baseStart_5104421 : Nat := 118140960795 + 5104421 * 2 ^ 59
def prefixEnd_5104421 : Nat := 4983230072969 + 3 ^ 40 * 5104421 * 2
def baseEnd_5104421 : Nat := 291224603989297629229189

theorem tailTrace_5104421 : CollatzResearch.WordTrace tailWord_5104421 prefixEnd_5104421 291224603989297629229189 := by
  unfold tailWord_5104421
  simp only [CollatzResearch.WordTrace]
  refine ⟨186173528640561957547097117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124115685760374638364731411 186173528640561957547097117)
  ·
    refine ⟨69815073240210734080161419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186173528640561957547097117 69815073240210734080161419)
    ·
      refine ⟨104722609860316101120242129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69815073240210734080161419 104722609860316101120242129)
      ·
        refine ⟨78541957395237075840181597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104722609860316101120242129 78541957395237075840181597)
        ·
          refine ⟨29453234023213903440068099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78541957395237075840181597 29453234023213903440068099)
          ·
            refine ⟨44179851034820855160102149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29453234023213903440068099 44179851034820855160102149)
            ·
              refine ⟨8283722069028910342519153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44179851034820855160102149 8283722069028910342519153)
              ·
                refine ⟨6212791551771682756889365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8283722069028910342519153 6212791551771682756889365)
                ·
                  refine ⟨291224603989297629229189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6212791551771682756889365 291224603989297629229189)
                  ·
                    rfl

theorem cell23_5104421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_5104421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104421 prefixEnd_5104421 := by exact prefixLift 5104421
  have htrace : WordTrace (prefixWord ++ tailWord_5104421) baseStart_5104421 baseEnd_5104421 := by
    simpa [prefixWord, tailWord_5104421, baseEnd_5104421] using wordTrace_append hprefix tailTrace_5104421
  have hstable : (prefixWord ++ tailWord_5104421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104421).length < 2 ^ (prefixWord ++ tailWord_5104421).sum := by decide
  have hdescent : baseEnd_5104421 < baseStart_5104421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104444 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_5104444 : Nat := 118140960795 + 5104444 * 2 ^ 59
def prefixEnd_5104444 : Nat := 4983230072969 + 3 ^ 40 * 5104444 * 2
def baseEnd_5104444 : Nat := 2621033245958732073075095

theorem tailTrace_5104444 : CollatzResearch.WordTrace tailWord_5104444 prefixEnd_5104444 2621033245958732073075095 := by
  unfold tailWord_5104444
  simp only [CollatzResearch.WordTrace]
  refine ⟨93087183759739316237592193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124116245012985754983456257 93087183759739316237592193)
  ·
    refine ⟨69815387819804487178194145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93087183759739316237592193 69815387819804487178194145)
    ·
      refine ⟨52361540864853365383645609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69815387819804487178194145 52361540864853365383645609)
      ·
        refine ⟨39271155648640024037734207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52361540864853365383645609 39271155648640024037734207)
        ·
          refine ⟨58906733472960036056601311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39271155648640024037734207 58906733472960036056601311)
          ·
            refine ⟨88360100209440054084901967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58906733472960036056601311 88360100209440054084901967)
            ·
              refine ⟨132540150314160081127352951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88360100209440054084901967 132540150314160081127352951)
              ·
                refine ⟨198810225471240121691029427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132540150314160081127352951 198810225471240121691029427)
                ·
                  refine ⟨298215338206860182536544141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198810225471240121691029427 298215338206860182536544141)
                  ·
                    refine ⟨111830751827572568451204053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 298215338206860182536544141 111830751827572568451204053)
                    ·
                      refine ⟨2621033245958732073075095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111830751827572568451204053 2621033245958732073075095)
                      ·
                        rfl

theorem cell23_5104444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_5104444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104444 prefixEnd_5104444 := by exact prefixLift 5104444
  have htrace : WordTrace (prefixWord ++ tailWord_5104444) baseStart_5104444 baseEnd_5104444 := by
    simpa [prefixWord, tailWord_5104444, baseEnd_5104444] using wordTrace_append hprefix tailTrace_5104444
  have hstable : (prefixWord ++ tailWord_5104444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104444).length < 2 ^ (prefixWord ++ tailWord_5104444).sum := by decide
  have hdescent : baseEnd_5104444 < baseStart_5104444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104451 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 1, 5]
def baseStart_5104451 : Nat := 118140960795 + 5104451 * 2 ^ 59
def prefixEnd_5104451 : Nat := 4983230072969 + 3 ^ 40 * 5104451 * 2
def baseEnd_5104451 : Nat := 873678946774437848562521

theorem tailTrace_5104451 : CollatzResearch.WordTrace tailWord_5104451 prefixEnd_5104451 873678946774437848562521 := by
  unfold tailWord_5104451
  simp only [CollatzResearch.WordTrace]
  refine ⟨186174622830453272670689207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124116415220302181780459471 186174622830453272670689207)
  ·
    refine ⟨279261934245679909006033811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186174622830453272670689207 279261934245679909006033811)
    ·
      refine ⟨418892901368519863509050717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279261934245679909006033811 418892901368519863509050717)
      ·
        refine ⟨157084838013194948815894019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 418892901368519863509050717 157084838013194948815894019)
        ·
          refine ⟨235627257019792423223841029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157084838013194948815894019 235627257019792423223841029)
          ·
            refine ⟨44180110691211079354470193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235627257019792423223841029 44180110691211079354470193)
            ·
              refine ⟨33135083018408309515852645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44180110691211079354470193 33135083018408309515852645)
              ·
                refine ⟨6212828065951558034222371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33135083018408309515852645 6212828065951558034222371)
                ·
                  refine ⟨9319242098927337051333557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6212828065951558034222371 9319242098927337051333557)
                  ·
                    refine ⟨873678946774437848562521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9319242098927337051333557 873678946774437848562521)
                    ·
                      rfl

theorem cell23_5104451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 5].length) (baseStart_5104451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104451 prefixEnd_5104451 := by exact prefixLift 5104451
  have htrace : WordTrace (prefixWord ++ tailWord_5104451) baseStart_5104451 baseEnd_5104451 := by
    simpa [prefixWord, tailWord_5104451, baseEnd_5104451] using wordTrace_append hprefix tailTrace_5104451
  have hstable : (prefixWord ++ tailWord_5104451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104451).length < 2 ^ (prefixWord ++ tailWord_5104451).sum := by decide
  have hdescent : baseEnd_5104451 < baseStart_5104451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104458 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2]
def baseStart_5104458 : Nat := 118140960795 + 5104458 * 2 ^ 59
def prefixEnd_5104458 : Nat := 4983230072969 + 3 ^ 40 * 5104458 * 2
def baseEnd_5104458 : Nat := 2621040434687895018300031

theorem tailTrace_5104458 : CollatzResearch.WordTrace tailWord_5104458 prefixEnd_5104458 2621040434687895018300031 := by
  unfold tailWord_5104458
  simp only [CollatzResearch.WordTrace]
  refine ⟨46543719535356978216548507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124116585427618608577462685 46543719535356978216548507)
  ·
    refine ⟨69815579303035467324822761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46543719535356978216548507 69815579303035467324822761)
    ·
      refine ⟨52361684477276600493617071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69815579303035467324822761 52361684477276600493617071)
      ·
        refine ⟨78542526715914900740425607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52361684477276600493617071 78542526715914900740425607)
        ·
          refine ⟨117813790073872351110638411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78542526715914900740425607 117813790073872351110638411)
          ·
            refine ⟨176720685110808526665957617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117813790073872351110638411 176720685110808526665957617)
            ·
              refine ⟨132540513833106394999468213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176720685110808526665957617 132540513833106394999468213)
              ·
                refine ⟨12425673171853724531200145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132540513833106394999468213 12425673171853724531200145)
                ·
                  refine ⟨9319254878890293398400109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12425673171853724531200145 9319254878890293398400109)
                  ·
                    refine ⟨3494720579583860024400041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9319254878890293398400109 3494720579583860024400041)
                    ·
                      refine ⟨2621040434687895018300031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494720579583860024400041 2621040434687895018300031)
                      ·
                        rfl

theorem cell23_5104458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_5104458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104458 prefixEnd_5104458 := by exact prefixLift 5104458
  have htrace : WordTrace (prefixWord ++ tailWord_5104458) baseStart_5104458 baseEnd_5104458 := by
    simpa [prefixWord, tailWord_5104458, baseEnd_5104458] using wordTrace_append hprefix tailTrace_5104458
  have hstable : (prefixWord ++ tailWord_5104458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104458).length < 2 ^ (prefixWord ++ tailWord_5104458).sum := by decide
  have hdescent : baseEnd_5104458 < baseStart_5104458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104482 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_5104482 : Nat := 118140960795 + 5104482 * 2 ^ 59
def prefixEnd_5104482 : Nat := 4983230072969 + 3 ^ 40 * 5104482 * 2
def baseEnd_5104482 : Nat := 2621052758223602924399921

theorem tailTrace_5104482 : CollatzResearch.WordTrace tailWord_5104482 prefixEnd_5104482 2621052758223602924399921 := by
  unfold tailWord_5104482
  simp only [CollatzResearch.WordTrace]
  refine ⟨46543938373335241241266925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124117168995560643310045133 46543938373335241241266925)
  ·
    refine ⟨17453976890000715465475097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46543938373335241241266925 17453976890000715465475097)
    ·
      refine ⟨13090482667500536599106323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17453976890000715465475097 13090482667500536599106323)
      ·
        refine ⟨19635724001250804898659485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13090482667500536599106323 19635724001250804898659485)
        ·
          refine ⟨7363396500469051836997307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19635724001250804898659485 7363396500469051836997307)
          ·
            refine ⟨11045094750703577755495961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7363396500469051836997307 11045094750703577755495961)
            ·
              refine ⟨8283821063027683316621971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11045094750703577755495961 8283821063027683316621971)
              ·
                refine ⟨12425731594541524974932957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8283821063027683316621971 12425731594541524974932957)
                ·
                  refine ⟨4659649347953071865599859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12425731594541524974932957 4659649347953071865599859)
                  ·
                    refine ⟨6989474021929607798399789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4659649347953071865599859 6989474021929607798399789)
                    ·
                      refine ⟨2621052758223602924399921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6989474021929607798399789 2621052758223602924399921)
                      ·
                        rfl

theorem cell23_5104482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_5104482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104482 prefixEnd_5104482 := by exact prefixLift 5104482
  have htrace : WordTrace (prefixWord ++ tailWord_5104482) baseStart_5104482 baseEnd_5104482 := by
    simpa [prefixWord, tailWord_5104482, baseEnd_5104482] using wordTrace_append hprefix tailTrace_5104482
  have hstable : (prefixWord ++ tailWord_5104482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104482).length < 2 ^ (prefixWord ++ tailWord_5104482).sum := by decide
  have hdescent : baseEnd_5104482 < baseStart_5104482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104491 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 3]
def baseStart_5104491 : Nat := 118140960795 + 5104491 * 2 ^ 59
def prefixEnd_5104491 : Nat := 4983230072969 + 3 ^ 40 * 5104491 * 2
def baseEnd_5104491 : Nat := 2621057379549493389187379

theorem tailTrace_5104491 : CollatzResearch.WordTrace tailWord_5104491 prefixEnd_5104491 2621057379549493389187379 := by
  unfold tailWord_5104491
  simp only [CollatzResearch.WordTrace]
  refine ⟨186176081750308359502145327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124117387833538906334763551 186176081750308359502145327)
  ·
    refine ⟨279264122625462539253217991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186176081750308359502145327 279264122625462539253217991)
    ·
      refine ⟨418896183938193808879826987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279264122625462539253217991 418896183938193808879826987)
      ·
        refine ⟨628344275907290713319740481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418896183938193808879826987 628344275907290713319740481)
        ·
          refine ⟨471258206930468034989805361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 628344275907290713319740481 471258206930468034989805361)
          ·
            refine ⟨353443655197851026242354021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471258206930468034989805361 353443655197851026242354021)
            ·
              refine ⟨66270685349597067420441379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 353443655197851026242354021 66270685349597067420441379)
              ·
                refine ⟨99406028024395601130662069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66270685349597067420441379 99406028024395601130662069)
                ·
                  refine ⟨9319315127287087605999569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99406028024395601130662069 9319315127287087605999569)
                  ·
                    refine ⟨6989486345465315704499677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9319315127287087605999569 6989486345465315704499677)
                    ·
                      refine ⟨2621057379549493389187379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6989486345465315704499677 2621057379549493389187379)
                      ·
                        rfl

theorem cell23_5104491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 3].length) (baseStart_5104491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104491 prefixEnd_5104491 := by exact prefixLift 5104491
  have htrace : WordTrace (prefixWord ++ tailWord_5104491) baseStart_5104491 baseEnd_5104491 := by
    simpa [prefixWord, tailWord_5104491, baseEnd_5104491] using wordTrace_append hprefix tailTrace_5104491
  have hstable : (prefixWord ++ tailWord_5104491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104491).length < 2 ^ (prefixWord ++ tailWord_5104491).sum := by decide
  have hdescent : baseEnd_5104491 < baseStart_5104491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104498 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_5104498 : Nat := 118140960795 + 5104498 * 2 ^ 59
def prefixEnd_5104498 : Nat := 4983230072969 + 3 ^ 40 * 5104498 * 2
def baseEnd_5104498 : Nat := 873686991304691620599949

theorem tailTrace_5104498 : CollatzResearch.WordTrace tailWord_5104498 prefixEnd_5104498 873686991304691620599949 := by
  unfold tailWord_5104498
  simp only [CollatzResearch.WordTrace]
  refine ⟨46544084265320749924412537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124117558040855333131766765 46544084265320749924412537)
  ·
    refine ⟨34908063198990562443309403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46544084265320749924412537 34908063198990562443309403)
    ·
      refine ⟨52362094798485843664964105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34908063198990562443309403 52362094798485843664964105)
      ·
        refine ⟨39271571098864382748723079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52362094798485843664964105 39271571098864382748723079)
        ·
          refine ⟨58907356648296574123084619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39271571098864382748723079 58907356648296574123084619)
          ·
            refine ⟨88361034972444861184626929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58907356648296574123084619 88361034972444861184626929)
            ·
              refine ⟨66270776229333645888470197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88361034972444861184626929 66270776229333645888470197)
              ·
                refine ⟨6212885271500029302044081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66270776229333645888470197 6212885271500029302044081)
                ·
                  refine ⟨4659663953625021976533061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6212885271500029302044081 4659663953625021976533061)
                  ·
                    refine ⟨873686991304691620599949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659663953625021976533061 873686991304691620599949)
                    ·
                      rfl

theorem cell23_5104498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_5104498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104498 prefixEnd_5104498 := by exact prefixLift 5104498
  have htrace : WordTrace (prefixWord ++ tailWord_5104498) baseStart_5104498 baseEnd_5104498 := by
    simpa [prefixWord, tailWord_5104498, baseEnd_5104498] using wordTrace_append hprefix tailTrace_5104498
  have hstable : (prefixWord ++ tailWord_5104498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104498).length < 2 ^ (prefixWord ++ tailWord_5104498).sum := by decide
  have hdescent : baseEnd_5104498 < baseStart_5104498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104505 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 3, 2, 2]
def baseStart_5104505 : Nat := 118140960795 + 5104505 * 2 ^ 59
def prefixEnd_5104505 : Nat := 4983230072969 + 3 ^ 40 * 5104505 * 2
def baseEnd_5104505 : Nat := 2621064568278656334412315

theorem tailTrace_5104505 : CollatzResearch.WordTrace tailWord_5104505 prefixEnd_5104505 2621064568278656334412315 := by
  unfold tailWord_5104505
  simp only [CollatzResearch.WordTrace]
  refine ⟨186176592372257639893154969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124117728248171759928769979 186176592372257639893154969)
  ·
    refine ⟨139632444279193229919866227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186176592372257639893154969 139632444279193229919866227)
    ·
      refine ⟨209448666418789844879799341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139632444279193229919866227 209448666418789844879799341)
      ·
        refine ⟨78543249907046191829924753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209448666418789844879799341 78543249907046191829924753)
        ·
          refine ⟨58907437430284643872443565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78543249907046191829924753 58907437430284643872443565)
          ·
            refine ⟨22090289036356741452166337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58907437430284643872443565 22090289036356741452166337)
            ·
              refine ⟨16567716777267556089124753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22090289036356741452166337 16567716777267556089124753)
              ·
                refine ⟨12425787582950667066843565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16567716777267556089124753 12425787582950667066843565)
                ·
                  refine ⟨4659670343606500150066337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12425787582950667066843565 4659670343606500150066337)
                  ·
                    refine ⟨3494752757704875112549753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4659670343606500150066337 3494752757704875112549753)
                    ·
                      refine ⟨2621064568278656334412315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494752757704875112549753 2621064568278656334412315)
                      ·
                        rfl

theorem cell23_5104505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_5104505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104505 prefixEnd_5104505 := by exact prefixLift 5104505
  have htrace : WordTrace (prefixWord ++ tailWord_5104505) baseStart_5104505 baseEnd_5104505 := by
    simpa [prefixWord, tailWord_5104505, baseEnd_5104505] using wordTrace_append hprefix tailTrace_5104505
  have hstable : (prefixWord ++ tailWord_5104505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104505).length < 2 ^ (prefixWord ++ tailWord_5104505).sum := by decide
  have hdescent : baseEnd_5104505 < baseStart_5104505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104511 : List Nat := [1, 1, 2, 2, 1, 1, 8, 7]
def baseStart_5104511 : Nat := 118140960795 + 5104511 * 2 ^ 59
def prefixEnd_5104511 : Nat := 4983230072969 + 3 ^ 40 * 5104511 * 2
def baseEnd_5104511 : Nat := 97076579598614196701381

theorem tailTrace_5104511 : CollatzResearch.WordTrace tailWord_5104511 prefixEnd_5104511 97076579598614196701381 := by
  unfold tailWord_5104511
  simp only [CollatzResearch.WordTrace]
  refine ⟨186176811210235902917873387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124117874140157268611915591 186176811210235902917873387)
  ·
    refine ⟨279265216815353854376810081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186176811210235902917873387 279265216815353854376810081)
    ·
      refine ⟨209448912611515390782607561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279265216815353854376810081 209448912611515390782607561)
      ·
        refine ⟨157086684458636543086955671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209448912611515390782607561 157086684458636543086955671)
        ·
          refine ⟨235630026687954814630433507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157086684458636543086955671 235630026687954814630433507)
          ·
            refine ⟨353445040031932221945650261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235630026687954814630433507 353445040031932221945650261)
            ·
              refine ⟨4141934062874205725925589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 353445040031932221945650261 4141934062874205725925589)
              ·
                refine ⟨97076579598614196701381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4141934062874205725925589 97076579598614196701381)
                ·
                  rfl

theorem cell23_5104511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 8, 7].length) (baseStart_5104511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104511 prefixEnd_5104511 := by exact prefixLift 5104511
  have htrace : WordTrace (prefixWord ++ tailWord_5104511) baseStart_5104511 baseEnd_5104511 := by
    simpa [prefixWord, tailWord_5104511, baseEnd_5104511] using wordTrace_append hprefix tailTrace_5104511
  have hstable : (prefixWord ++ tailWord_5104511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104511).length < 2 ^ (prefixWord ++ tailWord_5104511).sum := by decide
  have hdescent : baseEnd_5104511 < baseStart_5104511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104541 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_5104541 : Nat := 118140960795 + 5104541 * 2 ^ 59
def prefixEnd_5104541 : Nat := 4983230072969 + 3 ^ 40 * 5104541 * 2
def baseEnd_5104541 : Nat := 873694351194072731187383

theorem tailTrace_5104541 : CollatzResearch.WordTrace tailWord_5104541 prefixEnd_5104541 873694351194072731187383 := by
  unfold tailWord_5104541
  simp only [CollatzResearch.WordTrace]
  refine ⟨186177905400127218041465477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124118603600084812027643651 186177905400127218041465477)
  ·
    refine ⟨34908357262523853382774777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186177905400127218041465477 34908357262523853382774777)
    ·
      refine ⟨26181267946892890037081083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34908357262523853382774777 26181267946892890037081083)
      ·
        refine ⟨39271901920339335055621625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26181267946892890037081083 39271901920339335055621625)
        ·
          refine ⟨29453926440254501291716219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39271901920339335055621625 29453926440254501291716219)
          ·
            refine ⟨44180889660381751937574329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29453926440254501291716219 44180889660381751937574329)
            ·
              refine ⟨33135667245286313953180747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44180889660381751937574329 33135667245286313953180747)
              ·
                refine ⟨49703500867929470929771121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33135667245286313953180747 49703500867929470929771121)
                ·
                  refine ⟨37277625650947103197328341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49703500867929470929771121 37277625650947103197328341)
                  ·
                    refine ⟨873694351194072731187383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37277625650947103197328341 873694351194072731187383)
                    ·
                      rfl

theorem cell23_5104541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_5104541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104541 prefixEnd_5104541 := by exact prefixLift 5104541
  have htrace : WordTrace (prefixWord ++ tailWord_5104541) baseStart_5104541 baseEnd_5104541 := by
    simpa [prefixWord, tailWord_5104541, baseEnd_5104541] using wordTrace_append hprefix tailTrace_5104541
  have hstable : (prefixWord ++ tailWord_5104541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104541).length < 2 ^ (prefixWord ++ tailWord_5104541).sum := by decide
  have hdescent : baseEnd_5104541 < baseStart_5104541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104565 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 3, 3, 2]
def baseStart_5104565 : Nat := 118140960795 + 5104565 * 2 ^ 59
def prefixEnd_5104565 : Nat := 4983230072969 + 3 ^ 40 * 5104565 * 2
def baseEnd_5104565 : Nat := 2621095377117926099662039

theorem tailTrace_5104565 : CollatzResearch.WordTrace tailWord_5104565 prefixEnd_5104565 2621095377117926099662039 := by
  unfold tailWord_5104565
  simp only [CollatzResearch.WordTrace]
  refine ⟨186178780752040270140339149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124119187168026846760226099 186178780752040270140339149)
  ·
    refine ⟨69817042782015101302627181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186178780752040270140339149 69817042782015101302627181)
    ·
      refine ⟨26181391043255662988485193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69817042782015101302627181 26181391043255662988485193)
      ·
        refine ⟨19636043282441747241363895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26181391043255662988485193 19636043282441747241363895)
        ·
          refine ⟨29454064923662620862045843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19636043282441747241363895 29454064923662620862045843)
          ·
            refine ⟨44181097385493931293068765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29454064923662620862045843 44181097385493931293068765)
            ·
              refine ⟨16567911519560224234900787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44181097385493931293068765 16567911519560224234900787)
              ·
                refine ⟨24851867279340336352351181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16567911519560224234900787 24851867279340336352351181)
                ·
                  refine ⟨9319450229752626132131693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24851867279340336352351181 9319450229752626132131693)
                  ·
                    refine ⟨3494793836157234799549385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9319450229752626132131693 3494793836157234799549385)
                    ·
                      refine ⟨2621095377117926099662039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494793836157234799549385 2621095377117926099662039)
                      ·
                        rfl

theorem cell23_5104565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_5104565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104565 prefixEnd_5104565 := by exact prefixLift 5104565
  have htrace : WordTrace (prefixWord ++ tailWord_5104565) baseStart_5104565 baseEnd_5104565 := by
    simpa [prefixWord, tailWord_5104565, baseEnd_5104565] using wordTrace_append hprefix tailTrace_5104565
  have hstable : (prefixWord ++ tailWord_5104565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104565).length < 2 ^ (prefixWord ++ tailWord_5104565).sum := by decide
  have hdescent : baseEnd_5104565 < baseStart_5104565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104618 : List Nat := [3, 1, 3, 1, 2, 3, 1, 2, 7]
def baseStart_5104618 : Nat := 118140960795 + 5104618 * 2 ^ 59
def prefixEnd_5104618 : Nat := 4983230072969 + 3 ^ 40 * 5104618 * 2
def baseEnd_5104618 : Nat := 291235843510290488033255

theorem tailTrace_5104618 : CollatzResearch.WordTrace tailWord_5104618 prefixEnd_5104618 291235843510290488033255 := by
  unfold tailWord_5104618
  simp only [CollatzResearch.WordTrace]
  refine ⟨46545178455212065048004627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124120475880565506794679005 46545178455212065048004627)
  ·
    refine ⟨69817767682818097572006941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46545178455212065048004627 69817767682818097572006941)
    ·
      refine ⟨26181662881056786589502603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69817767682818097572006941 26181662881056786589502603)
      ·
        refine ⟨39272494321585179884253905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26181662881056786589502603 39272494321585179884253905)
        ·
          refine ⟨29454370741188884913190429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39272494321585179884253905 29454370741188884913190429)
          ·
            refine ⟨11045389027945831842446411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29454370741188884913190429 11045389027945831842446411)
            ·
              refine ⟨16568083541918747763669617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11045389027945831842446411 16568083541918747763669617)
              ·
                refine ⟨12426062656439060822752213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16568083541918747763669617 12426062656439060822752213)
                ·
                  refine ⟨291235843510290488033255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12426062656439060822752213 291235843510290488033255)
                  ·
                    rfl

theorem cell23_5104618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_5104618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104618 prefixEnd_5104618 := by exact prefixLift 5104618
  have htrace : WordTrace (prefixWord ++ tailWord_5104618) baseStart_5104618 baseEnd_5104618 := by
    simpa [prefixWord, tailWord_5104618, baseEnd_5104618] using wordTrace_append hprefix tailTrace_5104618
  have hstable : (prefixWord ++ tailWord_5104618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104618).length < 2 ^ (prefixWord ++ tailWord_5104618).sum := by decide
  have hdescent : baseEnd_5104618 < baseStart_5104618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104688 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 3]
def baseStart_5104688 : Nat := 118140960795 + 5104688 * 2 ^ 59
def prefixEnd_5104688 : Nat := 4983230072969 + 3 ^ 40 * 5104688 * 2
def baseEnd_5104688 : Nat := 2621158535238429118423973

theorem tailTrace_5104688 : CollatzResearch.WordTrace tailWord_5104688 prefixEnd_5104688 2621158535238429118423973 := by
  unfold tailWord_5104688
  simp only [CollatzResearch.WordTrace]
  refine ⟨93091633465297331073533359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124122177953729774764711145 93091633465297331073533359)
  ·
    refine ⟨139637450197945996610300039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93091633465297331073533359 139637450197945996610300039)
    ·
      refine ⟨209456175296918994915450059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139637450197945996610300039 209456175296918994915450059)
      ·
        refine ⟨314184262945378492373175089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209456175296918994915450059 314184262945378492373175089)
        ·
          refine ⟨235638197209033869279881317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314184262945378492373175089 235638197209033869279881317)
          ·
            refine ⟨44182161976693850489977747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 235638197209033869279881317 44182161976693850489977747)
            ·
              refine ⟨66273242965040775734966621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44182161976693850489977747 66273242965040775734966621)
              ·
                refine ⟨24852466111890290900612483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66273242965040775734966621 24852466111890290900612483)
                ·
                  refine ⟨37278699167835436350918725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24852466111890290900612483 37278699167835436350918725)
                  ·
                    refine ⟨6989756093969144315797261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37278699167835436350918725 6989756093969144315797261)
                    ·
                      refine ⟨2621158535238429118423973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6989756093969144315797261 2621158535238429118423973)
                      ·
                        rfl

theorem cell23_5104688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 3].length) (baseStart_5104688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104688 prefixEnd_5104688 := by exact prefixLift 5104688
  have htrace : WordTrace (prefixWord ++ tailWord_5104688) baseStart_5104688 baseEnd_5104688 := by
    simpa [prefixWord, tailWord_5104688, baseEnd_5104688] using wordTrace_append hprefix tailTrace_5104688
  have hstable : (prefixWord ++ tailWord_5104688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104688).length < 2 ^ (prefixWord ++ tailWord_5104688).sum := by decide
  have hdescent : baseEnd_5104688 < baseStart_5104688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104702 : List Nat := [4, 2, 1, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5104702 : Nat := 118140960795 + 5104702 * 2 ^ 59
def prefixEnd_5104702 : Nat := 4983230072969 + 3 ^ 40 * 5104702 * 2
def baseEnd_5104702 : Nat := 2621165723967592063648909

theorem tailTrace_5104702 : CollatzResearch.WordTrace tailWord_5104702 prefixEnd_5104702 2621165723967592063648909 := by
  unfold tailWord_5104702
  simp only [CollatzResearch.WordTrace]
  refine ⟨23272972194067992817259545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124122518368362628358717573 23272972194067992817259545)
  ·
    refine ⟨17454729145550994612944659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23272972194067992817259545 17454729145550994612944659)
    ·
      refine ⟨26182093718326491919416989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17454729145550994612944659 26182093718326491919416989)
      ·
        refine ⟨9818285144372434469781371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26182093718326491919416989 9818285144372434469781371)
        ·
          refine ⟨14727427716558651704672057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9818285144372434469781371 14727427716558651704672057)
          ·
            refine ⟨11045570787418988778504043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14727427716558651704672057 11045570787418988778504043)
            ·
              refine ⟨16568356181128483167756065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11045570787418988778504043 16568356181128483167756065)
              ·
                refine ⟨12426267135846362375817049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16568356181128483167756065 12426267135846362375817049)
                ·
                  refine ⟨9319700351884771781862787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12426267135846362375817049 9319700351884771781862787)
                  ·
                    refine ⟨13979550527827157672794181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9319700351884771781862787 13979550527827157672794181)
                    ·
                      refine ⟨2621165723967592063648909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13979550527827157672794181 2621165723967592063648909)
                      ·
                        rfl

theorem cell23_5104702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5104702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104702 prefixEnd_5104702 := by exact prefixLift 5104702
  have htrace : WordTrace (prefixWord ++ tailWord_5104702) baseStart_5104702 baseEnd_5104702 := by
    simpa [prefixWord, tailWord_5104702, baseEnd_5104702] using wordTrace_append hprefix tailTrace_5104702
  have hstable : (prefixWord ++ tailWord_5104702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104702).length < 2 ^ (prefixWord ++ tailWord_5104702).sum := by decide
  have hdescent : baseEnd_5104702 < baseStart_5104702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104735 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 5, 1, 3]
def baseStart_5104735 : Nat := 118140960795 + 5104735 * 2 ^ 59
def prefixEnd_5104735 : Nat := 4983230072969 + 3 ^ 40 * 5104735 * 2
def baseEnd_5104735 : Nat := 2621182668829190434536257

theorem tailTrace_5104735 : CollatzResearch.WordTrace tailWord_5104735 prefixEnd_5104735 2621182668829190434536257 := by
  unfold tailWord_5104735
  simp only [CollatzResearch.WordTrace]
  refine ⟨186184981161424389174027659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124123320774282926116018439 186184981161424389174027659)
  ·
    refine ⟨279277471742136583761041489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186184981161424389174027659 279277471742136583761041489)
    ·
      refine ⟨209458103806602437820781117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279277471742136583761041489 209458103806602437820781117)
      ·
        refine ⟨78546788927475914182792919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209458103806602437820781117 78546788927475914182792919)
        ·
          refine ⟨117820183391213871274189379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78546788927475914182792919 117820183391213871274189379)
          ·
            refine ⟨176730275086820806911284069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117820183391213871274189379 176730275086820806911284069)
            ·
              refine ⟨33136926578778901295865763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176730275086820806911284069 33136926578778901295865763)
              ·
                refine ⟨49705389868168351943798645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33136926578778901295865763 49705389868168351943798645)
                ·
                  refine ⟨4659880300140782994731123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49705389868168351943798645 4659880300140782994731123)
                  ·
                    refine ⟨6989820450211174492096685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4659880300140782994731123 6989820450211174492096685)
                    ·
                      refine ⟨2621182668829190434536257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6989820450211174492096685 2621182668829190434536257)
                      ·
                        rfl

theorem cell23_5104735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 1, 3].length) (baseStart_5104735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104735 prefixEnd_5104735 := by exact prefixLift 5104735
  have htrace : WordTrace (prefixWord ++ tailWord_5104735) baseStart_5104735 baseEnd_5104735 := by
    simpa [prefixWord, tailWord_5104735, baseEnd_5104735] using wordTrace_append hprefix tailTrace_5104735
  have hstable : (prefixWord ++ tailWord_5104735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104735).length < 2 ^ (prefixWord ++ tailWord_5104735).sum := by decide
  have hdescent : baseEnd_5104735 < baseStart_5104735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104775 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 2, 6, 2]
def baseStart_5104775 : Nat := 118140960795 + 5104775 * 2 ^ 59
def prefixEnd_5104775 : Nat := 4983230072969 + 3 ^ 40 * 5104775 * 2
def baseEnd_5104775 : Nat := 2621203208055370278036073

theorem tailTrace_5104775 : CollatzResearch.WordTrace tailWord_5104775 prefixEnd_5104775 2621203208055370278036073 := by
  unfold tailWord_5104775
  simp only [CollatzResearch.WordTrace]
  refine ⟨186186440081279476005483779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124124293387519650670322519 186186440081279476005483779)
  ·
    refine ⟨279279660121919214008225669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186186440081279476005483779 279279660121919214008225669)
    ·
      refine ⟨52364936272859852626542313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279279660121919214008225669 52364936272859852626542313)
      ·
        refine ⟨39273702204644889469906735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52364936272859852626542313 39273702204644889469906735)
        ·
          refine ⟨58910553306967334204860103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39273702204644889469906735 58910553306967334204860103)
          ·
            refine ⟨88365829960451001307290155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58910553306967334204860103 88365829960451001307290155)
            ·
              refine ⟨132548744940676501960935233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88365829960451001307290155 132548744940676501960935233)
              ·
                refine ⟨99411558705507376470701425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132548744940676501960935233 99411558705507376470701425)
                ·
                  refine ⟨74558669029130532353026069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99411558705507376470701425 74558669029130532353026069)
                  ·
                    refine ⟨3494937610740493704048097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74558669029130532353026069 3494937610740493704048097)
                    ·
                      refine ⟨2621203208055370278036073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494937610740493704048097 2621203208055370278036073)
                      ·
                        rfl

theorem cell23_5104775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_5104775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104775 prefixEnd_5104775 := by exact prefixLift 5104775
  have htrace : WordTrace (prefixWord ++ tailWord_5104775) baseStart_5104775 baseEnd_5104775 := by
    simpa [prefixWord, tailWord_5104775, baseEnd_5104775] using wordTrace_append hprefix tailTrace_5104775
  have hstable : (prefixWord ++ tailWord_5104775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104775).length < 2 ^ (prefixWord ++ tailWord_5104775).sum := by decide
  have hdescent : baseEnd_5104775 < baseStart_5104775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104805 : List Nat := [1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_5104805 : Nat := 118140960795 + 5104805 * 2 ^ 59
def prefixEnd_5104805 : Nat := 4983230072969 + 3 ^ 40 * 5104805 * 2
def baseEnd_5104805 : Nat := 2621218612475005160660935

theorem tailTrace_5104805 : CollatzResearch.WordTrace tailWord_5104805 prefixEnd_5104805 2621218612475005160660935 := by
  unfold tailWord_5104805
  simp only [CollatzResearch.WordTrace]
  refine ⟨186187534271170791129075869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124125022847447194086050579 186187534271170791129075869)
  ·
    refine ⟨69820325351689046673403451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186187534271170791129075869 69820325351689046673403451)
    ·
      refine ⟨104730488027533570010105177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69820325351689046673403451 104730488027533570010105177)
      ·
        refine ⟨78547866020650177507578883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104730488027533570010105177 78547866020650177507578883)
        ·
          refine ⟨117821799030975266261368325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78547866020650177507578883 117821799030975266261368325)
          ·
            refine ⟨22091587318307862424006561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117821799030975266261368325 22091587318307862424006561)
            ·
              refine ⟨16568690488730896818004921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22091587318307862424006561 16568690488730896818004921)
              ·
                refine ⟨12426517866548172613503691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16568690488730896818004921 12426517866548172613503691)
                ·
                  refine ⟨18639776799822258920255537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12426517866548172613503691 18639776799822258920255537)
                  ·
                    refine ⟨13979832599866694190191653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18639776799822258920255537 13979832599866694190191653)
                    ·
                      refine ⟨2621218612475005160660935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13979832599866694190191653 2621218612475005160660935)
                      ·
                        rfl

theorem cell23_5104805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_5104805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104805 prefixEnd_5104805 := by exact prefixLift 5104805
  have htrace : WordTrace (prefixWord ++ tailWord_5104805) baseStart_5104805 baseEnd_5104805 := by
    simpa [prefixWord, tailWord_5104805, baseEnd_5104805] using wordTrace_append hprefix tailTrace_5104805
  have hstable : (prefixWord ++ tailWord_5104805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104805).length < 2 ^ (prefixWord ++ tailWord_5104805).sum := by decide
  have hdescent : baseEnd_5104805 < baseStart_5104805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104835 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 2, 7, 2]
def baseStart_5104835 : Nat := 118140960795 + 5104835 * 2 ^ 59
def prefixEnd_5104835 : Nat := 4983230072969 + 3 ^ 40 * 5104835 * 2
def baseEnd_5104835 : Nat := 2621234016894640043285797

theorem tailTrace_5104835 : CollatzResearch.WordTrace tailWord_5104835 prefixEnd_5104835 2621234016894640043285797 := by
  unfold tailWord_5104835
  simp only [CollatzResearch.WordTrace]
  refine ⟨186188628461062106252667959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124125752307374737501778639 186188628461062106252667959)
  ·
    refine ⟨279282942691593159379001939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186188628461062106252667959 279282942691593159379001939)
    ·
      refine ⟨418924414037389739068502909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279282942691593159379001939 418924414037389739068502909)
      ·
        refine ⟨157096655264021152150688591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 418924414037389739068502909 157096655264021152150688591)
        ·
          refine ⟨235644982896031728226032887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157096655264021152150688591 235644982896031728226032887)
          ·
            refine ⟨353467474344047592339049331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235644982896031728226032887 353467474344047592339049331)
            ·
              refine ⟨530201211516071388508573997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353467474344047592339049331 530201211516071388508573997)
              ·
                refine ⟨198825454318526770690715249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530201211516071388508573997 198825454318526770690715249)
                ·
                  refine ⟨149119090738895078018036437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198825454318526770690715249 149119090738895078018036437)
                  ·
                    refine ⟨3494978689192853391047729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 149119090738895078018036437 3494978689192853391047729)
                    ·
                      refine ⟨2621234016894640043285797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3494978689192853391047729 2621234016894640043285797)
                      ·
                        rfl

theorem cell23_5104835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 7, 2].length) (baseStart_5104835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104835 prefixEnd_5104835 := by exact prefixLift 5104835
  have htrace : WordTrace (prefixWord ++ tailWord_5104835) baseStart_5104835 baseEnd_5104835 := by
    simpa [prefixWord, tailWord_5104835, baseEnd_5104835] using wordTrace_append hprefix tailTrace_5104835
  have hstable : (prefixWord ++ tailWord_5104835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104835).length < 2 ^ (prefixWord ++ tailWord_5104835).sum := by decide
  have hdescent : baseEnd_5104835 < baseStart_5104835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104836 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 2, 4]
def baseStart_5104836 : Nat := 118140960795 + 5104836 * 2 ^ 59
def prefixEnd_5104836 : Nat := 4983230072969 + 3 ^ 40 * 5104836 * 2
def baseEnd_5104836 : Nat := 873744843458431513124431

theorem tailTrace_5104836 : CollatzResearch.WordTrace tailWord_5104836 prefixEnd_5104836 873744843458431513124431 := by
  unfold tailWord_5104836
  simp only [CollatzResearch.WordTrace]
  refine ⟨93094332467029241711727181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124125776622705655615636241 93094332467029241711727181)
  ·
    refine ⟨34910374675135965641897693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93094332467029241711727181 34910374675135965641897693)
    ·
      refine ⟨13091390503175987115711635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34910374675135965641897693 13091390503175987115711635)
      ·
        refine ⟨19637085754763980673567453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13091390503175987115711635 19637085754763980673567453)
        ·
          refine ⟨7363907158036492752587795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19637085754763980673567453 7363907158036492752587795)
          ·
            refine ⟨11045860737054739128881693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7363907158036492752587795 11045860737054739128881693)
            ·
              refine ⟨4142197776395527173330635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11045860737054739128881693 4142197776395527173330635)
              ·
                refine ⟨6213296664593290759995953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4142197776395527173330635 6213296664593290759995953)
                ·
                  refine ⟨4659972498444968069996965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6213296664593290759995953 4659972498444968069996965)
                  ·
                    refine ⟨873744843458431513124431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4659972498444968069996965 873744843458431513124431)
                    ·
                      rfl

theorem cell23_5104836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_5104836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104836 prefixEnd_5104836 := by exact prefixLift 5104836
  have htrace : WordTrace (prefixWord ++ tailWord_5104836) baseStart_5104836 baseEnd_5104836 := by
    simpa [prefixWord, tailWord_5104836, baseEnd_5104836] using wordTrace_append hprefix tailTrace_5104836
  have hstable : (prefixWord ++ tailWord_5104836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104836).length < 2 ^ (prefixWord ++ tailWord_5104836).sum := by decide
  have hdescent : baseEnd_5104836 < baseStart_5104836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104842 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3]
def baseStart_5104842 : Nat := 118140960795 + 5104842 * 2 ^ 59
def prefixEnd_5104842 : Nat := 4983230072969 + 3 ^ 40 * 5104842 * 2
def baseEnd_5104842 : Nat := 2621237611259221515898265

theorem tailTrace_5104842 : CollatzResearch.WordTrace tailWord_5104842 prefixEnd_5104842 2621237611259221515898265 := by
  unfold tailWord_5104842
  simp only [CollatzResearch.WordTrace]
  refine ⟨46547220943009186612043195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124125922514691164298781853 46547220943009186612043195)
  ·
    refine ⟨69820831414513779918064793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46547220943009186612043195 69820831414513779918064793)
    ·
      refine ⟨52365623560885334938548595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69820831414513779918064793 52365623560885334938548595)
      ·
        refine ⟨78548435341328002407822893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52365623560885334938548595 78548435341328002407822893)
        ·
          refine ⟨29455663252998000902933585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78548435341328002407822893 29455663252998000902933585)
          ·
            refine ⟨22091747439748500677200189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29455663252998000902933585 22091747439748500677200189)
            ·
              refine ⟨8284405289905687753950071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22091747439748500677200189 8284405289905687753950071)
              ·
                refine ⟨12426607934858531630925107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8284405289905687753950071 12426607934858531630925107)
                ·
                  refine ⟨18639911902287797446387661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12426607934858531630925107 18639911902287797446387661)
                  ·
                    refine ⟨6989966963357924042395373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18639911902287797446387661 6989966963357924042395373)
                    ·
                      refine ⟨2621237611259221515898265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6989966963357924042395373 2621237611259221515898265)
                      ·
                        rfl

theorem cell23_5104842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_5104842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104842 prefixEnd_5104842 := by exact prefixLift 5104842
  have htrace : WordTrace (prefixWord ++ tailWord_5104842) baseStart_5104842 baseEnd_5104842 := by
    simpa [prefixWord, tailWord_5104842, baseEnd_5104842] using wordTrace_append hprefix tailTrace_5104842
  have hstable : (prefixWord ++ tailWord_5104842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104842).length < 2 ^ (prefixWord ++ tailWord_5104842).sum := by decide
  have hdescent : baseEnd_5104842 < baseStart_5104842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104915 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 3]
def baseStart_5104915 : Nat := 118140960795 + 5104915 * 2 ^ 59
def prefixEnd_5104915 : Nat := 4983230072969 + 3 ^ 40 * 5104915 * 2
def baseEnd_5104915 : Nat := 2621275095346999730285429

theorem tailTrace_5104915 : CollatzResearch.WordTrace tailWord_5104915 prefixEnd_5104915 2621275095346999730285429 := by
  unfold tailWord_5104915
  simp only [CollatzResearch.WordTrace]
  refine ⟨186191546300772279915580199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124127697533848186610386799 186191546300772279915580199)
  ·
    refine ⟨279287319451158419873370299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186191546300772279915580199 279287319451158419873370299)
    ·
      refine ⟨418930979176737629810055449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279287319451158419873370299 418930979176737629810055449)
      ·
        refine ⟨314198234382553222357541587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418930979176737629810055449 314198234382553222357541587)
        ·
          refine ⟨471297351573829833536312381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314198234382553222357541587 471297351573829833536312381)
          ·
            refine ⟨176736506840186187576117143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 471297351573829833536312381 176736506840186187576117143)
            ·
              refine ⟨265104760260279281364175715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176736506840186187576117143 265104760260279281364175715)
              ·
                refine ⟨397657140390418922046263573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265104760260279281364175715 397657140390418922046263573)
                ·
                  refine ⟨18640178455800886970918605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 397657140390418922046263573 18640178455800886970918605)
                  ·
                    refine ⟨6990066920925332614094477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18640178455800886970918605 6990066920925332614094477)
                    ·
                      refine ⟨2621275095346999730285429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6990066920925332614094477 2621275095346999730285429)
                      ·
                        rfl

theorem cell23_5104915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 3].length) (baseStart_5104915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104915 prefixEnd_5104915 := by exact prefixLift 5104915
  have htrace : WordTrace (prefixWord ++ tailWord_5104915) baseStart_5104915 baseEnd_5104915 := by
    simpa [prefixWord, tailWord_5104915, baseEnd_5104915] using wordTrace_append hprefix tailTrace_5104915
  have hstable : (prefixWord ++ tailWord_5104915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104915).length < 2 ^ (prefixWord ++ tailWord_5104915).sum := by decide
  have hdescent : baseEnd_5104915 < baseStart_5104915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104932 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_5104932 : Nat := 118140960795 + 5104932 * 2 ^ 59
def prefixEnd_5104932 : Nat := 4983230072969 + 3 ^ 40 * 5104932 * 2
def baseEnd_5104932 : Nat := 2621283824518126163772851

theorem tailTrace_5104932 : CollatzResearch.WordTrace tailWord_5104932 prefixEnd_5104932 2621283824518126163772851 := by
  unfold tailWord_5104932
  simp only [CollatzResearch.WordTrace]
  refine ⟨93096083170855345909474525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124128110894473794545966033 93096083170855345909474525)
  ·
    refine ⟨34911031189070754716052947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93096083170855345909474525 34911031189070754716052947)
    ·
      refine ⟨52366546783606132074079421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34911031189070754716052947 52366546783606132074079421)
      ·
        refine ⟨19637455043852299527779783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52366546783606132074079421 19637455043852299527779783)
        ·
          refine ⟨29456182565778449291669675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19637455043852299527779783 29456182565778449291669675)
          ·
            refine ⟨44184273848667673937504513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29456182565778449291669675 44184273848667673937504513)
            ·
              refine ⟨33138205386500755453128385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44184273848667673937504513 33138205386500755453128385)
              ·
                refine ⟨24853654039875566589846289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33138205386500755453128385 24853654039875566589846289)
                ·
                  refine ⟨18640240529906674942384717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24853654039875566589846289 18640240529906674942384717)
                  ·
                    refine ⟨6990090198715003103394269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18640240529906674942384717 6990090198715003103394269)
                    ·
                      refine ⟨2621283824518126163772851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6990090198715003103394269 2621283824518126163772851)
                      ·
                        rfl

theorem cell23_5104932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_5104932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104932 prefixEnd_5104932 := by exact prefixLift 5104932
  have htrace : WordTrace (prefixWord ++ tailWord_5104932) baseStart_5104932 baseEnd_5104932 := by
    simpa [prefixWord, tailWord_5104932, baseEnd_5104932] using wordTrace_append hprefix tailTrace_5104932
  have hstable : (prefixWord ++ tailWord_5104932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104932).length < 2 ^ (prefixWord ++ tailWord_5104932).sum := by decide
  have hdescent : baseEnd_5104932 < baseStart_5104932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104972 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_5104972 : Nat := 118140960795 + 5104972 * 2 ^ 59
def prefixEnd_5104972 : Nat := 4983230072969 + 3 ^ 40 * 5104972 * 2
def baseEnd_5104972 : Nat := 2621304363744306007272667

theorem tailTrace_5104972 : CollatzResearch.WordTrace tailWord_5104972 prefixEnd_5104972 2621304363744306007272667 := by
  unfold tailWord_5104972
  simp only [CollatzResearch.WordTrace]
  refine ⟨93096812630782889325202585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124129083507710519100270113 93096812630782889325202585)
  ·
    refine ⟨69822609473087166993901939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93096812630782889325202585 69822609473087166993901939)
    ·
      refine ⟨104733914209630750490852909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69822609473087166993901939 104733914209630750490852909)
      ·
        refine ⟨39275217828611531434069841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104733914209630750490852909 39275217828611531434069841)
        ·
          refine ⟨29456413371458648575552381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39275217828611531434069841 29456413371458648575552381)
          ·
            refine ⟨11046155014296993215832143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29456413371458648575552381 11046155014296993215832143)
            ·
              refine ⟨16569232521445489823748215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11046155014296993215832143 16569232521445489823748215)
              ·
                refine ⟨24853848782168234735622323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16569232521445489823748215 24853848782168234735622323)
                ·
                  refine ⟨37280773173252352103433485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24853848782168234735622323 37280773173252352103433485)
                  ·
                    refine ⟨13980289939969632038787557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37280773173252352103433485 13980289939969632038787557)
                    ·
                      refine ⟨2621304363744306007272667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13980289939969632038787557 2621304363744306007272667)
                      ·
                        rfl

theorem cell23_5104972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_5104972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104972 prefixEnd_5104972 := by exact prefixLift 5104972
  have htrace : WordTrace (prefixWord ++ tailWord_5104972) baseStart_5104972 baseEnd_5104972 := by
    simpa [prefixWord, tailWord_5104972, baseEnd_5104972] using wordTrace_append hprefix tailTrace_5104972
  have hstable : (prefixWord ++ tailWord_5104972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104972).length < 2 ^ (prefixWord ++ tailWord_5104972).sum := by decide
  have hdescent : baseEnd_5104972 < baseStart_5104972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104973 : List Nat := [1, 6, 1, 3, 1, 1, 2, 3, 5]
def baseStart_5104973 : Nat := 118140960795 + 5104973 * 2 ^ 59
def prefixEnd_5104973 : Nat := 4983230072969 + 3 ^ 40 * 5104973 * 2
def baseEnd_5104973 : Nat := 291256097469440055928907

theorem tailTrace_5104973 : CollatzResearch.WordTrace tailWord_5104973 prefixEnd_5104973 291256097469440055928907 := by
  unfold tailWord_5104973
  simp only [CollatzResearch.WordTrace]
  refine ⟨186193661734562155821191573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124129107823041437214127715 186193661734562155821191573)
  ·
    refine ⟨8727827893807601054118355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 186193661734562155821191573 8727827893807601054118355)
    ·
      refine ⟨13091741840711401581177533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8727827893807601054118355 13091741840711401581177533)
      ·
        refine ⟨4909403190266775592941575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13091741840711401581177533 4909403190266775592941575)
        ·
          refine ⟨7364104785400163389412363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4909403190266775592941575 7364104785400163389412363)
          ·
            refine ⟨11046157178100245084118545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7364104785400163389412363 11046157178100245084118545)
            ·
              refine ⟨8284617883575183813088909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11046157178100245084118545 8284617883575183813088909)
              ·
                refine ⟨3106731706340693929908341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8284617883575183813088909 3106731706340693929908341)
                ·
                  refine ⟨291256097469440055928907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3106731706340693929908341 291256097469440055928907)
                  ·
                    rfl

theorem cell23_5104973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_5104973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104973 prefixEnd_5104973 := by exact prefixLift 5104973
  have htrace : WordTrace (prefixWord ++ tailWord_5104973) baseStart_5104973 baseEnd_5104973 := by
    simpa [prefixWord, tailWord_5104973, baseEnd_5104973] using wordTrace_append hprefix tailTrace_5104973
  have hstable : (prefixWord ++ tailWord_5104973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104973).length < 2 ^ (prefixWord ++ tailWord_5104973).sum := by decide
  have hdescent : baseEnd_5104973 < baseStart_5104973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5104985 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_5104985 : Nat := 118140960795 + 5104985 * 2 ^ 59
def prefixEnd_5104985 : Nat := 4983230072969 + 3 ^ 40 * 5104985 * 2
def baseEnd_5104985 : Nat := 2621311038992814456410107

theorem tailTrace_5104985 : CollatzResearch.WordTrace tailWord_5104985 prefixEnd_5104985 2621311038992814456410107 := by
  unfold tailWord_5104985
  simp only [CollatzResearch.WordTrace]
  refine ⟨186194099410518681870628409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124129399607012454580418939 186194099410518681870628409)
  ·
    refine ⟨139645574557889011402971307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186194099410518681870628409 139645574557889011402971307)
    ·
      refine ⟨209468361836833517104456961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139645574557889011402971307 209468361836833517104456961)
      ·
        refine ⟨157101271377625137828342721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209468361836833517104456961 157101271377625137828342721)
        ·
          refine ⟨117825953533218853371257041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157101271377625137828342721 117825953533218853371257041)
          ·
            refine ⟨88369465149914140028442781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117825953533218853371257041 88369465149914140028442781)
            ·
              refine ⟨33138549431217802510666043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88369465149914140028442781 33138549431217802510666043)
              ·
                refine ⟨49707824146826703765999065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33138549431217802510666043 49707824146826703765999065)
                ·
                  refine ⟨37280868110120027824499299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49707824146826703765999065 37280868110120027824499299)
                  ·
                    refine ⟨55921302165180041736748949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37280868110120027824499299 55921302165180041736748949)
                    ·
                      refine ⟨2621311038992814456410107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55921302165180041736748949 2621311038992814456410107)
                      ·
                        rfl

theorem cell23_5104985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_5104985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5104985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5104985 prefixEnd_5104985 := by exact prefixLift 5104985
  have htrace : WordTrace (prefixWord ++ tailWord_5104985) baseStart_5104985 baseEnd_5104985 := by
    simpa [prefixWord, tailWord_5104985, baseEnd_5104985] using wordTrace_append hprefix tailTrace_5104985
  have hstable : (prefixWord ++ tailWord_5104985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5104985).length < 2 ^ (prefixWord ++ tailWord_5104985).sum := by decide
  have hdescent : baseEnd_5104985 < baseStart_5104985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5104985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105015 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_5105015 : Nat := 118140960795 + 5105015 * 2 ^ 59
def prefixEnd_5105015 : Nat := 4983230072969 + 3 ^ 40 * 5105015 * 2
def baseEnd_5105015 : Nat := 2621326443412449339034969

theorem tailTrace_5105015 : CollatzResearch.WordTrace tailWord_5105015 prefixEnd_5105015 2621326443412449339034969 := by
  unfold tailWord_5105015
  simp only [CollatzResearch.WordTrace]
  refine ⟨186195193600409996994220499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124130129066939997996146999 186195193600409996994220499)
  ·
    refine ⟨279292790400614995491330749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186195193600409996994220499 279292790400614995491330749)
    ·
      refine ⟨104734796400230623309249031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279292790400614995491330749 104734796400230623309249031)
      ·
        refine ⟨157102194600345934963873547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104734796400230623309249031 157102194600345934963873547)
        ·
          refine ⟨235653291900518902445810321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157102194600345934963873547 235653291900518902445810321)
          ·
            refine ⟨176739968925389176834357741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235653291900518902445810321 176739968925389176834357741)
            ·
              refine ⟨66277488347020941312884153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176739968925389176834357741 66277488347020941312884153)
              ·
                refine ⟨49708116260265705984663115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66277488347020941312884153 49708116260265705984663115)
                ·
                  refine ⟨74562174390398558976994673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49708116260265705984663115 74562174390398558976994673)
                  ·
                    refine ⟨55921630792798919232746005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74562174390398558976994673 55921630792798919232746005)
                    ·
                      refine ⟨2621326443412449339034969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55921630792798919232746005 2621326443412449339034969)
                      ·
                        rfl

theorem cell23_5105015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_5105015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105015 prefixEnd_5105015 := by exact prefixLift 5105015
  have htrace : WordTrace (prefixWord ++ tailWord_5105015) baseStart_5105015 baseEnd_5105015 := by
    simpa [prefixWord, tailWord_5105015, baseEnd_5105015] using wordTrace_append hprefix tailTrace_5105015
  have hstable : (prefixWord ++ tailWord_5105015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105015).length < 2 ^ (prefixWord ++ tailWord_5105015).sum := by decide
  have hdescent : baseEnd_5105015 < baseStart_5105015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105026 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_5105026 : Nat := 118140960795 + 5105026 * 2 ^ 59
def prefixEnd_5105026 : Nat := 4983230072969 + 3 ^ 40 * 5105026 * 2
def baseEnd_5105026 : Nat := 2621332091699648795997419

theorem tailTrace_5105026 : CollatzResearch.WordTrace tailWord_5105026 prefixEnd_5105026 2621332091699648795997419 := by
  unfold tailWord_5105026
  simp only [CollatzResearch.WordTrace]
  refine ⟨46548898700842536468217733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124130396535580097248580621 46548898700842536468217733)
  ·
    refine ⟨8727918506407975587790825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46548898700842536468217733 8727918506407975587790825)
    ·
      refine ⟨6545938879805981690843119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8727918506407975587790825 6545938879805981690843119)
      ·
        refine ⟨9818908319708972536264679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6545938879805981690843119 9818908319708972536264679)
        ·
          refine ⟨14728362479563458804397019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9818908319708972536264679 14728362479563458804397019)
          ·
            refine ⟨22092543719345188206595529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14728362479563458804397019 22092543719345188206595529)
            ·
              refine ⟨16569407789508891154946647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22092543719345188206595529 16569407789508891154946647)
              ·
                refine ⟨24854111684263336732419971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16569407789508891154946647 24854111684263336732419971)
                ·
                  refine ⟨37281167526395005098629957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24854111684263336732419971 37281167526395005098629957)
                  ·
                    refine ⟨6990218911199063455993117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37281167526395005098629957 6990218911199063455993117)
                    ·
                      refine ⟨2621332091699648795997419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6990218911199063455993117 2621332091699648795997419)
                      ·
                        rfl

theorem cell23_5105026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_5105026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105026 prefixEnd_5105026 := by exact prefixLift 5105026
  have htrace : WordTrace (prefixWord ++ tailWord_5105026) baseStart_5105026 baseEnd_5105026 := by
    simpa [prefixWord, tailWord_5105026, baseEnd_5105026] using wordTrace_append hprefix tailTrace_5105026
  have hstable : (prefixWord ++ tailWord_5105026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105026).length < 2 ^ (prefixWord ++ tailWord_5105026).sum := by decide
  have hdescent : baseEnd_5105026 < baseStart_5105026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105033 : List Nat := [1, 2, 1, 1, 7, 2, 1, 3, 1, 4]
def baseStart_5105033 : Nat := 118140960795 + 5105033 * 2 ^ 59
def prefixEnd_5105033 : Nat := 4983230072969 + 3 ^ 40 * 5105033 * 2
def baseEnd_5105033 : Nat := 873778562021410089536629

theorem tailTrace_5105033 : CollatzResearch.WordTrace tailWord_5105033 prefixEnd_5105033 873778562021410089536629 := by
  unfold tailWord_5105033
  simp only [CollatzResearch.WordTrace]
  refine ⟨186195850114344786068375753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124130566742896524045583835 186195850114344786068375753)
  ·
    refine ⟨139646887585758589551281815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186195850114344786068375753 139646887585758589551281815)
    ·
      refine ⟨209470331378637884326922723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139646887585758589551281815 209470331378637884326922723)
      ·
        refine ⟨314205497067956826490384085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209470331378637884326922723 314205497067956826490384085)
        ·
          refine ⟨7364191337530238120868377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 314205497067956826490384085 7364191337530238120868377)
          ·
            refine ⟨5523143503147678590651283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7364191337530238120868377 5523143503147678590651283)
            ·
              refine ⟨8284715254721517885976925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5523143503147678590651283 8284715254721517885976925)
              ·
                refine ⟨3106768220520569207241347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8284715254721517885976925 3106768220520569207241347)
                ·
                  refine ⟨4660152330780853810862021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3106768220520569207241347 4660152330780853810862021)
                  ·
                    refine ⟨873778562021410089536629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4660152330780853810862021 873778562021410089536629)
                    ·
                      rfl

theorem cell23_5105033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 1, 4].length) (baseStart_5105033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105033 prefixEnd_5105033 := by exact prefixLift 5105033
  have htrace : WordTrace (prefixWord ++ tailWord_5105033) baseStart_5105033 baseEnd_5105033 := by
    simpa [prefixWord, tailWord_5105033, baseEnd_5105033] using wordTrace_append hprefix tailTrace_5105033
  have hstable : (prefixWord ++ tailWord_5105033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105033).length < 2 ^ (prefixWord ++ tailWord_5105033).sum := by decide
  have hdescent : baseEnd_5105033 < baseStart_5105033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105049 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 4, 3, 2]
def baseStart_5105049 : Nat := 118140960795 + 5105049 * 2 ^ 59
def prefixEnd_5105049 : Nat := 4983230072969 + 3 ^ 40 * 5105049 * 2
def baseEnd_5105049 : Nat := 2621343901754702206009813

theorem tailTrace_5105049 : CollatzResearch.WordTrace tailWord_5105049 prefixEnd_5105049 2621343901754702206009813 := by
  unfold tailWord_5105049
  simp only [CollatzResearch.WordTrace]
  refine ⟨186196433682286820800958201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124130955788191213867305467 186196433682286820800958201)
  ·
    refine ⟨139647325261715115600718651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186196433682286820800958201 139647325261715115600718651)
    ·
      refine ⟨209470987892572673401077977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139647325261715115600718651 209470987892572673401077977)
      ·
        refine ⟨157103240919429505050808483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209470987892572673401077977 157103240919429505050808483)
        ·
          refine ⟨235654861379144257576212725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157103240919429505050808483 235654861379144257576212725)
          ·
            refine ⟨22092643254294774147769943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 235654861379144257576212725 22092643254294774147769943)
            ·
              refine ⟨33138964881442161221654915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22092643254294774147769943 33138964881442161221654915)
              ·
                refine ⟨49708447322163241832482373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33138964881442161221654915 49708447322163241832482373)
                ·
                  refine ⟨9320333872905607843590445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49708447322163241832482373 9320333872905607843590445)
                  ·
                    refine ⟨3495125202339602941346417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9320333872905607843590445 3495125202339602941346417)
                    ·
                      refine ⟨2621343901754702206009813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495125202339602941346417 2621343901754702206009813)
                      ·
                        rfl

theorem cell23_5105049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_5105049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105049 prefixEnd_5105049 := by exact prefixLift 5105049
  have htrace : WordTrace (prefixWord ++ tailWord_5105049) baseStart_5105049 baseEnd_5105049 := by
    simpa [prefixWord, tailWord_5105049, baseEnd_5105049] using wordTrace_append hprefix tailTrace_5105049
  have hstable : (prefixWord ++ tailWord_5105049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105049).length < 2 ^ (prefixWord ++ tailWord_5105049).sum := by decide
  have hdescent : baseEnd_5105049 < baseStart_5105049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105072 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 6, 4]
def baseStart_5105072 : Nat := 118140960795 + 5105072 * 2 ^ 59
def prefixEnd_5105072 : Nat := 4983230072969 + 3 ^ 40 * 5105072 * 2
def baseEnd_5105072 : Nat := 873785237269918538674069

theorem tailTrace_5105072 : CollatzResearch.WordTrace tailWord_5105072 prefixEnd_5105072 873785237269918538674069 := by
  unfold tailWord_5105072
  simp only [CollatzResearch.WordTrace]
  refine ⟨93098636280601747864522735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124131515040802330486030313 93098636280601747864522735)
  ·
    refine ⟨139647954420902621796784103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93098636280601747864522735 139647954420902621796784103)
    ·
      refine ⟨209471931631353932695176155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139647954420902621796784103 209471931631353932695176155)
      ·
        refine ⟨314207897447030899042764233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209471931631353932695176155 314207897447030899042764233)
        ·
          refine ⟨235655923085273174282073175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314207897447030899042764233 235655923085273174282073175)
          ·
            refine ⟨353483884627909761423109763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235655923085273174282073175 353483884627909761423109763)
            ·
              refine ⟨530225826941864642134664645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353483884627909761423109763 530225826941864642134664645)
              ·
                refine ⟨99417342551599620400249621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530225826941864642134664645 99417342551599620400249621)
                ·
                  refine ⟨4660187932106232206261701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99417342551599620400249621 4660187932106232206261701)
                  ·
                    refine ⟨873785237269918538674069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4660187932106232206261701 873785237269918538674069)
                    ·
                      rfl

theorem cell23_5105072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6, 4].length) (baseStart_5105072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105072 prefixEnd_5105072 := by exact prefixLift 5105072
  have htrace : WordTrace (prefixWord ++ tailWord_5105072) baseStart_5105072 baseEnd_5105072 := by
    simpa [prefixWord, tailWord_5105072, baseEnd_5105072] using wordTrace_append hprefix tailTrace_5105072
  have hstable : (prefixWord ++ tailWord_5105072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105072).length < 2 ^ (prefixWord ++ tailWord_5105072).sum := by decide
  have hdescent : baseEnd_5105072 < baseStart_5105072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105096 : List Nat := [2, 1, 3, 1, 3, 1, 5, 1, 1, 1, 4]
def baseStart_5105096 : Nat := 118140960795 + 5105096 * 2 ^ 59
def prefixEnd_5105096 : Nat := 4983230072969 + 3 ^ 40 * 5105096 * 2
def baseEnd_5105096 : Nat := 2621368035345463522122097

theorem tailTrace_5105096 : CollatzResearch.WordTrace tailWord_5105096 prefixEnd_5105096 2621368035345463522122097 := by
  unfold tailWord_5105096
  simp only [CollatzResearch.WordTrace]
  refine ⟨93099073956558273913959571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124132098608744365218612761 93099073956558273913959571)
  ·
    refine ⟨139648610934837410870939357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93099073956558273913959571 139648610934837410870939357)
    ·
      refine ⟨52368229100564029076602259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139648610934837410870939357 52368229100564029076602259)
      ·
        refine ⟨78552343650846043614903389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52368229100564029076602259 78552343650846043614903389)
        ·
          refine ⟨29457128869067266355588771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78552343650846043614903389 29457128869067266355588771)
          ·
            refine ⟨44185693303600899533383157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29457128869067266355588771 44185693303600899533383157)
            ·
              refine ⟨4142408747212584331254671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44185693303600899533383157 4142408747212584331254671)
              ·
                refine ⟨6213613120818876496882007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4142408747212584331254671 6213613120818876496882007)
                ·
                  refine ⟨9320419681228314745323011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6213613120818876496882007 9320419681228314745323011)
                  ·
                    refine ⟨13980629521842472117984517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9320419681228314745323011 13980629521842472117984517)
                    ·
                      refine ⟨2621368035345463522122097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13980629521842472117984517 2621368035345463522122097)
                      ·
                        rfl

theorem cell23_5105096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_5105096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105096 prefixEnd_5105096 := by exact prefixLift 5105096
  have htrace : WordTrace (prefixWord ++ tailWord_5105096) baseStart_5105096 baseEnd_5105096 := by
    simpa [prefixWord, tailWord_5105096, baseEnd_5105096] using wordTrace_append hprefix tailTrace_5105096
  have hstable : (prefixWord ++ tailWord_5105096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105096).length < 2 ^ (prefixWord ++ tailWord_5105096).sum := by decide
  have hdescent : baseEnd_5105096 < baseStart_5105096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105099 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 1, 2, 3]
def baseStart_5105099 : Nat := 118140960795 + 5105099 * 2 ^ 59
def prefixEnd_5105099 : Nat := 4983230072969 + 3 ^ 40 * 5105099 * 2
def baseEnd_5105099 : Nat := 2621369575787427010384583

theorem tailTrace_5105099 : CollatzResearch.WordTrace tailWord_5105099 prefixEnd_5105099 2621369575787427010384583 := by
  unfold tailWord_5105099
  simp only [CollatzResearch.WordTrace]
  refine ⟨186198257332105679340278351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124132171554737119560185567 186198257332105679340278351)
  ·
    refine ⟨279297385998158519010417527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186198257332105679340278351 279297385998158519010417527)
    ·
      refine ⟨418946078997237778515626291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279297385998158519010417527 418946078997237778515626291)
      ·
        refine ⟨628419118495856667773439437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418946078997237778515626291 628419118495856667773439437)
        ·
          refine ⟨235657169435946250415039789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 628419118495856667773439437 235657169435946250415039789)
          ·
            refine ⟨88371438538479843905639921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235657169435946250415039789 88371438538479843905639921)
            ·
              refine ⟨66278578903859882929229941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88371438538479843905639921 66278578903859882929229941)
              ·
                refine ⟨6213616772236864024615307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66278578903859882929229941 6213616772236864024615307)
                ·
                  refine ⟨9320425158355296036922961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6213616772236864024615307 9320425158355296036922961)
                  ·
                    refine ⟨6990318868766472027692221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9320425158355296036922961 6990318868766472027692221)
                    ·
                      refine ⟨2621369575787427010384583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6990318868766472027692221 2621369575787427010384583)
                      ·
                        rfl

theorem cell23_5105099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 2, 3].length) (baseStart_5105099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105099 prefixEnd_5105099 := by exact prefixLift 5105099
  have htrace : WordTrace (prefixWord ++ tailWord_5105099) baseStart_5105099 baseEnd_5105099 := by
    simpa [prefixWord, tailWord_5105099, baseEnd_5105099] using wordTrace_append hprefix tailTrace_5105099
  have hstable : (prefixWord ++ tailWord_5105099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105099).length < 2 ^ (prefixWord ++ tailWord_5105099).sum := by decide
  have hdescent : baseEnd_5105099 < baseStart_5105099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105150 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_5105150 : Nat := 118140960795 + 5105150 * 2 ^ 59
def prefixEnd_5105150 : Nat := 4983230072969 + 3 ^ 40 * 5105150 * 2
def baseEnd_5105150 : Nat := 2621395763300806310846849

theorem tailTrace_5105150 : CollatzResearch.WordTrace tailWord_5105150 prefixEnd_5105150 2621395763300806310846849 := by
  unfold tailWord_5105150
  simp only [CollatzResearch.WordTrace]
  refine ⟨23275014681865114381298113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124133411636613943366923269 23275014681865114381298113)
  ·
    refine ⟨17456261011398835785973585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23275014681865114381298113 17456261011398835785973585)
    ·
      refine ⟨13092195758549126839480189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17456261011398835785973585 13092195758549126839480189)
      ·
        refine ⟨4909573409455922564805071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13092195758549126839480189 4909573409455922564805071)
        ·
          refine ⟨7364360114183883847207607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4909573409455922564805071 7364360114183883847207607)
          ·
            refine ⟨11046540171275825770811411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7364360114183883847207607 11046540171275825770811411)
            ·
              refine ⟨16569810256913738656217117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11046540171275825770811411 16569810256913738656217117)
              ·
                refine ⟨6213678846342651996081419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16569810256913738656217117 6213678846342651996081419)
                ·
                  refine ⟨9320518269513977994122129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6213678846342651996081419 9320518269513977994122129)
                  ·
                    refine ⟨6990388702135483495591597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9320518269513977994122129 6990388702135483495591597)
                    ·
                      refine ⟨2621395763300806310846849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6990388702135483495591597 2621395763300806310846849)
                      ·
                        rfl

theorem cell23_5105150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_5105150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105150 prefixEnd_5105150 := by exact prefixLift 5105150
  have htrace : WordTrace (prefixWord ++ tailWord_5105150) baseStart_5105150 baseEnd_5105150 := by
    simpa [prefixWord, tailWord_5105150, baseEnd_5105150] using wordTrace_append hprefix tailTrace_5105150
  have hstable : (prefixWord ++ tailWord_5105150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105150).length < 2 ^ (prefixWord ++ tailWord_5105150).sum := by decide
  have hdescent : baseEnd_5105150 < baseStart_5105150 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105256 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 2, 5]
def baseStart_5105256 : Nat := 118140960795 + 5105256 * 2 ^ 59
def prefixEnd_5105256 : Nat := 4983230072969 + 3 ^ 40 * 5105256 * 2
def baseEnd_5105256 : Nat := 873816730750060965373787

theorem tailTrace_5105256 : CollatzResearch.WordTrace tailWord_5105256 prefixEnd_5105256 873816730750060965373787 := by
  unfold tailWord_5105256
  simp only [CollatzResearch.WordTrace]
  refine ⟨93101991796268447576871811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124135989061691263435829081 93101991796268447576871811)
  ·
    refine ⟨139652987694402671365307717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93101991796268447576871811 139652987694402671365307717)
    ·
      refine ⟨26184935192700500880995197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139652987694402671365307717 26184935192700500880995197)
      ·
        refine ⟨9819350697262687830373199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26184935192700500880995197 9819350697262687830373199)
        ·
          refine ⟨14729026045894031745559799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9819350697262687830373199 14729026045894031745559799)
          ·
            refine ⟨22093539068841047618339699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14729026045894031745559799 22093539068841047618339699)
            ·
              refine ⟨33140308603261571427509549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22093539068841047618339699 33140308603261571427509549)
              ·
                refine ⟨12427615726223089285316081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33140308603261571427509549 12427615726223089285316081)
                ·
                  refine ⟨9320711794667316963987061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12427615726223089285316081 9320711794667316963987061)
                  ·
                    refine ⟨873816730750060965373787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9320711794667316963987061 873816730750060965373787)
                    ·
                      rfl

theorem cell23_5105256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_5105256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105256 prefixEnd_5105256 := by exact prefixLift 5105256
  have htrace : WordTrace (prefixWord ++ tailWord_5105256) baseStart_5105256 baseEnd_5105256 := by
    simpa [prefixWord, tailWord_5105256, baseEnd_5105256] using wordTrace_append hprefix tailTrace_5105256
  have hstable : (prefixWord ++ tailWord_5105256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105256).length < 2 ^ (prefixWord ++ tailWord_5105256).sum := by decide
  have hdescent : baseEnd_5105256 < baseStart_5105256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105276 : List Nat := [2, 2, 2, 1, 1, 2, 1, 4, 2, 4, 2]
def baseStart_5105276 : Nat := 118140960795 + 5105276 * 2 ^ 59
def prefixEnd_5105276 : Nat := 4983230072969 + 3 ^ 40 * 5105276 * 2
def baseEnd_5105276 : Nat := 2621460461863272817871269

theorem tailTrace_5105276 : CollatzResearch.WordTrace tailWord_5105276 prefixEnd_5105276 2621460461863272817871269 := by
  unfold tailWord_5105276
  simp only [CollatzResearch.WordTrace]
  refine ⟨93102356526232219284735841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124136475368309625712981121 93102356526232219284735841)
  ·
    refine ⟨69826767394674164463551881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93102356526232219284735841 69826767394674164463551881)
    ·
      refine ⟨52370075546005623347663911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69826767394674164463551881 52370075546005623347663911)
      ·
        refine ⟨78555113319008435021495867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52370075546005623347663911 78555113319008435021495867)
        ·
          refine ⟨117832669978512652532243801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78555113319008435021495867 117832669978512652532243801)
          ·
            refine ⟨88374502483884489399182851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117832669978512652532243801 88374502483884489399182851)
            ·
              refine ⟨132561753725826734098774277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88374502483884489399182851 132561753725826734098774277)
              ·
                refine ⟨24855328823592512643520177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132561753725826734098774277 24855328823592512643520177)
                ·
                  refine ⟨18641496617694384482640133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24855328823592512643520177 18641496617694384482640133)
                  ·
                    refine ⟨3495280615817697090495025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18641496617694384482640133 3495280615817697090495025)
                    ·
                      refine ⟨2621460461863272817871269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495280615817697090495025 2621460461863272817871269)
                      ·
                        rfl

theorem cell23_5105276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 2, 4, 2].length) (baseStart_5105276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105276 prefixEnd_5105276 := by exact prefixLift 5105276
  have htrace : WordTrace (prefixWord ++ tailWord_5105276) baseStart_5105276 baseEnd_5105276 := by
    simpa [prefixWord, tailWord_5105276, baseEnd_5105276] using wordTrace_append hprefix tailTrace_5105276
  have hstable : (prefixWord ++ tailWord_5105276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105276).length < 2 ^ (prefixWord ++ tailWord_5105276).sum := by decide
  have hdescent : baseEnd_5105276 < baseStart_5105276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105310 : List Nat := [4, 3, 1, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_5105310 : Nat := 118140960795 + 5105310 * 2 ^ 59
def prefixEnd_5105310 : Nat := 4983230072969 + 3 ^ 40 * 5105310 * 2
def baseEnd_5105310 : Nat := 2621477920205525684846113

theorem tailTrace_5105310 : CollatzResearch.WordTrace tailWord_5105310 prefixEnd_5105310 2621477920205525684846113 := by
  unfold tailWord_5105310
  simp only [CollatzResearch.WordTrace]
  refine ⟨23275744141792657797026173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124137302089560841584139589 23275744141792657797026173)
  ·
    refine ⟨8728404053172246673884815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23275744141792657797026173 8728404053172246673884815)
    ·
      refine ⟨13092606079758370010827223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8728404053172246673884815 13092606079758370010827223)
      ·
        refine ⟨19638909119637555016240835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13092606079758370010827223 19638909119637555016240835)
        ·
          refine ⟨29458363679456332524361253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19638909119637555016240835 29458363679456332524361253)
          ·
            refine ⟨5523443189898062348317735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29458363679456332524361253 5523443189898062348317735)
            ·
              refine ⟨8285164784847093522476603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5523443189898062348317735 8285164784847093522476603)
              ·
                refine ⟨12427747177270640283714905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8285164784847093522476603 12427747177270640283714905)
                ·
                  refine ⟨9320810382952980212786179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12427747177270640283714905 9320810382952980212786179)
                  ·
                    refine ⟨13981215574429470319179269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9320810382952980212786179 13981215574429470319179269)
                    ·
                      refine ⟨2621477920205525684846113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13981215574429470319179269 2621477920205525684846113)
                      ·
                        rfl

theorem cell23_5105310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_5105310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105310 prefixEnd_5105310 := by exact prefixLift 5105310
  have htrace : WordTrace (prefixWord ++ tailWord_5105310) baseStart_5105310 baseEnd_5105310 := by
    simpa [prefixWord, tailWord_5105310, baseEnd_5105310] using wordTrace_append hprefix tailTrace_5105310
  have hstable : (prefixWord ++ tailWord_5105310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105310).length < 2 ^ (prefixWord ++ tailWord_5105310).sum := by decide
  have hdescent : baseEnd_5105310 < baseStart_5105310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105313 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_5105313 : Nat := 118140960795 + 5105313 * 2 ^ 59
def prefixEnd_5105313 : Nat := 4983230072969 + 3 ^ 40 * 5105313 * 2
def baseEnd_5105313 : Nat := 2621479460647489173108599

theorem tailTrace_5105313 : CollatzResearch.WordTrace tailWord_5105313 prefixEnd_5105313 2621479460647489173108599 := by
  unfold tailWord_5105313
  simp only [CollatzResearch.WordTrace]
  refine ⟨186206062553330393888568593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124137375035553595925712395 186206062553330393888568593)
  ·
    refine ⟨139654546914997795416426445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186206062553330393888568593 139654546914997795416426445)
    ·
      refine ⟨52370455093124173281159917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139654546914997795416426445 52370455093124173281159917)
      ·
        refine ⟨19638920659921564980434969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52370455093124173281159917 19638920659921564980434969)
        ·
          refine ⟨14729190494941173735326227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19638920659921564980434969 14729190494941173735326227)
          ·
            refine ⟨22093785742411760602989341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14729190494941173735326227 22093785742411760602989341)
            ·
              refine ⟨8285169653404410226121003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22093785742411760602989341 8285169653404410226121003)
              ·
                refine ⟨12427754480106615339181505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8285169653404410226121003 12427754480106615339181505)
                ·
                  refine ⟨9320815860079961504386129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12427754480106615339181505 9320815860079961504386129)
                  ·
                    refine ⟨6990611895059971128289597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9320815860079961504386129 6990611895059971128289597)
                    ·
                      refine ⟨2621479460647489173108599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6990611895059971128289597 2621479460647489173108599)
                      ·
                        rfl

theorem cell23_5105313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_5105313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105313 prefixEnd_5105313 := by exact prefixLift 5105313
  have htrace : WordTrace (prefixWord ++ tailWord_5105313) baseStart_5105313 baseEnd_5105313 := by
    simpa [prefixWord, tailWord_5105313, baseEnd_5105313] using wordTrace_append hprefix tailTrace_5105313
  have hstable : (prefixWord ++ tailWord_5105313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105313).length < 2 ^ (prefixWord ++ tailWord_5105313).sum := by decide
  have hdescent : baseEnd_5105313 < baseStart_5105313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105343 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 3, 1, 3]
def baseStart_5105343 : Nat := 118140960795 + 5105343 * 2 ^ 59
def prefixEnd_5105343 : Nat := 4983230072969 + 3 ^ 40 * 5105343 * 2
def baseEnd_5105343 : Nat := 2621494865067124055733461

theorem tailTrace_5105343 : CollatzResearch.WordTrace tailWord_5105343 prefixEnd_5105343 2621494865067124055733461 := by
  unfold tailWord_5105343
  simp only [CollatzResearch.WordTrace]
  refine ⟨186207156743221709012160683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124138104495481139341440455 186207156743221709012160683)
  ·
    refine ⟨279310735114832563518241025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186207156743221709012160683 279310735114832563518241025)
    ·
      refine ⟨209483051336124422638680769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279310735114832563518241025 209483051336124422638680769)
      ·
        refine ⟨157112288502093316979010577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209483051336124422638680769 157112288502093316979010577)
        ·
          refine ⟨117834216376569987734257933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157112288502093316979010577 117834216376569987734257933)
          ·
            refine ⟨44187831141213745400346725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117834216376569987734257933 44187831141213745400346725)
            ·
              refine ⟨8285218338977577262565011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44187831141213745400346725 8285218338977577262565011)
              ·
                refine ⟨12427827508466365893847517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8285218338977577262565011 12427827508466365893847517)
                ·
                  refine ⟨4660435315674887210192819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12427827508466365893847517 4660435315674887210192819)
                  ·
                    refine ⟨6990652973512330815289229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4660435315674887210192819 6990652973512330815289229)
                    ·
                      refine ⟨2621494865067124055733461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6990652973512330815289229 2621494865067124055733461)
                      ·
                        rfl

theorem cell23_5105343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 1, 3].length) (baseStart_5105343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105343 prefixEnd_5105343 := by exact prefixLift 5105343
  have htrace : WordTrace (prefixWord ++ tailWord_5105343) baseStart_5105343 baseEnd_5105343 := by
    simpa [prefixWord, tailWord_5105343, baseEnd_5105343] using wordTrace_append hprefix tailTrace_5105343
  have hstable : (prefixWord ++ tailWord_5105343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105343).length < 2 ^ (prefixWord ++ tailWord_5105343).sum := by decide
  have hdescent : baseEnd_5105343 < baseStart_5105343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105376 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 4, 4]
def baseStart_5105376 : Nat := 118140960795 + 5105376 * 2 ^ 59
def prefixEnd_5105376 : Nat := 4983230072969 + 3 ^ 40 * 5105376 * 2
def baseEnd_5105376 : Nat := 873837269976240808873603

theorem tailTrace_5105376 : CollatzResearch.WordTrace tailWord_5105376 prefixEnd_5105376 873837269976240808873603 := by
  unfold tailWord_5105376
  simp only [CollatzResearch.WordTrace]
  refine ⟨93104180176051077824055991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124138906901401437098741321 93104180176051077824055991)
  ·
    refine ⟨139656270264076616736083987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93104180176051077824055991 139656270264076616736083987)
    ·
      refine ⟨209484405396114925104125981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139656270264076616736083987 209484405396114925104125981)
      ·
        refine ⟨78556652023543096914047243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209484405396114925104125981 78556652023543096914047243)
        ·
          refine ⟨117834978035314645371070865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78556652023543096914047243 117834978035314645371070865)
          ·
            refine ⟨88376233526485984028303149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117834978035314645371070865 88376233526485984028303149)
            ·
              refine ⟨33141087572432244010613681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88376233526485984028303149 33141087572432244010613681)
              ·
                refine ⟨24855815679324183007960261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33141087572432244010613681 24855815679324183007960261)
                ·
                  refine ⟨4660465439873284313992549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24855815679324183007960261 4660465439873284313992549)
                  ·
                    refine ⟨873837269976240808873603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4660465439873284313992549 873837269976240808873603)
                    ·
                      rfl

theorem cell23_5105376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4, 4].length) (baseStart_5105376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105376 prefixEnd_5105376 := by exact prefixLift 5105376
  have htrace : WordTrace (prefixWord ++ tailWord_5105376) baseStart_5105376 baseEnd_5105376 := by
    simpa [prefixWord, tailWord_5105376, baseEnd_5105376] using wordTrace_append hprefix tailTrace_5105376
  have hstable : (prefixWord ++ tailWord_5105376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105376).length < 2 ^ (prefixWord ++ tailWord_5105376).sum := by decide
  have hdescent : baseEnd_5105376 < baseStart_5105376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105386 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5]
def baseStart_5105386 : Nat := 118140960795 + 5105386 * 2 ^ 59
def prefixEnd_5105386 : Nat := 4983230072969 + 3 ^ 40 * 5105386 * 2
def baseEnd_5105386 : Nat := 2621516944735267387495763

theorem tailTrace_5105386 : CollatzResearch.WordTrace tailWord_5105386 prefixEnd_5105386 2621516944735267387495763 := by
  unfold tailWord_5105386
  simp only [CollatzResearch.WordTrace]
  refine ⟨46552181270516481838994003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124139150054710618237317341 46552181270516481838994003)
  ·
    refine ⟨69828271905774722758491005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46552181270516481838994003 69828271905774722758491005)
    ·
      refine ⟨26185601964665521034434127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69828271905774722758491005 26185601964665521034434127)
      ·
        refine ⟨39278402946998281551651191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26185601964665521034434127 39278402946998281551651191)
        ·
          refine ⟨58917604420497422327476787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39278402946998281551651191 58917604420497422327476787)
          ·
            refine ⟨88376406630746133491215181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58917604420497422327476787 88376406630746133491215181)
            ·
              refine ⟨33141152486529800059205693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88376406630746133491215181 33141152486529800059205693)
              ·
                refine ⟨12427932182448675022202135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33141152486529800059205693 12427932182448675022202135)
                ·
                  refine ⟨18641898273673012533303203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12427932182448675022202135 18641898273673012533303203)
                  ·
                    refine ⟨27962847410509518799954805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18641898273673012533303203 27962847410509518799954805)
                    ·
                      refine ⟨2621516944735267387495763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27962847410509518799954805 2621516944735267387495763)
                      ·
                        rfl

theorem cell23_5105386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_5105386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105386 prefixEnd_5105386 := by exact prefixLift 5105386
  have htrace : WordTrace (prefixWord ++ tailWord_5105386) baseStart_5105386 baseEnd_5105386 := by
    simpa [prefixWord, tailWord_5105386, baseEnd_5105386] using wordTrace_append hprefix tailTrace_5105386
  have hstable : (prefixWord ++ tailWord_5105386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105386).length < 2 ^ (prefixWord ++ tailWord_5105386).sum := by decide
  have hdescent : baseEnd_5105386 < baseStart_5105386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105410 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_5105410 : Nat := 118140960795 + 5105410 * 2 ^ 59
def prefixEnd_5105410 : Nat := 4983230072969 + 3 ^ 40 * 5105410 * 2
def baseEnd_5105410 : Nat := 873843089423658431198551

theorem tailTrace_5105410 : CollatzResearch.WordTrace tailWord_5105410 prefixEnd_5105410 873843089423658431198551 := by
  unfold tailWord_5105410
  simp only [CollatzResearch.WordTrace]
  refine ⟨46552400108494744863712421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124139733622652652969899789 46552400108494744863712421)
  ·
    refine ⟨8728575020342764661946079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46552400108494744863712421 8728575020342764661946079)
    ·
      refine ⟨13092862530514146992919119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8728575020342764661946079 13092862530514146992919119)
      ·
        refine ⟨19639293795771220489378679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13092862530514146992919119 19639293795771220489378679)
        ·
          refine ⟨29458940693656830734068019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19639293795771220489378679 29458940693656830734068019)
          ·
            refine ⟨44188411040485246101102029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29458940693656830734068019 44188411040485246101102029)
            ·
              refine ⟨16570654140181967287913261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44188411040485246101102029 16570654140181967287913261)
              ·
                refine ⟨6213995302568237732967473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16570654140181967287913261 6213995302568237732967473)
                ·
                  refine ⟨4660496476926178299725605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6213995302568237732967473 4660496476926178299725605)
                  ·
                    refine ⟨873843089423658431198551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4660496476926178299725605 873843089423658431198551)
                    ·
                      rfl

theorem cell23_5105410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_5105410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105410 prefixEnd_5105410 := by exact prefixLift 5105410
  have htrace : WordTrace (prefixWord ++ tailWord_5105410) baseStart_5105410 baseEnd_5105410 := by
    simpa [prefixWord, tailWord_5105410, baseEnd_5105410] using wordTrace_append hprefix tailTrace_5105410
  have hstable : (prefixWord ++ tailWord_5105410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105410).length < 2 ^ (prefixWord ++ tailWord_5105410).sum := by decide
  have hdescent : baseEnd_5105410 < baseStart_5105410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105466 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_5105466 : Nat := 118140960795 + 5105466 * 2 ^ 59
def prefixEnd_5105466 : Nat := 4983230072969 + 3 ^ 40 * 5105466 * 2
def baseEnd_5105466 : Nat := 873852674395875691498465

theorem tailTrace_5105466 : CollatzResearch.WordTrace tailWord_5105466 prefixEnd_5105466 873852674395875691498465 := by
  unfold tailWord_5105466
  simp only [CollatzResearch.WordTrace]
  refine ⟨46552910730444025254722063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124141095281184067345925501 46552910730444025254722063)
  ·
    refine ⟨69829366095666037882083095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46552910730444025254722063 69829366095666037882083095)
    ·
      refine ⟨104744049143499056823124643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69829366095666037882083095 104744049143499056823124643)
      ·
        refine ⟨157116073715248585234686965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104744049143499056823124643 157116073715248585234686965)
        ·
          refine ⟨14729631910804554865751903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157116073715248585234686965 14729631910804554865751903)
          ·
            refine ⟨22094447866206832298627855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14729631910804554865751903 22094447866206832298627855)
            ·
              refine ⟨33141671799310248447941783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22094447866206832298627855 33141671799310248447941783)
              ·
                refine ⟨49712507698965372671912675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33141671799310248447941783 49712507698965372671912675)
                ·
                  refine ⟨74568761548448059007869013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49712507698965372671912675 74568761548448059007869013)
                  ·
                    refine ⟨873852674395875691498465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74568761548448059007869013 873852674395875691498465)
                    ·
                      rfl

theorem cell23_5105466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_5105466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105466 prefixEnd_5105466 := by exact prefixLift 5105466
  have htrace : WordTrace (prefixWord ++ tailWord_5105466) baseStart_5105466 baseEnd_5105466 := by
    simpa [prefixWord, tailWord_5105466, baseEnd_5105466] using wordTrace_append hprefix tailTrace_5105466
  have hstable : (prefixWord ++ tailWord_5105466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105466).length < 2 ^ (prefixWord ++ tailWord_5105466).sum := by decide
  have hdescent : baseEnd_5105466 < baseStart_5105466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105490 : List Nat := [3, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_5105490 : Nat := 118140960795 + 5105490 * 2 ^ 59
def prefixEnd_5105490 : Nat := 4983230072969 + 3 ^ 40 * 5105490 * 2
def baseEnd_5105490 : Nat := 2621570346723334980595285

theorem tailTrace_5105490 : CollatzResearch.WordTrace tailWord_5105490 prefixEnd_5105490 2621570346723334980595285 := by
  unfold tailWord_5105490
  simp only [CollatzResearch.WordTrace]
  refine ⟨46553129568422288279440481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124141678849126102078507949 46553129568422288279440481)
  ·
    refine ⟨34914847176316716209580361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46553129568422288279440481 34914847176316716209580361)
    ·
      refine ⟨26186135382237537157185271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34914847176316716209580361 26186135382237537157185271)
      ·
        refine ⟨39279203073356305735777907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26186135382237537157185271 39279203073356305735777907)
        ·
          refine ⟨58918804610034458603666861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39279203073356305735777907 58918804610034458603666861)
          ·
            refine ⟨22094551728762921976375073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58918804610034458603666861 22094551728762921976375073)
            ·
              refine ⟨16570913796572191482281305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22094551728762921976375073 16570913796572191482281305)
              ·
                refine ⟨12428185347429143611710979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16570913796572191482281305 12428185347429143611710979)
                ·
                  refine ⟨18642278021143715417566469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12428185347429143611710979 18642278021143715417566469)
                  ·
                    refine ⟨3495427128964446640793713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18642278021143715417566469 3495427128964446640793713)
                    ·
                      refine ⟨2621570346723334980595285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495427128964446640793713 2621570346723334980595285)
                      ·
                        rfl

theorem cell23_5105490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_5105490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105490 prefixEnd_5105490 := by exact prefixLift 5105490
  have htrace : WordTrace (prefixWord ++ tailWord_5105490) baseStart_5105490 baseEnd_5105490 := by
    simpa [prefixWord, tailWord_5105490, baseEnd_5105490] using wordTrace_append hprefix tailTrace_5105490
  have hstable : (prefixWord ++ tailWord_5105490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105490).length < 2 ^ (prefixWord ++ tailWord_5105490).sum := by decide
  have hdescent : baseEnd_5105490 < baseStart_5105490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105507 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 4, 2, 2]
def baseStart_5105507 : Nat := 118140960795 + 5105507 * 2 ^ 59
def prefixEnd_5105507 : Nat := 4983230072969 + 3 ^ 40 * 5105507 * 2
def baseEnd_5105507 : Nat := 2621579075894461414082707

theorem tailTrace_5105507 : CollatzResearch.WordTrace tailWord_5105507 prefixEnd_5105507 2621579075894461414082707 := by
  unfold tailWord_5105507
  simp only [CollatzResearch.WordTrace]
  refine ⟨186213138314627565021130775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124142092209751710014087183 186213138314627565021130775)
  ·
    refine ⟨279319707471941347531696163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186213138314627565021130775 279319707471941347531696163)
    ·
      refine ⟨418979561207912021297544245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279319707471941347531696163 418979561207912021297544245)
      ·
        refine ⟨39279333863241751996644773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 418979561207912021297544245 39279333863241751996644773)
        ·
          refine ⟨7364875099357828499370895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39279333863241751996644773 7364875099357828499370895)
          ·
            refine ⟨11047312649036742749056343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7364875099357828499370895 11047312649036742749056343)
            ·
              refine ⟨16570968973555114123584515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11047312649036742749056343 16570968973555114123584515)
              ·
                refine ⟨24856453460332671185376773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16570968973555114123584515 24856453460332671185376773)
                ·
                  refine ⟨4660585023812375847258145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24856453460332671185376773 4660585023812375847258145)
                  ·
                    refine ⟨3495438767859281885443609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4660585023812375847258145 3495438767859281885443609)
                    ·
                      refine ⟨2621579075894461414082707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495438767859281885443609 2621579075894461414082707)
                      ·
                        rfl

theorem cell23_5105507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_5105507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105507 prefixEnd_5105507 := by exact prefixLift 5105507
  have htrace : WordTrace (prefixWord ++ tailWord_5105507) baseStart_5105507 baseEnd_5105507 := by
    simpa [prefixWord, tailWord_5105507, baseEnd_5105507] using wordTrace_append hprefix tailTrace_5105507
  have hstable : (prefixWord ++ tailWord_5105507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105507).length < 2 ^ (prefixWord ++ tailWord_5105507).sum := by decide
  have hdescent : baseEnd_5105507 < baseStart_5105507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105570 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_5105570 : Nat := 118140960795 + 5105570 * 2 ^ 59
def prefixEnd_5105570 : Nat := 4983230072969 + 3 ^ 40 * 5105570 * 2
def baseEnd_5105570 : Nat := 2621611425175694667594917

theorem tailTrace_5105570 : CollatzResearch.WordTrace tailWord_5105570 prefixEnd_5105570 2621611425175694667594917 := by
  unfold tailWord_5105570
  simp only [CollatzResearch.WordTrace]
  refine ⟨46553859028349831695168541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124143624075599551187116109 46553859028349831695168541)
  ·
    refine ⟨17457697135631186885688203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46553859028349831695168541 17457697135631186885688203)
    ·
      refine ⟨26186545703446780328532305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17457697135631186885688203 26186545703446780328532305)
      ·
        refine ⟨19639909277585085246399229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26186545703446780328532305 19639909277585085246399229)
        ·
          refine ⟨7364965979094406967399711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19639909277585085246399229 7364965979094406967399711)
          ·
            refine ⟨11047448968641610451099567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7364965979094406967399711 11047448968641610451099567)
            ·
              refine ⟨16571173452962415676649351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11047448968641610451099567 16571173452962415676649351)
              ·
                refine ⟨24856760179443623514974027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16571173452962415676649351 24856760179443623514974027)
                ·
                  refine ⟨37285140269165435272461041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24856760179443623514974027 37285140269165435272461041)
                  ·
                    refine ⟨27963855201874076454345781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37285140269165435272461041 27963855201874076454345781)
                    ·
                      refine ⟨2621611425175694667594917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27963855201874076454345781 2621611425175694667594917)
                      ·
                        rfl

theorem cell23_5105570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_5105570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105570 prefixEnd_5105570 := by exact prefixLift 5105570
  have htrace : WordTrace (prefixWord ++ tailWord_5105570) baseStart_5105570 baseEnd_5105570 := by
    simpa [prefixWord, tailWord_5105570, baseEnd_5105570] using wordTrace_append hprefix tailTrace_5105570
  have hstable : (prefixWord ++ tailWord_5105570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105570).length < 2 ^ (prefixWord ++ tailWord_5105570).sum := by decide
  have hdescent : baseEnd_5105570 < baseStart_5105570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105583 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 3]
def baseStart_5105583 : Nat := 118140960795 + 5105583 * 2 ^ 59
def prefixEnd_5105583 : Nat := 4983230072969 + 3 ^ 40 * 5105583 * 2
def baseEnd_5105583 : Nat := 2621618100424203116732357

theorem tailTrace_5105583 : CollatzResearch.WordTrace tailWord_5105583 prefixEnd_5105583 2621618100424203116732357 := by
  unfold tailWord_5105583
  simp only [CollatzResearch.WordTrace]
  refine ⟨186215910262352230000897403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124143940174901486667264935 186215910262352230000897403)
  ·
    refine ⟨279323865393528345001346105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186215910262352230000897403 279323865393528345001346105)
    ·
      refine ⟨209492899045146258751009579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279323865393528345001346105 209492899045146258751009579)
      ·
        refine ⟨314239348567719388126514369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209492899045146258751009579 314239348567719388126514369)
        ·
          refine ⟨235679511425789541094885777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314239348567719388126514369 235679511425789541094885777)
          ·
            refine ⟨176759633569342155821164333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235679511425789541094885777 176759633569342155821164333)
            ·
              refine ⟨66284862588503308432936625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176759633569342155821164333 66284862588503308432936625)
              ·
                refine ⟨49713646941377481324702469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66284862588503308432936625 49713646941377481324702469)
                ·
                  refine ⟨9321308801508277748381713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49713646941377481324702469 9321308801508277748381713)
                  ·
                    refine ⟨6990981601131208311286285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9321308801508277748381713 6990981601131208311286285)
                    ·
                      refine ⟨2621618100424203116732357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6990981601131208311286285 2621618100424203116732357)
                      ·
                        rfl

theorem cell23_5105583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 3].length) (baseStart_5105583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105583 prefixEnd_5105583 := by exact prefixLift 5105583
  have htrace : WordTrace (prefixWord ++ tailWord_5105583) baseStart_5105583 baseEnd_5105583 := by
    simpa [prefixWord, tailWord_5105583, baseEnd_5105583] using wordTrace_append hprefix tailTrace_5105583
  have hstable : (prefixWord ++ tailWord_5105583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105583).length < 2 ^ (prefixWord ++ tailWord_5105583).sum := by decide
  have hdescent : baseEnd_5105583 < baseStart_5105583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105600 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 3]
def baseStart_5105600 : Nat := 118140960795 + 5105600 * 2 ^ 59
def prefixEnd_5105600 : Nat := 4983230072969 + 3 ^ 40 * 5105600 * 2
def baseEnd_5105600 : Nat := 2621626829595329550219779

theorem tailTrace_5105600 : CollatzResearch.WordTrace tailWord_5105600 prefixEnd_5105600 2621626829595329550219779 := by
  unfold tailWord_5105600
  simp only [CollatzResearch.WordTrace]
  refine ⟨93108265151645320952133127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124144353535527094602844169 93108265151645320952133127)
  ·
    refine ⟨139662397727467981428199691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93108265151645320952133127 139662397727467981428199691)
    ·
      refine ⟨209493596591201972142299537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139662397727467981428199691 209493596591201972142299537)
      ·
        refine ⟨157120197443401479106724653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209493596591201972142299537 157120197443401479106724653)
        ·
          refine ⟨58920074041275554665021745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157120197443401479106724653 58920074041275554665021745)
          ·
            refine ⟨44190055530956665998766309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58920074041275554665021745 44190055530956665998766309)
            ·
              refine ⟨8285635412054374874768683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44190055530956665998766309 8285635412054374874768683)
              ·
                refine ⟨12428453118081562312153025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8285635412054374874768683 12428453118081562312153025)
                ·
                  refine ⟨9321339838561171734114769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12428453118081562312153025 9321339838561171734114769)
                  ·
                    refine ⟨6991004878920878800586077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9321339838561171734114769 6991004878920878800586077)
                    ·
                      refine ⟨2621626829595329550219779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6991004878920878800586077 2621626829595329550219779)
                      ·
                        rfl

theorem cell23_5105600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_5105600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105600 prefixEnd_5105600 := by exact prefixLift 5105600
  have htrace : WordTrace (prefixWord ++ tailWord_5105600) baseStart_5105600 baseEnd_5105600 := by
    simpa [prefixWord, tailWord_5105600, baseEnd_5105600] using wordTrace_append hprefix tailTrace_5105600
  have hstable : (prefixWord ++ tailWord_5105600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105600).length < 2 ^ (prefixWord ++ tailWord_5105600).sum := by decide
  have hdescent : baseEnd_5105600 < baseStart_5105600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105620 : List Nat := [2, 4, 1, 2, 1, 1, 4, 2, 6]
def baseStart_5105620 : Nat := 118140960795 + 5105620 * 2 ^ 59
def prefixEnd_5105620 : Nat := 4983230072969 + 3 ^ 40 * 5105620 * 2
def baseEnd_5105620 : Nat := 291293011023157719107743

theorem tailTrace_5105620 : CollatzResearch.WordTrace tailWord_5105620 prefixEnd_5105620 291293011023157719107743 := by
  unfold tailWord_5105620
  simp only [CollatzResearch.WordTrace]
  refine ⟨93108629881609092659997157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124144839842145456879996209 93108629881609092659997157)
  ·
    refine ⟨17457868102801704873749467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93108629881609092659997157 17457868102801704873749467)
    ·
      refine ⟨26186802154202557310624201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17457868102801704873749467 26186802154202557310624201)
      ·
        refine ⟨19640101615651917982968151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26186802154202557310624201 19640101615651917982968151)
        ·
          refine ⟨29460152423477876974452227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19640101615651917982968151 29460152423477876974452227)
          ·
            refine ⟨44190228635216815461678341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29460152423477876974452227 44190228635216815461678341)
            ·
              refine ⟨8285667869103152899064689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44190228635216815461678341 8285667869103152899064689)
              ·
                refine ⟨6214250901827364674298517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8285667869103152899064689 6214250901827364674298517)
                ·
                  refine ⟨291293011023157719107743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6214250901827364674298517 291293011023157719107743)
                  ·
                    rfl

theorem cell23_5105620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_5105620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105620 prefixEnd_5105620 := by exact prefixLift 5105620
  have htrace : WordTrace (prefixWord ++ tailWord_5105620) baseStart_5105620 baseEnd_5105620 := by
    simpa [prefixWord, tailWord_5105620, baseEnd_5105620] using wordTrace_append hprefix tailTrace_5105620
  have hstable : (prefixWord ++ tailWord_5105620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105620).length < 2 ^ (prefixWord ++ tailWord_5105620).sum := by decide
  have hdescent : baseEnd_5105620 < baseStart_5105620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105633 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 3, 5]
def baseStart_5105633 : Nat := 118140960795 + 5105633 * 2 ^ 59
def prefixEnd_5105633 : Nat := 4983230072969 + 3 ^ 40 * 5105633 * 2
def baseEnd_5105633 : Nat := 873881258152309307035709

theorem tailTrace_5105633 : CollatzResearch.WordTrace tailWord_5105633 prefixEnd_5105633 873881258152309307035709 := by
  unfold tailWord_5105633
  simp only [CollatzResearch.WordTrace]
  refine ⟨186217733912171088540217553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124145155941447392360145035 186217733912171088540217553)
  ·
    refine ⟨139663300434128316405163165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186217733912171088540217553 139663300434128316405163165)
    ·
      refine ⟨52373737662798118651936187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139663300434128316405163165 52373737662798118651936187)
      ·
        refine ⟨78560606494197177977904281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52373737662798118651936187 78560606494197177977904281)
        ·
          refine ⟨58920454870647883483428211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78560606494197177977904281 58920454870647883483428211)
          ·
            refine ⟨88380682305971825225142317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58920454870647883483428211 88380682305971825225142317)
            ·
              refine ⟨33142755864739434459428369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88380682305971825225142317 33142755864739434459428369)
              ·
                refine ⟨24857066898554575844571277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33142755864739434459428369 24857066898554575844571277)
                ·
                  refine ⟨9321400086957965941714229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24857066898554575844571277 9321400086957965941714229)
                  ·
                    refine ⟨873881258152309307035709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9321400086957965941714229 873881258152309307035709)
                    ·
                      rfl

theorem cell23_5105633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_5105633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105633 prefixEnd_5105633 := by exact prefixLift 5105633
  have htrace : WordTrace (prefixWord ++ tailWord_5105633) baseStart_5105633 baseEnd_5105633 := by
    simpa [prefixWord, tailWord_5105633, baseEnd_5105633] using wordTrace_append hprefix tailTrace_5105633
  have hstable : (prefixWord ++ tailWord_5105633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105633).length < 2 ^ (prefixWord ++ tailWord_5105633).sum := by decide
  have hdescent : baseEnd_5105633 < baseStart_5105633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105640 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_5105640 : Nat := 118140960795 + 5105640 * 2 ^ 59
def prefixEnd_5105640 : Nat := 4983230072969 + 3 ^ 40 * 5105640 * 2
def baseEnd_5105640 : Nat := 2621647368821509393719595

theorem tailTrace_5105640 : CollatzResearch.WordTrace tailWord_5105640 prefixEnd_5105640 2621647368821509393719595 := by
  unfold tailWord_5105640
  simp only [CollatzResearch.WordTrace]
  refine ⟨93108994611572864367861187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124145326148763819157148249 93108994611572864367861187)
  ·
    refine ⟨139663491917359296551791781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93108994611572864367861187 139663491917359296551791781)
    ·
      refine ⟨26186904734504868103460959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139663491917359296551791781 26186904734504868103460959)
      ·
        refine ⟨39280357101757302155191439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26186904734504868103460959 39280357101757302155191439)
        ·
          refine ⟨58920535652635953232787159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39280357101757302155191439 58920535652635953232787159)
          ·
            refine ⟨88380803478953929849180739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58920535652635953232787159 88380803478953929849180739)
            ·
              refine ⟨132571205218430894773771109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88380803478953929849180739 132571205218430894773771109)
              ·
                refine ⟨24857100978455792770082083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132571205218430894773771109 24857100978455792770082083)
                ·
                  refine ⟨37285651467683689155123125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24857100978455792770082083 37285651467683689155123125)
                  ·
                    refine ⟨3495529825095345858292793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37285651467683689155123125 3495529825095345858292793)
                    ·
                      refine ⟨2621647368821509393719595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495529825095345858292793 2621647368821509393719595)
                      ·
                        rfl

theorem cell23_5105640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_5105640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105640 prefixEnd_5105640 := by exact prefixLift 5105640
  have htrace : WordTrace (prefixWord ++ tailWord_5105640) baseStart_5105640 baseEnd_5105640 := by
    simpa [prefixWord, tailWord_5105640, baseEnd_5105640] using wordTrace_append hprefix tailTrace_5105640
  have hstable : (prefixWord ++ tailWord_5105640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105640).length < 2 ^ (prefixWord ++ tailWord_5105640).sum := by decide
  have hdescent : baseEnd_5105640 < baseStart_5105640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105657 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 2, 3, 2]
def baseStart_5105657 : Nat := 118140960795 + 5105657 * 2 ^ 59
def prefixEnd_5105657 : Nat := 4983230072969 + 3 ^ 40 * 5105657 * 2
def baseEnd_5105657 : Nat := 2621656097992635827207017

theorem tailTrace_5105657 : CollatzResearch.WordTrace tailWord_5105657 prefixEnd_5105657 2621656097992635827207017 := by
  unfold tailWord_5105657
  simp only [CollatzResearch.WordTrace]
  refine ⟨186218609264084140639091225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124145739509389427092727483 186218609264084140639091225)
  ·
    refine ⟨139663956948063105479318419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186218609264084140639091225 139663956948063105479318419)
    ·
      refine ⟨209495935422094658218977629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139663956948063105479318419 209495935422094658218977629)
      ·
        refine ⟨78560975783285496832116611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209495935422094658218977629 78560975783285496832116611)
        ·
          refine ⟨117841463674928245248174917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78560975783285496832116611 117841463674928245248174917)
          ·
            refine ⟨22095274439049045984032797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117841463674928245248174917 22095274439049045984032797)
            ·
              refine ⟨8285727914643392244012299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22095274439049045984032797 8285727914643392244012299)
              ·
                refine ⟨12428591871965088366018449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8285727914643392244012299 12428591871965088366018449)
                ·
                  refine ⟨9321443903973816274513837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12428591871965088366018449 9321443903973816274513837)
                  ·
                    refine ⟨3495541463990181102942689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9321443903973816274513837 3495541463990181102942689)
                    ·
                      refine ⟨2621656097992635827207017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495541463990181102942689 2621656097992635827207017)
                      ·
                        rfl

theorem cell23_5105657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_5105657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105657 prefixEnd_5105657 := by exact prefixLift 5105657
  have htrace : WordTrace (prefixWord ++ tailWord_5105657) baseStart_5105657 baseEnd_5105657 := by
    simpa [prefixWord, tailWord_5105657, baseEnd_5105657] using wordTrace_append hprefix tailTrace_5105657
  have hstable : (prefixWord ++ tailWord_5105657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105657).length < 2 ^ (prefixWord ++ tailWord_5105657).sum := by decide
  have hdescent : baseEnd_5105657 < baseStart_5105657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105683 : List Nat := [1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 4]
def baseStart_5105683 : Nat := 118140960795 + 5105683 * 2 ^ 59
def prefixEnd_5105683 : Nat := 4983230072969 + 3 ^ 40 * 5105683 * 2
def baseEnd_5105683 : Nat := 2621669448489652725481897

theorem tailTrace_5105683 : CollatzResearch.WordTrace tailWord_5105683 prefixEnd_5105683 2621669448489652725481897 := by
  unfold tailWord_5105683
  simp only [CollatzResearch.WordTrace]
  refine ⟨186219557561989947079537703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124146371707993298053025135 186219557561989947079537703)
  ·
    refine ⟨279329336342984920619306555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186219557561989947079537703 279329336342984920619306555)
    ·
      refine ⟨418994004514477380928959833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279329336342984920619306555 418994004514477380928959833)
      ·
        refine ⟨314245503385858035696719875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418994004514477380928959833 314245503385858035696719875)
        ·
          refine ⟨471368255078787053545079813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314245503385858035696719875 471368255078787053545079813)
          ·
            refine ⟨88381547827272572539702465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 471368255078787053545079813 88381547827272572539702465)
            ·
              refine ⟨66286160870454429404776849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88381547827272572539702465 66286160870454429404776849)
              ·
                refine ⟨49714620652840822053582637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66286160870454429404776849 49714620652840822053582637)
                ·
                  refine ⟨18642982744815308270093489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49714620652840822053582637 18642982744815308270093489)
                  ·
                    refine ⟨13982237058611481202570117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18642982744815308270093489 13982237058611481202570117)
                    ·
                      refine ⟨2621669448489652725481897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13982237058611481202570117 2621669448489652725481897)
                      ·
                        rfl

theorem cell23_5105683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 4].length) (baseStart_5105683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105683 prefixEnd_5105683 := by exact prefixLift 5105683
  have htrace : WordTrace (prefixWord ++ tailWord_5105683) baseStart_5105683 baseEnd_5105683 := by
    simpa [prefixWord, tailWord_5105683, baseEnd_5105683] using wordTrace_append hprefix tailTrace_5105683
  have hstable : (prefixWord ++ tailWord_5105683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105683).length < 2 ^ (prefixWord ++ tailWord_5105683).sum := by decide
  have hdescent : baseEnd_5105683 < baseStart_5105683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105690 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5]
def baseStart_5105690 : Nat := 118140960795 + 5105690 * 2 ^ 59
def prefixEnd_5105690 : Nat := 4983230072969 + 3 ^ 40 * 5105690 * 2
def baseEnd_5105690 : Nat := 2621673042854234198094365

theorem tailTrace_5105690 : CollatzResearch.WordTrace tailWord_5105690 prefixEnd_5105690 2621673042854234198094365 := by
  unfold tailWord_5105690
  simp only [CollatzResearch.WordTrace]
  refine ⟨46554953218241146818760631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124146541915309724850028349 46554953218241146818760631)
  ·
    refine ⟨69832429827361720228140947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46554953218241146818760631 69832429827361720228140947)
    ·
      refine ⟨104748644741042580342211421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69832429827361720228140947 104748644741042580342211421)
      ·
        refine ⟨39280741777890967628329283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104748644741042580342211421 39280741777890967628329283)
        ·
          refine ⟨58921112666836451442493925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39280741777890967628329283 58921112666836451442493925)
          ·
            refine ⟨11047708625031834645467611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58921112666836451442493925 11047708625031834645467611)
            ·
              refine ⟨16571562937547751968201417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11047708625031834645467611 16571562937547751968201417)
              ·
                refine ⟨12428672203160813976151063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16571562937547751968201417 12428672203160813976151063)
                ·
                  refine ⟨18643008304741220964226595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12428672203160813976151063 18643008304741220964226595)
                  ·
                    refine ⟨27964512457111831446339893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18643008304741220964226595 27964512457111831446339893)
                    ·
                      refine ⟨2621673042854234198094365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27964512457111831446339893 2621673042854234198094365)
                      ·
                        rfl

theorem cell23_5105690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_5105690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105690 prefixEnd_5105690 := by exact prefixLift 5105690
  have htrace : WordTrace (prefixWord ++ tailWord_5105690) baseStart_5105690 baseEnd_5105690 := by
    simpa [prefixWord, tailWord_5105690, baseEnd_5105690] using wordTrace_append hprefix tailTrace_5105690
  have hstable : (prefixWord ++ tailWord_5105690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105690).length < 2 ^ (prefixWord ++ tailWord_5105690).sum := by decide
  have hdescent : baseEnd_5105690 < baseStart_5105690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105697 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 1, 6]
def baseStart_5105697 : Nat := 118140960795 + 5105697 * 2 ^ 59
def prefixEnd_5105697 : Nat := 4983230072969 + 3 ^ 40 * 5105697 * 2
def baseEnd_5105697 : Nat := 873892212406271890235611

theorem tailTrace_5105697 : CollatzResearch.WordTrace tailWord_5105697 prefixEnd_5105697 873892212406271890235611 := by
  unfold tailWord_5105697
  simp only [CollatzResearch.WordTrace]
  refine ⟨186220068183939227470547345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124146712122626151647031563 186220068183939227470547345)
  ·
    refine ⟨139665051137954420602910509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186220068183939227470547345 139665051137954420602910509)
    ·
      refine ⟨52374394176732907726091441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139665051137954420602910509 52374394176732907726091441)
      ·
        refine ⟨39280795632549680794568581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52374394176732907726091441 39280795632549680794568581)
        ·
          refine ⟨7365149181103065148981609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39280795632549680794568581 7365149181103065148981609)
          ·
            refine ⟨5523861885827298861736207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7365149181103065148981609 5523861885827298861736207)
            ·
              refine ⟨8285792828740948292604311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5523861885827298861736207 8285792828740948292604311)
              ·
                refine ⟨12428689243111422438906467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8285792828740948292604311 12428689243111422438906467)
                ·
                  refine ⟨18643033864667133658359701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12428689243111422438906467 18643033864667133658359701)
                  ·
                    refine ⟨873892212406271890235611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18643033864667133658359701 873892212406271890235611)
                    ·
                      rfl

theorem cell23_5105697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_5105697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105697 prefixEnd_5105697 := by exact prefixLift 5105697
  have htrace : WordTrace (prefixWord ++ tailWord_5105697) baseStart_5105697 baseEnd_5105697 := by
    simpa [prefixWord, tailWord_5105697, baseEnd_5105697] using wordTrace_append hprefix tailTrace_5105697
  have hstable : (prefixWord ++ tailWord_5105697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105697).length < 2 ^ (prefixWord ++ tailWord_5105697).sum := by decide
  have hdescent : baseEnd_5105697 < baseStart_5105697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105710 : List Nat := [4, 1, 3, 1, 1, 3, 1, 9]
def baseStart_5105710 : Nat := 118140960795 + 5105710 * 2 ^ 59
def prefixEnd_5105710 : Nat := 4983230072969 + 3 ^ 40 * 5105710 * 2
def baseEnd_5105710 : Nat := 97099381943234226660899

theorem tailTrace_5105710 : CollatzResearch.WordTrace tailWord_5105710 prefixEnd_5105710 97099381943234226660899 := by
  unfold tailWord_5105710
  simp only [CollatzResearch.WordTrace]
  refine ⟨23277567791611516336346323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124147028221928087127180389 23277567791611516336346323)
  ·
    refine ⟨34916351687417274504519485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23277567791611516336346323 34916351687417274504519485)
    ·
      refine ⟨13093631882781477939194807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34916351687417274504519485 13093631882781477939194807)
      ·
        refine ⟨19640447824172216908792211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13093631882781477939194807 19640447824172216908792211)
        ·
          refine ⟨29460671736258325363188317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19640447824172216908792211 29460671736258325363188317)
          ·
            refine ⟨11047751901096872011195619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29460671736258325363188317 11047751901096872011195619)
            ·
              refine ⟨16571627851645308016793429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11047751901096872011195619 16571627851645308016793429)
              ·
                refine ⟨97099381943234226660899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16571627851645308016793429 97099381943234226660899)
                ·
                  rfl

theorem cell23_5105710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_5105710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105710 prefixEnd_5105710 := by exact prefixLift 5105710
  have htrace : WordTrace (prefixWord ++ tailWord_5105710) baseStart_5105710 baseEnd_5105710 := by
    simpa [prefixWord, tailWord_5105710, baseEnd_5105710] using wordTrace_append hprefix tailTrace_5105710
  have hstable : (prefixWord ++ tailWord_5105710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105710).length < 2 ^ (prefixWord ++ tailWord_5105710).sum := by decide
  have hdescent : baseEnd_5105710 < baseStart_5105710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105733 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 5]
def baseStart_5105733 : Nat := 118140960795 + 5105733 * 2 ^ 59
def prefixEnd_5105733 : Nat := 4983230072969 + 3 ^ 40 * 5105733 * 2
def baseEnd_5105733 : Nat := 2621695122522377529856667

theorem tailTrace_5105733 : CollatzResearch.WordTrace tailWord_5105733 prefixEnd_5105733 2621695122522377529856667 := by
  unfold tailWord_5105733
  simp only [CollatzResearch.WordTrace]
  refine ⟨186221381211808805618857853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124147587474539203745905235 186221381211808805618857853)
  ·
    refine ⟨69833017954428302107071695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186221381211808805618857853 69833017954428302107071695)
    ·
      refine ⟨104749526931642453160607543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69833017954428302107071695 104749526931642453160607543)
      ·
        refine ⟨157124290397463679740911315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104749526931642453160607543 157124290397463679740911315)
        ·
          refine ⟨235686435596195519611366973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157124290397463679740911315 235686435596195519611366973)
          ·
            refine ⟨88382413348573319854262615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235686435596195519611366973 88382413348573319854262615)
            ·
              refine ⟨132573620022859979781393923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88382413348573319854262615 132573620022859979781393923)
              ·
                refine ⟨198860430034289969672090885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132573620022859979781393923 198860430034289969672090885)
                ·
                  refine ⟨37286330631429369313517041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198860430034289969672090885 37286330631429369313517041)
                  ·
                    refine ⟨27964747973572026985137781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37286330631429369313517041 27964747973572026985137781)
                    ·
                      refine ⟨2621695122522377529856667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27964747973572026985137781 2621695122522377529856667)
                      ·
                        rfl

theorem cell23_5105733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_5105733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105733 prefixEnd_5105733 := by exact prefixLift 5105733
  have htrace : WordTrace (prefixWord ++ tailWord_5105733) baseStart_5105733 baseEnd_5105733 := by
    simpa [prefixWord, tailWord_5105733, baseEnd_5105733] using wordTrace_append hprefix tailTrace_5105733
  have hstable : (prefixWord ++ tailWord_5105733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105733).length < 2 ^ (prefixWord ++ tailWord_5105733).sum := by decide
  have hdescent : baseEnd_5105733 < baseStart_5105733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105737 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 2, 1, 3]
def baseStart_5105737 : Nat := 118140960795 + 5105737 * 2 ^ 59
def prefixEnd_5105737 : Nat := 4983230072969 + 3 ^ 40 * 5105737 * 2
def baseEnd_5105737 : Nat := 2621697176444995514206649

theorem tailTrace_5105737 : CollatzResearch.WordTrace tailWord_5105737 prefixEnd_5105737 2621697176444995514206649 := by
  unfold tailWord_5105737
  simp only [CollatzResearch.WordTrace]
  refine ⟨186221527103794314302003465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124147684735862876201335643 186221527103794314302003465)
  ·
    refine ⟨139666145327845735726502599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186221527103794314302003465 139666145327845735726502599)
    ·
      refine ⟨209499217991768603589753899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139666145327845735726502599 209499217991768603589753899)
      ·
        refine ⟨314248826987652905384630849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209499217991768603589753899 314248826987652905384630849)
        ·
          refine ⟨235686620240739679038473137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314248826987652905384630849 235686620240739679038473137)
          ·
            refine ⟨176764965180554759278854853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235686620240739679038473137 176764965180554759278854853)
            ·
              refine ⟨33143430971354017364785285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176764965180554759278854853 33143430971354017364785285)
              ·
                refine ⟨6214393307128878255897241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33143430971354017364785285 6214393307128878255897241)
                ·
                  refine ⟨4660794980346658691922931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6214393307128878255897241 4660794980346658691922931)
                  ·
                    refine ⟨6991192470519988037884397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4660794980346658691922931 6991192470519988037884397)
                    ·
                      refine ⟨2621697176444995514206649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6991192470519988037884397 2621697176444995514206649)
                      ·
                        rfl

theorem cell23_5105737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 1, 3].length) (baseStart_5105737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105737 prefixEnd_5105737 := by exact prefixLift 5105737
  have htrace : WordTrace (prefixWord ++ tailWord_5105737) baseStart_5105737 baseEnd_5105737 := by
    simpa [prefixWord, tailWord_5105737, baseEnd_5105737] using wordTrace_append hprefix tailTrace_5105737
  have hstable : (prefixWord ++ tailWord_5105737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105737).length < 2 ^ (prefixWord ++ tailWord_5105737).sum := by decide
  have hdescent : baseEnd_5105737 < baseStart_5105737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105743 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_5105743 : Nat := 118140960795 + 5105743 * 2 ^ 59
def prefixEnd_5105743 : Nat := 4983230072969 + 3 ^ 40 * 5105743 * 2
def baseEnd_5105743 : Nat := 2621700257328922490731621

theorem tailTrace_5105743 : CollatzResearch.WordTrace tailWord_5105743 prefixEnd_5105743 2621700257328922490731621 := by
  unfold tailWord_5105743
  simp only [CollatzResearch.WordTrace]
  refine ⟨186221745941772577326721883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124147830627848384884481255 186221745941772577326721883)
  ·
    refine ⟨279332618912658865990082825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186221745941772577326721883 279332618912658865990082825)
    ·
      refine ⟨209499464184494149492562119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279332618912658865990082825 209499464184494149492562119)
      ·
        refine ⟨314249196276741224238843179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209499464184494149492562119 314249196276741224238843179)
        ·
          refine ⟨471373794415111836358264769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314249196276741224238843179 471373794415111836358264769)
          ·
            refine ⟨353530345811333877268698577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 471373794415111836358264769 353530345811333877268698577)
            ·
              refine ⟨265147759358500407951523933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353530345811333877268698577 265147759358500407951523933)
              ·
                refine ⟨99430409759437652981821475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265147759358500407951523933 99430409759437652981821475)
                ·
                  refine ⟨149145614639156479472732213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99430409759437652981821475 149145614639156479472732213)
                  ·
                    refine ⟨13982401372420919950568645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 149145614639156479472732213 13982401372420919950568645)
                    ·
                      refine ⟨2621700257328922490731621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13982401372420919950568645 2621700257328922490731621)
                      ·
                        rfl

theorem cell23_5105743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_5105743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105743 prefixEnd_5105743 := by exact prefixLift 5105743
  have htrace : WordTrace (prefixWord ++ tailWord_5105743) baseStart_5105743 baseEnd_5105743 := by
    simpa [prefixWord, tailWord_5105743, baseEnd_5105743] using wordTrace_append hprefix tailTrace_5105743
  have hstable : (prefixWord ++ tailWord_5105743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105743).length < 2 ^ (prefixWord ++ tailWord_5105743).sum := by decide
  have hdescent : baseEnd_5105743 < baseStart_5105743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105753 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 1, 8]
def baseStart_5105753 : Nat := 118140960795 + 5105753 * 2 ^ 59
def prefixEnd_5105753 : Nat := 4983230072969 + 3 ^ 40 * 5105753 * 2
def baseEnd_5105753 : Nat := 873901797378489150535525

theorem tailTrace_5105753 : CollatzResearch.WordTrace tailWord_5105753 prefixEnd_5105753 873901797378489150535525 := by
  unfold tailWord_5105753
  simp only [CollatzResearch.WordTrace]
  refine ⟨186222110671736349034585913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124148073781157566023057275 186222110671736349034585913)
  ·
    refine ⟨139666583003802261775939435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186222110671736349034585913 139666583003802261775939435)
    ·
      refine ⟨209499874505703392663909153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139666583003802261775939435 209499874505703392663909153)
      ·
        refine ⟨157124905879277544497931865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209499874505703392663909153 157124905879277544497931865)
        ·
          refine ⟨117843679409458158373448899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157124905879277544497931865 117843679409458158373448899)
          ·
            refine ⟨176765519114187237560173349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117843679409458158373448899 176765519114187237560173349)
            ·
              refine ⟨33143534833910107042532503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176765519114187237560173349 33143534833910107042532503)
              ·
                refine ⟨49715302250865160563798755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33143534833910107042532503 49715302250865160563798755)
                ·
                  refine ⟨74572953376297740845698133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49715302250865160563798755 74572953376297740845698133)
                  ·
                    refine ⟨873901797378489150535525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 74572953376297740845698133 873901797378489150535525)
                    ·
                      rfl

theorem cell23_5105753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_5105753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105753 prefixEnd_5105753 := by exact prefixLift 5105753
  have htrace : WordTrace (prefixWord ++ tailWord_5105753) baseStart_5105753 baseEnd_5105753 := by
    simpa [prefixWord, tailWord_5105753, baseEnd_5105753] using wordTrace_append hprefix tailTrace_5105753
  have hstable : (prefixWord ++ tailWord_5105753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105753).length < 2 ^ (prefixWord ++ tailWord_5105753).sum := by decide
  have hdescent : baseEnd_5105753 < baseStart_5105753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105764 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 1, 3, 2]
def baseStart_5105764 : Nat := 118140960795 + 5105764 * 2 ^ 59
def prefixEnd_5105764 : Nat := 4983230072969 + 3 ^ 40 * 5105764 * 2
def baseEnd_5105764 : Nat := 2621711040422666908569025

theorem tailTrace_5105764 : CollatzResearch.WordTrace tailWord_5105764 prefixEnd_5105764 2621711040422666908569025 := by
  unfold tailWord_5105764
  simp only [CollatzResearch.WordTrace]
  refine ⟨93111255937348248956618173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124148341249797665275490897 93111255937348248956618173)
  ·
    refine ⟨34916720976505593358731815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93111255937348248956618173 34916720976505593358731815)
    ·
      refine ⟨52375081464758390038097723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34916720976505593358731815 52375081464758390038097723)
      ·
        refine ⟨78562622197137585057146585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52375081464758390038097723 78562622197137585057146585)
        ·
          refine ⟨58921966647853188792859939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78562622197137585057146585 58921966647853188792859939)
          ·
            refine ⟨88382949971779783189289909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58921966647853188792859939 88382949971779783189289909)
            ·
              refine ⟨8285901559854354673995929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88382949971779783189289909 8285901559854354673995929)
              ·
                refine ⟨6214426169890766005496947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8285901559854354673995929 6214426169890766005496947)
                ·
                  refine ⟨9321639254836149008245421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6214426169890766005496947 9321639254836149008245421)
                  ·
                    refine ⟨3495614720563555878092033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9321639254836149008245421 3495614720563555878092033)
                    ·
                      refine ⟨2621711040422666908569025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495614720563555878092033 2621711040422666908569025)
                      ·
                        rfl

theorem cell23_5105764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_5105764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105764 prefixEnd_5105764 := by exact prefixLift 5105764
  have htrace : WordTrace (prefixWord ++ tailWord_5105764) baseStart_5105764 baseEnd_5105764 := by
    simpa [prefixWord, tailWord_5105764, baseEnd_5105764] using wordTrace_append hprefix tailTrace_5105764
  have hstable : (prefixWord ++ tailWord_5105764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105764).length < 2 ^ (prefixWord ++ tailWord_5105764).sum := by decide
  have hdescent : baseEnd_5105764 < baseStart_5105764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105777 : List Nat := [1, 2, 2, 2, 1, 1, 5, 2, 1, 4, 2]
def baseStart_5105777 : Nat := 118140960795 + 5105777 * 2 ^ 59
def prefixEnd_5105777 : Nat := 4983230072969 + 3 ^ 40 * 5105777 * 2
def baseEnd_5105777 : Nat := 2621717715671175357706465

theorem tailTrace_5105777 : CollatzResearch.WordTrace tailWord_5105777 prefixEnd_5105777 2621717715671175357706465 := by
  unfold tailWord_5105777
  simp only [CollatzResearch.WordTrace]
  refine ⟨186222986023649401133459585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124148657349099600755639723 186222986023649401133459585)
  ·
    refine ⟨139667239517737050850094689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186222986023649401133459585 139667239517737050850094689)
    ·
      refine ⟨104750429638302788137571017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139667239517737050850094689 104750429638302788137571017)
      ·
        refine ⟨78562822228727091103178263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104750429638302788137571017 78562822228727091103178263)
        ·
          refine ⟨117844233343090636654767395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78562822228727091103178263 117844233343090636654767395)
          ·
            refine ⟨176766350014635954982151093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117844233343090636654767395 176766350014635954982151093)
            ·
              refine ⟨16571845313872120779576665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176766350014635954982151093 16571845313872120779576665)
              ·
                refine ⟨12428883985404090584682499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16571845313872120779576665 12428883985404090584682499)
                ·
                  refine ⟨18643325978106135877023749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12428883985404090584682499 18643325978106135877023749)
                  ·
                    refine ⟨3495623620894900476941953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18643325978106135877023749 3495623620894900476941953)
                    ·
                      refine ⟨2621717715671175357706465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495623620894900476941953 2621717715671175357706465)
                      ·
                        rfl

theorem cell23_5105777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_5105777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105777 prefixEnd_5105777 := by exact prefixLift 5105777
  have htrace : WordTrace (prefixWord ++ tailWord_5105777) baseStart_5105777 baseEnd_5105777 := by
    simpa [prefixWord, tailWord_5105777, baseEnd_5105777] using wordTrace_append hprefix tailTrace_5105777
  have hstable : (prefixWord ++ tailWord_5105777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105777).length < 2 ^ (prefixWord ++ tailWord_5105777).sum := by decide
  have hdescent : baseEnd_5105777 < baseStart_5105777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105803 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 8]
def baseStart_5105803 : Nat := 118140960795 + 5105803 * 2 ^ 59
def prefixEnd_5105803 : Nat := 4983230072969 + 3 ^ 40 * 5105803 * 2
def baseEnd_5105803 : Nat := 2621731066168192255981345

theorem tailTrace_5105803 : CollatzResearch.WordTrace tailWord_5105803 prefixEnd_5105803 2621731066168192255981345 := by
  unfold tailWord_5105803
  simp only [CollatzResearch.WordTrace]
  refine ⟨186223934321555207573906063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124149289547703471715937375 186223934321555207573906063)
  ·
    refine ⟨279335901482332811360859095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186223934321555207573906063 279335901482332811360859095)
    ·
      refine ⟨419003852223499217041288643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279335901482332811360859095 419003852223499217041288643)
      ·
        refine ⟨628505778335248825561932965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419003852223499217041288643 628505778335248825561932965)
        ·
          refine ⟨117844833437859154792862431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 628505778335248825561932965 117844833437859154792862431)
          ·
            refine ⟨176767250156788732189293647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117844833437859154792862431 176767250156788732189293647)
            ·
              refine ⟨265150875235183098283940471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176767250156788732189293647 265150875235183098283940471)
              ·
                refine ⟨397726312852774647425910707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265150875235183098283940471 397726312852774647425910707)
                ·
                  refine ⟨596589469279161971138866061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 397726312852774647425910707 596589469279161971138866061)
                  ·
                    refine ⟨223721050979685739177074773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 596589469279161971138866061 223721050979685739177074773)
                    ·
                      refine ⟨2621731066168192255981345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 223721050979685739177074773 2621731066168192255981345)
                      ·
                        rfl

theorem cell23_5105803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_5105803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105803 prefixEnd_5105803 := by exact prefixLift 5105803
  have htrace : WordTrace (prefixWord ++ tailWord_5105803) baseStart_5105803 baseEnd_5105803 := by
    simpa [prefixWord, tailWord_5105803, baseEnd_5105803] using wordTrace_append hprefix tailTrace_5105803
  have hstable : (prefixWord ++ tailWord_5105803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105803).length < 2 ^ (prefixWord ++ tailWord_5105803).sum := by decide
  have hdescent : baseEnd_5105803 < baseStart_5105803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105845 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 2, 2, 2]
def baseStart_5105845 : Nat := 118140960795 + 5105845 * 2 ^ 59
def prefixEnd_5105845 : Nat := 4983230072969 + 3 ^ 40 * 5105845 * 2
def baseEnd_5105845 : Nat := 2621752632355681091656153

theorem tailTrace_5105845 : CollatzResearch.WordTrace tailWord_5105845 prefixEnd_5105845 2621752632355681091656153 := by
  unfold tailWord_5105845
  simp only [CollatzResearch.WordTrace]
  refine ⟨186225466187403048746934989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124150310791602032497956659 186225466187403048746934989)
  ·
    refine ⟨69834549820276143280100621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186225466187403048746934989 69834549820276143280100621)
    ·
      refine ⟨26187956182603553730037733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69834549820276143280100621 26187956182603553730037733)
      ·
        refine ⟨4910241784238166324382075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26187956182603553730037733 4910241784238166324382075)
        ·
          refine ⟨7365362676357249486573113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4910241784238166324382075 7365362676357249486573113)
          ·
            refine ⟨5524022007267937114929835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7365362676357249486573113 5524022007267937114929835)
            ·
              refine ⟨8286033010901905672394753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5524022007267937114929835 8286033010901905672394753)
              ·
                refine ⟨6214524758176429254296065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8286033010901905672394753 6214524758176429254296065)
                ·
                  refine ⟨4660893568632321940722049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6214524758176429254296065 4660893568632321940722049)
                  ·
                    refine ⟨3495670176474241455541537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4660893568632321940722049 3495670176474241455541537)
                    ·
                      refine ⟨2621752632355681091656153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495670176474241455541537 2621752632355681091656153)
                      ·
                        rfl

theorem cell23_5105845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_5105845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105845 prefixEnd_5105845 := by exact prefixLift 5105845
  have htrace : WordTrace (prefixWord ++ tailWord_5105845) baseStart_5105845 baseEnd_5105845 := by
    simpa [prefixWord, tailWord_5105845, baseEnd_5105845] using wordTrace_append hprefix tailTrace_5105845
  have hstable : (prefixWord ++ tailWord_5105845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105845).length < 2 ^ (prefixWord ++ tailWord_5105845).sum := by decide
  have hdescent : baseEnd_5105845 < baseStart_5105845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105867 : List Nat := [1, 1, 1, 1, 3, 2, 3, 3, 2, 4, 2]
def baseStart_5105867 : Nat := 118140960795 + 5105867 * 2 ^ 59
def prefixEnd_5105867 : Nat := 4983230072969 + 3 ^ 40 * 5105867 * 2
def baseEnd_5105867 : Nat := 2621763928930080005581051

theorem tailTrace_5105867 : CollatzResearch.WordTrace tailWord_5105867 prefixEnd_5105867 2621763928930080005581051 := by
  unfold tailWord_5105867
  simp only [CollatzResearch.WordTrace]
  refine ⟨186226268593323346504235855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124150845728882231002823903 186226268593323346504235855)
  ·
    refine ⟨279339402889985019756353783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186226268593323346504235855 279339402889985019756353783)
    ·
      refine ⟨419009104334977529634530675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279339402889985019756353783 419009104334977529634530675)
      ·
        refine ⟨628513656502466294451796013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 419009104334977529634530675 628513656502466294451796013)
        ·
          refine ⟨235692621188424860419423505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 628513656502466294451796013 235692621188424860419423505)
          ·
            refine ⟨176769465891318645314567629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235692621188424860419423505 176769465891318645314567629)
            ·
              refine ⟨66288549709244491992962861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176769465891318645314567629 66288549709244491992962861)
              ·
                refine ⟨24858206140966684497361073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66288549709244491992962861 24858206140966684497361073)
                ·
                  refine ⟨18643654605725013373020805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24858206140966684497361073 18643654605725013373020805)
                  ·
                    refine ⟨3495685238573440007441401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18643654605725013373020805 3495685238573440007441401)
                    ·
                      refine ⟨2621763928930080005581051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495685238573440007441401 2621763928930080005581051)
                      ·
                        rfl

theorem cell23_5105867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 4, 2].length) (baseStart_5105867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105867 prefixEnd_5105867 := by exact prefixLift 5105867
  have htrace : WordTrace (prefixWord ++ tailWord_5105867) baseStart_5105867 baseEnd_5105867 := by
    simpa [prefixWord, tailWord_5105867, baseEnd_5105867] using wordTrace_append hprefix tailTrace_5105867
  have hstable : (prefixWord ++ tailWord_5105867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105867).length < 2 ^ (prefixWord ++ tailWord_5105867).sum := by decide
  have hdescent : baseEnd_5105867 < baseStart_5105867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105887 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 3]
def baseStart_5105887 : Nat := 118140960795 + 5105887 * 2 ^ 59
def prefixEnd_5105887 : Nat := 4983230072969 + 3 ^ 40 * 5105887 * 2
def baseEnd_5105887 : Nat := 2621774198543169927330959

theorem tailTrace_5105887 : CollatzResearch.WordTrace tailWord_5105887 prefixEnd_5105887 2621774198543169927330959 := by
  unfold tailWord_5105887
  simp only [CollatzResearch.WordTrace]
  refine ⟨186226998053250889919963915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124151332035500593279975943 186226998053250889919963915)
  ·
    refine ⟨279340497079876334879945873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186226998053250889919963915 279340497079876334879945873)
    ·
      refine ⟨209505372809907251159959405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279340497079876334879945873 209505372809907251159959405)
      ·
        refine ⟨78564514803715219184984777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209505372809907251159959405 78564514803715219184984777)
        ·
          refine ⟨58923386102786414388738583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78564514803715219184984777 58923386102786414388738583)
          ·
            refine ⟨88385079154179621583107875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58923386102786414388738583 88385079154179621583107875)
            ·
              refine ⟨132577618731269432374661813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88385079154179621583107875 132577618731269432374661813)
              ·
                refine ⟨12429151756056509285124545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132577618731269432374661813 12429151756056509285124545)
                ·
                  refine ⟨9321863817042381963843409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12429151756056509285124545 9321863817042381963843409)
                  ·
                    refine ⟨6991397862781786472882557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9321863817042381963843409 6991397862781786472882557)
                    ·
                      refine ⟨2621774198543169927330959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6991397862781786472882557 2621774198543169927330959)
                      ·
                        rfl

theorem cell23_5105887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_5105887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105887 prefixEnd_5105887 := by exact prefixLift 5105887
  have htrace : WordTrace (prefixWord ++ tailWord_5105887) baseStart_5105887 baseEnd_5105887 := by
    simpa [prefixWord, tailWord_5105887, baseEnd_5105887] using wordTrace_append hprefix tailTrace_5105887
  have hstable : (prefixWord ++ tailWord_5105887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105887).length < 2 ^ (prefixWord ++ tailWord_5105887).sum := by decide
  have hdescent : baseEnd_5105887 < baseStart_5105887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105924 : List Nat := [2, 3, 2, 2, 3, 1, 1, 3, 6]
def baseStart_5105924 : Nat := 118140960795 + 5105924 * 2 ^ 59
def prefixEnd_5105924 : Nat := 4983230072969 + 3 ^ 40 * 5105924 * 2
def baseEnd_5105924 : Nat := 291310355258598475840921

theorem tailTrace_5105924 : CollatzResearch.WordTrace tailWord_5105924 prefixEnd_5105924 291310355258598475840921 := by
  unfold tailWord_5105924
  simp only [CollatzResearch.WordTrace]
  refine ⟨93114173777058422619530413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124152231702744563492707217 93114173777058422619530413)
  ·
    refine ⟨34917815166396908482323905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93114173777058422619530413 34917815166396908482323905)
    ·
      refine ⟨26188361374797681361742929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34917815166396908482323905 26188361374797681361742929)
      ·
        refine ⟨19641271031098261021307197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26188361374797681361742929 19641271031098261021307197)
        ·
          refine ⟨7365476636661847882990199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19641271031098261021307197 7365476636661847882990199)
          ·
            refine ⟨11048214954992771824485299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7365476636661847882990199 11048214954992771824485299)
            ·
              refine ⟨16572322432489157736727949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11048214954992771824485299 16572322432489157736727949)
              ·
                refine ⟨6214620912183434151272981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16572322432489157736727949 6214620912183434151272981)
                ·
                  refine ⟨291310355258598475840921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6214620912183434151272981 291310355258598475840921)
                  ·
                    rfl

theorem cell23_5105924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_5105924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105924 prefixEnd_5105924 := by exact prefixLift 5105924
  have htrace : WordTrace (prefixWord ++ tailWord_5105924) baseStart_5105924 baseEnd_5105924 := by
    simpa [prefixWord, tailWord_5105924, baseEnd_5105924] using wordTrace_append hprefix tailTrace_5105924
  have hstable : (prefixWord ++ tailWord_5105924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105924).length < 2 ^ (prefixWord ++ tailWord_5105924).sum := by decide
  have hdescent : baseEnd_5105924 < baseStart_5105924 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105934 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_5105934 : Nat := 118140960795 + 5105934 * 2 ^ 59
def prefixEnd_5105934 : Nat := 4983230072969 + 3 ^ 40 * 5105934 * 2
def baseEnd_5105934 : Nat := 2621798332133931243443243

theorem tailTrace_5105934 : CollatzResearch.WordTrace tailWord_5105934 prefixEnd_5105934 2621798332133931243443243 := by
  unfold tailWord_5105934
  simp only [CollatzResearch.WordTrace]
  refine ⟨23278589035510077118365607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124152474856053744631283237 23278589035510077118365607)
  ·
    refine ⟨34917883553265115677548411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23278589035510077118365607 34917883553265115677548411)
    ·
      refine ⟨52376825329897673516322617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34917883553265115677548411 52376825329897673516322617)
      ·
        refine ⟨39282618997423255137241963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52376825329897673516322617 39282618997423255137241963)
        ·
          refine ⟨58923928496134882705862945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39282618997423255137241963 58923928496134882705862945)
          ·
            refine ⟨44192946372101162029397209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58923928496134882705862945 44192946372101162029397209)
            ·
              refine ⟨33144709779075871522047907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44192946372101162029397209 33144709779075871522047907)
              ·
                refine ⟨49717064668613807283071861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33144709779075871522047907 49717064668613807283071861)
                ·
                  refine ⟨4660974812682544432787987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49717064668613807283071861 4660974812682544432787987)
                  ·
                    refine ⟨6991462219023816649181981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4660974812682544432787987 6991462219023816649181981)
                    ·
                      refine ⟨2621798332133931243443243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6991462219023816649181981 2621798332133931243443243)
                      ·
                        rfl

theorem cell23_5105934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_5105934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105934 prefixEnd_5105934 := by exact prefixLift 5105934
  have htrace : WordTrace (prefixWord ++ tailWord_5105934) baseStart_5105934 baseEnd_5105934 := by
    simpa [prefixWord, tailWord_5105934, baseEnd_5105934] using wordTrace_append hprefix tailTrace_5105934
  have hstable : (prefixWord ++ tailWord_5105934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105934).length < 2 ^ (prefixWord ++ tailWord_5105934).sum := by decide
  have hdescent : baseEnd_5105934 < baseStart_5105934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105937 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 3, 5]
def baseStart_5105937 : Nat := 118140960795 + 5105937 * 2 ^ 59
def prefixEnd_5105937 : Nat := 4983230072969 + 3 ^ 40 * 5105937 * 2
def baseEnd_5105937 : Nat := 873933290858631577235243

theorem tailTrace_5105937 : CollatzResearch.WordTrace tailWord_5105937 prefixEnd_5105937 873933290858631577235243 := by
  unfold tailWord_5105937
  simp only [CollatzResearch.WordTrace]
  refine ⟨186228821703069748459284065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124152547802046498972856043 186228821703069748459284065)
  ·
    refine ⟨139671616277302311344463049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186228821703069748459284065 139671616277302311344463049)
    ·
      refine ⟨104753712207976733508347287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139671616277302311344463049 104753712207976733508347287)
      ·
        refine ⟨157130568311965100262520931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104753712207976733508347287 157130568311965100262520931)
        ·
          refine ⟨235695852467947650393781397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157130568311965100262520931 235695852467947650393781397)
          ·
            refine ⟨11048243084435046112208503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 235695852467947650393781397 11048243084435046112208503)
            ·
              refine ⟨16572364626652569168312755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11048243084435046112208503 16572364626652569168312755)
              ·
                refine ⟨24858546939978853752469133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16572364626652569168312755 24858546939978853752469133)
                ·
                  refine ⟨9321955102492070157175925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24858546939978853752469133 9321955102492070157175925)
                  ·
                    refine ⟨873933290858631577235243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9321955102492070157175925 873933290858631577235243)
                    ·
                      rfl

theorem cell23_5105937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_5105937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105937 prefixEnd_5105937 := by exact prefixLift 5105937
  have htrace : WordTrace (prefixWord ++ tailWord_5105937) baseStart_5105937 baseEnd_5105937 := by
    simpa [prefixWord, tailWord_5105937, baseEnd_5105937] using wordTrace_append hprefix tailTrace_5105937
  have hstable : (prefixWord ++ tailWord_5105937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105937).length < 2 ^ (prefixWord ++ tailWord_5105937).sum := by decide
  have hdescent : baseEnd_5105937 < baseStart_5105937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105962 : List Nat := [3, 1, 4, 2, 3, 1, 2, 2, 1, 4]
def baseStart_5105962 : Nat := 118140960795 + 5105962 * 2 ^ 59
def prefixEnd_5105962 : Nat := 4983230072969 + 3 ^ 40 * 5105962 * 2
def baseEnd_5105962 : Nat := 873937569864085711297705

theorem tailTrace_5105962 : CollatzResearch.WordTrace tailWord_5105962 prefixEnd_5105962 873937569864085711297705 := by
  unfold tailWord_5105962
  simp only [CollatzResearch.WordTrace]
  refine ⟨46557433381994794432236035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124153155685319451819296093 46557433381994794432236035)
  ·
    refine ⟨69836150072992191648354053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46557433381994794432236035 69836150072992191648354053)
    ·
      refine ⟨13094278138686035934066385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69836150072992191648354053 13094278138686035934066385)
      ·
        refine ⟨9820708604014526950549789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13094278138686035934066385 9820708604014526950549789)
        ·
          refine ⟨3682765726505447606456171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9820708604014526950549789 3682765726505447606456171)
          ·
            refine ⟨5524148589758171409684257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682765726505447606456171 5524148589758171409684257)
            ·
              refine ⟨4143111442318628557263193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5524148589758171409684257 4143111442318628557263193)
              ·
                refine ⟨3107333581738971417947395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4143111442318628557263193 3107333581738971417947395)
                ·
                  refine ⟨4661000372608457126921093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107333581738971417947395 4661000372608457126921093)
                  ·
                    refine ⟨873937569864085711297705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4661000372608457126921093 873937569864085711297705)
                    ·
                      rfl

theorem cell23_5105962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_5105962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105962 prefixEnd_5105962 := by exact prefixLift 5105962
  have htrace : WordTrace (prefixWord ++ tailWord_5105962) baseStart_5105962 baseEnd_5105962 := by
    simpa [prefixWord, tailWord_5105962, baseEnd_5105962] using wordTrace_append hprefix tailTrace_5105962
  have hstable : (prefixWord ++ tailWord_5105962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105962).length < 2 ^ (prefixWord ++ tailWord_5105962).sum := by decide
  have hdescent : baseEnd_5105962 < baseStart_5105962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105967 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 4, 4]
def baseStart_5105967 : Nat := 118140960795 + 5105967 * 2 ^ 59
def prefixEnd_5105967 : Nat := 4983230072969 + 3 ^ 40 * 5105967 * 2
def baseEnd_5105967 : Nat := 873938425665176538110197

theorem tailTrace_5105967 : CollatzResearch.WordTrace tailWord_5105967 prefixEnd_5105967 873938425665176538110197 := by
  unfold tailWord_5105967
  simp only [CollatzResearch.WordTrace]
  refine ⟨186229915892961063582876155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124153277261974042388584103 186229915892961063582876155)
  ·
    refine ⟨279344873839441595374314233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186229915892961063582876155 279344873839441595374314233)
    ·
      refine ⟨209508655379581196530735675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279344873839441595374314233 209508655379581196530735675)
      ·
        refine ⟨314262983069371794796103513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209508655379581196530735675 314262983069371794796103513)
        ·
          refine ⟨235697237302028846097077635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314262983069371794796103513 235697237302028846097077635)
          ·
            refine ⟨353545855953043269145616453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235697237302028846097077635 353545855953043269145616453)
            ·
              refine ⟨66289847991195612964803085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 353545855953043269145616453 66289847991195612964803085)
              ·
                refine ⟨24858692996698354861801157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66289847991195612964803085 24858692996698354861801157)
                ·
                  refine ⟨4661004936880941536587717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24858692996698354861801157 4661004936880941536587717)
                  ·
                    refine ⟨873938425665176538110197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4661004936880941536587717 873938425665176538110197)
                    ·
                      rfl

theorem cell23_5105967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 4].length) (baseStart_5105967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105967 prefixEnd_5105967 := by exact prefixLift 5105967
  have htrace : WordTrace (prefixWord ++ tailWord_5105967) baseStart_5105967 baseEnd_5105967 := by
    simpa [prefixWord, tailWord_5105967, baseEnd_5105967] using wordTrace_append hprefix tailTrace_5105967
  have hstable : (prefixWord ++ tailWord_5105967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105967).length < 2 ^ (prefixWord ++ tailWord_5105967).sum := by decide
  have hdescent : baseEnd_5105967 < baseStart_5105967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105987 : List Nat := [1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 4]
def baseStart_5105987 : Nat := 118140960795 + 5105987 * 2 ^ 59
def prefixEnd_5105987 : Nat := 4983230072969 + 3 ^ 40 * 5105987 * 2
def baseEnd_5105987 : Nat := 2621825546608619536080499

theorem tailTrace_5105987 : CollatzResearch.WordTrace tailWord_5105987 prefixEnd_5105987 2621825546608619536080499 := by
  unfold tailWord_5105987
  simp only [CollatzResearch.WordTrace]
  refine ⟨186230645352888606998604215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124153763568592404665736143 186230645352888606998604215)
  ·
    refine ⟨279345968029332910497906323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186230645352888606998604215 279345968029332910497906323)
    ·
      refine ⟨419018952043999365746859485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279345968029332910497906323 419018952043999365746859485)
      ·
        refine ⟨157132107016499762155072307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419018952043999365746859485 157132107016499762155072307)
        ·
          refine ⟨235698160524749643232608461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157132107016499762155072307 235698160524749643232608461)
          ·
            refine ⟨88386810196781116212228173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235698160524749643232608461 88386810196781116212228173)
            ·
              refine ⟨33145053823792918579585565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88386810196781116212228173 33145053823792918579585565)
              ·
                refine ⟨12429395183922344467344587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33145053823792918579585565 12429395183922344467344587)
                ·
                  refine ⟨18644092775883516701016881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12429395183922344467344587 18644092775883516701016881)
                  ·
                    refine ⟨13983069581912637525762661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18644092775883516701016881 13983069581912637525762661)
                    ·
                      refine ⟨2621825546608619536080499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13983069581912637525762661 2621825546608619536080499)
                      ·
                        rfl

theorem cell23_5105987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_5105987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105987 prefixEnd_5105987 := by exact prefixLift 5105987
  have htrace : WordTrace (prefixWord ++ tailWord_5105987) baseStart_5105987 baseEnd_5105987 := by
    simpa [prefixWord, tailWord_5105987, baseEnd_5105987] using wordTrace_append hprefix tailTrace_5105987
  have hstable : (prefixWord ++ tailWord_5105987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105987).length < 2 ^ (prefixWord ++ tailWord_5105987).sum := by decide
  have hdescent : baseEnd_5105987 < baseStart_5105987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5105991 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 3, 2, 2]
def baseStart_5105991 : Nat := 118140960795 + 5105991 * 2 ^ 59
def prefixEnd_5105991 : Nat := 4983230072969 + 3 ^ 40 * 5105991 * 2
def baseEnd_5105991 : Nat := 2621827600531237520430481

theorem tailTrace_5105991 : CollatzResearch.WordTrace tailWord_5105991 prefixEnd_5105991 2621827600531237520430481 := by
  unfold tailWord_5105991
  simp only [CollatzResearch.WordTrace]
  refine ⟨186230791244874115681749827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124153860829916077121166551 186230791244874115681749827)
  ·
    refine ⟨279346186867311173522624741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186230791244874115681749827 279346186867311173522624741)
    ·
      refine ⟨52377410037620845035492139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279346186867311173522624741 52377410037620845035492139)
      ·
        refine ⟨78566115056431267553238209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52377410037620845035492139 78566115056431267553238209)
        ·
          refine ⟨58924586292323450664928657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78566115056431267553238209 58924586292323450664928657)
          ·
            refine ⟨44193439719242587998696493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58924586292323450664928657 44193439719242587998696493)
            ·
              refine ⟨16572539894715970499511185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44193439719242587998696493 16572539894715970499511185)
              ·
                refine ⟨12429404921036977874633389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16572539894715970499511185 12429404921036977874633389)
                ·
                  refine ⟨4661026845388866702987521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12429404921036977874633389 4661026845388866702987521)
                  ·
                    refine ⟨3495770134041650027240641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4661026845388866702987521 3495770134041650027240641)
                    ·
                      refine ⟨2621827600531237520430481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495770134041650027240641 2621827600531237520430481)
                      ·
                        rfl

theorem cell23_5105991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_5105991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5105991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5105991 prefixEnd_5105991 := by exact prefixLift 5105991
  have htrace : WordTrace (prefixWord ++ tailWord_5105991) baseStart_5105991 baseEnd_5105991 := by
    simpa [prefixWord, tailWord_5105991, baseEnd_5105991] using wordTrace_append hprefix tailTrace_5105991
  have hstable : (prefixWord ++ tailWord_5105991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5105991).length < 2 ^ (prefixWord ++ tailWord_5105991).sum := by decide
  have hdescent : baseEnd_5105991 < baseStart_5105991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5105991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106004 : List Nat := [2, 4, 1, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_5106004 : Nat := 118140960795 + 5106004 * 2 ^ 59
def prefixEnd_5106004 : Nat := 4983230072969 + 3 ^ 40 * 5106004 * 2
def baseEnd_5106004 : Nat := 2621834275779745969567921

theorem tailTrace_5106004 : CollatzResearch.WordTrace tailWord_5106004 prefixEnd_5106004 2621834275779745969567921 := by
  unfold tailWord_5106004
  simp only [CollatzResearch.WordTrace]
  refine ⟨93115632696913509450986533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124154176929218012601315377 93115632696913509450986533)
  ·
    refine ⟨17459181130671283022059975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93115632696913509450986533 17459181130671283022059975)
    ·
      refine ⟨26188771696006924533089963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17459181130671283022059975 26188771696006924533089963)
      ·
        refine ⟨39283157544010386799634945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26188771696006924533089963 39283157544010386799634945)
        ·
          refine ⟨29462368158007790099726209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39283157544010386799634945 29462368158007790099726209)
          ·
            refine ⟨22096776118505842574794657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29462368158007790099726209 22096776118505842574794657)
            ·
              refine ⟨16572582088879381931095993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22096776118505842574794657 16572582088879381931095993)
              ·
                refine ⟨12429436566659536448321995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16572582088879381931095993 12429436566659536448321995)
                ·
                  refine ⟨18644154849989304672482993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12429436566659536448321995 18644154849989304672482993)
                  ·
                    refine ⟨13983116137491978504362245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18644154849989304672482993 13983116137491978504362245)
                    ·
                      refine ⟨2621834275779745969567921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13983116137491978504362245 2621834275779745969567921)
                      ·
                        rfl

theorem cell23_5106004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_5106004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106004 prefixEnd_5106004 := by exact prefixLift 5106004
  have htrace : WordTrace (prefixWord ++ tailWord_5106004) baseStart_5106004 baseEnd_5106004 := by
    simpa [prefixWord, tailWord_5106004, baseEnd_5106004] using wordTrace_append hprefix tailTrace_5106004
  have hstable : (prefixWord ++ tailWord_5106004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106004).length < 2 ^ (prefixWord ++ tailWord_5106004).sum := by decide
  have hdescent : baseEnd_5106004 < baseStart_5106004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106018 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_5106018 : Nat := 118140960795 + 5106018 * 2 ^ 59
def prefixEnd_5106018 : Nat := 4983230072969 + 3 ^ 40 * 5106018 * 2
def baseEnd_5106018 : Nat := 873947154836302971597619

theorem tailTrace_5106018 : CollatzResearch.WordTrace tailWord_5106018 prefixEnd_5106018 873947154836302971597619 := by
  unfold tailWord_5106018
  simp only [CollatzResearch.WordTrace]
  refine ⟨46557944003944074823245677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124154517343850866195321805 46557944003944074823245677)
  ·
    refine ⟨17459229001479028058717129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46557944003944074823245677 17459229001479028058717129)
    ·
      refine ⟨13094421751109271044037847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17459229001479028058717129 13094421751109271044037847)
      ·
        refine ⟨19641632626663906566056771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13094421751109271044037847 19641632626663906566056771)
        ·
          refine ⟨29462448939995859849085157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19641632626663906566056771 29462448939995859849085157)
          ·
            refine ⟨5524209176249223721703467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29462448939995859849085157 5524209176249223721703467)
            ·
              refine ⟨8286313764373835582555201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5524209176249223721703467 8286313764373835582555201)
              ·
                refine ⟨6214735323280376686916401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8286313764373835582555201 6214735323280376686916401)
                ·
                  refine ⟨4661051492460282515187301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6214735323280376686916401 4661051492460282515187301)
                  ·
                    refine ⟨873947154836302971597619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4661051492460282515187301 873947154836302971597619)
                    ·
                      rfl

theorem cell23_5106018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_5106018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106018 prefixEnd_5106018 := by exact prefixLift 5106018
  have htrace : WordTrace (prefixWord ++ tailWord_5106018) baseStart_5106018 baseEnd_5106018 := by
    simpa [prefixWord, tailWord_5106018, baseEnd_5106018] using wordTrace_append hprefix tailTrace_5106018
  have hstable : (prefixWord ++ tailWord_5106018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106018).length < 2 ^ (prefixWord ++ tailWord_5106018).sum := by decide
  have hdescent : baseEnd_5106018 < baseStart_5106018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106098 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2]
def baseStart_5106098 : Nat := 118140960795 + 5106098 * 2 ^ 59
def prefixEnd_5106098 : Nat := 4983230072969 + 3 ^ 40 * 5106098 * 2
def baseEnd_5106098 : Nat := 2621882542961268601792489

theorem tailTrace_5106098 : CollatzResearch.WordTrace tailWord_5106098 prefixEnd_5106098 2621882542961268601792489 := by
  unfold tailWord_5106098
  simp only [CollatzResearch.WordTrace]
  refine ⟨46558673463871618238973737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124156462570324315303929965 46558673463871618238973737)
  ·
    refine ⟨34919005097903713679230303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46558673463871618238973737 34919005097903713679230303)
    ·
      refine ⟨52378507646855570518845455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34919005097903713679230303 52378507646855570518845455)
      ·
        refine ⟨78567761470283355778268183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52378507646855570518845455 78567761470283355778268183)
        ·
          refine ⟨117851642205425033667402275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78567761470283355778268183 117851642205425033667402275)
          ·
            refine ⟨176777463308137550501103413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117851642205425033667402275 176777463308137550501103413)
            ·
              refine ⟨16572887185137895359478445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176777463308137550501103413 16572887185137895359478445)
              ·
                refine ⟨6214832694426710759804417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16572887185137895359478445 6214832694426710759804417)
                ·
                  refine ⟨4661124520820033069853313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6214832694426710759804417 4661124520820033069853313)
                  ·
                    refine ⟨3495843390615024802389985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4661124520820033069853313 3495843390615024802389985)
                    ·
                      refine ⟨2621882542961268601792489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495843390615024802389985 2621882542961268601792489)
                      ·
                        rfl

theorem cell23_5106098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_5106098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106098 prefixEnd_5106098 := by exact prefixLift 5106098
  have htrace : WordTrace (prefixWord ++ tailWord_5106098) baseStart_5106098 baseEnd_5106098 := by
    simpa [prefixWord, tailWord_5106098, baseEnd_5106098] using wordTrace_append hprefix tailTrace_5106098
  have hstable : (prefixWord ++ tailWord_5106098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106098).length < 2 ^ (prefixWord ++ tailWord_5106098).sum := by decide
  have hdescent : baseEnd_5106098 < baseStart_5106098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106141 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_5106141 : Nat := 118140960795 + 5106141 * 2 ^ 59
def prefixEnd_5106141 : Nat := 4983230072969 + 3 ^ 40 * 5106141 * 2
def baseEnd_5106141 : Nat := 2621904622629411933554791

theorem tailTrace_5106141 : CollatzResearch.WordTrace tailWord_5106141 prefixEnd_5106141 2621904622629411933554791 := by
  unfold tailWord_5106141
  simp only [CollatzResearch.WordTrace]
  refine ⟨186236262194330691299710277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124157508129553794199806851 186236262194330691299710277)
  ·
    refine ⟨34919299161437004618695677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186236262194330691299710277 34919299161437004618695677)
    ·
      refine ⟨13094737185538876732010879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34919299161437004618695677 13094737185538876732010879)
      ·
        refine ⟨19642105778308315098016319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13094737185538876732010879 19642105778308315098016319)
        ·
          refine ⟨29463158667462472647024479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19642105778308315098016319 29463158667462472647024479)
          ·
            refine ⟨44194738001193708970536719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29463158667462472647024479 44194738001193708970536719)
            ·
              refine ⟨66292107001790563455805079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44194738001193708970536719 66292107001790563455805079)
              ·
                refine ⟨99438160502685845183707619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66292107001790563455805079 99438160502685845183707619)
                ·
                  refine ⟨149157240754028767775561429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99438160502685845183707619 149157240754028767775561429)
                  ·
                    refine ⟨3495872830172549244739721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 149157240754028767775561429 3495872830172549244739721)
                    ·
                      refine ⟨2621904622629411933554791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495872830172549244739721 2621904622629411933554791)
                      ·
                        rfl

theorem cell23_5106141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_5106141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106141 prefixEnd_5106141 := by exact prefixLift 5106141
  have htrace : WordTrace (prefixWord ++ tailWord_5106141) baseStart_5106141 baseEnd_5106141 := by
    simpa [prefixWord, tailWord_5106141, baseEnd_5106141] using wordTrace_append hprefix tailTrace_5106141
  have hstable : (prefixWord ++ tailWord_5106141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106141).length < 2 ^ (prefixWord ++ tailWord_5106141).sum := by decide
  have hdescent : baseEnd_5106141 < baseStart_5106141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106224 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 3, 5]
def baseStart_5106224 : Nat := 118140960795 + 5106224 * 2 ^ 59
def prefixEnd_5106224 : Nat := 4983230072969 + 3 ^ 40 * 5106224 * 2
def baseEnd_5106224 : Nat := 873982413841245036272303

theorem tailTrace_5106224 : CollatzResearch.WordTrace tailWord_5106224 prefixEnd_5106224 873982413841245036272303 := by
  unfold tailWord_5106224
  simp only [CollatzResearch.WordTrace]
  refine ⟨93119644726514998237490863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124159526302019997649987817 93119644726514998237490863)
  ·
    refine ⟨139679467089772497356236295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93119644726514998237490863 139679467089772497356236295)
    ·
      refine ⟨209519200634658746034354443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139679467089772497356236295 209519200634658746034354443)
      ·
        refine ⟨314278800951988119051531665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209519200634658746034354443 314278800951988119051531665)
        ·
          refine ⟨235709100713991089288648749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314278800951988119051531665 235709100713991089288648749)
          ·
            refine ⟨88390912767746658483243281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 235709100713991089288648749 88390912767746658483243281)
            ·
              refine ⟨66293184575809993862432461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88390912767746658483243281 66293184575809993862432461)
              ·
                refine ⟨24859944215928747698412173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66293184575809993862432461 24859944215928747698412173)
                ·
                  refine ⟨9322479080973280386904565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24859944215928747698412173 9322479080973280386904565)
                  ·
                    refine ⟨873982413841245036272303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9322479080973280386904565 873982413841245036272303)
                    ·
                      rfl

theorem cell23_5106224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_5106224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106224 prefixEnd_5106224 := by exact prefixLift 5106224
  have htrace : WordTrace (prefixWord ++ tailWord_5106224) baseStart_5106224 baseEnd_5106224 := by
    simpa [prefixWord, tailWord_5106224, baseEnd_5106224] using wordTrace_append hprefix tailTrace_5106224
  have hstable : (prefixWord ++ tailWord_5106224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106224).length < 2 ^ (prefixWord ++ tailWord_5106224).sum := by decide
  have hdescent : baseEnd_5106224 < baseStart_5106224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106231 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 1, 5, 2]
def baseStart_5106231 : Nat := 118140960795 + 5106231 * 2 ^ 59
def prefixEnd_5106231 : Nat := 4983230072969 + 3 ^ 40 * 5106231 * 2
def baseEnd_5106231 : Nat := 2621950835888316581429377

theorem tailTrace_5106231 : CollatzResearch.WordTrace tailWord_5106231 prefixEnd_5106231 2621950835888316581429377 := by
  unfold tailWord_5106231
  simp only [CollatzResearch.WordTrace]
  refine ⟨186239544764004636670486547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124159696509336424446991031 186239544764004636670486547)
  ·
    refine ⟨279359317146006955005729821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186239544764004636670486547 279359317146006955005729821)
    ·
      refine ⟨104759743929752608127148683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279359317146006955005729821 104759743929752608127148683)
      ·
        refine ⟨157139615894628912190723025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104759743929752608127148683 157139615894628912190723025)
        ·
          refine ⟨117854711920971684143042269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157139615894628912190723025 117854711920971684143042269)
          ·
            refine ⟨44195516970364381553640851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117854711920971684143042269 44195516970364381553640851)
            ·
              refine ⟨66293275455546572330461277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44195516970364381553640851 66293275455546572330461277)
              ·
                refine ⟨24859978295829964623922979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66293275455546572330461277 24859978295829964623922979)
                ·
                  refine ⟨37289967443744946935884469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24859978295829964623922979 37289967443744946935884469)
                  ·
                    refine ⟨3495934447851088775239169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37289967443744946935884469 3495934447851088775239169)
                    ·
                      refine ⟨2621950835888316581429377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3495934447851088775239169 2621950835888316581429377)
                      ·
                        rfl

theorem cell23_5106231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 5, 2].length) (baseStart_5106231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106231 prefixEnd_5106231 := by exact prefixLift 5106231
  have htrace : WordTrace (prefixWord ++ tailWord_5106231) baseStart_5106231 baseEnd_5106231 := by
    simpa [prefixWord, tailWord_5106231, baseEnd_5106231] using wordTrace_append hprefix tailTrace_5106231
  have hstable : (prefixWord ++ tailWord_5106231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106231).length < 2 ^ (prefixWord ++ tailWord_5106231).sum := by decide
  have hdescent : baseEnd_5106231 < baseStart_5106231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106284 : List Nat := [2, 2, 1, 1, 3, 1, 4, 9]
def baseStart_5106284 : Nat := 118140960795 + 5106284 * 2 ^ 59
def prefixEnd_5106284 : Nat := 4983230072969 + 3 ^ 40 * 5106284 * 2
def baseEnd_5106284 : Nat := 97110298161592773113579

theorem tailTrace_5106284 : CollatzResearch.WordTrace tailWord_5106284 prefixEnd_5106284 97110298161592773113579 := by
  unfold tailWord_5106284
  simp only [CollatzResearch.WordTrace]
  refine ⟨93120738916406313361082953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124160985221875084481443937 93120738916406313361082953)
  ·
    refine ⟨69840554187304735020812215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93120738916406313361082953 69840554187304735020812215)
    ·
      refine ⟨104760831280957102531218323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69840554187304735020812215 104760831280957102531218323)
      ·
        refine ⟨157141246921435653796827485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104760831280957102531218323 157141246921435653796827485)
        ·
          refine ⟨58927967595538370173810307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157141246921435653796827485 58927967595538370173810307)
          ·
            refine ⟨88391951393307555260715461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58927967595538370173810307 88391951393307555260715461)
            ·
              refine ⟨16573490886245166611384149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88391951393307555260715461 16573490886245166611384149)
              ·
                refine ⟨97110298161592773113579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16573490886245166611384149 97110298161592773113579)
                ·
                  rfl

theorem cell23_5106284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 9].length) (baseStart_5106284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106284 prefixEnd_5106284 := by exact prefixLift 5106284
  have htrace : WordTrace (prefixWord ++ tailWord_5106284) baseStart_5106284 baseEnd_5106284 := by
    simpa [prefixWord, tailWord_5106284, baseEnd_5106284] using wordTrace_append hprefix tailTrace_5106284
  have hstable : (prefixWord ++ tailWord_5106284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106284).length < 2 ^ (prefixWord ++ tailWord_5106284).sum := by decide
  have hdescent : baseEnd_5106284 < baseStart_5106284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106301 : List Nat := [1, 4, 1, 1, 6, 10]
def baseStart_5106301 : Nat := 118140960795 + 5106301 * 2 ^ 59
def prefixEnd_5106301 : Nat := 4983230072969 + 3 ^ 40 * 5106301 * 2
def baseEnd_5106301 : Nat := 10790069051580787273885

theorem tailTrace_5106301 : CollatzResearch.WordTrace tailWord_5106301 prefixEnd_5106301 10790069051580787273885 := by
  unfold tailWord_5106301
  simp only [CollatzResearch.WordTrace]
  refine ⟨186242097873751038625534757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124161398582500692417023171 186242097873751038625534757)
  ·
    refine ⟨34920393351328319742287767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186242097873751038625534757 34920393351328319742287767)
    ·
      refine ⟨52380590026992479613431651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34920393351328319742287767 52380590026992479613431651)
      ·
        refine ⟨78570885040488719420147477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52380590026992479613431651 78570885040488719420147477)
        ·
          refine ⟨3683010236272908722819413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 78570885040488719420147477 3683010236272908722819413)
          ·
            refine ⟨10790069051580787273885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3683010236272908722819413 10790069051580787273885)
            ·
              rfl

theorem cell23_5106301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 10].length) (baseStart_5106301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106301 prefixEnd_5106301 := by exact prefixLift 5106301
  have htrace : WordTrace (prefixWord ++ tailWord_5106301) baseStart_5106301 baseEnd_5106301 := by
    simpa [prefixWord, tailWord_5106301, baseEnd_5106301] using wordTrace_append hprefix tailTrace_5106301
  have hstable : (prefixWord ++ tailWord_5106301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106301).length < 2 ^ (prefixWord ++ tailWord_5106301).sum := by decide
  have hdescent : baseEnd_5106301 < baseStart_5106301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106311 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 3]
def baseStart_5106311 : Nat := 118140960795 + 5106311 * 2 ^ 59
def prefixEnd_5106311 : Nat := 4983230072969 + 3 ^ 40 * 5106311 * 2
def baseEnd_5106311 : Nat := 2621991914340676268429009

theorem tailTrace_5106311 : CollatzResearch.WordTrace tailWord_5106311 prefixEnd_5106311 2621991914340676268429009 := by
  unfold tailWord_5106311
  simp only [CollatzResearch.WordTrace]
  refine ⟨186242462603714810333398787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124161641735809873555599191 186242462603714810333398787)
  ·
    refine ⟨279363693905572215500098181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186242462603714810333398787 279363693905572215500098181)
    ·
      refine ⟨52380692607294790406268409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 279363693905572215500098181 52380692607294790406268409)
      ·
        refine ⟨39285519455471092804701307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52380692607294790406268409 39285519455471092804701307)
        ·
          refine ⟨58928279183206639207051961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39285519455471092804701307 58928279183206639207051961)
          ·
            refine ⟨44196209387404979405288971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58928279183206639207051961 44196209387404979405288971)
            ·
              refine ⟨66294314081107469107933457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44196209387404979405288971 66294314081107469107933457)
              ·
                refine ⟨49720735560830601830950093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66294314081107469107933457 49720735560830601830950093)
                ·
                  refine ⟨18645275835311475686606285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49720735560830601830950093 18645275835311475686606285)
                  ·
                    refine ⟨6991978438241803382477357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18645275835311475686606285 6991978438241803382477357)
                    ·
                      refine ⟨2621991914340676268429009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6991978438241803382477357 2621991914340676268429009)
                      ·
                        rfl

theorem cell23_5106311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_5106311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106311 prefixEnd_5106311 := by exact prefixLift 5106311
  have htrace : WordTrace (prefixWord ++ tailWord_5106311) baseStart_5106311 baseEnd_5106311 := by
    simpa [prefixWord, tailWord_5106311, baseEnd_5106311] using wordTrace_append hprefix tailTrace_5106311
  have hstable : (prefixWord ++ tailWord_5106311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106311).length < 2 ^ (prefixWord ++ tailWord_5106311).sum := by decide
  have hdescent : baseEnd_5106311 < baseStart_5106311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106328 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 1, 3, 3]
def baseStart_5106328 : Nat := 118140960795 + 5106328 * 2 ^ 59
def prefixEnd_5106328 : Nat := 4983230072969 + 3 ^ 40 * 5106328 * 2
def baseEnd_5106328 : Nat := 2622000643511802701916431

theorem tailTrace_5106328 : CollatzResearch.WordTrace tailWord_5106328 prefixEnd_5106328 2622000643511802701916431 := by
  unfold tailWord_5106328
  simp only [CollatzResearch.WordTrace]
  refine ⟨93121541322326611118383819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124162055096435481491178425 93121541322326611118383819)
  ·
    refine ⟨139682311983489916677575729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93121541322326611118383819 139682311983489916677575729)
    ·
      refine ⟨104761733987617437508181797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139682311983489916677575729 104761733987617437508181797)
      ·
        refine ⟨19642825122678269532784087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104761733987617437508181797 19642825122678269532784087)
        ·
          refine ⟨29464237684017404299176131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19642825122678269532784087 29464237684017404299176131)
          ·
            refine ⟨44196356526026106448764197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29464237684017404299176131 44196356526026106448764197)
            ·
              refine ⟨8286816848629894959143287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44196356526026106448764197 8286816848629894959143287)
              ·
                refine ⟨12430225272944842438714931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8286816848629894959143287 12430225272944842438714931)
                ·
                  refine ⟨18645337909417263658072397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12430225272944842438714931 18645337909417263658072397)
                  ·
                    refine ⟨6992001716031473871777149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18645337909417263658072397 6992001716031473871777149)
                    ·
                      refine ⟨2622000643511802701916431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6992001716031473871777149 2622000643511802701916431)
                      ·
                        rfl

theorem cell23_5106328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_5106328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106328 prefixEnd_5106328 := by exact prefixLift 5106328
  have htrace : WordTrace (prefixWord ++ tailWord_5106328) baseStart_5106328 baseEnd_5106328 := by
    simpa [prefixWord, tailWord_5106328, baseEnd_5106328] using wordTrace_append hprefix tailTrace_5106328
  have hstable : (prefixWord ++ tailWord_5106328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106328).length < 2 ^ (prefixWord ++ tailWord_5106328).sum := by decide
  have hdescent : baseEnd_5106328 < baseStart_5106328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106346 : List Nat := [3, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_5106346 : Nat := 118140960795 + 5106346 * 2 ^ 59
def prefixEnd_5106346 : Nat := 4983230072969 + 3 ^ 40 * 5106346 * 2
def baseEnd_5106346 : Nat := 2622009886163583631491349

theorem tailTrace_5106346 : CollatzResearch.WordTrace tailWord_5106346 prefixEnd_5106346 2622009886163583631491349 := by
  unfold tailWord_5106346
  simp only [CollatzResearch.WordTrace]
  refine ⟨46560934789647002827730723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124162492772392007540615261 46560934789647002827730723)
  ·
    refine ⟨69841402184470504241596085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46560934789647002827730723 69841402184470504241596085)
    ·
      refine ⟨6547631454794109772649633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69841402184470504241596085 6547631454794109772649633)
      ·
        refine ⟨4910723591095582329487225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6547631454794109772649633 4910723591095582329487225)
        ·
          refine ⟨3683042693321686747115419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4910723591095582329487225 3683042693321686747115419)
          ·
            refine ⟨5524564039982530120673129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683042693321686747115419 5524564039982530120673129)
            ·
              refine ⟨4143423029986897590504847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5524564039982530120673129 4143423029986897590504847)
              ·
                refine ⟨6215134544980346385757271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4143423029986897590504847 6215134544980346385757271)
                ·
                  refine ⟨9322701817470519578635907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6215134544980346385757271 9322701817470519578635907)
                  ·
                    refine ⟨13984052726205779367953861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9322701817470519578635907 13984052726205779367953861)
                    ·
                      refine ⟨2622009886163583631491349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13984052726205779367953861 2622009886163583631491349)
                      ·
                        rfl

theorem cell23_5106346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_5106346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106346 prefixEnd_5106346 := by exact prefixLift 5106346
  have htrace : WordTrace (prefixWord ++ tailWord_5106346) baseStart_5106346 baseEnd_5106346 := by
    simpa [prefixWord, tailWord_5106346, baseEnd_5106346] using wordTrace_append hprefix tailTrace_5106346
  have hstable : (prefixWord ++ tailWord_5106346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106346).length < 2 ^ (prefixWord ++ tailWord_5106346).sum := by decide
  have hdescent : baseEnd_5106346 < baseStart_5106346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106355 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 1, 3, 2]
def baseStart_5106355 : Nat := 118140960795 + 5106355 * 2 ^ 59
def prefixEnd_5106355 : Nat := 4983230072969 + 3 ^ 40 * 5106355 * 2
def baseEnd_5106355 : Nat := 2622014507489474096278807

theorem tailTrace_5106355 : CollatzResearch.WordTrace tailWord_5106355 prefixEnd_5106355 2622014507489474096278807 := by
  unfold tailWord_5106355
  simp only [CollatzResearch.WordTrace]
  refine ⟨186244067415555405848000519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124162711610370270565333679 186244067415555405848000519)
  ·
    refine ⟨279366101123333108772000779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186244067415555405848000519 279366101123333108772000779)
    ·
      refine ⟨419049151684999663158001169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279366101123333108772000779 419049151684999663158001169)
      ·
        refine ⟨314286863763749747368500877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 419049151684999663158001169 314286863763749747368500877)
        ·
          refine ⟨117857573911406155263187829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314286863763749747368500877 117857573911406155263187829)
          ·
            refine ⟨11049147554194327055923859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117857573911406155263187829 11049147554194327055923859)
            ·
              refine ⟨16573721331291490583885789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11049147554194327055923859 16573721331291490583885789)
              ·
                refine ⟨6215145499234308968957171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16573721331291490583885789 6215145499234308968957171)
                ·
                  refine ⟨9322718248851463453435757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6215145499234308968957171 9322718248851463453435757)
                  ·
                    refine ⟨3496019343319298795038409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9322718248851463453435757 3496019343319298795038409)
                    ·
                      refine ⟨2622014507489474096278807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496019343319298795038409 2622014507489474096278807)
                      ·
                        rfl

theorem cell23_5106355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 3, 2].length) (baseStart_5106355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106355 prefixEnd_5106355 := by exact prefixLift 5106355
  have htrace : WordTrace (prefixWord ++ tailWord_5106355) baseStart_5106355 baseEnd_5106355 := by
    simpa [prefixWord, tailWord_5106355, baseEnd_5106355] using wordTrace_append hprefix tailTrace_5106355
  have hstable : (prefixWord ++ tailWord_5106355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106355).length < 2 ^ (prefixWord ++ tailWord_5106355).sum := by decide
  have hdescent : baseEnd_5106355 < baseStart_5106355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106389 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5106389 : Nat := 118140960795 + 5106389 * 2 ^ 59
def prefixEnd_5106389 : Nat := 4983230072969 + 3 ^ 40 * 5106389 * 2
def baseEnd_5106389 : Nat := 2622031965831726963253651

theorem tailTrace_5106389 : CollatzResearch.WordTrace tailWord_5106389 prefixEnd_5106389 2622031965831726963253651 := by
  unfold tailWord_5106389
  simp only [CollatzResearch.WordTrace]
  refine ⟨186245307497432229654738221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124163538331621486436492147 186245307497432229654738221)
  ·
    refine ⟨69841990311537086120526833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186245307497432229654738221 69841990311537086120526833)
    ·
      refine ⟨52381492733652814590395125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69841990311537086120526833 52381492733652814590395125)
      ·
        refine ⟨4910764943779951367849543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52381492733652814590395125 4910764943779951367849543)
        ·
          refine ⟨7366147415669927051774315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4910764943779951367849543 7366147415669927051774315)
          ·
            refine ⟨11049221123504890577661473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366147415669927051774315 11049221123504890577661473)
            ·
              refine ⟨8286915842628667933246105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11049221123504890577661473 8286915842628667933246105)
              ·
                refine ⟨6215186881971500949934579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8286915842628667933246105 6215186881971500949934579)
                ·
                  refine ⟨9322780322957251424901869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6215186881971500949934579 9322780322957251424901869)
                  ·
                    refine ⟨3496042621108969284338201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9322780322957251424901869 3496042621108969284338201)
                    ·
                      refine ⟨2622031965831726963253651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496042621108969284338201 2622031965831726963253651)
                      ·
                        rfl

theorem cell23_5106389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5106389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106389 prefixEnd_5106389 := by exact prefixLift 5106389
  have htrace : WordTrace (prefixWord ++ tailWord_5106389) baseStart_5106389 baseEnd_5106389 := by
    simpa [prefixWord, tailWord_5106389, baseEnd_5106389] using wordTrace_append hprefix tailTrace_5106389
  have hstable : (prefixWord ++ tailWord_5106389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106389).length < 2 ^ (prefixWord ++ tailWord_5106389).sum := by decide
  have hdescent : baseEnd_5106389 < baseStart_5106389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106391 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 7]
def baseStart_5106391 : Nat := 118140960795 + 5106391 * 2 ^ 59
def prefixEnd_5106391 : Nat := 4983230072969 + 3 ^ 40 * 5106391 * 2
def baseEnd_5106391 : Nat := 291336999199226217269849

theorem tailTrace_5106391 : CollatzResearch.WordTrace tailWord_5106391 prefixEnd_5106391 291336999199226217269849 := by
  unfold tailWord_5106391
  simp only [CollatzResearch.WordTrace]
  refine ⟨186245380443424983996311027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124163586962283322664207351 186245380443424983996311027)
  ·
    refine ⟨279368070665137475994466541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186245380443424983996311027 279368070665137475994466541)
    ·
      refine ⟨104763026499426553497924953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279368070665137475994466541 104763026499426553497924953)
      ·
        refine ⟨78572269874569915123443715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104763026499426553497924953 78572269874569915123443715)
        ·
          refine ⟨117858404811854872685165573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78572269874569915123443715 117858404811854872685165573)
          ·
            refine ⟨22098450902222788628468545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117858404811854872685165573 22098450902222788628468545)
            ·
              refine ⟨16573838176667091471351409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22098450902222788628468545 16573838176667091471351409)
              ·
                refine ⟨12430378632500318603513557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16573838176667091471351409 12430378632500318603513557)
                ·
                  refine ⟨291336999199226217269849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12430378632500318603513557 291336999199226217269849)
                  ·
                    rfl

theorem cell23_5106391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 7].length) (baseStart_5106391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106391 prefixEnd_5106391 := by exact prefixLift 5106391
  have htrace : WordTrace (prefixWord ++ tailWord_5106391) baseStart_5106391 baseEnd_5106391 := by
    simpa [prefixWord, tailWord_5106391, baseEnd_5106391] using wordTrace_append hprefix tailTrace_5106391
  have hstable : (prefixWord ++ tailWord_5106391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106391).length < 2 ^ (prefixWord ++ tailWord_5106391).sum := by decide
  have hdescent : baseEnd_5106391 < baseStart_5106391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106441 : List Nat := [1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_5106441 : Nat := 118140960795 + 5106441 * 2 ^ 59
def prefixEnd_5106441 : Nat := 4983230072969 + 3 ^ 40 * 5106441 * 2
def baseEnd_5106441 : Nat := 2622058666825760759803411

theorem tailTrace_5106441 : CollatzResearch.WordTrace tailWord_5106441 prefixEnd_5106441 2622058666825760759803411 := by
  unfold tailWord_5106441
  simp only [CollatzResearch.WordTrace]
  refine ⟨186247204093243842535631177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124164802728829228357087451 186247204093243842535631177)
  ·
    refine ⟨139685403069932881901723383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186247204093243842535631177 139685403069932881901723383)
    ·
      refine ⟨209528104604899322852585075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139685403069932881901723383 209528104604899322852585075)
      ·
        refine ⟨314292156907348984278877613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209528104604899322852585075 314292156907348984278877613)
        ·
          refine ⟨117859558840255869104579105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314292156907348984278877613 117859558840255869104579105)
          ·
            refine ⟨88394669130191901828434329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117859558840255869104579105 88394669130191901828434329)
            ·
              refine ⟨66296001847643926371325747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88394669130191901828434329 66296001847643926371325747)
              ·
                refine ⟨99444002771465889556988621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66296001847643926371325747 99444002771465889556988621)
                ·
                  refine ⟨37291501039299708583870733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99444002771465889556988621 37291501039299708583870733)
                  ·
                    refine ⟨13984312889737390718951525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37291501039299708583870733 13984312889737390718951525)
                    ·
                      refine ⟨2622058666825760759803411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13984312889737390718951525 2622058666825760759803411)
                      ·
                        rfl

theorem cell23_5106441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_5106441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106441 prefixEnd_5106441 := by exact prefixLift 5106441
  have htrace : WordTrace (prefixWord ++ tailWord_5106441) baseStart_5106441 baseEnd_5106441 := by
    simpa [prefixWord, tailWord_5106441, baseEnd_5106441] using wordTrace_append hprefix tailTrace_5106441
  have hstable : (prefixWord ++ tailWord_5106441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106441).length < 2 ^ (prefixWord ++ tailWord_5106441).sum := by decide
  have hdescent : baseEnd_5106441 < baseStart_5106441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106455 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 2, 5]
def baseStart_5106455 : Nat := 118140960795 + 5106455 * 2 ^ 59
def prefixEnd_5106455 : Nat := 4983230072969 + 3 ^ 40 * 5106455 * 2
def baseEnd_5106455 : Nat := 874021951851641235009449

theorem tailTrace_5106455 : CollatzResearch.WordTrace tailWord_5106455 prefixEnd_5106455 874021951851641235009449 := by
  unfold tailWord_5106455
  simp only [CollatzResearch.WordTrace]
  refine ⟨186247714715193122926640819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124165143143462081951093879 186247714715193122926640819)
  ·
    refine ⟨279371572072789684389961229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186247714715193122926640819 279371572072789684389961229)
    ·
      refine ⟨104764339527296131646235461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 279371572072789684389961229 104764339527296131646235461)
      ·
        refine ⟨19643313661368024683669149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104764339527296131646235461 19643313661368024683669149)
        ·
          refine ⟨7366242623013009256375931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19643313661368024683669149 7366242623013009256375931)
          ·
            refine ⟨11049363934519513884563897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366242623013009256375931 11049363934519513884563897)
            ·
              refine ⟨8287022950889635413422923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11049363934519513884563897 8287022950889635413422923)
              ·
                refine ⟨12430534426334453120134385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8287022950889635413422923 12430534426334453120134385)
                ·
                  refine ⟨9322900819750839840100789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12430534426334453120134385 9322900819750839840100789)
                  ·
                    refine ⟨874021951851641235009449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9322900819750839840100789 874021951851641235009449)
                    ·
                      rfl

theorem cell23_5106455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 5].length) (baseStart_5106455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106455 prefixEnd_5106455 := by exact prefixLift 5106455
  have htrace : WordTrace (prefixWord ++ tailWord_5106455) baseStart_5106455 baseEnd_5106455 := by
    simpa [prefixWord, tailWord_5106455, baseEnd_5106455] using wordTrace_append hprefix tailTrace_5106455
  have hstable : (prefixWord ++ tailWord_5106455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106455).length < 2 ^ (prefixWord ++ tailWord_5106455).sum := by decide
  have hdescent : baseEnd_5106455 < baseStart_5106455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106501 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 6]
def baseStart_5106501 : Nat := 118140960795 + 5106501 * 2 ^ 59
def prefixEnd_5106501 : Nat := 4983230072969 + 3 ^ 40 * 5106501 * 2
def baseEnd_5106501 : Nat := 2622089475665030525053135

theorem tailTrace_5106501 : CollatzResearch.WordTrace tailWord_5106501 prefixEnd_5106501 2622089475665030525053135 := by
  unfold tailWord_5106501
  simp only [CollatzResearch.WordTrace]
  refine ⟨186249392473026472782815357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124166261648684315188543571 186249392473026472782815357)
  ·
    refine ⟨69843522177384927293555759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186249392473026472782815357 69843522177384927293555759)
    ·
      refine ⟨104765283266077390940333639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69843522177384927293555759 104765283266077390940333639)
      ·
        refine ⟨157147924899116086410500459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104765283266077390940333639 157147924899116086410500459)
        ·
          refine ⟨235721887348674129615750689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157147924899116086410500459 235721887348674129615750689)
          ·
            refine ⟨176791415511505597211813017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235721887348674129615750689 176791415511505597211813017)
            ·
              refine ⟨132593561633629197908859763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176791415511505597211813017 132593561633629197908859763)
              ·
                refine ⟨198890342450443796863289645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132593561633629197908859763 198890342450443796863289645)
                ·
                  refine ⟨74583878418916423823733617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198890342450443796863289645 74583878418916423823733617)
                  ·
                    refine ⟨55937908814187317867800213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 74583878418916423823733617 55937908814187317867800213)
                    ·
                      refine ⟨2622089475665030525053135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55937908814187317867800213 2622089475665030525053135)
                      ·
                        rfl

theorem cell23_5106501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_5106501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106501 prefixEnd_5106501 := by exact prefixLift 5106501
  have htrace : WordTrace (prefixWord ++ tailWord_5106501) baseStart_5106501 baseEnd_5106501 := by
    simpa [prefixWord, tailWord_5106501, baseEnd_5106501] using wordTrace_append hprefix tailTrace_5106501
  have hstable : (prefixWord ++ tailWord_5106501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106501).length < 2 ^ (prefixWord ++ tailWord_5106501).sum := by decide
  have hdescent : baseEnd_5106501 < baseStart_5106501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106509 : List Nat := [1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_5106509 : Nat := 118140960795 + 5106509 * 2 ^ 59
def prefixEnd_5106509 : Nat := 4983230072969 + 3 ^ 40 * 5106509 * 2
def baseEnd_5106509 : Nat := 2622093583510266493753099

theorem tailTrace_5106509 : CollatzResearch.WordTrace tailWord_5106509 prefixEnd_5106509 2622093583510266493753099 := by
  unfold tailWord_5106509
  simp only [CollatzResearch.WordTrace]
  refine ⟨186249684256997490149106581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124166456171331660099404387 186249684256997490149106581)
  ·
    refine ⟨8730453949546757350739371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 186249684256997490149106581 8730453949546757350739371)
    ·
      refine ⟨13095680924320136026109057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8730453949546757350739371 13095680924320136026109057)
      ·
        refine ⟨9821760693240102019581793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13095680924320136026109057 9821760693240102019581793)
        ·
          refine ⟨7366320519930076514686345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9821760693240102019581793 7366320519930076514686345)
          ·
            refine ⟨5524740389947557386014759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7366320519930076514686345 5524740389947557386014759)
            ·
              refine ⟨8287110584921336079022139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5524740389947557386014759 8287110584921336079022139)
              ·
                refine ⟨12430665877382004118533209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8287110584921336079022139 12430665877382004118533209)
                ·
                  refine ⟨9322999408036503088899907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12430665877382004118533209 9322999408036503088899907)
                  ·
                    refine ⟨13984499112054754633349861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9322999408036503088899907 13984499112054754633349861)
                    ·
                      refine ⟨2622093583510266493753099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13984499112054754633349861 2622093583510266493753099)
                      ·
                        rfl

theorem cell23_5106509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_5106509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106509 prefixEnd_5106509 := by exact prefixLift 5106509
  have htrace : WordTrace (prefixWord ++ tailWord_5106509) baseStart_5106509 baseEnd_5106509 := by
    simpa [prefixWord, tailWord_5106509, baseEnd_5106509] using wordTrace_append hprefix tailTrace_5106509
  have hstable : (prefixWord ++ tailWord_5106509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106509).length < 2 ^ (prefixWord ++ tailWord_5106509).sum := by decide
  have hdescent : baseEnd_5106509 < baseStart_5106509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106565 : List Nat := [1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 4]
def baseStart_5106565 : Nat := 118140960795 + 5106565 * 2 ^ 59
def prefixEnd_5106565 : Nat := 4983230072969 + 3 ^ 40 * 5106565 * 2
def baseEnd_5106565 : Nat := 2622122338426918274652841

theorem tailTrace_5106565 : CollatzResearch.WordTrace tailWord_5106565 prefixEnd_5106565 2622122338426918274652841 := by
  unfold tailWord_5106565
  simp only [CollatzResearch.WordTrace]
  refine ⟨186251726744794611713145149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124167817829863074475430099 186251726744794611713145149)
  ·
    refine ⟨69844397529297979392429431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186251726744794611713145149 69844397529297979392429431)
    ·
      refine ⟨104766596293946969088644147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69844397529297979392429431 104766596293946969088644147)
      ·
        refine ⟨157149894440920453632966221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104766596293946969088644147 157149894440920453632966221)
        ·
          refine ⟨58931210415345170112362333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 157149894440920453632966221 58931210415345170112362333)
          ·
            refine ⟨22099203905754438792135875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58931210415345170112362333 22099203905754438792135875)
            ·
              refine ⟨33148805858631658188203813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22099203905754438792135875 33148805858631658188203813)
              ·
                refine ⟨6215401098493435910288215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33148805858631658188203813 6215401098493435910288215)
                ·
                  refine ⟨9323101647740153865432323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6215401098493435910288215 9323101647740153865432323)
                  ·
                    refine ⟨13984652471610230798148485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9323101647740153865432323 13984652471610230798148485)
                    ·
                      refine ⟨2622122338426918274652841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13984652471610230798148485 2622122338426918274652841)
                      ·
                        rfl

theorem cell23_5106565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 4].length) (baseStart_5106565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106565 prefixEnd_5106565 := by exact prefixLift 5106565
  have htrace : WordTrace (prefixWord ++ tailWord_5106565) baseStart_5106565 baseEnd_5106565 := by
    simpa [prefixWord, tailWord_5106565, baseEnd_5106565] using wordTrace_append hprefix tailTrace_5106565
  have hstable : (prefixWord ++ tailWord_5106565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106565).length < 2 ^ (prefixWord ++ tailWord_5106565).sum := by decide
  have hdescent : baseEnd_5106565 < baseStart_5106565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106612 : List Nat := [2, 5, 2, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_5106612 : Nat := 118140960795 + 5106612 * 2 ^ 59
def prefixEnd_5106612 : Nat := 4983230072969 + 3 ^ 40 * 5106612 * 2
def baseEnd_5106612 : Nat := 2622146472017679590765125

theorem tailTrace_5106612 : CollatzResearch.WordTrace tailWord_5106612 prefixEnd_5106612 2622146472017679590765125 := by
  unfold tailWord_5106612
  simp only [CollatzResearch.WordTrace]
  refine ⟨93126720487812169370053045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124168960650416225826737393 93126720487812169370053045)
  ·
    refine ⟨8730630045732390878442473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93126720487812169370053045 8730630045732390878442473)
    ·
      refine ⟨6547972534299293158831855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8730630045732390878442473 6547972534299293158831855)
      ·
        refine ⟨9821958801448939738247783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6547972534299293158831855 9821958801448939738247783)
        ·
          refine ⟨14732938202173409607371675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9821958801448939738247783 14732938202173409607371675)
          ·
            refine ⟨22099407303260114411057513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14732938202173409607371675 22099407303260114411057513)
            ·
              refine ⟨16574555477445085808293135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22099407303260114411057513 16574555477445085808293135)
              ·
                refine ⟨24861833216167628712439703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16574555477445085808293135 24861833216167628712439703)
                ·
                  refine ⟨37292749824251443068659555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24861833216167628712439703 37292749824251443068659555)
                  ·
                    refine ⟨55939124736377164602989333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37292749824251443068659555 55939124736377164602989333)
                    ·
                      refine ⟨2622146472017679590765125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55939124736377164602989333 2622146472017679590765125)
                      ·
                        rfl

theorem cell23_5106612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_5106612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106612 prefixEnd_5106612 := by exact prefixLift 5106612
  have htrace : WordTrace (prefixWord ++ tailWord_5106612) baseStart_5106612 baseEnd_5106612 := by
    simpa [prefixWord, tailWord_5106612, baseEnd_5106612] using wordTrace_append hprefix tailTrace_5106612
  have hstable : (prefixWord ++ tailWord_5106612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106612).length < 2 ^ (prefixWord ++ tailWord_5106612).sum := by decide
  have hdescent : baseEnd_5106612 < baseStart_5106612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106630 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5106630 : Nat := 118140960795 + 5106630 * 2 ^ 59
def prefixEnd_5106630 : Nat := 4983230072969 + 3 ^ 40 * 5106630 * 2
def baseEnd_5106630 : Nat := 874051904889820173446681

theorem tailTrace_5106630 : CollatzResearch.WordTrace tailWord_5106630 prefixEnd_5106630 874051904889820173446681 := by
  unfold tailWord_5106630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5820440546548722744195667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 124169398326372751876174229 5820440546548722744195667)
  ·
    refine ⟨8730660819823084116293501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5820440546548722744195667 8730660819823084116293501)
    ·
      refine ⟨3273997807433656543610063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8730660819823084116293501 3273997807433656543610063)
      ·
        refine ⟨4910996711150484815415095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3273997807433656543610063 4910996711150484815415095)
        ·
          refine ⟨7366495066725727223122643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4910996711150484815415095 7366495066725727223122643)
          ·
            refine ⟨11049742600088590834683965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366495066725727223122643 11049742600088590834683965)
            ·
              refine ⟨4143653475033221563006487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11049742600088590834683965 4143653475033221563006487)
              ·
                refine ⟨6215480212549832344509731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4143653475033221563006487 6215480212549832344509731)
                ·
                  refine ⟨9323220318824748516764597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6215480212549832344509731 9323220318824748516764597)
                  ·
                    refine ⟨874051904889820173446681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9323220318824748516764597 874051904889820173446681)
                    ·
                      rfl

theorem cell23_5106630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5106630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106630 prefixEnd_5106630 := by exact prefixLift 5106630
  have htrace : WordTrace (prefixWord ++ tailWord_5106630) baseStart_5106630 baseEnd_5106630 := by
    simpa [prefixWord, tailWord_5106630, baseEnd_5106630] using wordTrace_append hprefix tailTrace_5106630
  have hstable : (prefixWord ++ tailWord_5106630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106630).length < 2 ^ (prefixWord ++ tailWord_5106630).sum := by decide
  have hdescent : baseEnd_5106630 < baseStart_5106630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106632 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_5106632 : Nat := 118140960795 + 5106632 * 2 ^ 59
def prefixEnd_5106632 : Nat := 4983230072969 + 3 ^ 40 * 5106632 * 2
def baseEnd_5106632 : Nat := 2622156741630769512515033

theorem tailTrace_5106632 : CollatzResearch.WordTrace tailWord_5106632 prefixEnd_5106632 2622156741630769512515033 := by
  unfold tailWord_5106632
  simp only [CollatzResearch.WordTrace]
  refine ⟨93127085217775941077917075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124169446957034588103889433 93127085217775941077917075)
  ·
    refine ⟨139690627826663911616875613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93127085217775941077917075 139690627826663911616875613)
    ·
      refine ⟨52383985434998966856328355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139690627826663911616875613 52383985434998966856328355)
      ·
        refine ⟨78575978152498450284492533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52383985434998966856328355 78575978152498450284492533)
        ·
          refine ⟨7366497951796729714171175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78575978152498450284492533 7366497951796729714171175)
          ·
            refine ⟨11049746927695094571256763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366497951796729714171175 11049746927695094571256763)
            ·
              refine ⟨16574620391542641856885145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11049746927695094571256763 16574620391542641856885145)
              ·
                refine ⟨12430965293656981392663859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16574620391542641856885145 12430965293656981392663859)
                ·
                  refine ⟨18646447940485472088995789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12430965293656981392663859 18646447940485472088995789)
                  ·
                    refine ⟨6992417977682052033373421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18646447940485472088995789 6992417977682052033373421)
                    ·
                      refine ⟨2622156741630769512515033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6992417977682052033373421 2622156741630769512515033)
                      ·
                        rfl

theorem cell23_5106632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_5106632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106632 prefixEnd_5106632 := by exact prefixLift 5106632
  have htrace : WordTrace (prefixWord ++ tailWord_5106632) baseStart_5106632 baseEnd_5106632 := by
    simpa [prefixWord, tailWord_5106632, baseEnd_5106632] using wordTrace_append hprefix tailTrace_5106632
  have hstable : (prefixWord ++ tailWord_5106632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106632).length < 2 ^ (prefixWord ++ tailWord_5106632).sum := by decide
  have hdescent : baseEnd_5106632 < baseStart_5106632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106649 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 2, 1, 3]
def baseStart_5106649 : Nat := 118140960795 + 5106649 * 2 ^ 59
def prefixEnd_5106649 : Nat := 4983230072969 + 3 ^ 40 * 5106649 * 2
def baseEnd_5106649 : Nat := 2622165470801895946002455

theorem tailTrace_5106649 : CollatzResearch.WordTrace tailWord_5106649 prefixEnd_5106649 2622165470801895946002455 := by
  unfold tailWord_5106649
  simp only [CollatzResearch.WordTrace]
  refine ⟨186254790476490294059203001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124169860317660196039468667 186254790476490294059203001)
  ·
    refine ⟨139691092857367720544402251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186254790476490294059203001 139691092857367720544402251)
    ·
      refine ⟨209536639286051580816603377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139691092857367720544402251 209536639286051580816603377)
      ·
        refine ⟨157152479464538685612452533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209536639286051580816603377 157152479464538685612452533)
        ·
          refine ⟨14733044949800501776167425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 157152479464538685612452533 14733044949800501776167425)
          ·
            refine ⟨11049783712350376332125569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14733044949800501776167425 11049783712350376332125569)
            ·
              refine ⟨8287337784262782249094177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11049783712350376332125569 8287337784262782249094177)
              ·
                refine ⟨6215503338197086686820633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8287337784262782249094177 6215503338197086686820633)
                ·
                  refine ⟨4661627503647815015115475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6215503338197086686820633 4661627503647815015115475)
                  ·
                    refine ⟨6992441255471722522673213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4661627503647815015115475 6992441255471722522673213)
                    ·
                      refine ⟨2622165470801895946002455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6992441255471722522673213 2622165470801895946002455)
                      ·
                        rfl

theorem cell23_5106649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_5106649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106649 prefixEnd_5106649 := by exact prefixLift 5106649
  have htrace : WordTrace (prefixWord ++ tailWord_5106649) baseStart_5106649 baseEnd_5106649 := by
    simpa [prefixWord, tailWord_5106649, baseEnd_5106649] using wordTrace_append hprefix tailTrace_5106649
  have hstable : (prefixWord ++ tailWord_5106649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106649).length < 2 ^ (prefixWord ++ tailWord_5106649).sum := by decide
  have hdescent : baseEnd_5106649 < baseStart_5106649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106672 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 6, 2, 2]
def baseStart_5106672 : Nat := 118140960795 + 5106672 * 2 ^ 59
def prefixEnd_5106672 : Nat := 4983230072969 + 3 ^ 40 * 5106672 * 2
def baseEnd_5106672 : Nat := 2622177280856949356014849

theorem tailTrace_5106672 : CollatzResearch.WordTrace tailWord_5106672 prefixEnd_5106672 2622177280856949356014849 := by
  unfold tailWord_5106672
  simp only [CollatzResearch.WordTrace]
  refine ⟨93127814677703484493645135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124170419570271312658193513 93127814677703484493645135)
  ·
    refine ⟨139691722016555226740467703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93127814677703484493645135 139691722016555226740467703)
    ·
      refine ⟨209537583024832840110701555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139691722016555226740467703 209537583024832840110701555)
      ·
        refine ⟨314306374537249260166052333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209537583024832840110701555 314306374537249260166052333)
        ·
          refine ⟨117864890451468472562269625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 314306374537249260166052333 117864890451468472562269625)
          ·
            refine ⟨88398667838601354421702219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117864890451468472562269625 88398667838601354421702219)
            ·
              refine ⟨132598001757902031632553329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88398667838601354421702219 132598001757902031632553329)
              ·
                refine ⟨99448501318426523724414997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132598001757902031632553329 99448501318426523724414997)
                ·
                  refine ⟨4661648499301243299581953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99448501318426523724414997 4661648499301243299581953)
                  ·
                    refine ⟨3496236374475932474686465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4661648499301243299581953 3496236374475932474686465)
                    ·
                      refine ⟨2622177280856949356014849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496236374475932474686465 2622177280856949356014849)
                      ·
                        rfl

theorem cell23_5106672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6, 2, 2].length) (baseStart_5106672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106672 prefixEnd_5106672 := by exact prefixLift 5106672
  have htrace : WordTrace (prefixWord ++ tailWord_5106672) baseStart_5106672 baseEnd_5106672 := by
    simpa [prefixWord, tailWord_5106672, baseEnd_5106672] using wordTrace_append hprefix tailTrace_5106672
  have hstable : (prefixWord ++ tailWord_5106672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106672).length < 2 ^ (prefixWord ++ tailWord_5106672).sum := by decide
  have hdescent : baseEnd_5106672 < baseStart_5106672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106712 : List Nat := [2, 1, 2, 3, 2, 2, 2, 4, 5]
def baseStart_5106712 : Nat := 118140960795 + 5106712 * 2 ^ 59
def prefixEnd_5106712 : Nat := 4983230072969 + 3 ^ 40 * 5106712 * 2
def baseEnd_5106712 : Nat := 291355313342569911057185

theorem tailTrace_5106712 : CollatzResearch.WordTrace tailWord_5106712 prefixEnd_5106712 291355313342569911057185 := by
  unfold tailWord_5106712
  simp only [CollatzResearch.WordTrace]
  refine ⟨93128544137631027909373195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124171392183508037212497593 93128544137631027909373195)
  ·
    refine ⟨139692816206446541864059793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93128544137631027909373195 139692816206446541864059793)
    ·
      refine ⟨104769612154834906398044845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139692816206446541864059793 104769612154834906398044845)
      ·
        refine ⟨39288604558063089899266817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104769612154834906398044845 39288604558063089899266817)
        ·
          refine ⟨29466453418547317424450113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39288604558063089899266817 29466453418547317424450113)
          ·
            refine ⟨22099840063910488068337585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29466453418547317424450113 22099840063910488068337585)
            ·
              refine ⟨16574880047932866051253189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22099840063910488068337585 16574880047932866051253189)
              ·
                refine ⟨3107790008987412384609973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16574880047932866051253189 3107790008987412384609973)
                ·
                  refine ⟨291355313342569911057185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3107790008987412384609973 291355313342569911057185)
                  ·
                    rfl

theorem cell23_5106712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 4, 5].length) (baseStart_5106712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106712 prefixEnd_5106712 := by exact prefixLift 5106712
  have htrace : WordTrace (prefixWord ++ tailWord_5106712) baseStart_5106712 baseEnd_5106712 := by
    simpa [prefixWord, tailWord_5106712, baseEnd_5106712] using wordTrace_append hprefix tailTrace_5106712
  have hstable : (prefixWord ++ tailWord_5106712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106712).length < 2 ^ (prefixWord ++ tailWord_5106712).sum := by decide
  have hdescent : baseEnd_5106712 < baseStart_5106712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106722 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_5106722 : Nat := 118140960795 + 5106722 * 2 ^ 59
def prefixEnd_5106722 : Nat := 4983230072969 + 3 ^ 40 * 5106722 * 2
def baseEnd_5106722 : Nat := 2622202954889674160389619

theorem tailTrace_5106722 : CollatzResearch.WordTrace tailWord_5106722 prefixEnd_5106722 2622202954889674160389619 := by
  unfold tailWord_5106722
  simp only [CollatzResearch.WordTrace]
  refine ⟨46564363251306456881652605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124171635336817218351073613 46564363251306456881652605)
  ·
    refine ⟨17461636219239921330619727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46564363251306456881652605 17461636219239921330619727)
    ·
      refine ⟨26192454328859881995929591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17461636219239921330619727 26192454328859881995929591)
      ·
        refine ⟨39288681493289822993894387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26192454328859881995929591 39288681493289822993894387)
        ·
          refine ⟨58933022239934734490841581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39288681493289822993894387 58933022239934734490841581)
          ·
            refine ⟨22099883339975525434065593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58933022239934734490841581 22099883339975525434065593)
            ·
              refine ⟨16574912504981644075549195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22099883339975525434065593 16574912504981644075549195)
              ·
                refine ⟨24862368757472466113323793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16574912504981644075549195 24862368757472466113323793)
                ·
                  refine ⟨18646776568104349584992845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24862368757472466113323793 18646776568104349584992845)
                  ·
                    refine ⟨6992541213039131094372317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18646776568104349584992845 6992541213039131094372317)
                    ·
                      refine ⟨2622202954889674160389619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6992541213039131094372317 2622202954889674160389619)
                      ·
                        rfl

theorem cell23_5106722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_5106722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106722 prefixEnd_5106722 := by exact prefixLift 5106722
  have htrace : WordTrace (prefixWord ++ tailWord_5106722) baseStart_5106722 baseEnd_5106722 := by
    simpa [prefixWord, tailWord_5106722, baseEnd_5106722] using wordTrace_append hprefix tailTrace_5106722
  have hstable : (prefixWord ++ tailWord_5106722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106722).length < 2 ^ (prefixWord ++ tailWord_5106722).sum := by decide
  have hdescent : baseEnd_5106722 < baseStart_5106722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106742 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_5106742 : Nat := 118140960795 + 5106742 * 2 ^ 59
def prefixEnd_5106742 : Nat := 4983230072969 + 3 ^ 40 * 5106742 * 2
def baseEnd_5106742 : Nat := 874071074834254694046509

theorem tailTrace_5106742 : CollatzResearch.WordTrace tailWord_5106742 prefixEnd_5106742 874071074834254694046509 := by
  unfold tailWord_5106742
  simp only [CollatzResearch.WordTrace]
  refine ⟨11641136404072085683896155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124172121643435580628225653 11641136404072085683896155)
  ·
    refine ⟨17461704606108128525844233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11641136404072085683896155 17461704606108128525844233)
    ·
      refine ⟨13096278454581096394383175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17461704606108128525844233 13096278454581096394383175)
      ·
        refine ⟨19644417681871644591574763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13096278454581096394383175 19644417681871644591574763)
        ·
          refine ⟨29466626522807466887362145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19644417681871644591574763 29466626522807466887362145)
          ·
            refine ⟨22099969892105600165521609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29466626522807466887362145 22099969892105600165521609)
            ·
              refine ⟨16574977419079200124141207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22099969892105600165521609 16574977419079200124141207)
              ·
                refine ⟨24862466128618800186211811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16574977419079200124141207 24862466128618800186211811)
                ·
                  refine ⟨37293699192928200279317717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24862466128618800186211811 37293699192928200279317717)
                  ·
                    refine ⟨874071074834254694046509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37293699192928200279317717 874071074834254694046509)
                    ·
                      rfl

theorem cell23_5106742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_5106742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106742 prefixEnd_5106742 := by exact prefixLift 5106742
  have htrace : WordTrace (prefixWord ++ tailWord_5106742) baseStart_5106742 baseEnd_5106742 := by
    simpa [prefixWord, tailWord_5106742, baseEnd_5106742] using wordTrace_append hprefix tailTrace_5106742
  have hstable : (prefixWord ++ tailWord_5106742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106742).length < 2 ^ (prefixWord ++ tailWord_5106742).sum := by decide
  have hdescent : baseEnd_5106742 < baseStart_5106742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106762 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2]
def baseStart_5106762 : Nat := 118140960795 + 5106762 * 2 ^ 59
def prefixEnd_5106762 : Nat := 4983230072969 + 3 ^ 40 * 5106762 * 2
def baseEnd_5106762 : Nat := 2622223494115854003889435

theorem tailTrace_5106762 : CollatzResearch.WordTrace tailWord_5106762 prefixEnd_5106762 2622223494115854003889435 := by
  unfold tailWord_5106762
  simp only [CollatzResearch.WordTrace]
  refine ⟨46564727981270228589516635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124172607950053942905377693 46564727981270228589516635)
  ·
    refine ⟨69847091971905342884274953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46564727981270228589516635 69847091971905342884274953)
    ·
      refine ⟨52385318978929007163206215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69847091971905342884274953 52385318978929007163206215)
      ·
        refine ⟨78577978468393510744809323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52385318978929007163206215 78577978468393510744809323)
        ·
          refine ⟨117866967702590266117213985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78577978468393510744809323 117866967702590266117213985)
          ·
            refine ⟨88400225776942699587910489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117866967702590266117213985 88400225776942699587910489)
            ·
              refine ⟨66300169332707024690932867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88400225776942699587910489 66300169332707024690932867)
              ·
                refine ⟨99450253999060537036399301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66300169332707024690932867 99450253999060537036399301)
                ·
                  refine ⟨18646922624823850694324869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99450253999060537036399301 18646922624823850694324869)
                  ·
                    refine ⟨3496297992154472005185913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18646922624823850694324869 3496297992154472005185913)
                    ·
                      refine ⟨2622223494115854003889435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496297992154472005185913 2622223494115854003889435)
                      ·
                        rfl

theorem cell23_5106762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_5106762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106762 prefixEnd_5106762 := by exact prefixLift 5106762
  have htrace : WordTrace (prefixWord ++ tailWord_5106762) baseStart_5106762 baseEnd_5106762 := by
    simpa [prefixWord, tailWord_5106762, baseEnd_5106762] using wordTrace_append hprefix tailTrace_5106762
  have hstable : (prefixWord ++ tailWord_5106762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106762).length < 2 ^ (prefixWord ++ tailWord_5106762).sum := by decide
  have hdescent : baseEnd_5106762 < baseStart_5106762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106774 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_5106774 : Nat := 118140960795 + 5106774 * 2 ^ 59
def prefixEnd_5106774 : Nat := 4983230072969 + 3 ^ 40 * 5106774 * 2
def baseEnd_5106774 : Nat := 2622229655883707956939381

theorem tailTrace_5106774 : CollatzResearch.WordTrace tailWord_5106774 prefixEnd_5106774 2622229655883707956939381 := by
  unfold tailWord_5106774
  simp only [CollatzResearch.WordTrace]
  refine ⟨11641209350064840025468961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124172899734024960271668917 11641209350064840025468961)
  ·
    refine ⟨8730907012548630019101721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11641209350064840025468961 8730907012548630019101721)
    ·
      refine ⟨6548180259411472514326291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8730907012548630019101721 6548180259411472514326291)
      ·
        refine ⟨9822270389117208771489437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6548180259411472514326291 9822270389117208771489437)
        ·
          refine ⟨3683351395918953289308539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9822270389117208771489437 3683351395918953289308539)
          ·
            refine ⟨5525027093878429933962809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683351395918953289308539 5525027093878429933962809)
            ·
              refine ⟨4143770320408822450472107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5525027093878429933962809 4143770320408822450472107)
              ·
                refine ⟨6215655480613233675708161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4143770320408822450472107 6215655480613233675708161)
                ·
                  refine ⟨4661741610459925256781121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6215655480613233675708161 4661741610459925256781121)
                  ·
                    refine ⟨3496306207844943942585841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4661741610459925256781121 3496306207844943942585841)
                    ·
                      refine ⟨2622229655883707956939381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496306207844943942585841 2622229655883707956939381)
                      ·
                        rfl

theorem cell23_5106774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_5106774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106774 prefixEnd_5106774 := by exact prefixLift 5106774
  have htrace : WordTrace (prefixWord ++ tailWord_5106774) baseStart_5106774 baseEnd_5106774 := by
    simpa [prefixWord, tailWord_5106774, baseEnd_5106774] using wordTrace_append hprefix tailTrace_5106774
  have hstable : (prefixWord ++ tailWord_5106774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106774).length < 2 ^ (prefixWord ++ tailWord_5106774).sum := by decide
  have hdescent : baseEnd_5106774 < baseStart_5106774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106806 : List Nat := [5, 1, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_5106806 : Nat := 118140960795 + 5106806 * 2 ^ 59
def prefixEnd_5106806 : Nat := 4983230072969 + 3 ^ 40 * 5106806 * 2
def baseEnd_5106806 : Nat := 874082029088217277246411

theorem tailTrace_5106806 : CollatzResearch.WordTrace tailWord_5106806 prefixEnd_5106806 874082029088217277246411 := by
  unfold tailWord_5106806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11641282296057594367041767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124173677824614339915112181 11641282296057594367041767)
  ·
    refine ⟨17461923444086391550562651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11641282296057594367041767 17461923444086391550562651)
    ·
      refine ⟨26192885166129587325843977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17461923444086391550562651 26192885166129587325843977)
      ·
        refine ⟨19644663874597190494382983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26192885166129587325843977 19644663874597190494382983)
        ·
          refine ⟨29466995811895785741574475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19644663874597190494382983 29466995811895785741574475)
          ·
            refine ⟨44200493717843678612361713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29466995811895785741574475 44200493717843678612361713)
            ·
              refine ⟨33150370288382758959271285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44200493717843678612361713 33150370288382758959271285)
              ·
                refine ⟨3107847214535883652431683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33150370288382758959271285 3107847214535883652431683)
                ·
                  refine ⟨4661770821803825478647525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3107847214535883652431683 4661770821803825478647525)
                  ·
                    refine ⟨874082029088217277246411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4661770821803825478647525 874082029088217277246411)
                    ·
                      rfl

theorem cell23_5106806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_5106806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106806 prefixEnd_5106806 := by exact prefixLift 5106806
  have htrace : WordTrace (prefixWord ++ tailWord_5106806) baseStart_5106806 baseEnd_5106806 := by
    simpa [prefixWord, tailWord_5106806, baseEnd_5106806] using wordTrace_append hprefix tailTrace_5106806
  have hstable : (prefixWord ++ tailWord_5106806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106806).length < 2 ^ (prefixWord ++ tailWord_5106806).sum := by decide
  have hdescent : baseEnd_5106806 < baseStart_5106806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106846 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_5106846 : Nat := 118140960795 + 5106846 * 2 ^ 59
def prefixEnd_5106846 : Nat := 4983230072969 + 3 ^ 40 * 5106846 * 2
def baseEnd_5106846 : Nat := 2622266626490831675239049

theorem tailTrace_5106846 : CollatzResearch.WordTrace tailWord_5106846 prefixEnd_5106846 2622266626490831675239049 := by
  unfold tailWord_5106846
  simp only [CollatzResearch.WordTrace]
  refine ⟨23282746957097074588015549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124174650437851064469416261 23282746957097074588015549)
  ·
    refine ⟨8731030108911402970505831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23282746957097074588015549 8731030108911402970505831)
    ·
      refine ⟨13096545163367104455758747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8731030108911402970505831 13096545163367104455758747)
      ·
        refine ⟨19644817745050656683638121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13096545163367104455758747 19644817745050656683638121)
        ·
          refine ⟨14733613308787992512728591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19644817745050656683638121 14733613308787992512728591)
          ·
            refine ⟨22100419963181988769092887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14733613308787992512728591 22100419963181988769092887)
            ·
              refine ⟨33150629944772983153639331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22100419963181988769092887 33150629944772983153639331)
              ·
                refine ⟨49725944917159474730458997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33150629944772983153639331 49725944917159474730458997)
                ·
                  refine ⟨4661807335983700755980531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49725944917159474730458997 4661807335983700755980531)
                  ·
                    refine ⟨6992711003975551133970797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4661807335983700755980531 6992711003975551133970797)
                    ·
                      refine ⟨2622266626490831675239049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6992711003975551133970797 2622266626490831675239049)
                      ·
                        rfl

theorem cell23_5106846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_5106846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106846 prefixEnd_5106846 := by exact prefixLift 5106846
  have htrace : WordTrace (prefixWord ++ tailWord_5106846) baseStart_5106846 baseEnd_5106846 := by
    simpa [prefixWord, tailWord_5106846, baseEnd_5106846] using wordTrace_append hprefix tailTrace_5106846
  have hstable : (prefixWord ++ tailWord_5106846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106846).length < 2 ^ (prefixWord ++ tailWord_5106846).sum := by decide
  have hdescent : baseEnd_5106846 < baseStart_5106846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106866 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_5106866 : Nat := 118140960795 + 5106866 * 2 ^ 59
def prefixEnd_5106866 : Nat := 4983230072969 + 3 ^ 40 * 5106866 * 2
def baseEnd_5106866 : Nat := 874092298701307198996319

theorem tailTrace_5106866 : CollatzResearch.WordTrace tailWord_5106866 prefixEnd_5106866 874092298701307198996319 := by
  unfold tailWord_5106866
  simp only [CollatzResearch.WordTrace]
  refine ⟨46565676279176035029963113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124175136744469426746568301 46565676279176035029963113)
  ·
    refine ⟨34924257209382026272472335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46565676279176035029963113 34924257209382026272472335)
    ·
      refine ⟨52386385814073039408708503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34924257209382026272472335 52386385814073039408708503)
      ·
        refine ⟨78579578721109559113062755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52386385814073039408708503 78579578721109559113062755)
        ·
          refine ⟨117869368081664338669594133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78579578721109559113062755 117869368081664338669594133)
          ·
            refine ⟨5525126628828015875137225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117869368081664338669594133 5525126628828015875137225)
            ·
              refine ⟨4143844971621011906352919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5525126628828015875137225 4143844971621011906352919)
              ·
                refine ⟨6215767457431517859529379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4143844971621011906352919 6215767457431517859529379)
                ·
                  refine ⟨9323651186147276789294069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6215767457431517859529379 9323651186147276789294069)
                  ·
                    refine ⟨874092298701307198996319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9323651186147276789294069 874092298701307198996319)
                    ·
                      rfl

theorem cell23_5106866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_5106866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106866 prefixEnd_5106866 := by exact prefixLift 5106866
  have htrace : WordTrace (prefixWord ++ tailWord_5106866) baseStart_5106866 baseEnd_5106866 := by
    simpa [prefixWord, tailWord_5106866, baseEnd_5106866] using wordTrace_append hprefix tailTrace_5106866
  have hstable : (prefixWord ++ tailWord_5106866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106866).length < 2 ^ (prefixWord ++ tailWord_5106866).sum := by decide
  have hdescent : baseEnd_5106866 < baseStart_5106866 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106870 : List Nat := [5, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_5106870 : Nat := 118140960795 + 5106870 * 2 ^ 59
def prefixEnd_5106870 : Nat := 4983230072969 + 3 ^ 40 * 5106870 * 2
def baseEnd_5106870 : Nat := 291364327780726620148771

theorem tailTrace_5106870 : CollatzResearch.WordTrace tailWord_5106870 prefixEnd_5106870 291364327780726620148771 := by
  unfold tailWord_5106870
  simp only [CollatzResearch.WordTrace]
  refine ⟨11641428188043103050187379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124175234005793099201998709 11641428188043103050187379)
  ·
    refine ⟨17462142282064654575281069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11641428188043103050187379 17462142282064654575281069)
    ·
      refine ⟨6548303355774245465730401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17462142282064654575281069 6548303355774245465730401)
      ·
        refine ⟨4911227516830684099297801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6548303355774245465730401 4911227516830684099297801)
        ·
          refine ⟨3683420637623013074473351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4911227516830684099297801 3683420637623013074473351)
          ·
            refine ⟨5525130956434519611710027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3683420637623013074473351 5525130956434519611710027)
            ·
              refine ⟨8287696434651779417565041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5525130956434519611710027 8287696434651779417565041)
              ·
                refine ⟨6215772325988834563173781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8287696434651779417565041 6215772325988834563173781)
                ·
                  refine ⟨291364327780726620148771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6215772325988834563173781 291364327780726620148771)
                  ·
                    rfl

theorem cell23_5106870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_5106870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106870 prefixEnd_5106870 := by exact prefixLift 5106870
  have htrace : WordTrace (prefixWord ++ tailWord_5106870) baseStart_5106870 baseEnd_5106870 := by
    simpa [prefixWord, tailWord_5106870, baseEnd_5106870] using wordTrace_append hprefix tailTrace_5106870
  have hstable : (prefixWord ++ tailWord_5106870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106870).length < 2 ^ (prefixWord ++ tailWord_5106870).sum := by decide
  have hdescent : baseEnd_5106870 < baseStart_5106870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106872 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 5, 2, 3]
def baseStart_5106872 : Nat := 118140960795 + 5106872 * 2 ^ 59
def prefixEnd_5106872 : Nat := 4983230072969 + 3 ^ 40 * 5106872 * 2
def baseEnd_5106872 : Nat := 2622279976987848573513929

theorem tailTrace_5106872 : CollatzResearch.WordTrace tailWord_5106872 prefixEnd_5106872 2622279976987848573513929 := by
  unfold tailWord_5106872
  simp only [CollatzResearch.WordTrace]
  refine ⟨93131461977341201572285435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124175282636454935429713913 93131461977341201572285435)
  ·
    refine ⟨139697192966011802358428153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93131461977341201572285435 139697192966011802358428153)
    ·
      refine ⟨104772894724508851768821115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139697192966011802358428153 104772894724508851768821115)
      ·
        refine ⟨157159342086763277653231673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104772894724508851768821115 157159342086763277653231673)
        ·
          refine ⟨117869506565072458239923755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157159342086763277653231673 117869506565072458239923755)
          ·
            refine ⟨176804259847608687359885633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117869506565072458239923755 176804259847608687359885633)
            ·
              refine ⟨132603194885706515519914225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176804259847608687359885633 132603194885706515519914225)
              ·
                refine ⟨99452396164279886639935669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132603194885706515519914225 99452396164279886639935669)
                ·
                  refine ⟨9323662140401239372493969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99452396164279886639935669 9323662140401239372493969)
                  ·
                    refine ⟨6992746605300929529370477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9323662140401239372493969 6992746605300929529370477)
                    ·
                      refine ⟨2622279976987848573513929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6992746605300929529370477 2622279976987848573513929)
                      ·
                        rfl

theorem cell23_5106872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_5106872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106872 prefixEnd_5106872 := by exact prefixLift 5106872
  have htrace : WordTrace (prefixWord ++ tailWord_5106872) baseStart_5106872 baseEnd_5106872 := by
    simpa [prefixWord, tailWord_5106872, baseEnd_5106872] using wordTrace_append hprefix tailTrace_5106872
  have hstable : (prefixWord ++ tailWord_5106872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106872).length < 2 ^ (prefixWord ++ tailWord_5106872).sum := by decide
  have hdescent : baseEnd_5106872 < baseStart_5106872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106879 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 2, 4]
def baseStart_5106879 : Nat := 118140960795 + 5106879 * 2 ^ 59
def prefixEnd_5106879 : Nat := 4983230072969 + 3 ^ 40 * 5106879 * 2
def baseEnd_5106879 : Nat := 874094523784143348708799

theorem tailTrace_5106879 : CollatzResearch.WordTrace tailWord_5106879 prefixEnd_5106879 874094523784143348708799 := by
  unfold tailWord_5106879
  simp only [CollatzResearch.WordTrace]
  refine ⟨186263179265657043340075691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124175452843771362226717127 186263179265657043340075691)
  ·
    refine ⟨279394768898485565010113537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186263179265657043340075691 279394768898485565010113537)
    ·
      refine ⟨209546076673864173757585153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279394768898485565010113537 209546076673864173757585153)
      ·
        refine ⟨157159557505398130318188865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209546076673864173757585153 157159557505398130318188865)
        ·
          refine ⟨117869668129048597738641649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157159557505398130318188865 117869668129048597738641649)
          ·
            refine ⟨88402251096786448303981237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117869668129048597738641649 88402251096786448303981237)
            ·
              refine ⟨8287711040323729528498241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88402251096786448303981237 8287711040323729528498241)
              ·
                refine ⟨6215783280242797146373681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8287711040323729528498241 6215783280242797146373681)
                ·
                  refine ⟨4661837460182097859780261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6215783280242797146373681 4661837460182097859780261)
                  ·
                    refine ⟨874094523784143348708799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4661837460182097859780261 874094523784143348708799)
                    ·
                      rfl

theorem cell23_5106879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 4].length) (baseStart_5106879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106879 prefixEnd_5106879 := by exact prefixLift 5106879
  have htrace : WordTrace (prefixWord ++ tailWord_5106879) baseStart_5106879 baseEnd_5106879 := by
    simpa [prefixWord, tailWord_5106879, baseEnd_5106879] using wordTrace_append hprefix tailTrace_5106879
  have hstable : (prefixWord ++ tailWord_5106879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106879).length < 2 ^ (prefixWord ++ tailWord_5106879).sum := by decide
  have hdescent : baseEnd_5106879 < baseStart_5106879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106885 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 7]
def baseStart_5106885 : Nat := 118140960795 + 5106885 * 2 ^ 59
def prefixEnd_5106885 : Nat := 4983230072969 + 3 ^ 40 * 5106885 * 2
def baseEnd_5106885 : Nat := 2622286652236357022651369

theorem tailTrace_5106885 : CollatzResearch.WordTrace tailWord_5106885 prefixEnd_5106885 2622286652236357022651369 := by
  unfold tailWord_5106885
  simp only [CollatzResearch.WordTrace]
  refine ⟨186263398103635306364794109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124175598735756870909862739 186263398103635306364794109)
  ·
    refine ⟨69848774288863239886797791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 186263398103635306364794109 69848774288863239886797791)
    ·
      refine ⟨104773161433294859830196687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69848774288863239886797791 104773161433294859830196687)
      ·
        refine ⟨157159742149942289745295031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104773161433294859830196687 157159742149942289745295031)
        ·
          refine ⟨235739613224913434617942547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157159742149942289745295031 235739613224913434617942547)
          ·
            refine ⟨353609419837370151926913821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235739613224913434617942547 353609419837370151926913821)
            ·
              refine ⟨132603532439013806972592683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 353609419837370151926913821 132603532439013806972592683)
              ·
                refine ⟨198905298658520710458889025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132603532439013806972592683 198905298658520710458889025)
                ·
                  refine ⟨149178973993890532844166769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198905298658520710458889025 149178973993890532844166769)
                  ·
                    refine ⟨111884230495417899633125077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 149178973993890532844166769 111884230495417899633125077)
                    ·
                      refine ⟨2622286652236357022651369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 111884230495417899633125077 2622286652236357022651369)
                      ·
                        rfl

theorem cell23_5106885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_5106885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106885 prefixEnd_5106885 := by exact prefixLift 5106885
  have htrace : WordTrace (prefixWord ++ tailWord_5106885) baseStart_5106885 baseEnd_5106885 := by
    simpa [prefixWord, tailWord_5106885, baseEnd_5106885] using wordTrace_append hprefix tailTrace_5106885
  have hstable : (prefixWord ++ tailWord_5106885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106885).length < 2 ^ (prefixWord ++ tailWord_5106885).sum := by decide
  have hdescent : baseEnd_5106885 < baseStart_5106885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106895 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 6]
def baseStart_5106895 : Nat := 118140960795 + 5106895 * 2 ^ 59
def prefixEnd_5106895 : Nat := 4983230072969 + 3 ^ 40 * 5106895 * 2
def baseEnd_5106895 : Nat := 2622291787042901983526323

theorem tailTrace_5106895 : CollatzResearch.WordTrace tailWord_5106895 prefixEnd_5106895 2622291787042901983526323 := by
  unfold tailWord_5106895
  simp only [CollatzResearch.WordTrace]
  refine ⟨186263762833599078072658139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124175841889066052048438759 186263762833599078072658139)
  ·
    refine ⟨279395644250398617108987209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 186263762833599078072658139 279395644250398617108987209)
    ·
      refine ⟨209546733187798962831740407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279395644250398617108987209 209546733187798962831740407)
      ·
        refine ⟨314320099781698444247610611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209546733187798962831740407 314320099781698444247610611)
        ·
          refine ⟨471480149672547666371415917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314320099781698444247610611 471480149672547666371415917)
          ·
            refine ⟨176805056127205374889280969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 471480149672547666371415917 176805056127205374889280969)
            ·
              refine ⟨132603792095404031166960727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176805056127205374889280969 132603792095404031166960727)
              ·
                refine ⟨198905688143106046750441091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132603792095404031166960727 198905688143106046750441091)
                ·
                  refine ⟨298358532214659070125661637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198905688143106046750441091 298358532214659070125661637)
                  ·
                    refine ⟨55942224790248575648561557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 298358532214659070125661637 55942224790248575648561557)
                    ·
                      refine ⟨2622291787042901983526323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55942224790248575648561557 2622291787042901983526323)
                      ·
                        rfl

theorem cell23_5106895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_5106895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106895 prefixEnd_5106895 := by exact prefixLift 5106895
  have htrace : WordTrace (prefixWord ++ tailWord_5106895) baseStart_5106895 baseEnd_5106895 := by
    simpa [prefixWord, tailWord_5106895, baseEnd_5106895] using wordTrace_append hprefix tailTrace_5106895
  have hstable : (prefixWord ++ tailWord_5106895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106895).length < 2 ^ (prefixWord ++ tailWord_5106895).sum := by decide
  have hdescent : baseEnd_5106895 < baseStart_5106895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106909 : List Nat := [1, 4, 3, 2, 2, 1, 1, 9]
def baseStart_5106909 : Nat := 118140960795 + 5106909 * 2 ^ 59
def prefixEnd_5106909 : Nat := 4983230072969 + 3 ^ 40 * 5106909 * 2
def baseEnd_5106909 : Nat := 97122184287854256620417

theorem tailTrace_5106909 : CollatzResearch.WordTrace tailWord_5106909 prefixEnd_5106909 97122184287854256620417 := by
  unfold tailWord_5106909
  simp only [CollatzResearch.WordTrace]
  refine ⟨186264273455548358463667781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124176182303698905642445187 186264273455548358463667781)
  ·
    refine ⟨34924551272915317211937709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 186264273455548358463667781 34924551272915317211937709)
    ·
      refine ⟨13096706727343243954476641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34924551272915317211937709 13096706727343243954476641)
      ·
        refine ⟨9822530045507432965857481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13096706727343243954476641 9822530045507432965857481)
        ·
          refine ⟨7366897534130574724393111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9822530045507432965857481 7366897534130574724393111)
          ·
            refine ⟨11050346301195862086589667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7366897534130574724393111 11050346301195862086589667)
            ·
              refine ⟨16575519451793793129884501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11050346301195862086589667 16575519451793793129884501)
              ·
                refine ⟨97122184287854256620417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16575519451793793129884501 97122184287854256620417)
                ·
                  rfl

theorem cell23_5106909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 9].length) (baseStart_5106909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106909 prefixEnd_5106909 := by exact prefixLift 5106909
  have htrace : WordTrace (prefixWord ++ tailWord_5106909) baseStart_5106909 baseEnd_5106909 := by
    simpa [prefixWord, tailWord_5106909, baseEnd_5106909] using wordTrace_append hprefix tailTrace_5106909
  have hstable : (prefixWord ++ tailWord_5106909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106909).length < 2 ^ (prefixWord ++ tailWord_5106909).sum := by decide
  have hdescent : baseEnd_5106909 < baseStart_5106909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106929 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 5, 3, 2]
def baseStart_5106929 : Nat := 118140960795 + 5106929 * 2 ^ 59
def prefixEnd_5106929 : Nat := 4983230072969 + 3 ^ 40 * 5106929 * 2
def baseEnd_5106929 : Nat := 2622309245385154850501167

theorem tailTrace_5106929 : CollatzResearch.WordTrace tailWord_5106929 prefixEnd_5106929 2622309245385154850501167 := by
  unfold tailWord_5106929
  simp only [CollatzResearch.WordTrace]
  refine ⟨186265002915475901879395841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124176668610317267919597227 186265002915475901879395841)
  ·
    refine ⟨139698752186606926409546881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186265002915475901879395841 139698752186606926409546881)
    ·
      refine ⟨104774064139955194807160161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139698752186606926409546881 104774064139955194807160161)
      ·
        refine ⟨78580548104966396105370121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104774064139955194807160161 78580548104966396105370121)
        ·
          refine ⟨58935411078724797079027591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78580548104966396105370121 58935411078724797079027591)
          ·
            refine ⟨88403116618087195618541387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58935411078724797079027591 88403116618087195618541387)
            ·
              refine ⟨132604674927130793427812081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88403116618087195618541387 132604674927130793427812081)
              ·
                refine ⟨99453506195348095070859061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132604674927130793427812081 99453506195348095070859061)
                ·
                  refine ⟨9323766205813883912893037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99453506195348095070859061 9323766205813883912893037)
                  ·
                    refine ⟨3496412327180206467334889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9323766205813883912893037 3496412327180206467334889)
                    ·
                      refine ⟨2622309245385154850501167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496412327180206467334889 2622309245385154850501167)
                      ·
                        rfl

theorem cell23_5106929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_5106929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106929 prefixEnd_5106929 := by exact prefixLift 5106929
  have htrace : WordTrace (prefixWord ++ tailWord_5106929) baseStart_5106929 baseEnd_5106929 := by
    simpa [prefixWord, tailWord_5106929, baseEnd_5106929] using wordTrace_append hprefix tailTrace_5106929
  have hstable : (prefixWord ++ tailWord_5106929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106929).length < 2 ^ (prefixWord ++ tailWord_5106929).sum := by decide
  have hdescent : baseEnd_5106929 < baseStart_5106929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5106993 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 2, 2, 2]
def baseStart_5106993 : Nat := 118140960795 + 5106993 * 2 ^ 59
def prefixEnd_5106993 : Nat := 4983230072969 + 3 ^ 40 * 5106993 * 2
def baseEnd_5106993 : Nat := 2622342108147042600100873

theorem tailTrace_5106993 : CollatzResearch.WordTrace tailWord_5106993 prefixEnd_5106993 2622342108147042600100873 := by
  unfold tailWord_5106993
  simp only [CollatzResearch.WordTrace]
  refine ⟨186267337187244040809725633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124178224791496027206483755 186267337187244040809725633)
  ·
    refine ⟨139700502890433030607294225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 186267337187244040809725633 139700502890433030607294225)
    ·
      refine ⟨104775377167824772955470669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139700502890433030607294225 104775377167824772955470669)
      ·
        refine ⟨39290766437934289858301501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104775377167824772955470669 39290766437934289858301501)
        ·
          refine ⟨14734037414225358696863063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39290766437934289858301501 14734037414225358696863063)
          ·
            refine ⟨22101056121338038045294595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14734037414225358696863063 22101056121338038045294595)
            ·
              refine ⟨33151584182007057067941893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22101056121338038045294595 33151584182007057067941893)
              ·
                refine ⟨6215922034126323200239105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33151584182007057067941893 6215922034126323200239105)
                ·
                  refine ⟨4661941525594742400179329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6215922034126323200239105 4661941525594742400179329)
                  ·
                    refine ⟨3496456144196056800134497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4661941525594742400179329 3496456144196056800134497)
                    ·
                      refine ⟨2622342108147042600100873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3496456144196056800134497 2622342108147042600100873)
                      ·
                        rfl

theorem cell23_5106993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_5106993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5106993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5106993 prefixEnd_5106993 := by exact prefixLift 5106993
  have htrace : WordTrace (prefixWord ++ tailWord_5106993) baseStart_5106993 baseEnd_5106993 := by
    simpa [prefixWord, tailWord_5106993, baseEnd_5106993] using wordTrace_append hprefix tailTrace_5106993
  have hstable : (prefixWord ++ tailWord_5106993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5106993).length < 2 ^ (prefixWord ++ tailWord_5106993).sum := by decide
  have hdescent : baseEnd_5106993 < baseStart_5106993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5106993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
